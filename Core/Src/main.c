/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : SCT013-5A/1V | STM32F410RBTx | FreeRTOS
  *                   True RMS + Normalization + ON/OFF/Cycle Counters + Timer
  *
  * CALIBRATION:
  *   CALIBRATION_FACTOR : 6.5   (raw 0.120A × 6.5 = 0.780A multimeter)
  *   IRMS_MAX           : 0.78A (maps to Norm 1.000)
  *   NOISE_FLOOR        : 0.10A (above noise ~0.083A when load is OFF)
  *   DEBOUNCE_HIGH      : 0.25A (confirmed ON threshold)
  *
  * NEW IN v7:
  *   Load ON duration timer — tracks how long the load has been ON.
  *   Uses FreeRTOS osKernelGetTickCount() (1 tick = 1 ms).
  *   Two values reported:
  *     - Current session ON time : how long load has been ON this time
  *     - Total ON time           : cumulative across all ON cycles
  *
  * UART OUTPUT FORMAT (115200 baud, every 500 ms):
  *   When ON:
  *     Irms: 0.780 A | Norm: 1.000 | State: ON  | ON: 1 | OFF: 0 | Cycles: 0 | OnTime: 00h 00m 05s | Total: 00h 00m 05s
  *   When OFF:
  *     Irms: 0.000 A | Norm: 0.000 | State: OFF | ON: 1 | OFF: 1 | Cycles: 1 | OnTime: 00h 00m 00s | Total: 00h 00m 12s
  *
  * HARDWARE:
  *   PA0 = ADC1_IN0  (SCT013 conditioning PCB output)
  *   PA2 = USART2_TX
  *   PA3 = USART2_RX
  ******************************************************************************
  */
/* USER CODE END Header */

#include "main.h"
#include "cmsis_os.h"

/* USER CODE BEGIN Includes */
#include <stdio.h>
#include <string.h>
#include <math.h>
/* USER CODE END Includes */

/* USER CODE BEGIN PD */
#define ADC_BUF_SIZE        2048
#define VDDA                3.3f
#define ADC_MAX             4095.0f
#define V_MIDPOINT          (VDDA / 2.0f)
#define SCT013_SENSITIVITY  5.0f
#define CALIBRATION_FACTOR  6.5f
#define IRMS_MAX            0.78f
#define NOISE_FLOOR         0.10f
#define DEBOUNCE_HIGH       0.25f
/* USER CODE END PD */

/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef hadc1;
DMA_HandleTypeDef hdma_adc1;
UART_HandleTypeDef huart2;

osThreadId_t defaultTaskHandle;
const osThreadAttr_t defaultTask_attributes = {
  .name       = "defaultTask",
  .stack_size = 512 * 4,
  .priority   = (osPriority_t) osPriorityNormal,
};
osThreadId_t ProcessTaskHandle;
const osThreadAttr_t ProcessTask_attributes = {
  .name       = "ProcessTask",
  .stack_size = 256 * 4,
  .priority   = (osPriority_t) osPriorityNormal,
};

/* USER CODE BEGIN PV */
uint16_t adc_buffer[ADC_BUF_SIZE];

osSemaphoreId_t dma_done_sem;
const osSemaphoreAttr_t dma_done_sem_attr = { .name = "DmaDone" };

/* ── Shared results ──────────────────────────────────────────────────────── */
volatile float    g_irms            = 0.0f;
volatile float    g_normalized      = 0.0f;
volatile uint8_t  g_load_on         = 0;
volatile uint32_t g_on_count        = 0;
volatile uint32_t g_off_count       = 0;
volatile uint32_t g_cycles          = 0;

/* ── Timer variables ─────────────────────────────────────────────────────── */
volatile uint32_t g_on_start_tick   = 0;  /* tick when load switched ON        */
volatile uint32_t g_session_on_ms   = 0;  /* ms load has been ON this session  */
volatile uint32_t g_total_on_ms     = 0;  /* ms load has been ON across all sessions */

char uart_buf[128];
/* USER CODE END PV */

void SystemClock_Config(void);
static void MX_GPIO_Init(void);
static void MX_DMA_Init(void);
static void MX_ADC1_Init(void);
static void MX_USART2_UART_Init(void);
void StartDefaultTask(void *argument);
void StartTask02(void *argument);

/* USER CODE BEGIN PFP */
static float calculate_irms_true(void);
static void  update_state_machine(float irms);
static void  uart_send(const char *msg);
static void  format_duration(uint32_t ms, char *buf, int buf_size);
/* USER CODE END PFP */

/* USER CODE BEGIN 0 */

void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef *hadc)
{
    if (hadc->Instance == ADC1)
        osSemaphoreRelease(dma_done_sem);
}

/* ── True RMS ────────────────────────────────────────────────────────────── */
static float calculate_irms_true(void)
{
    float sum_sq = 0.0f;
    for (int i = 0; i < ADC_BUF_SIZE; i++)
    {
        float v    = ((float)adc_buffer[i] / ADC_MAX) * VDDA;
        float v_ac = v - V_MIDPOINT;
        sum_sq    += (v_ac * v_ac);
    }
    float vrms = sqrtf(sum_sq / (float)ADC_BUF_SIZE);
    float irms = vrms * SCT013_SENSITIVITY * CALIBRATION_FACTOR;
    return (irms < 0.0f) ? 0.0f : irms;
}

/* ── Format ms duration → "HHh MMm SSs" string ──────────────────────────── */
static void format_duration(uint32_t ms, char *buf, int buf_size)
{
    uint32_t total_sec = ms / 1000;
    uint32_t hours     = total_sec / 3600;
    uint32_t minutes   = (total_sec % 3600) / 60;
    uint32_t seconds   = total_sec % 60;
    snprintf(buf, buf_size, "%02luh %02lum %02lus", hours, minutes, seconds);
}

/* ── State machine ───────────────────────────────────────────────────────────
 *
 *  OFF → ON  : Irms >= DEBOUNCE_HIGH
 *                → g_on_count++
 *                → record g_on_start_tick (current tick)
 *
 *  ON  → OFF : Irms < NOISE_FLOOR
 *                → g_off_count++, g_cycles++
 *                → compute session duration, add to g_total_on_ms
 *                → reset g_session_on_ms = 0
 *
 *  While ON  : g_session_on_ms = current_tick - g_on_start_tick (live update)
 *
 * ────────────────────────────────────────────────────────────────────────── */
static void update_state_machine(float irms)
{
    uint32_t now = osKernelGetTickCount();   /* 1 tick = 1 ms */

    if (g_load_on == 0)
    {
        /* Currently OFF */
        if (irms >= DEBOUNCE_HIGH)
        {
            g_load_on       = 1;
            g_on_count++;
            g_on_start_tick = now;          /* start the stopwatch             */
            g_session_on_ms = 0;
        }
    }
    else
    {
        /* Currently ON — update live session timer every cycle */
        g_session_on_ms = now - g_on_start_tick;

        if (irms < NOISE_FLOOR)
        {
            /* Load switched OFF */
            g_total_on_ms  += g_session_on_ms; /* bank the session time        */
            g_session_on_ms = 0;               /* reset current session        */
            g_load_on       = 0;
            g_off_count++;
            g_cycles++;
        }
    }

    /* Update shared display values */
    if (g_load_on == 0)
    {
        g_normalized = 0.0f;
        g_irms       = 0.0f;
    }
    else
    {
        float norm = irms / IRMS_MAX;
        if (norm > 1.0f) norm = 1.0f;
        g_normalized = norm;
        g_irms       = irms;
    }
}

static void uart_send(const char *msg)
{
    HAL_UART_Transmit(&huart2, (uint8_t *)msg, (uint16_t)strlen(msg), 200);
}

/* USER CODE END 0 */

int main(void)
{
    HAL_Init();
    SystemClock_Config();
    MX_GPIO_Init();
    MX_DMA_Init();
    MX_ADC1_Init();
    MX_USART2_UART_Init();
    osKernelInitialize();

    /* USER CODE BEGIN RTOS_SEMAPHORES */
    dma_done_sem = osSemaphoreNew(1, 0, &dma_done_sem_attr);
    /* USER CODE END RTOS_SEMAPHORES */

    defaultTaskHandle = osThreadNew(StartDefaultTask, NULL, &defaultTask_attributes);
    ProcessTaskHandle = osThreadNew(StartTask02,      NULL, &ProcessTask_attributes);

    osKernelStart();
    while (1) {}
}

/* ════════════════════════════════════════════════════════════════════════════
 * TASK 1 — defaultTask  (ADC → RMS → state machine)
 * ════════════════════════════════════════════════════════════════════════════*/
void StartDefaultTask(void *argument)
{
    /* USER CODE BEGIN 5 */
    if (HAL_ADC_Start_DMA(&hadc1, (uint32_t *)adc_buffer, ADC_BUF_SIZE) != HAL_OK)
    {
        uart_send("ERROR: ADC DMA start failed\r\n");
        Error_Handler();
    }

    uart_send("=== SCT013 | Cal=6.5 | ON Duration Timer ACTIVE ===\r\n");

    for (;;)
    {
        osSemaphoreAcquire(dma_done_sem, osWaitForever);
        float irms = calculate_irms_true();
        update_state_machine(irms);
    }
    /* USER CODE END 5 */
}

/* ════════════════════════════════════════════════════════════════════════════
 * TASK 2 — ProcessTask  (UART print every 500 ms)
 *
 * Example output sequence (switching on for 12s then off):
 *
 *   Irms: 0.000 A | Norm: 0.000 | State: OFF | ON:0 OFF:0 Cyc:0 | Session: 00h 00m 00s | Total: 00h 00m 00s
 *   Irms: 0.780 A | Norm: 1.000 | State: ON  | ON:1 OFF:0 Cyc:0 | Session: 00h 00m 05s | Total: 00h 00m 05s
 *   Irms: 0.780 A | Norm: 1.000 | State: ON  | ON:1 OFF:0 Cyc:0 | Session: 00h 00m 10s | Total: 00h 00m 10s
 *   Irms: 0.000 A | Norm: 0.000 | State: OFF | ON:1 OFF:1 Cyc:1 | Session: 00h 00m 00s | Total: 00h 00m 12s
 *   Irms: 0.780 A | Norm: 1.000 | State: ON  | ON:2 OFF:1 Cyc:1 | Session: 00h 00m 03s | Total: 00h 00m 15s
 * ════════════════════════════════════════════════════════════════════════════*/
void StartTask02(void *argument)
{
    /* USER CODE BEGIN StartTask02 */
    osDelay(300);

    char session_str[16];
    char total_str[16];

    for (;;)
    {
        /* Snapshot all shared variables atomically */
        float    irms        = g_irms;
        float    norm        = g_normalized;
        uint8_t  state       = g_load_on;
        uint32_t on_cnt      = g_on_count;
        uint32_t off_cnt     = g_off_count;
        uint32_t cycles      = g_cycles;
        uint32_t session_ms  = g_session_on_ms;
        uint32_t total_ms    = g_total_on_ms + session_ms; /* include live session */

        /* Format durations */
        format_duration(session_ms, session_str, sizeof(session_str));
        format_duration(total_ms,   total_str,   sizeof(total_str));

        int len = snprintf(uart_buf, sizeof(uart_buf),
                           "Irms: %.3f A | Norm: %.3f | State: %-3s | "
                           "ON:%lu OFF:%lu Cyc:%lu | "
                           "Session: %s | Total: %s\r\n",
                           irms, norm,
                           state ? "ON" : "OFF",
                           on_cnt, off_cnt, cycles,
                           session_str,
                           total_str);

        if (len > 0)
            HAL_UART_Transmit(&huart2, (uint8_t *)uart_buf, (uint16_t)len, 200);

        osDelay(500);
    }
    /* USER CODE END StartTask02 */
}

/* ─── Peripheral inits ───────────────────────────────────────────────────── */
void SystemClock_Config(void)
{
    RCC_OscInitTypeDef RCC_OscInitStruct = {0};
    RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};
    __HAL_RCC_PWR_CLK_ENABLE();
    __HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE1);
    RCC_OscInitStruct.OscillatorType      = RCC_OSCILLATORTYPE_HSI;
    RCC_OscInitStruct.HSIState            = RCC_HSI_ON;
    RCC_OscInitStruct.HSICalibrationValue = RCC_HSICALIBRATION_DEFAULT;
    RCC_OscInitStruct.PLL.PLLState        = RCC_PLL_NONE;
    if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK) Error_Handler();
    RCC_ClkInitStruct.ClockType      = RCC_CLOCKTYPE_HCLK | RCC_CLOCKTYPE_SYSCLK
                                     | RCC_CLOCKTYPE_PCLK1 | RCC_CLOCKTYPE_PCLK2;
    RCC_ClkInitStruct.SYSCLKSource   = RCC_SYSCLKSOURCE_HSI;
    RCC_ClkInitStruct.AHBCLKDivider  = RCC_SYSCLK_DIV1;
    RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV1;
    RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;
    if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_0) != HAL_OK) Error_Handler();
}

static void MX_ADC1_Init(void)
{
    ADC_ChannelConfTypeDef sConfig = {0};
    hadc1.Instance                   = ADC1;
    hadc1.Init.ClockPrescaler        = ADC_CLOCK_SYNC_PCLK_DIV2;
    hadc1.Init.Resolution            = ADC_RESOLUTION_12B;
    hadc1.Init.ScanConvMode          = DISABLE;
    hadc1.Init.ContinuousConvMode    = ENABLE;
    hadc1.Init.DiscontinuousConvMode = DISABLE;
    hadc1.Init.ExternalTrigConvEdge  = ADC_EXTERNALTRIGCONVEDGE_NONE;
    hadc1.Init.ExternalTrigConv      = ADC_SOFTWARE_START;
    hadc1.Init.DataAlign             = ADC_DATAALIGN_RIGHT;
    hadc1.Init.NbrOfConversion       = 1;
    hadc1.Init.DMAContinuousRequests = ENABLE;
    hadc1.Init.EOCSelection          = ADC_EOC_SINGLE_CONV;
    if (HAL_ADC_Init(&hadc1) != HAL_OK) Error_Handler();
    sConfig.Channel      = ADC_CHANNEL_0;
    sConfig.Rank         = 1;
    sConfig.SamplingTime = ADC_SAMPLETIME_144CYCLES;
    if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK) Error_Handler();
}

static void MX_USART2_UART_Init(void)
{
    huart2.Instance          = USART2;
    huart2.Init.BaudRate     = 115200;
    huart2.Init.WordLength   = UART_WORDLENGTH_8B;
    huart2.Init.StopBits     = UART_STOPBITS_1;
    huart2.Init.Parity       = UART_PARITY_NONE;
    huart2.Init.Mode         = UART_MODE_TX_RX;
    huart2.Init.HwFlowCtl    = UART_HWCONTROL_NONE;
    huart2.Init.OverSampling = UART_OVERSAMPLING_16;
    if (HAL_UART_Init(&huart2) != HAL_OK) Error_Handler();
}

static void MX_DMA_Init(void)
{
    __HAL_RCC_DMA2_CLK_ENABLE();
    HAL_NVIC_SetPriority(DMA2_Stream0_IRQn, 5, 0);
    HAL_NVIC_EnableIRQ(DMA2_Stream0_IRQn);
}

static void MX_GPIO_Init(void)
{
    __HAL_RCC_GPIOA_CLK_ENABLE();
}

void HAL_TIM_PeriodElapsedCallback(TIM_HandleTypeDef *htim)
{
    if (htim->Instance == TIM6) HAL_IncTick();
}

void Error_Handler(void)
{
    __disable_irq();
    while (1) {}
}

#ifdef USE_FULL_ASSERT
void assert_failed(uint8_t *file, uint32_t line) {}
#endif
