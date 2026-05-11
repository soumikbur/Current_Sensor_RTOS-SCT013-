/* USER CODE BEGIN Header */
/**
 ******************************************************************************
 * @file           : main.c
 * @brief          : SCT013-5A/1V | STM32F410RBTx | FreeRTOS
 * True RMS + Piecewise Calibration + ON/OFF/Cycle + Timer
 *
 * CALIBRATION METHOD (v8 - Updated for 6 points + Deadband + Raw tracking):
 * Single CALIBRATION_FACTOR is REMOVED.
 * Replaced with a 6-point piecewise linear lookup table built from
 * actual multimeter measurements across the full load range.
 *
 * Measured data (3 × 200W bulbs + Hairdryer, 230V India):
 * ┌────────────────┬────────────────┼─────────────────┐
 * │      Load      │ Sensor (raw V) │ Multimeter (true)│
 * ├────────────────┼────────────────┼─────────────────┤
 * │      0         │   0.0000       │    0.000 A      │
 * │      1 Bulb    │   0.0154       │    0.770 A      │
 * │      2 Bulbs   │   0.0310       │    1.550 A      │
 * │      3 Bulbs   │   0.0462       │    2.310 A      │
 * │ Hairdryer Low  │   0.1343       │    5.160 A      │
 * │ Hairdryer High │   0.1532       │    7.660 A      │
 * └────────────────┴────────────────┴─────────────────┘
 *
 * Why non-linear?
 * The SCT013-5A/1V internal burden resistor becomes slightly non-linear
 * at higher currents, causing the sensor to underread progressively.
 * Piecewise interpolation corrects this accurately across full range.
 *
 * THRESHOLDS:
 * NOISE_FLOOR   : 0.10A (above ~0.083A noise when load is OFF)
 * DEBOUNCE_HIGH : 0.30A (confirmed ON — safely above noise)
 * IRMS_MAX      : 7.66A (Hairdryer High = full scale → Norm 1.000)
 *
 * HARDWARE:
 * PA0 = ADC1_IN0  (SCT013 conditioning PCB output)
 * PA2 = USART2_TX
 * PA3 = USART2_RX
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
#define ADC_BUF_SIZE 2048
#define VDDA 3.3f
#define ADC_MAX 4095.0f
#define V_MIDPOINT (VDDA / 2.0f)

/* ── 6-Point Piecewise calibration table ────────────────────────────────────
 * cal_raw[]  = Raw VRMS from the sensor
 * cal_true[] = Actual multimeter measurements (3 bulbs + Hairdryer High/Low)
 * ────────────────────────────────────────────────────────────────────────── */
#define CAL_POINTS 6

static const float cal_raw[]  = {0.00f, 0.0138f, 0.0246f, 0.0356f, 0.0790f, 0.1178f};
static const float cal_true[] = {0.00f, 0.77f,   1.55f,   2.31f,   5.16f,   7.66f};

/* ── Normalization ────────────────────────────────────────────────────────── */
/* Full scale = Hairdryer High (7.66A) → Norm 1.000                          */
#define IRMS_MAX 7.66f

/* ── State machine thresholds ─────────────────────────────────────────────── */
#define NOISE_FLOOR 0.10f   /* A — above residual noise when OFF       */
#define DEBOUNCE_HIGH 0.30f /* A — confirmed load ON                   */

/* USER CODE END PD */

/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef hadc1;
DMA_HandleTypeDef hdma_adc1;
UART_HandleTypeDef huart2;

osThreadId_t defaultTaskHandle;
const osThreadAttr_t defaultTask_attributes = {
    .name = "defaultTask",
    .stack_size = 512 * 4,
    .priority = (osPriority_t)osPriorityNormal,
};
osThreadId_t ProcessTaskHandle;
const osThreadAttr_t ProcessTask_attributes = {
    .name = "ProcessTask",
    .stack_size = 256 * 4,
    .priority = (osPriority_t)osPriorityNormal,
};

/* USER CODE BEGIN PV */
uint16_t adc_buffer[ADC_BUF_SIZE];

osSemaphoreId_t dma_done_sem;
const osSemaphoreAttr_t dma_done_sem_attr = {.name = "DmaDone"};

/* ── Shared results ──────────────────────────────────────────────────────── */
volatile float g_irms = 0.0f;
volatile float g_raw_vrms = 0.0f;
volatile float g_normalized = 0.0f;
volatile uint8_t g_load_on = 0;
volatile uint32_t g_on_count = 0;
volatile uint32_t g_off_count = 0;
volatile uint32_t g_cycles = 0;

/* ── Timer variables ─────────────────────────────────────────────────────── */
volatile uint32_t g_on_start_tick = 0;
volatile uint32_t g_session_on_ms = 0;
volatile uint32_t g_total_on_ms = 0;

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
static float calculate_irms_raw(void);
static float apply_calibration(float raw_irms);
static void update_state_machine(float irms);
static void uart_send(const char *msg);
static void format_duration(uint32_t ms, char *buf, int buf_size);
/* USER CODE END PFP */

/* USER CODE BEGIN 0 */

void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef *hadc)
{
    if (hadc->Instance == ADC1)
        osSemaphoreRelease(dma_done_sem);
}

/* ── True RMS (raw, before calibration correction) ──────────────────────── */
static float calculate_irms_raw(void)
{
    float sum_sq = 0.0f;
    for (int i = 0; i < ADC_BUF_SIZE; i++)
    {
        float v = ((float)adc_buffer[i] / ADC_MAX) * VDDA;
        float v_ac = v - V_MIDPOINT;
        sum_sq += (v_ac * v_ac);
    }

    float vrms = sqrtf(sum_sq / (float)ADC_BUF_SIZE);

    /* --- NEW DEADBAND / NOISE FILTER --- */
    /* If the raw VRMS is below ~9mV (typical noise), force it to 0.0 */
    /* This prevents background noise from being amplified into "phantom" current */
    if (vrms < 0.009f)
    {
        vrms = 0.0f;
    }

    return vrms;
}

/* ── Piecewise linear calibration ────────────────────────────────────────────
 *
 * Maps raw sensor reading → true current using the measured lookup table.
 *
 * Method: find which segment of cal_raw[] the input falls in, then
 * interpolate linearly between the two surrounding calibration points.
 * ────────────────────────────────────────────────────────────────────────── */
static float apply_calibration(float raw)
{
    /* Below minimum or above maximum: clamp to table edges */
    if (raw <= cal_raw[0])
        return cal_true[0];
    if (raw >= cal_raw[CAL_POINTS - 1])
    {
        /* Extrapolate beyond last point using last segment slope */
        float slope = (cal_true[CAL_POINTS - 1] - cal_true[CAL_POINTS - 2]) / (cal_raw[CAL_POINTS - 1] - cal_raw[CAL_POINTS - 2]);
        return cal_true[CAL_POINTS - 1] + slope * (raw - cal_raw[CAL_POINTS - 1]);
    }

    /* Find the correct segment */
    for (int i = 0; i < CAL_POINTS - 1; i++)
    {
        if (raw >= cal_raw[i] && raw < cal_raw[i + 1])
        {
            /* Linear interpolation within this segment */
            float t = (raw - cal_raw[i]) / (cal_raw[i + 1] - cal_raw[i]);
            return cal_true[i] + t * (cal_true[i + 1] - cal_true[i]);
        }
    }
    return raw; /* fallback — should never reach here */
}

/* ── Format ms → "HHh MMm SSs" ──────────────────────────────────────────── */
static void format_duration(uint32_t ms, char *buf, int buf_size)
{
    uint32_t total_sec = ms / 1000;
    uint32_t hours = total_sec / 3600;
    uint32_t minutes = (total_sec % 3600) / 60;
    uint32_t seconds = total_sec % 60;
    snprintf(buf, buf_size, "%02luh %02lum %02lus", hours, minutes, seconds);
}

/* ── State machine ───────────────────────────────────────────────────────── */
static void update_state_machine(float irms)
{
    uint32_t now = osKernelGetTickCount();

    if (g_load_on == 0)
    {
        if (irms >= DEBOUNCE_HIGH)
        {
            g_load_on = 1;
            g_on_count++;
            g_on_start_tick = now;
            g_session_on_ms = 0;
        }
    }
    else
    {
        g_session_on_ms = now - g_on_start_tick;

        if (irms < NOISE_FLOOR)
        {
            g_total_on_ms += g_session_on_ms;
            g_session_on_ms = 0;
            g_load_on = 0;
            g_off_count++;
            g_cycles++;
        }
    }

    if (g_load_on == 0)
    {
        g_normalized = 0.0f;
        g_irms = 0.0f;
    }
    else
    {
        float norm = irms / IRMS_MAX;
        if (norm > 1.0f)
            norm = 1.0f;
        g_normalized = norm;
        g_irms = irms;
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
    ProcessTaskHandle = osThreadNew(StartTask02, NULL, &ProcessTask_attributes);

    osKernelStart();
    while (1)
    {
    }
}

/* ════════════════════════════════════════════════════════════════════════════
 * TASK 1 — defaultTask  (ADC → raw RMS → calibration table → state machine)
 * ════════════════════════════════════════════════════════════════════════════*/
void StartDefaultTask(void *argument)
{
    /* USER CODE BEGIN 5 */
    if (HAL_ADC_Start_DMA(&hadc1, (uint32_t *)adc_buffer, ADC_BUF_SIZE) != HAL_OK)
    {
        uart_send("ERROR: ADC DMA start failed\r\n");
        Error_Handler();
    }

    uart_send("=== SCT013 | Piecewise Cal | Max=7.66A ===\r\n");

    for (;;)
    {
        osSemaphoreAcquire(dma_done_sem, osWaitForever);

        float raw = calculate_irms_raw();    /* sensor reading              */
        g_raw_vrms = raw;                    /* Track raw voltage for debugging */
        float irms = apply_calibration(raw); /* corrected via lookup table  */

        update_state_machine(irms);
    }
    /* USER CODE END 5 */
}

/* ════════════════════════════════════════════════════════════════════════════
 * TASK 2 — ProcessTask  (UART print every 500 ms)
 * ════════════════════════════════════════════════════════════════════════════*/
void StartTask02(void *argument)
{
    /* USER CODE BEGIN StartTask02 */
    osDelay(300);

    char session_str[16];
    char total_str[16];

    for (;;)
    {
        float irms = g_irms;
        float norm = g_normalized;
        uint8_t state = g_load_on;
        uint32_t on_cnt = g_on_count;
        uint32_t off_cnt = g_off_count;
        uint32_t cycles = g_cycles;
        uint32_t session_ms = g_session_on_ms;
        uint32_t total_ms = g_total_on_ms + session_ms;

        format_duration(session_ms, session_str, sizeof(session_str));
        format_duration(total_ms, total_str, sizeof(total_str));

        int len = snprintf(uart_buf, sizeof(uart_buf),
                           "Raw V: %.4f | Irms: %.3f A | Norm: %.3f | State: %-3s | "
                           "ON:%lu OFF:%lu Cyc:%lu | "
                           "Session: %s | Total: %s\r\n",
                           g_raw_vrms, irms, norm,
                           state ? "ON" : "OFF",
                           on_cnt, off_cnt, cycles,
                           session_str, total_str);

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
    RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSI;
    RCC_OscInitStruct.HSIState = RCC_HSI_ON;
    RCC_OscInitStruct.HSICalibrationValue = RCC_HSICALIBRATION_DEFAULT;
    RCC_OscInitStruct.PLL.PLLState = RCC_PLL_NONE;
    if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
        Error_Handler();
    RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK | RCC_CLOCKTYPE_SYSCLK | RCC_CLOCKTYPE_PCLK1 | RCC_CLOCKTYPE_PCLK2;
    RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_HSI;
    RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
    RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV1;
    RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;
    if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_0) != HAL_OK)
        Error_Handler();
}

static void MX_ADC1_Init(void)
{
    ADC_ChannelConfTypeDef sConfig = {0};
    hadc1.Instance = ADC1;
    hadc1.Init.ClockPrescaler = ADC_CLOCK_SYNC_PCLK_DIV2;
    hadc1.Init.Resolution = ADC_RESOLUTION_12B;
    hadc1.Init.ScanConvMode = DISABLE;
    hadc1.Init.ContinuousConvMode = ENABLE;
    hadc1.Init.DiscontinuousConvMode = DISABLE;
    hadc1.Init.ExternalTrigConvEdge = ADC_EXTERNALTRIGCONVEDGE_NONE;
    hadc1.Init.ExternalTrigConv = ADC_SOFTWARE_START;
    hadc1.Init.DataAlign = ADC_DATAALIGN_RIGHT;
    hadc1.Init.NbrOfConversion = 1;
    hadc1.Init.DMAContinuousRequests = ENABLE;
    hadc1.Init.EOCSelection = ADC_EOC_SINGLE_CONV;
    if (HAL_ADC_Init(&hadc1) != HAL_OK)
        Error_Handler();
    sConfig.Channel = ADC_CHANNEL_0;
    sConfig.Rank = 1;
    sConfig.SamplingTime = ADC_SAMPLETIME_144CYCLES;
    if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
        Error_Handler();
}

static void MX_USART2_UART_Init(void)
{
    huart2.Instance = USART2;
    huart2.Init.BaudRate = 115200;
    huart2.Init.WordLength = UART_WORDLENGTH_8B;
    huart2.Init.StopBits = UART_STOPBITS_1;
    huart2.Init.Parity = UART_PARITY_NONE;
    huart2.Init.Mode = UART_MODE_TX_RX;
    huart2.Init.HwFlowCtl = UART_HWCONTROL_NONE;
    huart2.Init.OverSampling = UART_OVERSAMPLING_16;
    if (HAL_UART_Init(&huart2) != HAL_OK)
        Error_Handler();
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
    if (htim->Instance == TIM6)
        HAL_IncTick();
}

void Error_Handler(void)
{
    __disable_irq();
    while (1)
    {
    }
}

#ifdef USE_FULL_ASSERT
void assert_failed(uint8_t *file, uint32_t line) {}
#endif
