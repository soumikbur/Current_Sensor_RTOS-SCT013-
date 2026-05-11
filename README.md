# STM32 FreeRTOS True RMS Current Monitor (SCT013)

A FreeRTOS-based STM32 firmware project for accurate AC current measurement using the SCT013-5A/1V split-core current transformer and STM32F410RBTx microcontroller.

The system performs high-speed ADC sampling using DMA, calculates True RMS current values, applies piecewise linear calibration for sensor correction, and tracks load activity using a real-time state machine.

---

## Features

* True RMS current calculation
* ADC + DMA high-speed waveform sampling
* 2048-sample RMS processing buffer
* Piecewise linear calibration table
* Deadband noise filtering
* FreeRTOS task-based architecture
* UART telemetry output
* Load ON/OFF state detection
* Session uptime and cycle tracking

---

## FreeRTOS Architecture

### Task 1 (Default Task)

* Waits for ADC DMA completion
* Computes RMS current
* Applies calibration logic
* Updates load state machine

### Task 2 (Process Task)

* Formats telemetry data
* Sends UART output every 500ms
* Runs independently without blocking ADC acquisition

---

## Signal Processing

### True RMS Measurement

The ADC continuously samples the AC waveform through DMA.

The firmware calculates:

RMS = sqrt(mean(x²))

This enables accurate current monitoring even for non-sinusoidal loads.

---

### Piecewise Linear Calibration

The SCT013 sensor becomes progressively non-linear at higher currents.

To correct this, a 6-point lookup table is used:

static const float cal_raw[] = {
0.00f,
0.0154f,
0.0310f,
0.0462f,
0.1343f,
0.1532f
};

static const float cal_true[] = {
0.00f,
0.77f,
1.55f,
2.31f,
5.16f,
7.66f
};

Linear interpolation is performed between points for accurate scaling.

---

### Deadband Noise Filter

Residual electrical noise below approximately 9mV RMS is automatically clamped to:

0.000 A

This prevents phantom current readings when the load is OFF.

---

## Hardware Requirements

### MCU

* STM32F410RBTx

### Sensor

* SCT013-5A/1V Current Transformer

### Signal Conditioning

* AC biasing circuit centered at VDD / 2

### Test Loads

* 3 × 200W incandescent bulbs
* Hairdryer (Low / High)

---

## Pin Configuration

PA0 → ADC1_IN0 (SCT013 input)
PA2 → USART2_TX
PA3 → USART2_RX

---

## UART Telemetry

Baud Rate:
115200

Example Output:

=== SCT013 | Piecewise Cal | Max=7.66A ===

Raw V: 0.0000 | Irms: 0.000 A | Norm: 0.000 | State: OFF

Raw V: 0.0154 | Irms: 0.770 A | Norm: 0.100 | State: ON

Raw V: 0.0462 | Irms: 2.310 A | Norm: 0.301 | State: ON

Raw V: 0.1532 | Irms: 7.660 A | Norm: 1.000 | State: ON

---

## Calibration Procedure

1. Connect a multimeter in series with the load
2. Turn ON a known load
3. Observe `Raw V` in UART terminal
4. Compare with multimeter current reading
5. Update:

   * `cal_raw[]`
   * `cal_true[]`
6. Rebuild and flash firmware

---

## Building the Project

1. Open project in STM32CubeIDE
2. Build project
3. Flash STM32F410 board
4. Open UART terminal at 115200 baud

---

## Tools Used

* STM32CubeIDE
* FreeRTOS
* STM32 HAL Drivers
* UART Serial Monitor

---

## Author

Soumik Ghosh
