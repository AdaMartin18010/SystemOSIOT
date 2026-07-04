# 传感器到操作系统的完整映射


<!-- TOC START -->

- [传感器到操作系统的完整映射](#传感器到操作系统的完整映射)
  - [1. 完整数据路径](#1-完整数据路径)
  - [2. 各层详解](#2-各层详解)
    - [2.1 物理层](#21-物理层)
    - [2.2 设备树描述](#22-设备树描述)
    - [2.3 总线驱动匹配](#23-总线驱动匹配)
    - [2.4 IIO 子系统](#24-iio-子系统)
    - [2.5 Input 子系统](#25-input-子系统)
    - [2.6 hwmon / thermal](#26-hwmon--thermal)
  - [3. 用户态访问方式](#3-用户态访问方式)
  - [4. 场景分析](#4-场景分析)
  - [5. 跨层映射表](#5-跨层映射表)
  - [6. 相关文件](#6-相关文件)
  - [国际权威来源链接 | International Authoritative Sources](#国际权威来源链接--international-authoritative-sources)

<!-- TOC END -->

> **目标**：展示一个典型传感器如何从硬件连接到 Linux 用户态应用，涉及总线、驱动、子系统、sysfs、API。

---

## 1. 完整数据路径

```mermaid
graph LR
    A[物理传感器] -->|I2C/SPI/UART| B[SoC 外设控制器]
    B -->|I2C/SPI/UART Controller Driver| C[Linux Bus Core]
    C -->|Device Tree Match| D[Sensor Driver]
    D -->|Industrial I/O| E[IIO Subsystem]
    E -->|sysfs| F[/sys/bus/iio/devices/iio:device0/]
    F -->|read| G[用户态应用]
    D -->|中断| H[kernel event]
    H -->|input subsystem| I[/dev/input/event0]
```

---

## 2. 各层详解

### 2.1 物理层

| 接口 | 典型传感器 | 关键信号 |
|------|------------|----------|
| I2C | BME280, MPU6050, BH1750 | SDA, SCL |
| SPI | ADXL345, W25Q Flash | MOSI, MISO, SCK, CS |
| UART | GPS, PM2.5 | TX, RX |
| ADC | 光照、温度模拟传感器 | 模拟电压 |
| GPIO | PIR 人体红外 | 数字中断 |

### 2.2 设备树描述

```dts
&i2c1 {
    bme280@76 {
        compatible = "bosch,bme280";
        reg = <0x76>;
        status = "okay";
    };
};
```

### 2.3 总线驱动匹配

| 总线 | 驱动注册 | 匹配依据 |
|------|----------|----------|
| I2C | `i2c_driver` | `of_match_table` + `i2c_device_id` |
| SPI | `spi_driver` | `of_match_table` + `spi_device_id` |
| Platform | `platform_driver` | `of_match_table` + `platform_device_id` |

### 2.4 IIO 子系统

| 概念 | 说明 |
|------|------|
| `struct iio_dev` | IIO 设备描述 |
| `struct iio_chan_spec` | 通道规格 |
| `iio_trigger` | 触发采样 |
| `iio_buffer` | 批量数据缓冲 |
| sysfs | `/sys/bus/iio/devices/iio:deviceX/in_temp_input` |

### 2.5 Input 子系统

| 概念 | 说明 |
|------|------|
| `struct input_dev` | 输入设备描述 |
| `input_event` | 上报事件 |
| 用户接口 | `/dev/input/eventX` |
| 适用 | 按键、触摸屏、运动传感器 |

### 2.6 hwmon / thermal

| 子系统 | 用途 |
|--------|------|
| hwmon | 硬件监控：温度、电压、风扇 |
| thermal | 热管理：温度区域、冷却策略 |

---

## 3. 用户态访问方式

| 方式 | 路径 | 适用 |
|------|------|------|
| sysfs | `/sys/bus/iio/devices/iio:device0/in_temp_input` | 简单轮询 |
| input event | `/dev/input/event0` | 事件驱动 |
| libiio | `iio_context`, `iio_channel` | 跨平台访问 |
| chardev | `/dev/iio:device0` | 直接 ioctl |
| network | `iiod` | 远程访问 |

---

## 4. 场景分析

| 场景 | 总线 | 子系统 | 用户接口 | 关键参数 |
|------|------|--------|----------|----------|
| 环境监测 | I2C | IIO | sysfs / libiio | 采样周期，精度 |
| 可穿戴设备 | I2C/SPI | IIO + input | /dev/input | 中断触发，功耗 |
| 工业监控 | 4-20mA/ADC | IIO/hwmon | sysfs | 线性校准 |
| 智能家居 | GPIO | input | /dev/input | 中断防抖 |

---

## 5. 跨层映射表

| 层级 | 关键元素 | 说明 |
|------|----------|------|
| 硬件 | BME280, I2C bus | 物理传感器与总线 |
| 控制器驱动 | `i2c-imx` | SoC I2C 控制器驱动 |
| 总线核心 | `i2c-core` | 提供 `i2c_transfer` |
| 设备驱动 | `bme280_i2c_driver` | 传感器协议解析 |
| 子系统 | `industrialio` | 标准化数据暴露 |
| sysfs | `in_temp_input` | 用户态可读文件 |
| 应用 | Python/C 程序 | 读取、处理、上报 |

---

## 6. 相关文件

- [外设概念树](../../2.操作系统/02-operating-systems/07-peripherals/peripheral-concept-tree.md)
- [I2C](../../2.操作系统/02-operating-systems/07-peripherals/i2c.md)
- [SPI](../../2.操作系统/02-operating-systems/07-peripherals/spi.md)
- [跨层映射](../../2.操作系统/02-operating-systems/08-interfaces/cross-layer-mapping.md)

## 国际权威来源链接 | International Authoritative Sources

- [NXP I²C-bus Specification UM10204, Rev. 7](https://www.nxp.com/docs/en/user-guide/UM10204.pdf)
- [Motorola SPI Block Guide V04.01 (S12SPIV4/D)](https://www.nxp.com/)
- [Linux Kernel Documentation — Industrial I/O](https://docs.kernel.org/driver-api/iio/)
- [Linux Kernel Documentation — Device Tree Bindings](https://docs.kernel.org/devicetree/bindings/)
- [ARM Architecture Reference Manual](https://developer.arm.com/documentation)
- [项目国际化权威标准基线 — 3. 物联网嵌入式系统](../../../docs/international-baseline.md)
