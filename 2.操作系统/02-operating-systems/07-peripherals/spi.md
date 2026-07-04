# SPI 总线


<!-- TOC START -->

- [SPI 总线](#spi-总线)
  - [1. SPI 信号线](#1-spi-信号线)
  - [2. 时钟极性与相位](#2-时钟极性与相位)
  - [3. 数据传输](#3-数据传输)
  - [4. Linux SPI 框架](#4-linux-spi-框架)
    - [4.1 核心结构](#41-核心结构)
    - [4.2 设备树绑定](#42-设备树绑定)
    - [4.3 核心 API](#43-核心-api)
  - [5. 用户态访问](#5-用户态访问)
  - [6. 场景分析](#6-场景分析)
  - [7. 术语表](#7-术语表)
  - [8. 相关文件](#8-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：Motorola SPI Block Guide, Linux Kernel `drivers/spi/`, Linux Device Drivers。
>
> **目标**：系统讲解 SPI 协议、时序、CPOL/CPHA、Linux SPI 驱动框架与设备树绑定。

---

## 1. SPI 信号线

| 信号 | 说明 |
|------|------|
| SCK | 串行时钟（Serial Clock） |
| MOSI | 主机输出从机输入（Master Out Slave In） |
| MISO | 主机输入从机输出（Master In Slave Out） |
| CS/SS | 片选（Chip Select / Slave Select） |

---

## 2. 时钟极性与相位

| 模式 | CPOL | CPHA | 采样边沿 |
|------|------|------|----------|
| 0 | 0 | 0 | 上升沿 |
| 1 | 0 | 1 | 下降沿 |
| 2 | 1 | 0 | 下降沿 |
| 3 | 1 | 1 | 上升沿 |

---

## 3. 数据传输

- 全双工：MOSI 和 MISO 同时传输。
- 无地址：通过独立 CS 选择从设备。
- 无 ACK：无硬件级应答。

---

## 4. Linux SPI 框架

### 4.1 核心结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct spi_master` / `struct spi_controller` | `include/linux/spi/spi.h` | SPI 控制器 |
| `struct spi_device` | `include/linux/spi/spi.h` | SPI 从设备 |
| `struct spi_driver` | `include/linux/spi/spi.h` | SPI 驱动 |
| `struct spi_transfer` | `include/linux/spi/spi.h` | 单次传输 |
| `struct spi_message` | `include/linux/spi/spi.h` | 一次消息（多个 transfer） |

### 4.2 设备树绑定

```dts
&spi0 {
    pinctrl-0 = <&spi0_pins>;
    status = "okay";

    flash@0 {
        compatible = "jedec,spi-nor";
        reg = <0>;              /* CS 0 */
        spi-max-frequency = <50000000>;
        spi-cpol;
        spi-cpha;
    };
};
```

### 4.3 核心 API

| API | 说明 |
|-----|------|
| `spi_sync()` | 同步传输 |
| `spi_async()` | 异步传输 |
| `spi_write()` | 只写 |
| `spi_read()` | 只读 |
| `spi_write_then_read()` | 先写后读 |

---

## 5. 用户态访问

| 方式 | 路径 | 说明 |
|------|------|------|
| spidev | `/dev/spidevX.Y` | 用户态 SPI 字符设备 |
| ioctl | `SPI_IOC_MESSAGE` | 构造 spi_ioc_transfer |

---

## 6. 场景分析

| 场景 | 关键参数 | 验证指标 |
|------|----------|----------|
| SPI Flash | 时钟频率，CPOL/CPHA | 读写吞吐 |
| 显示屏 | 时钟频率，CS 时序 | 刷新帧率 |
| ADC 采样 | 采样率，时钟相位 | 采样精度 |
| RF 模块 | 全双工，时序 | 误码率 |

---

## 7. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| SPI | Serial Peripheral Interface | 串行外设接口 |
| MOSI | Master Out Slave In | 主机输出从机输入 |
| MISO | Master In Slave Out | 主机输入从机输出 |
| CS | Chip Select | 片选信号 |
| CPOL | Clock Polarity | 时钟极性 |
| CPHA | Clock Phase | 时钟相位 |
| spidev | SPI Device | Linux 用户态 SPI 接口 |

---

## 8. 相关文件

- [外设概念树](./peripheral-concept-tree.md)
- [外设总线选择决策树](./decision-tree-peripheral-bus.md)
- [I2C](./i2c.md)

## 国际权威来源链接 / Authoritative Sources

- [Motorola SPI Block Guide V04.01 (NXP/Freescale S12SPIV4/D)](https://www.nxp.com/docs/en/reference-manual/S12SPIV4.pdf)
- [Linux SPI subsystem documentation](https://docs.kernel.org/spi/)
- [Linux Device Drivers - SPI chapter](https://static.lwn.net/images/pdf/LDD3/ch16.pdf)
