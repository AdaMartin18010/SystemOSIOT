# UART 串口


<!-- TOC START -->

- [UART 串口](#uart-串口)
  - [1. UART 信号线](#1-uart-信号线)
  - [2. 帧格式](#2-帧格式)
  - [3. 流控](#3-流控)
  - [4. 16550 UART](#4-16550-uart)
  - [5. Linux Serial 子系统](#5-linux-serial-子系统)
    - [5.1 层次](#51-层次)
    - [5.2 核心结构](#52-核心结构)
    - [5.3 配置](#53-配置)
- [查看串口](#查看串口)
- [配置波特率](#配置波特率)
  - [6. 场景分析](#6-场景分析)
  - [7. 术语表](#7-术语表)
  - [8. 相关文件](#8-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：16550 UART Datasheet, Linux Kernel `drivers/tty/serial/`, Linux Device Drivers。
>
> **目标**：系统讲解 UART 协议、波特率、流控、FIFO、Linux tty/serial 子系统。

---

## 1. UART 信号线

| 信号 | 说明 |
|------|------|
| TX | 发送数据 |
| RX | 接收数据 |
| RTS | 请求发送（硬件流控） |
| CTS | 清除发送（硬件流控） |
| GND | 地线 |

---

## 2. 帧格式

```
| Start | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | Parity | Stop |
|   0   |  LSB → MSB                |   P   |  1   |
```

| 参数 | 常见值 |
|------|--------|
| 数据位 | 8 |
| 停止位 | 1, 2 |
| 校验 | None, Even, Odd |
| 波特率 | 9600, 115200, 921600 |

---

## 3. 流控

| 类型 | 说明 |
|------|------|
| 无流控 | 仅 TX/RX |
| RTS/CTS | 硬件流控 |
| XON/XOFF | 软件流控 |

---

## 4. 16550 UART

| 寄存器 | 说明 |
|--------|------|
| THR | 发送保持寄存器 |
| RBR | 接收缓冲寄存器 |
| IER | 中断使能寄存器 |
| IIR | 中断识别寄存器 |
| FCR | FIFO 控制寄存器 |
| LCR | 线路控制寄存器 |
| MCR | Modem 控制寄存器 |
| LSR | 线路状态寄存器 |

---

## 5. Linux Serial 子系统

### 5.1 层次

```
Application
  ↓ /dev/ttyS0
    ↓ tty core
      ↓ line discipline
        ↓ uart driver
          ↓ 16550 / platform serial
```

### 5.2 核心结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct uart_port` | `include/linux/serial_core.h` | UART 端口 |
| `struct uart_driver` | `include/linux/serial_core.h` | UART 驱动 |
| `struct tty_struct` | `include/linux/tty.h` | TTY 设备 |

### 5.3 配置

```bash
# 查看串口
stty -F /dev/ttyS0

# 配置波特率
stty -F /dev/ttyS0 115200 cs8 -cstopb -parenb
```

---

## 6. 场景分析

| 场景 | 关键参数 | 验证指标 |
|------|----------|----------|
| 调试控制台 | baud rate, earlycon | 启动日志完整 |
| GPS 模块 | 9600/115200, NMEA | 数据完整 |
| 蓝牙模块 | 波特率匹配 | 连接稳定 |
| 工业 RS-485 | 半双工，终端电阻 | 通信距离 |

---

## 7. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| UART | Universal Asynchronous Receiver/Transmitter | 通用异步收发器 |
| Baud Rate | 波特率 | 每秒传输的符号数 |
| FIFO | First In First Out | 硬件缓冲，减少中断次数 |
| RTS/CTS | Request To Send / Clear To Send | 硬件流控信号 |
| Line Discipline | 线路规程 | TTY 层协议处理（如 N_TTY） |

---

## 8. 相关文件

- [外设概念树](./peripheral-concept-tree.md)
- [外设总线选择决策树](./decision-tree-peripheral-bus.md)

## 国际权威来源链接 / Authoritative Sources

- [16550 UART specification (National Semiconductor/Texas Instruments)](https://www.ti.com/lit/ds/symlink/pc16550d.pdf)
- [Linux serial/UART core documentation](https://docs.kernel.org/driver-api/serial/)
- [Linux Device Drivers - TTY layer](https://static.lwn.net/images/pdf/LDD3/ch18.pdf)
