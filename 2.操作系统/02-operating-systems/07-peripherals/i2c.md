# I2C 总线


<!-- TOC START -->

- [I2C 总线](#i2c-总线)
  - [1. I2C 基础](#1-i2c-基础)
    - [1.1 信号线](#11-信号线)
    - [1.2 电气特性](#12-电气特性)
    - [1.3 速度模式](#13-速度模式)
  - [2. 协议时序](#2-协议时序)
    - [2.1 起始与停止条件](#21-起始与停止条件)
    - [2.2 数据传输](#22-数据传输)
    - [2.3 7-bit 地址格式](#23-7-bit-地址格式)
  - [3. Linux I2C 框架](#3-linux-i2c-框架)
    - [3.1 核心结构](#31-核心结构)
    - [3.2 驱动匹配流程](#32-驱动匹配流程)
    - [3.3 核心 API](#33-核心-api)
    - [3.4 设备树绑定示例](#34-设备树绑定示例)
  - [4. 用户态访问](#4-用户态访问)
  - [5. 常见问题](#5-常见问题)
  - [6. 场景分析](#6-场景分析)
  - [7. 术语表](#7-术语表)
  - [8. 国际来源映射](#8-国际来源映射)
  - [9. 相关文件](#9-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：NXP I2C-bus Specification UM10204, Linux Kernel `drivers/i2c/`, Linux Device Drivers。
>
> **目标**：系统讲解 I2C 协议、时序、Linux I2C 驱动框架、设备树绑定与调试。

---

## 1. I2C 基础

### 1.1 信号线

| 信号 | 说明 |
|------|------|
| SDA | 串行数据线（Serial Data Line） |
| SCL | 串行时钟线（Serial Clock Line） |

### 1.2 电气特性

- 开漏输出，需外部上拉电阻。
- 总线空闲时 SDA 和 SCL 均为高。
- 设备通过地址区分。

### 1.3 速度模式

| 模式 | 速度 |
|------|------|
| Standard-mode | 100 kbit/s |
| Fast-mode | 400 kbit/s |
| Fast-mode Plus | 1 Mbit/s |
| High-speed mode | 3.4 Mbit/s |
| Ultra Fast-mode | 5 Mbit/s（单向） |

---

## 2. 协议时序

### 2.1 起始与停止条件

```
SDA  ──┐    ┌─────────┐     ┌───
       │    │         │     │
SCL  ──┴────┘         └─────┘
       ↑ Start           ↑ Stop
```

- **Start**：SCL 高电平时，SDA 从高变低。
- **Stop**：SCL 高电平时，SDA 从低变高。

### 2.2 数据传输

```
SCL  ─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌───────┐
      └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘       │
SDA  ────┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐
         └───┘   └───┘   └───┘   └───┘   └───┘   │
         D7  D6  D5  D4  D3  D2  D1  D0  ACK
```

- 每 8 个数据位后跟 1 个 ACK/NACK。
- SCL 高电平时 SDA 必须稳定。

### 2.3 7-bit 地址格式

```
Start | Slave Addr (7) | R/W | ACK | Data 1 | ACK | ... | Stop
```

- 地址 0x00~0x07 和 0x78~0x7F 保留。
- 实际可用地址：0x08~0x77。

---

## 3. Linux I2C 框架

### 3.1 核心结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct i2c_adapter` | `include/linux/i2c.h` | I2C 控制器适配器 |
| `struct i2c_algorithm` | `include/linux/i2c.h` | 控制器算法（master_xfer） |
| `struct i2c_client` | `include/linux/i2c.h` | I2C 从设备 |
| `struct i2c_driver` | `include/linux/i2c.h` | I2C 设备驱动 |
| `struct i2c_msg` | `include/uapi/linux/i2c.h` | 单次传输消息 |

### 3.2 驱动匹配流程

```
DTS i2c 节点
  ↓ i2c-core 解析
  ↓ 创建 i2c_client
  ↓ 匹配 i2c_driver (of_match_table / i2c_device_id)
  ↓ driver->probe(client)
```

### 3.3 核心 API

| API | 说明 |
|-----|------|
| `i2c_transfer()` | 传输一个或多个 i2c_msg |
| `i2c_smbus_read_byte_data()` | SMBus 读 1 字节 |
| `i2c_smbus_write_byte_data()` | SMBus 写 1 字节 |
| `i2c_smbus_read_word_data()` | SMBus 读 2 字节 |
| `i2c_master_send()` | 简化发送 |
| `i2c_master_recv()` | 简化接收 |

### 3.4 设备树绑定示例

```dts
&i2c1 {
    clock-frequency = <400000>;
    pinctrl-0 = <&i2c1_pins>;
    status = "okay";

    eeprom@50 {
        compatible = "atmel,24c32";
        reg = <0x50>;
        pagesize = <32>;
    };
};
```

---

## 4. 用户态访问

| 方式 | 路径/工具 | 说明 |
|------|-----------|------|
| i2c-dev | `/dev/i2c-0` | 用户态通过 ioctl 访问 |
| i2cdetect | 命令 | 扫描总线上的设备 |
| i2cdump | 命令 | 读取设备寄存器 |
| i2cget / i2cset | 命令 | 读写单个寄存器 |
| libi2c | 库 | 用户态库 |

---

## 5. 常见问题

| 问题 | 原因 | 解决 |
|------|------|------|
| 地址冲突 | 两个设备地址相同 | 使用 I2C mux/switch |
| 通信不稳定 | 上拉电阻不匹配 | 计算并调整上拉电阻 |
| Clock stretching | 从机拉低 SCL | 主机需支持，检查设备要求 |
| 信号反射 | 线缆过长 | 缩短走线，降低速率 |
| ACK 失败 | 设备未响应 | 检查地址、供电、复位 |

---

## 6. 场景分析

| 场景 | 关键参数 | 验证指标 |
|------|----------|----------|
| 多传感器阵列 | 地址分配，总线电容 | 总线占用率，误码率 |
| EEPROM 存储 | 页大小，写保护 | 写入寿命，吞吐 |
| 温度传感器 | 转换时间，分辨率 | 采样精度 |
| OLED 显示屏 | 速率，命令序列 | 刷新帧率 |

---

## 7. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| SDA | Serial Data Line | I2C 串行数据线 |
| SCL | Serial Clock Line | I2C 串行时钟线 |
| ACK | Acknowledge | 应答信号 |
| NACK | Not Acknowledge | 非应答信号 |
| Clock Stretching | 时钟拉伸 | 从设备拉低 SCL 暂停通信 |
| SMBus | System Management Bus | 基于 I2C 的子集，用于系统管理 |
| I2C Adapter | I2C 适配器 | Linux 中 I2C 控制器的抽象 |
| I2C Client | I2C 客户端 | Linux 中 I2C 从设备的抽象 |

---

## 8. 国际来源映射

| 概念 | 来源类型 | 来源 | 位置 |
|------|----------|------|------|
| I2C 协议 | Datasheet | NXP | UM10204 I2C-bus Specification |
| Linux I2C | SourceCode | Linux Kernel | `drivers/i2c/` |
| SMBus | Standard | SBS | SMBus Spec |

---

## 9. 相关文件

- [外设概念树](./peripheral-concept-tree.md)
- [外设总线选择决策树](./decision-tree-peripheral-bus.md)
- [传感器到操作系统映射](../../../3.物联网嵌入式系统/05-peripheral-interface-analysis/sensor-to-os-mapping.md)

## 国际权威来源链接 / Authoritative Sources

- [NXP I²C-bus Specification and User Manual UM10204 (Rev. 7, 2021)](https://www.nxp.com/docs/en/user-guide/UM10204.pdf)
- [Linux I2C subsystem documentation](https://docs.kernel.org/i2c/)
- [Linux Device Drivers - I2C chapter](https://static.lwn.net/images/pdf/LDD3/ch08.pdf)
