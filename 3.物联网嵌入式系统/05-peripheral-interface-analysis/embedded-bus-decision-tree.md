# 嵌入式外设总线选择决策树

> **目标**：为 MCU/MPU 嵌入式系统选择合适的外设总线：I2C / SPI / UART / CAN / USB / PCIe。

---

## 1. 决策树

```mermaid
graph TD
    A[需要连接外设] -->|板内近距离, 2~3 线, 低速| B[I2C]
    A -->|板内全双工, 4+ 线, 中高速| C[SPI]
    A -->|异步点对点, 调试/串口| D[UART]
    A -->|车载/工业, 多主, 高可靠| E[CAN]
    A -->|热插拔, 通用外设, 供电| F[USB]
    A -->|高带宽, 板级扩展, DMA| G[PCIe]

    B -->|传感器, EEPROM, RTC| B1[典型: 温度/IMU/触摸]
    C -->|Flash, ADC, 显示屏| C1[典型: NOR Flash/SDR]
    D -->|调试 console, GPS, 蓝牙透传| D1[典型: AT 命令/日志]
    E -->|汽车 ECU, 工业控制| E1[典型: 发动机/机器人]
    F -->|键盘, U 盘, 摄像头| F1[典型: HID/MSC/UVC]
    G -->|NVMe SSD, GPU, 网卡| G1[典型: 高性能扩展]
```

---

## 2. 总线属性对比

| 总线 | 线数 | 速率 | 距离 | 拓扑 | 主从 | 典型距离 |
|------|------|------|------|------|------|----------|
| I2C | 2 (SDA+SCL) | ≤ 3.4 Mbps (HS) | 短 | 总线 | 多主 | 板内 cm |
| SPI | 4+ (MOSI/MISO/SCK/CS) | 数十 MHz | 短 | 星型 | 一主多从 | 板内 cm |
| UART | 2 (TX/RX) | ≤ 数 Mbps | 中 | 点对点 | 无 | 数米 |
| CAN | 2 (CANH/CANL) | ≤ 1 Mbps (CAN) / 8 Mbps (CAN-FD) | 长 | 总线 | 多主 | 数十米 |
| USB | 4 (2.0) / 9 (3.0) | ≤ 20 Gbps | 中 | 星型 | 主从 | 数米 |
| PCIe | ≥ 4 lane | GB/s 级 | 板内 | 点对点 | 主从 | cm |

---

## 3. 选择矩阵

| 需求 | 推荐总线 | 原因 |
|------|----------|------|
| 最少引脚 | I2C | 仅 2 线 |
| 最高吞吐 | PCIe / SPI | 高时钟/多 lane |
| 远距离高可靠 | CAN | 差分、仲裁、CRC |
| 热插拔 | USB | 标准协议栈、供电 |
| 调试串口 | UART | 简单、无需时钟 |
| 多主访问 | I2C / CAN | 总线仲裁 |
| 低功耗传感器 | I2C / SPI | 简单、可休眠 |

---

## 4. Linux/RTOS 映射

| 总线 | Linux 子系统 | RTOS 抽象 |
|------|--------------|-----------|
| I2C | `i2c_adapter` / `i2c_client` | I2C HAL |
| SPI | `spi_master` / `spi_device` | SPI HAL |
| UART | `uart_driver` / `tty` | UART HAL |
| CAN | `socketcan` / `can_dev` | CAN HAL |
| USB | `usb_hcd` / `usb_device` | USB Stack |
| PCIe | `pci_dev` / `pci_driver` | — |

---

## 5. 相关文件

- [外设总线决策树](../../../2.操作系统/02-operating-systems/07-peripherals/decision-tree-peripheral-bus.md)
- [I2C](../../../2.操作系统/02-operating-systems/07-peripherals/i2c.md)
- [SPI](../../../2.操作系统/02-operating-systems/07-peripherals/spi.md)
- [UART](../../../2.操作系统/02-operating-systems/07-peripherals/uart.md)
- [CAN](../../../2.操作系统/02-operating-systems/07-peripherals/can.md)
