# 07-peripherals / 外设与总线


<!-- TOC START -->

- [07-peripherals / 外设与总线](#07-peripherals--外设与总线)
  - [文件列表](#文件列表)
  - [返回](#返回)
  - [质量治理注记（2026-11）](#质量治理注记2026-11)

<!-- TOC END -->

本目录覆盖嵌入式与服务器中常见外设总线：PCIe、USB、I2C、SPI、UART、GPIO、CAN，以及中断、DMA、IOMMU 等底层机制。

## 文件列表

- [peripheral-concept-tree.md](./peripheral-concept-tree.md) — 外设总线全局概念树
- [interrupts-and-dma.md](./interrupts-and-dma.md) — 中断控制器、threaded IRQ、DMA 引擎、IOMMU
- [decision-tree-peripheral-bus.md](./decision-tree-peripheral-bus.md) — I2C/SPI/UART/CAN/USB/PCIe 选择决策树
- [i2c.md](./i2c.md) — I2C 协议与 Linux 驱动
- [pcie.md](./pcie.md) — PCIe 枚举、配置空间、MSI/MSI-X、SR-IOV
- [usb.md](./usb.md) — USB 描述符、URB、xHCI、USB gadget
- [spi.md](./spi.md) — SPI 时序、CPOL/CPHA、`spi_driver`
- [uart.md](./uart.md) — UART 波特率、流控、console、earlycon
- [gpio.md](./gpio.md) — pinctrl、gpiochip、中断触发
- [can.md](./can.md) — CAN 帧格式、socketcan、汽车电子

## 返回

- [返回操作系统总览](../README.md)

## 质量治理注记（2026-11）

本目录原 5 个内容文件经全库质量审计归类为模板填充（C 类），已整体归档至 `docs/Refactor/archive/2026-quality-audit/2.操作系统/02-operating-systems/07-peripherals/`（原相对路径不变，可恢复）。保留本 README 作为目录骨架。
