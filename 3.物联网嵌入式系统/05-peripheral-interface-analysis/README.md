# 05-peripheral-interface-analysis / 外设接口分析


<!-- TOC START -->

- [05-peripheral-interface-analysis / 外设接口分析](#05-peripheral-interface-analysis--外设接口分析)
  - [文件列表](#文件列表)
  - [返回](#返回)
  - [质量治理注记（2026-11）](#质量治理注记2026-11)

<!-- TOC END -->

本目录从物联网/嵌入式视角分析外设接口选择、传感器到 OS 的映射以及低功耗设计。

## 文件列表

- [sensor-to-os-mapping.md](./sensor-to-os-mapping.md) — 传感器 → I2C/SPI driver → iio/input → 应用
- [embedded-bus-decision-tree.md](./embedded-bus-decision-tree.md) — 嵌入式外设总线选择
- [low-power-interface.md](./low-power-interface.md) — 低功耗接口与电源管理

## 返回

- [返回物联网嵌入式系统总览](../README.md)

## 质量治理注记（2026-11）

本目录原 1 个内容文件经全库质量审计归类为模板填充（C 类），已整体归档至 `docs/Refactor/archive/2026-quality-audit/3.物联网嵌入式系统/05-peripheral-interface-analysis/`（原相对路径不变，可恢复）。保留本 README 作为目录骨架。
