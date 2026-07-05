# 04-rtos-concepts / RTOS 概念


<!-- TOC START -->

- [04-rtos-concepts / RTOS 概念](#04-rtos-concepts--rtos-概念)
  - [文件列表](#文件列表)
  - [返回](#返回)

<!-- TOC END -->

本目录整理实时操作系统的概念树、主流 RTOS 对比与可调度性分析。

## 文件列表

- [rtos-concept-tree.md](./rtos-concept-tree.md) — RTOS 全局概念树
- [rtos-attribute-relationship-map.md](./rtos-attribute-relationship-map.md) — RTOS 属性-关系映射
- [rtos-mechanism-composition-tree.md](./rtos-mechanism-composition-tree.md) — RTOS 机制组合树
- [rtos-dependency-tree.md](./rtos-dependency-tree.md) — RTOS 依赖树
- [rtos-scenario-analysis-tree.md](./rtos-scenario-analysis-tree.md) — RTOS 场景分析树
- [rtos-source-mapping.md](./rtos-source-mapping.md) — RTOS 国际来源映射
- [freertos-zephyr-rtems-vxworks-map.md](./freertos-zephyr-rtems-vxworks-map.md) — FreeRTOS / Zephyr / RTEMS / VxWorks 对比映射
- [real-time-schedulability.md](./real-time-schedulability.md) — RM / EDF / 响应时间分析

## 形式化工件

- [FreeRTOS 固定优先级调度 TLA+](../../tools/tla-specifications/FreeRTOS_TaskScheduler.tla) + [配置](../../tools/tla-specifications/FreeRTOS_TaskScheduler.cfg) — TLC 已通过
- [RTOS 可调度性 UPPAAL](../../tools/uppaal-models/RTOS_Schedulability.xml) — 双周期任务固定优先级调度时间自动机
- [RMS 利用率边界 Coq 证明](../../tools/coq-verification/RTOSSchedulability.v) — Liu & Layland (1973) n=2/3 边界

## 国际标准映射

- [RTOS 安全认证国际标准映射](../3.0%20国际标准映射/rtos-safety-standards-mapping.md) — ISO 26262 / IEC 61508 / DO-178C / IEC 62304 / ARINC 653

## 返回

- [返回物联网嵌入式系统总览](../README.md)
