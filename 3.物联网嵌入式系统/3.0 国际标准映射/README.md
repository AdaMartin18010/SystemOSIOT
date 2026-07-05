# 3.0 物联网嵌入式系统 — 国际标准映射


<!-- TOC START -->

- [3.0 物联网嵌入式系统 — 国际标准映射](#30-物联网嵌入式系统--国际标准映射)
  - [1. 主要对标标准](#1-主要对标标准)
  - [2. 概念到权威来源映射表](#2-概念到权威来源映射表)
  - [3. 标准条款映射表](#3-标准条款映射表)
  - [4. 覆盖缺口与补齐计划](#4-覆盖缺口与补齐计划)
  - [5. 形式化工件链接](#5-形式化工件链接)
  - [6. 维护记录](#6-维护记录)

<!-- TOC END -->

## 1. 主要对标标准

| 标准/规范 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| ISO/IEC 30141 | 2024 (Edition 2) | <https://www.iso.org/standard/88800.html> | 3.1, 3.3 |
| IEC 62443-2-1 | 2024 | <https://webstore.iec.ch/en/publication/62883> | 3.1, 3.2, 3.7 |
| NIST SP 800-213 / 800-213A | 2024 | <https://csrc.nist.gov/publications/detail/sp/800/213/final> | 3.1, 3.2, 3.7 |
| MQTT | v5.0 (OASIS) | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> | 3.1, 3.6, 3.7 |
| CoAP | RFC 7252/8323 | <https://doi.org/10.17487/RFC7252> | 3.1, 3.6 |
| LwM2M | 1.2 | <https://omaspecworks.org/> | 3.1, 3.6 |
| Matter / Thread | 1.4 / 1.4 | <https://csa-iot.org/all-solutions/matter/> | 3.1, 3.5, 3.7 |
| FreeRTOS | 最新 | <https://www.freertos.org/Documentation/RTOS-book> | 03-embedded-linux, 04-rtos-concepts |
| Zephyr Project | 最新 | <https://docs.zephyrproject.org/> | 04-rtos-concepts, 06-decision-trees |
| RTEMS | 最新 | <https://docs.rtems.org/> | 04-rtos-concepts |
| NXP I²C-bus Specification (UM10204) | Rev. 7, 2021 | <https://www.nxp.com/docs/en/user-guide/UM10204.pdf> | 05-peripheral-interface-analysis |
| Motorola SPI Block Guide | V04.01 (S12SPIV4/D) | NXP/Freescale | 05-peripheral-interface-analysis |
| ISO 11898 (CAN) | 2015/2020/2021 | <https://www.iso.org/standard/63648.html> | 05-peripheral-interface-analysis |
| Bosch CAN Specification 2.0 | 2.0 | <https://www.bosch-semiconductors.com/us/ip-modules/can-protocol/can-2-0.html> | 05-peripheral-interface-analysis |
| PCI Express Base Specification | 6.0/7.0 | <https://pcisig.com/specifications> | 05-peripheral-interface-analysis |
| USB 2.0/3.2/4 Specifications | 最新 | <https://www.usb.org/documents> | 05-peripheral-interface-analysis |
| Intel 64 and IA-32 Architectures Software Developer's Manual | Vol. 3A | <https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html> | 03-embedded-linux, 3.7 |
| ARM Architecture Reference Manual / GIC | 最新 | <https://developer.arm.com/documentation> | 03-embedded-linux, 04-rtos-concepts |
| RISC-V Privileged Spec / PLIC | 最新 | <https://riscv.org/technical/specifications/> | 04-rtos-concepts |
| Liu & Layland, "Scheduling Algorithms for Multiprogramming in a Hard-Real-Time Environment" | JACM 1973 | DOI: 10.1145/321738.321743 | 3.1, 3.4, 04-rtos-concepts |
| Buttazzo, *Hard Real-Time Computing Systems* | 4th Ed. | Springer | 3.1, 3.4, 04-rtos-concepts |

## 2. 概念到权威来源映射表

| 概念/主题 | 权威来源 | 章节/条目 | 项目覆盖文件 |
|---|---|---|---|
| IoT 参考架构 | ISO/IEC 30141:2024 | Clause 5, 6 | `3.1 知识梳理/3.1.1 基本概念.md` |
| IoT 可信性 | ISO/IEC 30141:2024 | Trustworthiness | `3.2 批判分析/3.2.1 主要争议.md` |
| 工业控制系统安全 | IEC 62443-2-1:2024 | Security Levels SL0–SL4 | `3.2 批判分析/`, `3.7 系统运行时语义/` |
| IoT 设备网络安全需求 | NIST SP 800-213 / 800-213A | Device Cybersecurity Requirement Catalog | `3.1 知识梳理/`, `3.2 批判分析/`, `3.7 系统运行时语义/` |
| MQTT 控制包与会话 | OASIS MQTT v5.0 | §2.2, §3 | `3.1 知识梳理/3.1.1 基本概念.md`, `3.6 形式语义/` |
| CoAP 请求/响应模型 | RFC 7252 / RFC 8323 | §2, §12 | `3.1 知识梳理/3.1.1 基本概念.md`, `3.6 形式语义/` |
| 轻量级 M2M 对象模型 | OMA LwM2M 1.2 | Core, Transport, Objects | `3.1 知识梳理/`, `3.6 形式语义/` |
| Matter 设备认证与会话 | Matter 1.4 | Core Specification | `3.1 知识梳理/`, `3.5 多表征/` |
| Thread 低功耗 mesh 网络 | Thread 1.4 | Thread Specification | `3.1 知识梳理/`, `3.5 多表征/` |
| 硬实时调度理论 | Liu & Layland (1973) | Rate Monotonic Utilization Bound | `3.1 知识梳理/`, `3.4 形式化证明/`, `04-rtos-concepts/real-time-schedulability.md` |
| 实时系统教材 | Buttazzo (2024) | RM / EDF / Response Time Analysis | `3.1 知识梳理/`, `3.4 形式化证明/`, `04-rtos-concepts/` |
| FreeRTOS 任务/调度/同步 | FreeRTOS Documentation | Kernel, Task, Queue, Semaphore | `04-rtos-concepts/rtos-concept-tree.md`, `04-rtos-concepts/freertos-zephyr-rtems-vxworks-map.md` |
| Zephyr 内核与驱动 | Zephyr Project Documentation | Kernel, Device Driver Model | `04-rtos-concepts/` |
| RTEMS 实时内核 | RTEMS Documentation | Classic API, POSIX API | `04-rtos-concepts/` |
| I²C 总线电气与协议 | NXP UM10204 | Rev. 7 | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md`, `05-peripheral-interface-analysis/sensor-to-os-mapping.md` |
| SPI 接口 | Motorola SPI Block Guide | V04.01 | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md`, `05-peripheral-interface-analysis/sensor-to-os-mapping.md` |
| CAN 总线 | ISO 11898 / Bosch CAN 2.0 | Data Link Layer, Physical Layer | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md` |
| PCIe 高速串行扩展 | PCI Express Base Specification | 6.0/7.0 | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md` |
| USB 通用串行总线 | USB 2.0/3.2/4 Specifications | USB.org | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md` |
| x86 系统编程 | Intel SDM Vol. 3A | System Programming Guide | `03-embedded-linux/`, `3.7 系统运行时语义/` |
| ARM 体系结构 | ARM Architecture Reference Manual | ARMv7/ARMv8, GIC | `03-embedded-linux/`, `04-rtos-concepts/` |
| RISC-V 特权架构 | RISC-V Privileged Spec | Supervisor / Hypervisor / PLIC | `04-rtos-concepts/` |

## 3. 标准条款映射表

| 标准条款 | 条款标题 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| ISO/IEC 30141:2024 5 | IoT Reference Architecture | 3.1 知识梳理 | `3.1.1 基本概念.md` | 部分覆盖 |
| ISO/IEC 30141:2024 6 | Trustworthiness | 3.2 批判分析 | `3.2.1 主要争议.md` | 未覆盖 |
| IEC 62443-2-1:2024 | Asset owner security requirements | 3.2, 3.7 | 待补充 | 未覆盖 |
| NIST SP 800-213A | IoT Device Cybersecurity Requirement Catalog | 3.2, 3.7 | 待补充 | 未覆盖 |
| ISO 26262:2018 | Road vehicles — Functional Safety | 3.2, 3.4, 04-rtos-concepts | `rtos-safety-standards-mapping.md` | 已覆盖 |
| IEC 61508:2010 | Functional safety of E/E/PE systems | 3.2, 3.4, 04-rtos-concepts | `rtos-safety-standards-mapping.md` | 已覆盖 |
| DO-178C / ED-12C | Software Considerations in Airborne Systems | 3.2, 3.4, 04-rtos-concepts | `rtos-safety-standards-mapping.md` | 已覆盖 |
| IEC 62304:2006+A1:2015 | Medical device software life cycle | 3.2, 3.4 | `rtos-safety-standards-mapping.md` | 已覆盖 |
| ARINC 653 Part 1 | Avionics Application Standard Software Interface | 2018 | `rtos-safety-standards-mapping.md` | 已覆盖 |
| MQTT v5.0 2.2 | Control Packets | 3.1, 3.6 | `3.1.1 基本概念.md` | 部分覆盖 |
| CoAP RFC 7252 2 | Messages / Request/Response | 3.1, 3.6 | `3.1.1 基本概念.md` | 部分覆盖 |
| LwM2M 1.2 Core | Objects and Resources | 3.1, 3.6 | 待补充 | 未覆盖 |
| Matter 1.4 Core | Device Attestation | 3.1, 3.5 | 待补充 | 未覆盖 |
| Thread 1.4 | Mesh Link Establishment | 3.1, 3.5 | 待补充 | 未覆盖 |
| NXP UM10204 3 | I²C Bus Protocol | 3.1, 05 | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md` | 部分覆盖 |
| Bosch CAN 2.0 3 | Message Transfer | 3.1, 05 | `05-peripheral-interface-analysis/embedded-bus-decision-tree.md` | 部分覆盖 |

## 4. 覆盖缺口与补齐计划

1. **ISO/IEC 30141:2024 Trustworthiness**：当前 3.2 批判分析未系统覆盖安全、隐私、可靠性、弹性等可信维度；计划在 3.2.1 中增加对 ISO/IEC 30141:2024 Clause 6 的对照分析。
2. **IEC 62443 安全等级（SL0–SL4）与 NIST SP 800-213A 需求目录**：3.2 与 3.7 缺少安全等级到控制措施的映射表；计划新增 `3.2.4 安全等级映射.md` 或在 3.7 运行时语义中补充安全状态机。
3. **MQTT v5.0 Properties / CoAP Observe / LwM2M 对象模型**：3.6 形式语义目前以概念描述为主，需补充协议状态机、属性语义与形式化规约。
4. **Matter/Thread 1.4 设备认证与会话建立**：3.1 与 3.5 尚未覆盖 commissioning、attestation、CASE/PASE 会话；计划新增专题或扩展 3.5 多表征。
5. **I²C/SPI/CAN/USB/PCIe 电气与协议细节**：05-peripheral-interface-analysis 当前为决策树与高层映射，需补充时序图、电气特性表和错误处理机制。
6. **x86/ARM/RISC-V 架构依赖的运行时语义**：3.7 系统运行时语义目前侧重任务调度，需补充中断控制器（GIC/PLIC）、系统调用、内存序的架构级来源映射。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| IoT 实时调度 UPPAAL | `tools/uppaal-models/IoT_Scheduling.xml` | 传感器节点周期性采样-处理-传输-睡眠时间自动机 |
| RTOS 可调度性 UPPAAL | `tools/uppaal-models/RTOS_Schedulability.xml` | 双周期任务固定优先级调度时间自动机 |
| FreeRTOS 固定优先级调度 TLA+ | `tools/tla-specifications/FreeRTOS_TaskScheduler.tla` + `.cfg` | TLC 已通过：最高优先级就绪任务运行、无死锁 |
| OS 调度器 Coq 证明 | `tools/coq-verification/OSScheduler.v` | 调度后运行任务优先级不低于就绪队列任务 |
| OS 调度器 Isabelle/HOL 证明 | `tools/isabelle-verification/OS_Scheduler.thy` | 同上，Isabelle/HOL 版本 |
| OS 内存管理 Coq 证明 | `tools/coq-verification/OSMemory.v` | 页表 present 映射数不超过物理帧数 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-05 | 补齐 ISO/IEC 30141、IEC 62443、NIST SP 800-213、MQTT/CoAP/LwM2M、Matter/Thread、FreeRTOS/Zephyr/RTEMS、I²C/SPI/CAN/PCIe/USB、Intel SDM/ARM/RISC-V 全量映射；新增覆盖缺口与补齐计划 | Kimi Code CLI |
