<!-- 创建理由：补齐 RTOS 安全认证国际标准映射，将 ISO 26262 / IEC 61508 / DO-178C / IEC 62304 / ARINC 653 的条款、要求与 RTOS 实现机制显式关联，支撑可追溯的形式化与认证知识。 -->

# RTOS 安全认证国际标准映射

<!-- TOC START -->

- [RTOS 安全认证国际标准映射](#rtos-安全认证国际标准映射)
  - [1. 主要对标标准](#1-主要对标标准)
  - [2. 安全完整性等级与确定性等级](#2-安全完整性等级与确定性等级)
  - [3. 标准条款到 RTOS 机制映射](#3-标准条款到-rtos-机制映射)
  - [4. 认证生命周期与 RTOS 证据](#4-认证生命周期与-rtos-证据)
  - [5. 形式化工件链接](#5-形式化工件链接)
  - [6. 覆盖缺口与补齐计划](#6-覆盖缺口与补齐计划)
  - [7. 维护记录](#7-维护记录)

<!-- TOC END -->

> **权威来源**：ISO 26262:2018, IEC 61508:2010, DO-178C / ED-12C (2011), IEC 62304:2006+A1:2015, ARINC 653 Part 1 (2018)。
> **目标**：把功能安全、航空电子分区和医疗软件标准中直接影响 RTOS 设计与验证的条款，映射到 FreeRTOS / Zephyr / RTEMS / QNX 的具体机制与项目形式化工件。

---

## 1. 主要对标标准

| 标准/规范 | 全称 | 版本 | 官方链接 | 访问日期 | 对应 RTOS 主题 |
|---|---|---|---|---|---|
| ISO 26262 | Road vehicles — Functional Safety | 2018 | <https://www.iso.org/standard/68383.html> | 2026-07-06 | 汽车 ECU 软件安全、ASIL、确定性调度 |
| IEC 61508 | Functional safety of electrical/electronic/programmable electronic safety-related systems | 2010 | <https://webstore.iec.ch/publication/66912> | 2026-07-06 | 通用工业安全、SIL、软件生命周期 |
| DO-178C | Software Considerations in Airborne Systems and Equipment Certification | 2011 | <https://www.rtca.org/product/do-178c/> | 2026-07-06 | 航空软件生命周期、DAL、验证等级 |
| ED-12C | Software Considerations in Airborne Systems and Equipment Certification (EUROCAE) | 2011 | <https://www.eurocae.net/> | 2026-07-06 | DO-178C 欧洲对应版本 |
| IEC 62304 | Medical device software — Software life cycle processes | 2006 + A1:2015 | <https://www.iso.org/standard/38421.html> | 2026-07-06 | 医疗软件安全分类 Class A/B/C |
| ARINC 653 | Avionics Application Standard Software Interface | Part 1, 2018 | <https://www.arinc.com/cf/store/catalog_detail.cfm?item_id=1326> | 2026-07-06 | 航空电子 IMA 分区、健康监控 |

---

## 2. 安全完整性等级与确定性等级

| 标准 | 等级体系 | 与 RTOS 属性的关系 |
|---|---|---|
| ISO 26262 | ASIL A / B / C / D（D 最严格） | 需要更高确定性、更严格时序验证、更完整故障处理 |
| IEC 61508 | SIL 1 / 2 / 3 / 4 | 要求可复现的时序行为、冗余/容错机制、形式化或半形式化验证 |
| DO-178C | DAL A / B / C / D / E（A 最严格） | DAL A 要求 MC/DC 覆盖、需求追踪、结构化覆盖与确定性调度证据 |
| IEC 62304 | Class A / B / C（C 最严格） | Class C 需要完整软件生命周期控制、风险分析与故障处理 |
| ARINC 653 | N/A（分区隔离为强制要求） | 时间分区、空间分区、健康监控为 IMA 核心要求 |

---

## 3. 标准条款到 RTOS 机制映射

| 标准条款 | 主题 | 对应 RTOS 机制 | FreeRTOS | Zephyr | RTEMS | QNX | 项目覆盖文件 |
|---|---|---|---|---|---|---|---|
| ISO 26262-6:2018 7.1 | 软件设计与实现 | 静态设计、编码规范、确定性调度 | FreeRTOS Kernel | Zephyr Kernel | Classic/POSIX API | Neutrino Kernel | `04-rtos-concepts/rtos-concept-tree.md` |
| ISO 26262-6:2018 7.4.18 | 调度机制 | 固定优先级抢占、时间片、互斥量优先级继承 | `FreeRTOS_TaskScheduler.tla` | `k_thread` 优先级 | Rate Monotonic Manager | Adaptive Partitioning | `tools/tla-specifications/FreeRTOS_TaskScheduler.tla` |
| IEC 61508-3:2010 7.4.7 | 软件架构设计 | 模块化、信息隐藏、错误检测 | MPU / User Mode | Userspace / Memory Domains | Region/Partition Manager | Safe Kernel | `04-rtos-concepts/rtos-mechanism-composition-tree.md` |
| IEC 61508-3:2010 7.4.9 | 调度与执行时序 | 最坏执行时间、响应时间分析 | `vTaskDelayUntil` | `k_timer` / deadlines | Rate Monotonic / EDF | Time Partitioning | `04-rtos-concepts/real-time-schedulability.md` |
| DO-178C 6.1 | 软件需求过程 | 需求可追溯、验证计划 | Requirements Traceability | Zephyr Test Framework | RTEMS Test Suite | QNX Momentics | `04-rtos-concepts/rtos-source-mapping.md` |
| DO-178C 6.3 | 软件设计过程 | 高层/低层设计、接口定义 | API Reference | Kernel Services | Classic API Spec | Programmers Guide | `04-rtos-concepts/rtos-dependency-tree.md` |
| DO-178C 6.4 | 软件编码过程 | 编码标准、结构化覆盖 | MISRA C / Coverity | Coding Guidelines | POSIX compliance | QNX Safe C | `04-rtos-concepts/rtos-attribute-relationship-map.md` |
| ARINC 653 3.1 | 分区调度 | 时间分区、主时间帧、分区窗口 | N/A（需 SafeRTOS/SAFERTOS） | N/A | ARINC 653 API (optional) | QNX for Safety | `tools/uppaal-models/RTOS_Schedulability.xml` |
| ARINC 653 3.2 | 空间分区 | 内存保护、MMU/MPU | FreeRTOS-MPU | Memory Protection | Memory Regions | Adaptive Partitioning | `04-rtos-concepts/rtos-mechanism-composition-tree.md` |
| ARINC 653 3.4 | 健康监控 | 错误处理、看门狗、恢复 | Watchdog / Hook | Fatal Handler | Fatal Error Manager | Health Monitor | `04-rtos-concepts/rtos-scenario-analysis-tree.md` |
| IEC 62304 5.3.5 | 软件详细设计 | 任务/线程、同步机制 | Tasks / Queues / Semaphores | Threads / Mutexes / Semaphores | Tasks / Semaphores | Threads / Msg Passing | `04-rtos-concepts/rtos-concept-tree.md` |
| IEC 62304 5.3.9 | 风险控制措施 | 互斥、优先级天花板、超时 | Mutex Priority Inheritance | `K_MUTEX_DEFINE` | Priority Ceiling | Priority Inheritance | `04-rtos-concepts/rtos-attribute-relationship-map.md` |

---

## 4. 认证生命周期与 RTOS 证据

| 阶段 | 标准对应 | 需要产生的 RTOS 证据 | 形式化工件示例 |
|---|---|---|---|
| 需求定义 | ISO 26262-3 / IEC 61508-1 / DO-178C 6.1 | 调度需求、时序需求、安全需求 | TLA+ 状态机需求规约 |
| 架构设计 | ISO 26262-6 7.4 / IEC 61508-3 7.4 | 任务优先级表、资源依赖图、分区设计 | Mermaid 依赖图、Alloy 架构约束 |
| 详细设计 | DO-178C 6.3 / IEC 62304 5.3.5 | 任务状态机、同步协议、错误处理流程 | TLA+ `FreeRTOS_TaskScheduler.tla` |
| 编码与静态分析 | DO-178C 6.4 / IEC 62304 5.3.6 | 编码规范符合性、覆盖率报告 | 待接入 CI |
| 单元/集成测试 | ISO 26262-6 9 / DO-178C 6.5 | 时序测试、边界测试、故障注入 | UPPAAL `RTOS_Schedulability.xml` |
| 验证与确认 | IEC 61508-1 7.18 / DO-178C 6.6 | 形式化验证报告、模型检验日志 | TLC 输出日志、Coq/Isabelle 证明 |

---

## 5. 形式化工件链接

| 工件 | 路径 | 验证引擎 | 说明 |
|---|---|---|---|
| FreeRTOS 固定优先级调度 TLA+ | `tools/tla-specifications/FreeRTOS_TaskScheduler.tla` + `.cfg` | TLC | 验证最高优先级就绪任务正在运行、无死锁 |
| RTOS 可调度性 UPPAAL | `tools/uppaal-models/RTOS_Schedulability.xml` | UPPAAL 5.0 | 两周期任务固定优先级调度时间自动机 |
| OS 调度器 Coq 证明 | `tools/coq-verification/OSScheduler.v` | Coq 8.19+ | 调度后运行任务优先级不低于就绪队列中任何任务 |
| OS 调度器 Isabelle/HOL 证明 | `tools/isabelle-verification/OS_Scheduler.thy` | Isabelle/HOL 2024 | 同上，Isabelle/HOL 版本 |
| OS 内存管理 Coq 证明 | `tools/coq-verification/OSMemory.v` | Coq 8.19+ | 页表映射数量不超过物理帧数 |

---

## 6. 覆盖缺口与补齐计划

1. **ARINC 653 分区形式化**：当前无时间/空间分区 TLA+/UPPAAL 模型；计划创建 `ARINC653_PartitionScheduling.tla` 或扩展 UPPAAL 模型。
2. **ISO 26262 ASIL 到 RTOS 配置映射**：需要把 ASIL A~D 的时序、冗余、错误处理要求显式映射到 FreeRTOS/Zephyr 配置选项。
3. **IEC 61508 SIL 证据模板**：缺少 SIL 1~4 的软件验证等级检查清单与证据模板。
4. **DO-178C 结构化覆盖与 MC/DC**：当前未覆盖航空软件的覆盖度要求与 RTOS 代码实例。
5. **IEC 62304 医疗软件风险管理**：缺少 Class A/B/C 与 RTOS 任务关键度对应表。
6. **CI 形式化验证门禁**：TLA+ 已通过 TLC，但 Coq/Isabelle/UPPAAL 需工具链安装后接入 CI。

---

## 7. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-06 | 创建 RTOS 安全认证国际标准映射，覆盖 ISO 26262 / IEC 61508 / DO-178C / IEC 62304 / ARINC 653 | Kimi Code CLI |
