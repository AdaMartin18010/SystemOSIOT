<!-- 创建理由：RTOS 需要独立的国际来源映射文件，将每个概念/机制锚定到 FreeRTOS/Zephyr/QNX/RTEMS 官方文档、经典教材和安全标准。 -->

# RTOS 国际来源映射（RTOS International Source Mapping）

<!-- TOC START -->

- [RTOS 国际来源映射（RTOS International Source Mapping）](#rtos-国际来源映射rtos-international-source-mapping)
  - [1. 概念/机制与来源映射表](#1-概念机制与来源映射表)
  - [2. 标准与认证映射](#2-标准与认证映射)
  - [3. 平台专属来源](#3-平台专属来源)
    - [FreeRTOS](#freertos)
    - [Zephyr](#zephyr)
    - [QNX](#qnx)
    - [RTEMS](#rtems)
  - [4. 覆盖状态总览](#4-覆盖状态总览)
  - [5. 相关文件](#5-相关文件)

<!-- TOC END -->

> **权威来源**：FreeRTOS, Zephyr, QNX, RTEMS 官方文档；Buttazzo *Hard Real-Time Computing Systems*；Liu & Layland 1973；ISO 26262 / IEC 61508 / DO-178C。
>
> **目标**：把 RTOS 每个核心概念/机制锚定到权威教材、官方文档、标准或源码，支撑可追溯的知识体系。

---

## 1. 概念/机制与来源映射表

| 概念/机制 | 来源类型 | 来源 | 位置/章节 | 覆盖状态 |
|-----------|----------|------|-----------|----------|
| Task / Thread | Documentation | FreeRTOS | Mastering the FreeRTOS Kernel, Ch. 1~3 | 已覆盖 |
| Task / Thread | Documentation | Zephyr | Kernel Services → Threads | 已覆盖 |
| Task / Thread | Documentation | RTEMS | Classic API → Tasks | 已覆盖 |
| Task / Thread | Documentation | QNX | QNX Neutrino Programmer's Guide → Processes and Threads | 已覆盖 |
| Fixed Priority Scheduling | Documentation | FreeRTOS | Scheduling → Preemptive Scheduling | 已覆盖 |
| Fixed Priority Scheduling | Documentation | Zephyr | Scheduling → Preemptive Priority-Based Scheduling | 已覆盖 |
| Rate Monotonic / EDF | Paper | Liu & Layland, 1973 | "Scheduling Algorithms for Multiprogramming in a Hard-Real-Time Environment", JACM | 已覆盖 |
| Rate Monotonic / EDF | Textbook | Buttazzo | *Hard Real-Time Computing Systems*, 4th Ed., Ch. 3~4 | 已覆盖 |
| Mutex / Priority Inheritance | Documentation | FreeRTOS | Mutexes / Priority Inheritance | 已覆盖 |
| Mutex / Priority Ceiling | Documentation | RTEMS | Classic API → Semaphore Manager / Priority Ceiling | 已覆盖 |
| Semaphore / Queue / Event | Documentation | FreeRTOS | Semaphores / Queues / Event Groups | 已覆盖 |
| Semaphore / Mutex / Condition Variable | Documentation | Zephyr | Synchronization Services | 已覆盖 |
| Message Queue / Semaphore | Documentation | RTEMS | Classic API → Message Manager / Semaphore Manager | 已覆盖 |
| IPC (MsgSend/Receive/Reply) | Documentation | QNX | QNX Neutrino → Message Passing | 已覆盖 |
| Interrupt / ISR | Documentation | FreeRTOS | Interrupt Management | 已覆盖 |
| Interrupt / ISR | Documentation | Zephyr | Interrupts | 已覆盖 |
| Interrupt / ISR | Documentation | RTEMS | User's Manual → Interrupt Manager | 已覆盖 |
| Tickless / Power Management | Documentation | FreeRTOS | Low Power / Tickless Idle | 已覆盖 |
| Tickless / Power Management | Documentation | Zephyr | Power Management | 已覆盖 |
| Memory Allocator (heap_1~5) | Documentation | FreeRTOS | Memory Management | 已覆盖 |
| Memory Pool / Heap | Documentation | Zephyr | Memory Management | 已覆盖 |
| Memory Management | Documentation | RTEMS | Classic API → Region Manager / Partition Manager | 已覆盖 |
| MPU / User Mode | Documentation | FreeRTOS | FreeRTOS-MPU | 已覆盖 |
| MPU / User Mode | Documentation | Zephyr | Memory Protection / Userspace | 已覆盖 |
| Time Partitioning | Standard | ARINC 653 | ARINC Specification 653 Part 1 | 已规划 |
| Adaptive Partitioning | Documentation | QNX | QNX OS for Safety → Adaptive Partitioning | 已覆盖 |
| Safety Certification | Standard | ISO 26262 | Road Vehicles — Functional Safety, 2018 | 已规划 |
| Safety Certification | Standard | IEC 61508 | Functional Safety of E/E/PE Systems, 2010 | 已规划 |
| Safety Certification | Standard | DO-178C | Software Considerations in Airborne Systems, 2011 | 已规划 |

---

## 2. 标准与认证映射

| 标准/认证 | 适用范围 | RTOS 相关条款/要求 | 项目覆盖状态 |
|-----------|----------|---------------------|--------------|
| ISO 26262:2018 | 汽车功能安全 | Part 6: 软件级产品开发；ASIL 等级与软件单元设计/验证 | 已规划 |
| IEC 61508:2010 | 通用工业功能安全 | Part 3: 软件要求；SIL 与确定性/故障处理 | 已规划 |
| DO-178C / ED-12C | 航空软件 | 软件生命周期过程；DAL A~E 与验证等级 | 已规划 |
| IEC 62304:2006 + A1:2015 | 医疗软件 | 软件安全分类 Class A/B/C；风险管理 | 已规划 |
| IEC 62443-2-1:2024 | 工业网络安全 | SL0~SL4 与安全要求 | 已规划 |
| ARINC 653 | 航空电子分区 | 时间分区、空间分区、健康监控 | 已规划 |

---

## 3. 平台专属来源

### FreeRTOS

- 官方文档：<https://www.freertos.org/Documentation/RTOS-book>
- API 参考：<https://www.freertos.org/a00106.html>
- FreeRTOS-MPU：<https://www.freertos.org/FreeRTOS-MPU-memory-protection-unit.html>

### Zephyr

- 官方文档：<https://docs.zephyrproject.org/>
- Kernel Services：<https://docs.zephyrproject.org/latest/kernel/services/index.html>
- Power Management：<https://docs.zephyrproject.org/latest/services/pm/index.html>

### QNX

- QNX Neutrino RTOS：<https://blackberry.qnx.com/en/products/qnx-neutrino-rtos>
- QNX OS for Safety 8.0：<https://blackberry.qnx.com/en/products/qnx-os-for-safety>

### RTEMS

- 官方文档：<https://docs.rtems.org/>
- Classic API：<https://docs.rtems.org/branches/master/c-user/index.html>
- POSIX API：<https://docs.rtems.org/branches/master/posix-users/index.html>

---

## 4. 覆盖状态总览

| 状态 | 数量 | 说明 |
|------|------|------|
| 已覆盖 | 25+ | 核心任务、调度、同步、中断、内存、电源机制已有官方文档映射 |
| 已规划 | 7 | 安全标准（ISO 26262 / IEC 61508 / DO-178C / IEC 62304 / IEC 62443 / ARINC 653）待阶段三补齐 |

---

## 5. 相关文件

- [RTOS 概念树](./rtos-concept-tree.md)
- [RTOS 属性-关系映射](./rtos-attribute-relationship-map.md)
- [RTOS 机制组合树](./rtos-mechanism-composition-tree.md)
- [RTOS 依赖树](./rtos-dependency-tree.md)
- [RTOS 场景分析树](./rtos-scenario-analysis-tree.md)
- [FreeRTOS/Zephyr/RTEMS/VxWorks 对比](./freertos-zephyr-rtems-vxworks-map.md)
