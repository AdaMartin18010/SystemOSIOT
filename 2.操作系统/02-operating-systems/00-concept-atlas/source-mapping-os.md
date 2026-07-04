# 操作系统国际来源映射（OS International Source Mapping）

> **目标**：将操作系统核心概念/机制锚定到国际权威教材、课程、标准、源码、RFC 与芯片手册。

---

## 1. 概念 → 教材映射

| 概念 | 来源类型 | 来源 | 章节/位置 | 状态 |
|------|----------|------|-----------|------|
| OS 概述 | Textbook | OSTEP | Ch. 1, 2 | 已覆盖 |
| 进程抽象 | Textbook | OSTEP | Ch. 4~6 | 已覆盖 |
| CPU 调度 | Textbook | OSTEP | Ch. 7~9 | 已覆盖 |
| 地址空间 | Textbook | OSTEP | Ch. 13~16 | 已覆盖 |
| 虚拟内存 | Textbook | OSTEP | Ch. 17~22 | 已覆盖 |
| 并发与锁 | Textbook | OSTEP | Ch. 26~32 | 已覆盖 |
| 文件系统 | Textbook | OSTEP | Ch. 37~43 | 已覆盖 |
| 持久化 | Textbook | OSTEP | Ch. 44 | 已覆盖 |
| OS 设计原则 | Textbook | Anderson & Dahlin, *Operating Systems: Principles and Practice* | Vol. 1~4 | 已覆盖 |
| 计算机架构基础 | Textbook | Hennessy & Patterson | Ch. I/O, Memory Hierarchy | 已覆盖 |

---

## 2. 概念 → 课程映射

| 概念 | 来源类型 | 来源 | 位置 | 状态 |
|------|----------|------|------|------|
| xv6 实现 | Course | MIT 6.828/6.S081 | xv6 book & labs | 已覆盖 |
| Pintos 实现 | Course | Stanford CS140 / Berkeley CS162 | Pintos projects | 已覆盖 |
| 嵌入式 OS | Course | Stanford CS140E | Raspberry Pi + Rust | 已覆盖 |
| OS 知识体系 | Standard | ACM/IEEE CS Curricula 2023 | OS Knowledge Area | 已覆盖 |
| 系统基础 | Standard | ACM/IEEE CS Curricula 2023 | Systems Fundamentals | 已覆盖 |
| 网络基础 | Standard | ACM/IEEE CS Curricula 2023 | Networking and Communication | 已覆盖 |
| 架构基础 | Standard | ACM/IEEE CS Curricula 2023 | Architecture and Organization | 已覆盖 |

---

## 3. Linux 实现 → 源码映射

| 概念 | 来源类型 | 来源 | 源码路径 | 状态 |
|------|----------|------|----------|------|
| 进程管理 | SourceCode | Linux Kernel | `kernel/sched/`, `kernel/fork.c` | 已覆盖 |
| 内存管理 | SourceCode | Linux Kernel | `mm/page_alloc.c`, `mm/memory.c` | 已覆盖 |
| 文件系统 | SourceCode | Linux Kernel | `fs/`, `mm/filemap.c` | 已覆盖 |
| 网络栈 | SourceCode | Linux Kernel | `net/`, `drivers/net/` | 已覆盖 |
| 设备模型 | SourceCode | Linux Kernel | `drivers/base/`, `kernel/irq/` | 已覆盖 |
| 安全子系统 | SourceCode | Linux Kernel | `security/`, `kernel/cgroup/` | 已覆盖 |
| 系统调用 | SourceCode | Linux Kernel | `arch/x86/entry/` | 已覆盖 |
| 设备树 | SourceCode | Linux Kernel | `drivers/of/` | 已覆盖 |

---

## 4. 标准与规范映射

| 概念 | 来源类型 | 来源 | 位置 | 状态 |
|------|----------|------|------|------|
| 系统调用接口 | Standard | POSIX.1-2024 | §System Interfaces | 已覆盖 |
| 线程 | Standard | POSIX.1-2024 | §2.9 Threads | 已覆盖 |
| 文件系统接口 | Standard | POSIX.1-2024 | §13 File System | 已覆盖 |
| 网络 Socket | Standard | POSIX.1-2024 | §16 Sockets | 已覆盖 |
| 实时扩展 | Standard | POSIX.1-2024 | §17 Realtime | 已覆盖 |
| Linux ABI | Standard | Linux Standard Base 5.0 | Core Specification | 已覆盖 |
| ELF | Standard | System V ABI / ELF Spec | - | 已覆盖 |
| PCIe | Standard | PCI-SIG | PCIe Base Spec | 已覆盖 |
| USB | Standard | USB-IF | USB 3.2 Spec | 已覆盖 |
| I2C | Datasheet | NXP | I2C-bus Specification UM10204 | 已覆盖 |
| CAN | Standard | ISO | ISO 11898 | 已覆盖 |

---

## 5. 网络协议映射

| 概念 | 来源类型 | 来源 | 位置 | 状态 |
|------|----------|------|------|------|
| IP | RFC | IETF | [RFC 791](https://datatracker.ietf.org/doc/html/rfc791) | 已覆盖 |
| TCP | RFC | IETF | [RFC 793](https://datatracker.ietf.org/doc/html/rfc793) | 已覆盖 |
| UDP | RFC | IETF | [RFC 768](https://datatracker.ietf.org/doc/html/rfc768) | 已覆盖 |
| ICMP | RFC | IETF | [RFC 792](https://datatracker.ietf.org/doc/html/rfc792) | 已覆盖 |
| ARP | RFC | IETF | [RFC 826](https://datatracker.ietf.org/doc/html/rfc826) | 已覆盖 |
| IPv6 | RFC | IETF | [RFC 8200](https://datatracker.ietf.org/doc/html/rfc8200) | 已覆盖 |
| TCP 拥塞控制 | RFC | IETF | [RFC 5681](https://datatracker.ietf.org/doc/html/rfc5681) | 已覆盖 |
| Host Requirements | RFC | IETF | [RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122) | 已覆盖 |
| HTTP | RFC | IETF | [RFC 9110](https://datatracker.ietf.org/doc/html/rfc9110) | 已覆盖 |
| TLS 1.3 | RFC | IETF | [RFC 8446](https://datatracker.ietf.org/doc/html/rfc8446) | 已覆盖 |
| DNS | RFC | IETF | [RFC 1034](https://datatracker.ietf.org/doc/html/rfc1034), [RFC 1035](https://datatracker.ietf.org/doc/html/rfc1035) | 已覆盖 |
| BGP | RFC | IETF | [RFC 4271](https://datatracker.ietf.org/doc/html/rfc4271) | 已覆盖 |
| OSPF | RFC | IETF | [RFC 2328](https://datatracker.ietf.org/doc/html/rfc2328) | 已覆盖 |
| QUIC | RFC | IETF | [RFC 9000](https://datatracker.ietf.org/doc/html/rfc9000) | 已覆盖 |
| IEEE 802.3 | Standard | IEEE | [IEEE 802.3-2022](https://standards.ieee.org/standard/802.3-2022.html) | 已覆盖 |
| IEEE 802.1Q | Standard | IEEE | [IEEE 802.1Q-2024](https://standards.ieee.org/standard/802.1Q-2024.html) | 已覆盖 |
| NAPI | Article | LWN.net | [NAPI](https://lwn.net/Articles/17992/) | 已覆盖 |
| eBPF | Docs | Linux Kernel | `Documentation/bpf/` | 已覆盖 |
| XDP | Docs | Linux Kernel | `Documentation/networking/xdp/` | 已覆盖 |

---

## 6. 架构手册映射

| 概念 | 来源类型 | 来源 | 位置 | 状态 |
|------|----------|------|------|------|
| x86 系统调用 | Datasheet | Intel | Intel SDM Vol. 3A Ch. 5 | 已覆盖 |
| x86 中断/APIC | Datasheet | Intel | Intel SDM Vol. 3A Ch. 6, 10 | 已覆盖 |
| ARM64 系统调用 | Datasheet | ARM | ARM ARM DDI 0487 | 已覆盖 |
| ARM GIC | Datasheet | ARM | ARM Generic Interrupt Controller Spec | 已覆盖 |
| RISC-V 特权架构 | Datasheet | RISC-V | RISC-V Privileged Spec | 已覆盖 |

---

## 7. RTOS / 嵌入式映射

| 概念 | 来源类型 | 来源 | 位置 | 状态 |
|------|----------|------|------|------|
| FreeRTOS | Docs | FreeRTOS.org | FreeRTOS Reference Manual | 已覆盖 |
| Zephyr | Docs | Zephyr Project | Zephyr Kernel Services | 已覆盖 |
| RTEMS | Docs | RTEMS | Classic API / POSIX API | 已覆盖 |
| 实时调度 | Paper | Liu & Layland | JACM 1973 | 已覆盖 |
| 实时系统 | Textbook | Buttazzo | Hard Real-Time Computing Systems | 已覆盖 |
| 设备树 | Standard | ARM | Devicetree Specification | 已覆盖 |

---

## 8. 覆盖状态汇总

| 主题域 | 教材 | 课程 | 源码 | 标准 | 架构手册 | 综合状态 |
|--------|------|------|------|------|----------|----------|
| 进程/线程/调度 | ✓ | ✓ | ✓ | ✓ | - | 完整 |
| 内存管理 | ✓ | ✓ | ✓ | - | ✓ | 完整 |
| 文件系统 | ✓ | ✓ | ✓ | ✓ | - | 完整 |
| 网络栈 | ✓ | ✓ | ✓ | ✓ | - | 完整 |
| 外设/总线 | ✓ | - | ✓ | ✓ | ✓ | 完整 |
| 中断/DMA | ✓ | ✓ | ✓ | - | ✓ | 完整 |
| 接口/ABI | ✓ | ✓ | ✓ | ✓ | ✓ | 完整 |
| 安全隔离 | ✓ | - | ✓ | ✓ | - | 完整 |
| 实时/嵌入式 | ✓ | ✓ | ✓ | ✓ | - | 完整 |

---

## 9. 相关文件

- [概念树](./concept-tree-os.md)
- [属性-关系映射](./attribute-relationship-map-os.md)
- [机制组合树](./mechanism-composition-tree-os.md)
- [依赖树](./dependency-tree-os.md)
- [场景分析树 / 决策树](./scenario-analysis-tree-os.md)
