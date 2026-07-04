# 2.0 操作系统 — 国际标准映射


<!-- TOC START -->

- [2.0 操作系统 — 国际标准映射](#20-操作系统-国际标准映射)
  - [1. 主要对标标准](#1-主要对标标准)
  - [2. 详细映射子文档](#2-详细映射子文档)
  - [3. 标准条款映射表](#3-标准条款映射表)
  - [4. 覆盖缺口与补齐计划](#4-覆盖缺口与补齐计划)
  - [5. 形式化工件链接](#5-形式化工件链接)
  - [6. 维护记录](#6-维护记录)

<!-- TOC END -->

## 1. 主要对标标准

| 标准/规范 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| POSIX.1 / IEEE Std 1003.1 | 2024 (Issue 8) | <https://pubs.opengroup.org/onlinepubs/9799919799/> | 2.1, 2.3, 2.6, 2.8 |
| Linux Standard Base (LSB) | 5.0 / ISO/IEC 23360-1-x:2021 | <https://refspecs.linuxfoundation.org/lsb.shtml> | 2.1, 2.3 |
| Single UNIX Specification (SUSv4) | 2018 Edition / Issue 7 TC2 | <https://pubs.opengroup.org/onlinepubs/9699919799/> | 2.1, 2.3, 2.6 |
| Common Criteria (CC) | ISO/IEC 15408:2022 | <https://www.iso.org/standard/72891.html> | 2.2, 2.4, 2.7 |
| TCSEC / Orange Book | DoD 5200.28-STD (historical, 1985) | <https://csrc.nist.gov/csrc/media/publications/conference-paper/1998/10/08/proceedings-of-the-21st-nissc-1998/documents/early-cs-papers/tcsec85.pdf> | 2.2 |
| NIST SP 800-53 Rev. 5 | Rev. 5 (2020; upd. 2024) | <https://csrc.nist.gov/publications/detail/sp/800-53/rev-5/final> | 2.2, 2.4, 2.8 |
| Microsoft Windows Internals | 第 7 版 / Windows 11/Server 2022 | <https://learn.microsoft.com/en-us/windows-hardware/drivers/kernel/> | 2.1, 2.3, 2.8 |
| seL4 | SOSP 2009 / current master | <https://sel4.systems/>; DOI: 10.1145/1629575.1629596 | 2.1, 2.4, 2.6, 2.7 |
| EAL (Evaluation Assurance Levels) | ISO/IEC 15408:2022 Part 3 | <https://www.iso.org/standard/72891.html> | 2.4, 2.7 |
| ARM TrustZone | ARMv8-M / ARMv9 Architecture | <https://developer.arm.com/documentation/100690/latest/> | 2.2, 2.3, 2.6 |
| TPM (Trusted Platform Module) | TPM 2.0 Library Spec v1.83 | <https://trustedcomputinggroup.org/resource/tpm-library-specification/> | 2.2, 2.4, 2.8 |
| ACPI | ACPI Spec 6.5 (2022) | <https://uefi.org/specifications> | 2.1, 2.3, 2.8 |
| UEFI | UEFI Spec 2.10 | <https://uefi.org/specifications> | 2.1, 2.3, 2.8 |
| ELF (Executable and Linkable Format) | System V ABI / TIS ELF 1.2 | <https://refspecs.linuxfoundation.org/elf/elf.pdf> | 2.1, 2.3, 2.6 |
| DWARF | DWARF Standard v5 / v6 draft | <https://dwarfstd.org/> | 2.1, 2.6 |

## 2. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [2.0.1 POSIX 与 Linux 标准条款映射](2.0.1%20POSIX%20与%20Linux%20标准条款映射.md) | POSIX.1-2024、LSB 5.0、SUSv4 关键条款与进程/线程/调度/内存/文件系统映射 |
| [2.0.2 操作系统安全与可信计算标准映射](2.0.2%20操作系统安全与可信计算标准映射.md) | Common Criteria、TCSEC、NIST SP 800-53、seL4、EAL、TrustZone、TPM 条款映射 |

## 3. 标准条款映射表

| 标准条款 | 条款标题 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| POSIX.1-2024 §3 | Definitions（进程、线程、文件描述符等术语） | 2.1 知识梳理 | [2.1.1 基本概念.md](../2.1%20知识梳理/2.1.1%20基本概念.md) | 部分覆盖 |
| POSIX.1-2024 §3.283 | Thread（线程模型与 pthread 语义） | 2.1, 2.3, 2.6 | 2.1 知识梳理、2.3 形式化结构 | 部分覆盖 |
| POSIX.1-2024 §3.141 | Process（进程生命周期、fork/exec/wait） | 2.1, 2.3, 2.6 | 2.1 知识梳理、2.6 形式语义 | 部分覆盖 |
| POSIX.1-2024 §13 | File System Interfaces（open/close/read/write/权限） | 2.1, 2.3 | 2.1 知识梳理 | 部分覆盖 |
| POSIX.1-2024 §16 | Networking Interfaces（socket、TCP/UDP 抽象） | 2.1, 2.6, 2.8 | 2.6 形式语义、2.8 系统运行时语义 | 部分覆盖 |
| POSIX.1-2024 §17 | Realtime（实时调度、优先级、信号量） | 2.1, 2.8 | 2.8 系统运行时语义 | 未覆盖 |
| LSB 5.0 Core §15 | System Initialization（SysV init/LSB headers） | 2.1, 2.8 | 2.8 系统运行时语义 | 未覆盖 |
| ISO/IEC 15408:2022 §7 (ASE) | Security Target evaluation | 2.2, 2.4 | 2.2 批判分析、2.4 形式化证明 | 未覆盖 |
| ISO/IEC 15408:2022 §8–10 (ADV/ATE/AVA) | Design, tests, vulnerability assessment | 2.4, 2.7 | 2.4 形式化证明、2.7 形式证明 | 未覆盖 |
| NIST SP 800-53 Rev.5 AC-3 | Access Enforcement | 2.2, 2.4 | 2.2 批判分析 | 未覆盖 |
| NIST SP 800-53 Rev.5 SC-39 | Process Isolation | 2.2, 2.3 | 2.3 形式化结构 | 未覆盖 |
| seL4 SOSP 2009 | Functional correctness proof of seL4 microkernel | 2.4, 2.6, 2.7 | 2.4 形式化证明、2.7 形式证明 | 未覆盖 |
| TCG TPM 2.0 Part 1 §12 | Trusted Computing Base (TCB) definition | 2.2, 2.4 | 2.2 批判分析 | 未覆盖 |
| ACPI 6.5 §5.2 | ACPI Namespace and Definition Blocks | 2.1, 2.3 | 2.3 形式化结构 | 未覆盖 |
| UEFI 2.10 §2–3 | Boot Services, Runtime Services | 2.1, 2.8 | 2.8 系统运行时语义 | 未覆盖 |
| ELF §1–2 | Object File Format / Sections / Segments | 2.1, 2.3 | 2.3 形式化结构 | 部分覆盖 |
| DWARF v5 §2 | Debugging Information Entries (DIEs) | 2.1, 2.6 | 2.6 形式语义 | 未覆盖 |

## 4. 覆盖缺口与补齐计划

1. **POSIX.1-2024 条款级全覆盖**：将第 3、11、13、16、17 章的关键定义与系统调用语义，逐条映射到 `2.1 知识梳理`、`2.3 形式化结构` 与 `2.6 形式语义` 对应小节。
2. **实时与调度形式化**：补充实时调度（SCHED_FIFO/SCHED_RR、EDF、优先级倒置）与 POSIX 实时扩展的形式化模型，并建立 `2.8 系统运行时语义` 的运行时证据。
3. **安全标准工程化映射**：将 Common Criteria 2022、NIST SP 800-53 Rev.5 的控制族（AC/SC/CM/AU 等）与 TCSEC 安全等级映射到访问控制、进程隔离、可信启动、审计等章节。
4. **可信计算根与启动链**：补充 TPM 2.0、UEFI Secure Boot、ACPI、TrustZone 与操作系统启动/运行时安全的关联，建立从硬件信任根到 OS TCB 的端到端映射。
5. **可执行格式与调试语义**：建立 ELF、DWARF 与程序加载、地址空间布局、调试信息语义的形式化/结构化描述，并关联 `2.3 形式化结构` 与 `2.6 形式语义`。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| OS 调度/内存形式化证明 | 待补充 | 当前未找到操作系统专用 Coq/Isabelle/TLA+ 工件，详见 [`validation/formal-artifacts-gap-audit.md`](../../validation/formal-artifacts-gap-audit.md)。 |
| seL4  Isabelle/HOL 证明 | <https://github.com/seL4/l4v> | 项目外部参考；本项目尚未建立本地可运行副本。 |
| Linux Kernel Memory Model (LKMM) | <https://github.com/torvalds/linux/tree/master/tools/memory-model> | 项目外部参考；可与 `2.6 形式语义` 内存模型对照。 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-02 | 扩展主要对标标准、标准条款映射表、缺口计划、形式化工件链接，新增 2.0.1 / 2.0.2 子文档 | Kimi Code CLI |
