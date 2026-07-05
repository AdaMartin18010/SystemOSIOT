# 操作系统依赖树（OS Dependency Tree）


<!-- TOC START -->

- [操作系统依赖树（OS Dependency Tree）](#操作系统依赖树os-dependency-tree)
  - [1. 学习依赖树](#1-学习依赖树)
  - [2. 实现依赖树](#2-实现依赖树)
  - [3. 部署依赖树（嵌入式 Linux）](#3-部署依赖树嵌入式-linux)
  - [4. 系统调用实现依赖](#4-系统调用实现依赖)
  - [5. 网络数据路径依赖](#5-网络数据路径依赖)
  - [6. 关键依赖说明](#6-关键依赖说明)
  - [7. 学习路径建议](#7-学习路径建议)
    - [7.1 本科生路径](#71-本科生路径)
    - [7.2 工程师路径](#72-工程师路径)
  - [8. CS2013 学习路径 → 概念 → Linux 实现 → 形式化模型](#8-cs2013-学习路径--概念--linux-实现--形式化模型)
  - [9. 国际来源映射](#9-国际来源映射)
  - [9. 相关文件](#9-相关文件)

<!-- TOC END -->

> **权威来源**：OSTEP, ACM/IEEE CS2013 Operating Systems KA, MIT 6.S081 xv6, Stanford CS140 Pintos, CMU 15-410。
>
> **目标**：明确操作系统概念、实现与部署之间的前置-后置关系，支持学习路径与工程落地。
>
> **边类型**：
>
> - `hard-depends-on`（硬依赖）：没有前者无法实现后者
> - `soft-depends-on`（软依赖）：建议先理解前者
> - `enables`（使能）：前者使后者成为可能

---

## 1. 学习依赖树

```mermaid
graph TD
    A[计算机组成原理] -->|soft-depends-on| B[CPU 模式与特权级]
    B -->|hard-depends-on| C[系统调用]
    C -->|hard-depends-on| D[进程抽象]
    D -->|soft-depends-on| E[线程]
    D -->|hard-depends-on| F[地址空间]
    F -->|hard-depends-on| G[虚拟内存]
    G -->|hard-depends-on| H[分页与页表]
    H -->|hard-depends-on| I[MMU]

    D -->|soft-depends-on| J[调度]
    E -->|hard-depends-on| K[同步原语]
    K -->|soft-depends-on| L[死锁]

    C -->|soft-depends-on| M[文件系统]
    M -->|soft-depends-on| N[持久化与缓存]

    D -->|soft-depends-on| O[网络套接字]
    O -->|hard-depends-on| P[网络协议栈]
    P -->|soft-depends-on| Q[I/O 与中断]

    B -->|soft-depends-on| R[设备管理]
    R -->|hard-depends-on| S[中断与 DMA]
    R -->|soft-depends-on| T[设备驱动]
    T -->|soft-depends-on| U[设备树/BSP]

    D -->|soft-depends-on| V[安全与隔离]
    V -->|soft-depends-on| W[Capabilities/LSM]
```

---

## 2. 实现依赖树

```mermaid
graph TD
    HW[硬件] -->|hard-depends-on| ARCH[arch/ 代码]
    ARCH -->|hard-depends-on| BOOT[Bootloader]
    BOOT -->|hard-depends-on| KERNEL[Kernel Image]

    HW -->|hard-depends-on| MMU2[MMU 初始化]
    MMU2 -->|hard-depends-on| MM[内存管理子系统]
    MM -->|hard-depends-on| SCHED[调度器]
    SCHED -->|hard-depends-on| PROC[进程管理]

    HW -->|hard-depends-on| IRQ[中断控制器]
    IRQ -->|hard-depends-on| TIMERS[定时器]
    TIMERS -->|hard-depends-on| SCHED

    HW -->|hard-depends-on| BUS[总线控制器]
    BUS -->|hard-depends-on| DTB[设备树解析]
    DTB -->|hard-depends-on| DRIVER_PROBE[驱动 probe]
    DRIVER_PROBE -->|hard-depends-on| DEV_MODEL[设备模型]

    MM -->|enables| FS[文件系统]
    PROC -->|enables| FS
    FS -->|enables| VFS[VFS]
    VFS -->|enables| ROOTFS[Root Filesystem]

    IRQ -->|enables| NET[网络中断]
    NET -->|enables| NETSTACK[网络协议栈]
    BUS -->|enables| NIC[网卡驱动]
    NIC -->|enables| NETSTACK

    PROC -->|enables| IPC[进程间通信]
    PROC -->|enables| SIGNAL[信号]

    PROC -->|enables| SEC[安全子系统]
    MM -->|enables| SEC
    FS -->|enables| SEC
```

---

## 3. 部署依赖树（嵌入式 Linux）

```mermaid
graph LR
    SOC[SoC 硬件] -->|hard-depends-on| BL[Boot ROM]
    BL -->|hard-depends-on| SPL[SPL / First Stage Bootloader]
    SPL -->|hard-depends-on| UBOOT[U-Boot]
    UBOOT -->|hard-depends-on| DTB[Device Tree Blob]
    UBOOT -->|hard-depends-on| KERNEL[Kernel Image zImage/uImage]
    KERNEL -->|hard-depends-on| INITRAMFS[initramfs]
    INITRAMFS -->|hard-depends-on| ROOTFS[Root Filesystem]
    ROOTFS -->|hard-depends-on| INIT[init / systemd]
    INIT -->|hard-depends-on| APP[Applications]
```

---

## 4. 系统调用实现依赖

```mermaid
graph LR
    USER[用户程序] -->|hard-depends-on| GLIBC[glibc]
    GLIBC -->|hard-depends-on| VDSO[vDSO]
    GLIBC -->|hard-depends-on| SYSCALL_INSTR[syscall/sysret 指令]
    SYSCALL_INSTR -->|hard-depends-on| ENTRY[arch/x86/entry/entry_64.S]
    ENTRY -->|hard-depends-on| SYSCALL_TABLE[sys_call_table]
    SYSCALL_TABLE -->|hard-depends-on| SYSCALL_DEFINE[SYSCALL_DEFINE*]
    SYSCALL_DEFINE -->|hard-depends-on| VFS2[VFS / 子系统实现]
```

---

## 5. 网络数据路径依赖

```mermaid
graph LR
    APP[应用 socket()] -->|hard-depends-on| SOCK[struct socket]
    SOCK -->|hard-depends-on| SK[struct sock]
    SK -->|hard-depends-on| TCP[TCP / UDP]
    TCP -->|hard-depends-on| IP[IP 层]
    IP -->|hard-depends-on| ROUTE[路由子系统]
    ROUTE -->|hard-depends-on| NEIGH[邻居子系统 ARP/ND]
    NEIGH -->|hard-depends-on| DEV[net_device]
    DEV -->|hard-depends-on| DRIVER[NIC Driver]
    DRIVER -->|hard-depends-on| DMA4[DMA Ring]
    DMA4 -->|hard-depends-on| PHY[PHY / MAC]
```

---

## 6. 关键依赖说明

| 依赖关系 | 类型 | 说明 |
|----------|------|------|
| MMU → 虚拟内存 | hard | 无 MMU 无法实现硬件地址翻译 |
| 系统调用 → 进程 | hard | 进程是系统调用调度的主体 |
| 中断 → 调度器 | hard | 调度器依赖时钟中断进行时间片管理 |
| 进程 → 线程 | soft | 线程可视为轻量级进程，建议先理解进程 |
| 文件系统 → 块设备 | hard | 持久化文件系统必须依赖块存储 |
| 网络栈 → 中断/DMA | hard | 网络数据包收发依赖 NIC 中断与 DMA |
| 设备树 → 驱动 probe | hard | 嵌入式设备发现通常依赖设备树 |
| 虚拟内存 → 安全隔离 | hard | 地址空间隔离是安全基础 |

---

## 7. 学习路径建议

### 7.1 本科生路径

1. 计算机组成原理 → CPU 模式 → 系统调用
2. 进程/线程 → 调度 → 同步 → 死锁
3. 地址空间 → 分页 → 虚拟内存
4. 文件系统 → I/O → 设备管理
5. 网络套接字 → 协议栈概览
6. 安全与隔离概念

### 7.2 工程师路径

1. 在本科路径基础上，深入 Linux 源码：
   - `kernel/sched/`、`kernel/fork.c`
   - `mm/page_alloc.c`、`mm/memory.c`
   - `fs/`、`block/`
   - `net/`、`drivers/net/`
   - `drivers/base/`、`kernel/irq/`
2. 通过 `strace`/`perf`/`bpftool` 跟踪真实系统调用与事件。
3. 阅读 `Documentation/` 与 LWN 文章。

---

## 8. CS2013 学习路径 → 概念 → Linux 实现 → 形式化模型

```mermaid
graph LR
    CS[ACM/IEEE CS2013 OS KA] -->|LO| CONCEPT[OS Core Concepts]
    CONCEPT -->|instance| LINUX[Linux Kernel Implementation]
    LINUX -->|formalize| FORMAL[Formal Models]

    CS -->|OS/Overview| OS_OVER[OS Overview]
    CS -->|OS/Operating System Principles| OS_PRIN[OS Principles]
    CS -->|OS/Concurrency| OS_CONC[Concurrency]
    CS -->|OS/Scheduling and Dispatch| OS_SCHED[Scheduling]
    CS -->|OS/Memory Management| OS_MEM[Memory Management]
    CS -->|OS/Security and Protection| OS_SEC[Security & Protection]
    CS -->|OS/Device Management| OS_DEV[Device Management]
    CS -->|OS/File Systems| OS_FS[File Systems]
    CS -->|OS/Virtual Machines| OS_VM[Virtual Machines]
    CS -->|OS/Real Time and Embedded Systems| OS_RT[Real Time & Embedded]

    OS_OVER -->|leads-to| OS_PRIN
    OS_PRIN -->|leads-to| OS_SCHED
    OS_PRIN -->|leads-to| OS_MEM
    OS_SCHED -->|leads-to| OS_CONC
    OS_MEM -->|leads-to| OS_FS
    OS_CONC -->|leads-to| OS_SEC
    OS_DEV -->|leads-to| OS_RT
    OS_FS -->|leads-to| OS_VM

    OS_SCHED -->|Linux| LINUX_SCHED[kernel/sched/]
    OS_MEM -->|Linux| LINUX_MEM[mm/]
    OS_CONC -->|Linux| LINUX_SYNC[kernel/locking/]
    OS_FS -->|Linux| LINUX_FS[fs/]
    OS_DEV -->|Linux| LINUX_DRV[drivers/]
    OS_SEC -->|Linux| LINUX_SEC[security/, kernel/cgroup/, kernel/nsproxy.c]
    OS_RT -->|Linux| LINUX_RT[kernel/sched/rt.c, PREEMPT_RT]

    LINUX_SCHED -->|TLA+| FORMAL_SCHED[OS_SchedulerFairness.tla]
    LINUX_MEM -->|TLA+| FORMAL_MEM[OS_PageFault.tla]
    LINUX_SCHED -->|Coq| FORMAL_COQ[OSScheduler.v]
    LINUX_MEM -->|Coq| FORMAL_COQ_MEM[OSMemory.v]
```

**说明**：

- 该依赖树将 CS2013 的学习成果（LO）映射到项目中的概念、Linux 源码实现和形式化工件。
- 每个 CS2013 知识单元对应一个或多个项目文件，最终关联到阶段四将创建的形式化模型。

---

## 9. 国际来源映射

| 依赖主题 | 来源类型 | 来源 | 位置 |
|----------|----------|------|------|
| 学习路径 | Standard | ACM/IEEE CS2013 | OS Knowledge Area |
| CS2013 → Linux → 形式化 | Course/Standard | CS2013 + MIT 6.S081 + CMU 15-410 | Learning Outcomes + xv6/Pintos projects |
| 系统启动 | Textbook | OSTEP | Ch. 1 Dialogue |
| xv6 启动 | Course | MIT 6.S081 | xv6 book Ch. 1 |
| Linux 启动 | SourceCode | Linux Kernel | init/main.c, arch/x86/ |
| 嵌入式启动 | Textbook | Embedded Linux Primer / LDD | Bootloader chapters |

---

## 9. 相关文件

- [概念树](./concept-tree-os.md)
- [属性-关系映射](./attribute-relationship-map-os.md)
- [机制组合树](./mechanism-composition-tree-os.md)
- [场景分析树 / 决策树](./scenario-analysis-tree-os.md)
