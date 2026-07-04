# 操作系统机制组合树（OS Mechanism Composition Tree）


<!-- TOC START -->

- [操作系统机制组合树（OS Mechanism Composition Tree）](#操作系统机制组合树os-mechanism-composition-tree)
  - [1. 多任务（Multitasking）](#1-多任务multitasking)
  - [2. 虚拟内存（Virtual Memory）](#2-虚拟内存virtual-memory)
  - [3. 文件系统持久化（File System Persistence）](#3-文件系统持久化file-system-persistence)
  - [4. 网络栈吞吐（Network Stack Throughput）](#4-网络栈吞吐network-stack-throughput)
  - [5. 外设访问（Peripheral Access）](#5-外设访问peripheral-access)
  - [6. 实时性（Real-Time）](#6-实时性real-time)
  - [7. 安全隔离（Security Isolation）](#7-安全隔离security-isolation)
  - [8. 国际来源映射](#8-国际来源映射)

<!-- TOC END -->

> **权威来源**：OSTEP, Berkeley CS162, MIT xv6, Linux Kernel Development。
>
> **目标**：解释“底层机制如何组合成系统能力/性质”，建立机制 → 子机制 → 性质 → 场景的完整链条。

---

## 1. 多任务（Multitasking）

```mermaid
graph TD
    MT[多任务 Multitasking] -->|requires| CS[上下文切换 Context Switch]
    MT -->|requires| SCHED[调度器 Scheduler]
    MT -->|requires| INT[中断/陷阱 Interrupt/Trap]
    MT -->|requires| MMU[内存管理单元 MMU]

    CS -->|uses| REGS[保存/恢复寄存器]
    CS -->|uses| PCB[进程控制块 PCB/task_struct]
    CS -->|uses| KSTACK[内核栈]

    SCHED -->|uses| RQ[就绪队列 Ready Queue]
    SCHED -->|policy| CFS[Linux CFS]
    SCHED -->|policy| RT[SCHED_FIFO/RR]
    SCHED -->|policy| MLFQ[MLFQ]

    INT -->|uses| TIMER[定时器中断]
    INT -->|uses| SYSCALL[系统调用陷阱]
    INT -->|uses| IVT[中断向量表]

    MMU -->|uses| PT[页表 Page Table]
    MMU -->|uses| TLB[TLB]

    MT -->|enables| TS[分时系统]
    MT -->|enables| MP[多道程序]
    MT -->|enables| RESP[交互式响应]
```

**组合语义**：

- 上下文切换 + 调度器 + 定时器中断 → 抢占式多任务
- MMU + 页表 → 进程地址空间隔离 → 多任务安全
- 中断/陷阱 → 用户态 ↔ 内核态切换入口

---

## 2. 虚拟内存（Virtual Memory）

```mermaid
graph TD
    VM[虚拟内存 Virtual Memory] -->|requires| PAGING[分页 Paging]
    VM -->|requires| PT[页表 Page Table]
    VM -->|requires| MMU2[MMU]
    VM -->|requires| SW[交换/页面置换]

    PAGING -->|uses| PAGE[页 Page]
    PAGING -->|uses| FRAME[页框 Frame]

    PT -->|uses| PTE[页表项 PTE]
    PT -->|accelerated-by| TLB[TLB]
    PT -->|hierarchy| L4[4/5 级页表]

    SW -->|algorithm| LRU[LRU/Clock]
    SW -->|algorithm| WS[Working Set]
    SW -->|uses| DEMAND[请求调页 Demand Paging]
    SW -->|uses| COW[写时复制 COW]

    VM -->|enables| ISOL[地址空间隔离]
    VM -->|enables| OVER[超额使用 Overcommit]
    VM -->|enables| SHM[共享内存 Shared Memory]
    VM -->|enables| MMAP[内存映射文件 mmap]
```

**组合语义**：

- 分页 + 页表 + MMU → 虚拟地址 → 物理地址翻译
- TLB → 加速地址翻译
- 请求调页 + 页面置换 → 物理内存按需使用，支持虚拟内存大于物理内存
- 写时复制 → 高效进程创建与内存共享

---

## 3. 文件系统持久化（File System Persistence）

```mermaid
graph TD
    FS[文件系统 File System] -->|uses| VFS[虚拟文件系统 VFS]
    FS -->|uses| CACHE[缓存层 Cache]
    FS -->|uses| FSIMPL[具体文件系统实现]
    FS -->|uses| CONS[一致性机制]

    VFS -->|uses| INODE[Inode]
    VFS -->|uses| DENTRY[Dentry]
    VFS -->|uses| SB[Superblock]
    VFS -->|uses| FOP[file_operations]

    CACHE -->|uses| PCACHE[页缓存 Page Cache]
    CACHE -->|uses| BCACHE[Buffer Cache]
    CACHE -->|uses| WRITEBACK[写回 Writeback]

    FSIMPL -->|instance| EXT4[ext4]
    FSIMPL -->|instance| XFS[XFS]
    FSIMPL -->|instance| BTRFS[Btrfs]

    CONS -->|uses| JOURNAL[日志 Journaling]
    CONS -->|uses| COW2[写时复制 COW]
    CONS -->|uses| ORDERED[Ordered Writes]

    FS -->|enables| PERSIST[持久化存储]
    FS -->|enables| NAMESPACE[文件命名空间]
    FS -->|enables| SHARING[文件共享]
```

**组合语义**：

- VFS + 具体文件系统 → 统一接口 + 多种存储格式
- 页缓存 + 写回 → 性能优化
- 日志/COW → 崩溃一致性

---

## 4. 网络栈吞吐（Network Stack Throughput）

```mermaid
graph TD
    NT[网络吞吐 Network Throughput] -->|requires| SOCKET[Socket API]
    NT -->|requires| PROTO[TCP/IP Protocol Stack]
    NT -->|requires| OFFLOAD[硬件卸载 Offload]
    NT -->|requires| MULTIQ[多队列 Multi-Queue]

    SOCKET -->|uses| SKB[sk_buff]
    SOCKET -->|uses| EPOLL[epoll]
    SOCKET -->|uses| IOURING[io_uring]

    PROTO -->|uses| TCP[TCP]
    PROTO -->|uses| IP[IP]
    PROTO -->|uses| ROUTE[路由子系统]
    PROTO -->|uses| NETFILTER[netfilter]

    OFFLOAD -->|uses| GRO[GRO]
    OFFLOAD -->|uses| GSO[GSO]
    OFFLOAD -->|uses| TSO[TSO]
    OFFLOAD -->|uses| CHECKSUM[Checksum Offload]

    MULTIQ -->|uses| RPS[RPS]
    MULTIQ -->|uses| RFS[RFS]
    MULTIQ -->|uses| XPS[XPS]
    MULTIQ -->|uses| RSS[RSS]

    NT -->|enables| HPCONN[高并发连接]
    NT -->|enables| LOWLAT[低延迟网络]
    NT -->|enables| HIGHBW[高带宽传输]
```

**组合语义**：

- Socket API + sk_buff → 统一数据包抽象
- TCP/IP + 路由 + netfilter → 协议处理与策略控制
- GRO/GSO/TSO + Checksum Offload → 减少 CPU 拷贝与计算
- RPS/RFS/XPS/RSS → 多核并行处理

---

## 5. 外设访问（Peripheral Access）

```mermaid
graph TD
    PA[外设访问 Peripheral Access] -->|requires| BUS[总线 Bus]
    PA -->|requires| DRIVER[设备驱动 Driver]
    PA -->|requires| IRQ[中断 IRQ]
    PA -->|requires| DMA3[DMA]
    PA -->|requires| DT[设备树 Device Tree]

    BUS -->|instance| PCIE[PCIe]
    BUS -->|instance| USB[USB]
    BUS -->|instance| I2C[I2C]
    BUS -->|instance| SPI[SPI]
    BUS -->|instance| UART[UART]
    BUS -->|instance| GPIO[GPIO]

    DRIVER -->|uses| PROBE[probe]
    DRIVER -->|uses| REMOVE[remove]
    DRIVER -->|uses| OPS[ops 回调]

    IRQ -->|uses| HANDLER[ISR]
    IRQ -->|uses| THREADED[Threaded IRQ]
    IRQ -->|uses| AFFINITY[IRQ Affinity]

    DMA3 -->|uses| MAP[dma_map_sg]
    DMA3 -->|uses| COHERENT[Coherent Memory]
    DMA3 -->|uses| SYNC[Cache Sync]

    DT -->|uses| COMPATIBLE[compatible]
    DT -->|uses| REG[reg]
    DT -->|uses| INTERRUPTS[interrupts]

    PA -->|enables| SENSOR[传感器接入]
    PA -->|enables| STORAGE[存储设备接入]
    PA -->|enables| NETWORK[网卡接入]
```

**组合语义**：

- 总线 + 设备树 → 设备发现与驱动匹配
- 驱动 + 中断/DMA → 高效数据传输
- sysfs/udev → 用户态访问接口

---

## 6. 实时性（Real-Time）

```mermaid
graph TD
    RT[实时性 Real-Time] -->|requires| PREEMPT[可抢占内核]
    RT -->|requires| PS[优先级调度]
    RT -->|requires| TIRQ[Threaded IRQ]
    RT -->|requires| LOCK[优先级继承锁]
    RT -->|requires| ANALYSIS[可调度性分析]

    PREEMPT -->|uses| PREEMPT_RT[PREEMPT_RT Patch]
    PS -->|uses| SCHED_FIFO[SCHED_FIFO]
    PS -->|uses| SCHED_RR[SCHED_RR]
    PS -->|uses| EDF[EDF]

    TIRQ -->|uses| IRQ_THREAD[kirqsd]
    LOCK -->|uses| PI_MUTEX[PI Mutex]
    LOCK -->|uses| RT_MUTEX[RT Mutex]

    ANALYSIS -->|uses| RMA[Rate Monotonic Analysis]
    ANALYSIS -->|uses| EDF2[Earliest Deadline First]
    ANALYSIS -->|uses| WCET[Worst-Case Execution Time]

    RT -->|enables| HARD_RT[硬实时]
    RT -->|enables| SOFT_RT[软实时]
```

---

## 7. 安全隔离（Security Isolation）

```mermaid
graph TD
    SI[安全隔离 Security Isolation] -->|requires| UMK[用户态/内核态]
    SI -->|requires| VM2[虚拟内存隔离]
    SI -->|requires| CAP[权能 Capabilities]
    SI -->|requires| NS[命名空间 Namespaces]
    SI -->|requires| CG[cgroups]
    SI -->|requires| LSM[LSM]
    SI -->|requires| SECCOMP[seccomp]

    UMK -->|uses| RING[特权级 Ring 0/3]
    UMK -->|uses| SYSCALL2[System Call Gate]

    VM2 -->|uses| PT2[Page Table Isolation]
    VM2 -->|uses| KASLR[KASLR]

    NS -->|types| PID_NS[PID]
    NS -->|types| NET_NS[Network]
    NS -->|types| MNT_NS[Mount]
    NS -->|types| USER_NS[User]

    LSM -->|instance| SELINUX[SELinux]
    LSM -->|instance| APPARMOR[AppArmor]

    SI -->|enables| SANDBOX[沙箱]
    SI -->|enables| CONTAINER[容器隔离]
    SI -->|enables| MAC_ENF[强制访问控制]
```

---

## 8. 国际来源映射

| 系统能力 | 关键机制 | 来源类型 | 来源 | 位置 |
|----------|----------|----------|------|------|
| 多任务 | 上下文切换、调度、中断 | Textbook | OSTEP | Ch. 4~9 |
| 虚拟内存 | 分页、页表、TLB | Textbook | OSTEP | Ch. 13~22 |
| 文件系统 | VFS、缓存、日志 | Textbook | OSTEP | Ch. 37~43 |
| 网络吞吐 | NAPI、GRO/GSO、RPS/RFS | SourceCode | Linux Kernel | net/core/, net/sched/ |
| 外设访问 | 设备树、中断、DMA | SourceCode | Linux Kernel | drivers/base/, kernel/irq/ |
| 实时性 | PREEMPT_RT、RMA/EDF | Paper/Textbook | Liu & Layland 1973; Buttazzo | - |
| 安全隔离 | namespaces/cgroups/LSM | SourceCode | Linux Kernel | kernel/nsproxy.c, kernel/cgroup/, security/ |
