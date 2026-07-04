# 操作系统概念树（Operating Systems Concept Tree）


<!-- TOC START -->

- [操作系统概念树（Operating Systems Concept Tree）](#操作系统概念树operating-systems-concept-tree)
  - [1. 全局概念树（Mermaid）](#1-全局概念树mermaid)
  - [2. 核心子域概念展开](#2-核心子域概念展开)
    - [2.1 进程管理（Process Management）](#21-进程管理process-management)
      - [属性-关系映射（精选）](#属性-关系映射精选)
    - [2.2 内存管理（Memory Management）](#22-内存管理memory-management)
      - [属性-关系映射（精选）](#属性-关系映射精选-1)
    - [2.3 文件系统与持久化（File System \& Persistence）](#23-文件系统与持久化file-system--persistence)
      - [属性-关系映射（精选）](#属性-关系映射精选-2)
    - [2.4 设备管理（Device Management）](#24-设备管理device-management)
    - [2.5 网络子系统（Networking Subsystem）](#25-网络子系统networking-subsystem)
    - [2.6 外设与总线（Peripheral \& Bus）](#26-外设与总线peripheral--bus)
    - [2.7 接口与抽象层（Interface \& Abstraction）](#27-接口与抽象层interface--abstraction)
    - [2.8 安全与保护（Security \& Protection）](#28-安全与保护security--protection)
  - [3. 主题间关系：虚拟化 · 并发 · 持久化](#3-主题间关系虚拟化--并发--持久化)
  - [4. 术语表](#4-术语表)
  - [5. 国际来源映射](#5-国际来源映射)
  - [6. 相关文件](#6-相关文件)

<!-- TOC END -->

> **权威来源**：OSTEP (Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*), ACM/IEEE CS Curricula 2023 OS Knowledge Areas, MIT xv6, IITBombay OS Lectures.
>
> **说明**：本文件以“根概念 → 核心子域 → 关键概念 → 机制/策略 → 实例”五级结构，建立操作系统领域的全局概念树。边标注关系类型：`is-a`（泛化）、`part-of`（组成）、`depends-on`（依赖）、`instance-of`（实例）。

---

## 1. 全局概念树（Mermaid）

```mermaid
graph TD
    OS[操作系统 Operating System] -->|is-a| SS[系统软件 System Software]
    OS -->|part-of| K[内核 Kernel]
    OS -->|provides| ABI[应用二进制接口 ABI / 系统调用接口]
    OS -->|manages| HW[硬件资源 Hardware Resources]

    K -->|part-of| PM[进程管理 Process Management]
    K -->|part-of| MM[内存管理 Memory Management]
    K -->|part-of| FS[文件系统 File System]
    K -->|part-of| DM[设备管理 Device Management]
    K -->|part-of| NS[网络子系统 Networking Subsystem]
    K -->|part-of| PER[外设与总线 Peripheral & Bus]
    K -->|part-of| IF[接口与抽象层 Interface & Abstraction]
    K -->|part-of| SEC[安全与保护 Security & Protection]

    NS -->|uses| SOCKET[Socket]
    NS -->|uses| PROTO[TCP/IP/UDP/ICMP]
    NS -->|uses| ROUTE[Routing]
    NS -->|uses| NETDEV[net_device]
    NS -->|uses| SKB[sk_buff]
    NS -->|uses| EPOLL[epoll]
    NS -->|uses| IOURING[io_uring]
    NS -->|uses| NETFILTER[netfilter]
    NS -->|uses| EBPF[eBPF/XDP]

    PER -->|uses| BUS[总线 Bus]
    PER -->|uses| DRIVER[设备驱动 Driver]
    PER -->|uses| IRQ[中断 Interrupt]
    PER -->|uses| DMA[DMA]
    PER -->|uses| DT[设备树 Device Tree]
    BUS -->|instance| PCIE[PCIe]
    BUS -->|instance| USB[USB]
    BUS -->|instance| I2C[I2C]
    BUS -->|instance| SPI[SPI]
    BUS -->|instance| UART[UART]
    BUS -->|instance| GPIO[GPIO]
    BUS -->|instance| CAN[CAN]

    IF -->|uses| SYSCALL[System Call]
    IF -->|uses| ABI[ABI/API]
    IF -->|uses| VDSO[vDSO]
    IF -->|uses| ELF[ELF]
    IF -->|uses| POSIX[POSIX]
    IF -->|uses| HAL[HAL]
    IF -->|uses| BSP[BSP]

    PM -->|abstracts| PROC[进程 Process]
    PROC -->|is-a| THREAD[线程 Thread]
    PROC -->|is-a| FIBER[纤程/协程 Fiber/Coroutine]
    PM -->|uses| SCHED[调度器 Scheduler]
    PM -->|uses| SYNC[同步原语 Synchronization Primitives]
    PM -->|handles| DEAD[死锁 Deadlock]

    MM -->|abstracts| AS[地址空间 Address Space]
    AS -->|uses| PAGING[分页 Paging]
    AS -->|uses| SEG[分段 Segmentation]
    MM -->|uses| VM[虚拟内存 Virtual Memory]
    VM -->|uses| PT[页表 Page Table]
    VM -->|uses| TLB[转译后备缓冲器 TLB]
    VM -->|uses| SW[交换/页面置换 Swapping/Page Replacement]

    FS -->|abstracts| FILE[文件 File]
    FS -->|uses| VFS[虚拟文件系统 VFS]
    FS -->|uses| CACHE[页缓存/缓冲缓存 Page/Buffer Cache]
    FS -->|uses| JOURNAL[日志/写时复制 Journaling/COW]
    FS -->|instance-of| EXT4[ext4]
    FS -->|instance-of| BTRFS[Btrfs]
    FS -->|instance-of| XFS[XFS]

    DM -->|uses| INT[中断 Interrupt]
    DM -->|uses| DMA[直接内存访问 DMA]
    DM -->|uses| DRIVER[设备驱动 Device Driver]
    DM -->|uses| BLOCK[块 I/O 层 Block I/O Layer]

    SEC -->|uses| ACL[访问控制列表 ACL]
    SEC -->|uses| CAP[权能 Capabilities]
    SEC -->|uses| LSM[Linux Security Modules]
    SEC -->|uses| CRYPTO[加密与完整性 Crypto & Integrity]
```

---

## 2. 核心子域概念展开

### 2.1 进程管理（Process Management）

```mermaid
graph TD
    PM[进程管理] -->|part-of| PCB[进程控制块 PCB]
    PM -->|part-of| STATE[进程状态机 Process State Machine]
    PM -->|part-of| API[进程 API]
    PM -->|part-of| SCHED[调度器]
    PM -->|part-of| SYNC[同步]
    PM -->|part-of| IPC[进程间通信 IPC]

    PCB -->|contains| PID[PID]
    PCB -->|contains| REGS[寄存器现场]
    PCB -->|contains| MMU_CTX[MMU 上下文]
    PCB -->|contains| FD[文件描述符表]

    STATE -->|is-a| NEW[New]
    STATE -->|is-a| READY[Ready]
    STATE -->|is-a| RUNNING[Running]
    STATE -->|is-a| WAITING[Waiting/Blocked]
    STATE -->|is-a| TERMINATED[Terminated]
    STATE -->|is-a| ZOMBIE[Zombie]

    SCHED -->|uses| CS[上下文切换 Context Switch]
    SCHED -->|policy| FIFO[FCFS/FIFO]
    SCHED -->|policy| SJF[SJF/STCF]
    SCHED -->|policy| RR[Round Robin]
    SCHED -->|policy| MLFQ[MLFQ]
    SCHED -->|policy| PS[优先级调度 Priority Scheduling]
    SCHED -->|policy| CFS[Linux CFS]

    SYNC -->|is-a| LOCK[互斥锁 Mutex]
    SYNC -->|is-a| SEM[信号量 Semaphore]
    SYNC -->|is-a| COND[条件变量 Condition Variable]
    SYNC -->|is-a| RW[读写锁 RWLock]
    SYNC -->|is-a| SPIN[自旋锁 Spinlock]
    SYNC -->|problem| RACE[竞态条件 Race Condition]
    SYNC -->|problem| PI[优先级倒置 Priority Inversion]

    IPC -->|is-a| PIPE[管道 Pipe]
    IPC -->|is-a| MSG[消息队列 Message Queue]
    IPC -->|is-a| SHM[共享内存 Shared Memory]
    IPC -->|is-a| SIGNAL[信号 Signal]
    IPC -->|is-a| SOCKET[Socket]

    DEAD[死锁] -->|condition| MUT[互斥 Mutual Exclusion]
    DEAD -->|condition| HOLD[占有并等待 Hold and Wait]
    DEAD -->|condition| NO_PREEMPT[非抢占 No Preemption]
    DEAD -->|condition| CIRC[循环等待 Circular Wait]
    DEAD -->|prevention| PREV[预防]
    DEAD -->|avoidance| AVOID[避免：银行家算法]
    DEAD -->|detection| DET[检测与恢复]
```

#### 属性-关系映射（精选）

| 概念 | 属性/关系 | 类型/取值 | 说明 |
|------|-----------|-----------|------|
| Process | pid | ℕ | 系统唯一进程标识 |
| Process | state | {new, ready, running, waiting, terminated, zombie} | 生命周期状态 |
| Process | address_space | AddressSpace | 虚拟地址空间；由 MM 子系统管理 |
| Process | parent_of | Process → Process | 父子关系；Linux 中构成森林 |
| Thread | tid | ℕ | 线程标识；与进程共享地址空间 |
| Thread | stack | MemoryRegion | 独立栈空间 |
| Scheduler | ready_queue | Set<Process> | 就绪进程集合 |
| Scheduler | policy | Policy | 决定下一个运行进程 |
| Mutex | owner | Thread ∪ {⊥} | 当前持有线程；支持优先级继承 |
| Deadlock | resource_allocation_graph | Graph | 检测循环等待的图结构 |

---

### 2.2 内存管理（Memory Management）

```mermaid
graph TD
    MM[内存管理] -->|part-of| AS[地址空间]
    MM -->|part-of| ALLOC[物理内存分配]
    MM -->|part-of| VM[虚拟内存]

    AS -->|contains| TEXT[代码段 Text]
    AS -->|contains| DATA[数据段 Data]
    AS -->|contains| BSS[BSS]
    AS -->|contains| HEAP[堆 Heap]
    AS -->|contains| STACK[栈 Stack]
    AS -->|uses| PAGING[分页]
    AS -->|uses| SEG[分段]

    PAGING -->|uses| PAGE[页 Page]
    PAGING -->|uses| FRAME[页框 Frame]
    PAGING -->|uses| PT[页表 Page Table]
    PT -->|uses| PTE[页表项 PTE]
    PT -->|accelerated-by| TLB[TLB]
    TLB -->|miss-handled-by| PTW[页表遍历 Page Table Walk]

    VM -->|uses| DEMAND[请求调页 Demand Paging]
    VM -->|uses| COW[写时复制 Copy-on-Write]
    VM -->|uses| SWAPPING[交换 Swapping]
    VM -->|uses| REP[页面置换 Page Replacement]
    REP -->|algorithm| FIFO2[FIFO]
    REP -->|algorithm| OPT[OPT]
    REP -->|algorithm| LRU[LRU]
    REP -->|algorithm| CLOCK[Clock]
    REP -->|algorithm| WS[工作集 Working Set]

    ALLOC -->|algorithm| BUDDY[伙伴系统 Buddy System]
    ALLOC -->|algorithm| SLAB[SLAB/SLUB]
    ALLOC -->|issue| FRAG[内/外部碎片 Fragmentation]
```

#### 属性-关系映射（精选）

| 概念 | 属性/关系 | 类型/取值 | 说明 |
|------|-----------|-----------|------|
| Address Space | virtual_range | [0, 2^N - 1] | N 为架构地址宽度 |
| Page | size | 4 KiB / 2 MiB / 1 GiB | 架构与配置相关 |
| Page Table | levels | ℕ | x86-64 通常 4~5 级 |
| PTE | flags | {present, rw, user, accessed, dirty, nx} | 页权限与状态 |
| TLB | entry_count | ℕ | 硬件相关；上下文切换时可能刷新 |
| Page Fault | reason | {major, minor, protection, invalid} | 触发调页或段错误 |
| Working Set | W(t, Δ) | Set<Pages> | 时间窗口 Δ 内访问的页集合 |

---

### 2.3 文件系统与持久化（File System & Persistence）

```mermaid
graph TD
    FS[文件系统] -->|part-of| VFS[虚拟文件系统 VFS]
    FS -->|part-of| IMPL[具体文件系统]
    FS -->|part-of| CACHE[缓存层]
    FS -->|part-of| CONS[一致性机制]

    VFS -->|uses| SB[超级块 Superblock]
    VFS -->|uses| INODE[索引节点 Inode]
    VFS -->|uses| DENTRY[目录项 Dentry]
    VFS -->|uses| FOP[file_operations]

    IMPL -->|instance| EXT4[ext4]
    IMPL -->|instance| XFS[XFS]
    IMPL -->|instance| BTRFS[Btrfs]
    IMPL -->|instance| TMPFS[tmpfs]
    IMPL -->|instance| PROC[procfs]
    IMPL -->|instance| SYSFS[sysfs]

    CACHE -->|uses| PCACHE[页缓存 Page Cache]
    CACHE -->|uses| BCACHE[缓冲缓存 Buffer Cache]
    CACHE -->|uses| FLUSH[刷盘策略]

    CONS -->|uses| JOURNAL[日志 Journaling]
    CONS -->|uses| COW2[写时复制 COW]
    CONS -->|uses| CHECKSUM[校验和 Checksum]
    CONS -->|metric| CRASH[崩溃一致性 Crash Consistency]
```

#### 属性-关系映射（精选）

| 概念 | 属性/关系 | 类型/取值 | 说明 |
|------|-----------|-----------|------|
| File | fd | ℕ | 进程内文件描述符 |
| File | offset | ℕ | 当前读写位置 |
| Inode | inode_number | ℕ | 文件系统内唯一标识 |
| Inode | metadata | {mode, uid, gid, size, timestamps} | 文件元数据 |
| Dentry | name → inode | Map | 路径名到 inode 的缓存 |
| Superblock | filesystem_type | String | 文件系统类型标识 |
| Page Cache | cached_pages | Set<Page> | 缓存的文件页 |
| Crash Consistency | atomicity | Boolean | 系统崩溃后元数据一致性 |

---

### 2.4 设备管理（Device Management）

```mermaid
graph TD
    DM[设备管理] -->|part-of| DD[设备驱动]
    DM -->|part-of| IO[ I/O 子系统]
    DM -->|part-of| BUS[总线子系统]

    DD -->|type| CHAR[字符设备]
    DD -->|type| BLOCK2[块设备]
    DD -->|type| NETDEV[网络设备]
    DD -->|model| LINUX_DM[Linux 设备模型]
    LINUX_DM -->|uses| BUS2[总线 Bus]
    LINUX_DM -->|uses| DEVICE[设备 Device]
    LINUX_DM -->|uses| DRIVER2[驱动 Driver]
    LINUX_DM -->|uses| CLASS[设备类 Class]

    IO -->|mechanism| INT[中断 Interrupt]
    IO -->|mechanism| DMA2[DMA]
    IO -->|mechanism| POLL[轮询 Polling]
    IO -->|scheduling| ELEVATOR[I/O 调度器]

    BUS -->|instance| PCI[PCI/PCIe]
    BUS -->|instance| USB[USB]
    BUS -->|instance| I2C[I2C]
    BUS -->|instance| SPI[SPI]
    BUS -->|instance| PLATFORM[Platform]
```

---

### 2.5 网络子系统（Networking Subsystem）

```mermaid
graph TD
    NS[网络子系统] -->|part-of| SOCK[Socket 层]
    NS -->|part-of| INET[INET 层]
    NS -->|part-of| TRANS[传输层]
    NS -->|part-of| NET[网络层]
    NS -->|part-of| LINK[链路层]
    NS -->|part-of| NETDEV2[网络设备层]

    SOCK -->|uses| SOCKET[struct socket]
    SOCK -->|uses| VFS_NET[socket_file_ops]

    INET -->|uses| SOCK2[struct sock]
    INET -->|uses| INETSK[struct inet_sock]

    TRANS -->|instance| TCP[TCP]
    TRANS -->|instance| UDP[UDP]
    TCP -->|state| TCPSTATE[CLOSED/LISTEN/ESTABLISHED/TIME_WAIT...]

    NET -->|uses| IP[IP]
    NET -->|uses| ROUTE2[Routing]
    NET -->|uses| NEIGH[Neighbour ARP/ND]

    LINK -->|uses| ETH[Ethernet]
    LINK -->|uses| BRIDGE[Bridge]
    LINK -->|uses| VLAN[VLAN]

    NETDEV2 -->|uses| NDO[net_device_ops]
    NETDEV2 -->|uses| SKB2[sk_buff]
    NETDEV2 -->|uses| NAPI[NAPI]
    NETDEV2 -->|uses| OFFLOAD[GRO/GSO/TSO]

    NS -->|policy| NF[netfilter]
    NS -->|programmable| EBPF2[eBPF/XDP]
    NS -->|qos| TC[Traffic Control]
```

### 2.6 外设与总线（Peripheral & Bus）

```mermaid
graph TD
    PER2[外设与总线] -->|part-of| BUS2[总线]
    PER2 -->|part-of| DEV[设备]
    PER2 -->|part-of| DRV[驱动]
    PER2 -->|part-of| IRQ2[中断]
    PER2 -->|part-of| DMA2[DMA]

    BUS2 -->|instance| PCIE2[PCIe]
    BUS2 -->|instance| USB2[USB]
    BUS2 -->|instance| I2C2[I2C]
    BUS2 -->|instance| SPI2[SPI]
    BUS2 -->|instance| UART2[UART]
    BUS2 -->|instance| GPIO2[GPIO]
    BUS2 -->|instance| CAN2[CAN]
    BUS2 -->|instance| PLATFORM[Platform]

    DEV -->|type| CHAR2[字符设备]
    DEV -->|type| BLOCK2[块设备]
    DEV -->|type| NETDEV3[网络设备]
    DEV -->|type| SENSOR[传感器]

    DRV -->|model| LDM[Linux Device Model]
    LDM -->|uses| BUS_TYPE[bus_type]
    LDM -->|uses| DEVICE[device]
    LDM -->|uses| DRIVER[device_driver]

    IRQ2 -->|controller| APIC[APIC]
    IRQ2 -->|controller| GIC[GIC]
    IRQ2 -->|controller| PLIC[PLIC]

    DMA2 -->|engine| DMAE[DMA Engine]
    DMA2 -->|remapping| IOMMU[IOMMU]
```

### 2.7 接口与抽象层（Interface & Abstraction）

```mermaid
graph TD
    IF2[接口与抽象层] -->|uses| SYSCALL2[System Call]
    IF2 -->|uses| ABI2[ABI/API]
    IF2 -->|uses| VDSO2[vDSO]
    IF2 -->|uses| ELF2[ELF]
    IF2 -->|uses| POSIX2[POSIX]
    IF2 -->|uses| HAL2[HAL]
    IF2 -->|uses| BSP2[BSP]
    IF2 -->|uses| DT2[Device Tree]
    IF2 -->|uses| ACPI2[ACPI]

    SYSCALL2 -->|hardware| INSTR[syscall/svc/ecall]
    SYSCALL2 -->|table| SYSTBL[sys_call_table]
    SYSCALL2 -->|define| SYSDEF[SYSCALL_DEFINE*]

    ABI2 -->|calling| AMD64[System V AMD64 ABI]
    ABI2 -->|calling| AAPCS[AAPCS]
    ABI2 -->|binary| ELF3[ELF]

    POSIX2 -->|process| POSIX_PROC[§3 Process/Threads]
    POSIX2 -->|filesystem| POSIX_FS[§13 File System]
    POSIX2 -->|network| POSIX_NET[§16 Sockets]
    POSIX2 -->|realtime| POSIX_RT[§17 Realtime]
```

### 2.8 安全与保护（Security & Protection）

```mermaid
graph TD
    SEC[安全与保护] -->|part-of| AUTH[认证 Authentication]
    SEC -->|part-of| AUTHZ[授权 Authorization]
    SEC -->|part-of| ISOL[隔离 Isolation]
    SEC -->|part-of| AUDIT[审计 Audit]

    AUTHZ -->|model| DAC[自主访问控制 DAC]
    AUTHZ -->|model| MAC[强制访问控制 MAC]
    AUTHZ -->|model| RBAC[基于角色的访问控制 RBAC]
    AUTHZ -->|model| CAP2[权能 Capabilities]

    ISOL -->|mechanism| UMODE[用户态/内核态]
    ISOL -->|mechanism| ASLR[ASLR]
    ISOL -->|mechanism| NAMESPACE[命名空间 Namespace]
    ISOL -->|mechanism| CGROUP[cgroup]
    ISOL -->|mechanism| SECCOMP[seccomp]

    MAC -->|instance| SELINUX[SELinux]
    MAC -->|instance| APPARMOR[AppArmor]
    MAC -->|framework| LSM[Linux Security Modules]
```

---

## 3. 主题间关系：虚拟化 · 并发 · 持久化

依据 OSTEP 的三大主题，将上述概念聚类：

| OSTEP 主题 | 核心概念 | 典型机制 | 典型策略 |
|------------|----------|----------|----------|
| Virtualization（CPU） | 进程、线程、地址空间 | 上下文切换、系统调用、陷阱 | CFS、MLFQ、优先级调度 |
| Virtualization（Memory） | 虚拟地址空间、页、页框 | 分页、TLB、请求调页 | LRU、工作集、伙伴分配 |
| Concurrency | 线程、锁、信号量、条件变量 | 原子操作、内存屏障、futex | 银行家算法、优先级继承 |
| Persistence | 文件、inode、超级块 | VFS、日志、COW | 写回/直写、I/O 调度 |

---

## 4. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| 进程 | Process | 运行中的程序实例，拥有独立地址空间和资源集合 |
| 线程 | Thread | 进程内的执行单元，共享进程地址空间 |
| 进程控制块 | PCB / Process Control Block | 操作系统描述和管理进程的数据结构 |
| 上下文切换 | Context Switch | 保存当前进程状态并恢复另一个进程状态的过程 |
| 虚拟内存 | Virtual Memory | 通过页表将虚拟地址映射到物理地址，实现隔离与超量使用 |
| 页表 | Page Table | 存储虚拟页到物理页框映射的数据结构 |
| 虚拟文件系统 | VFS | 为不同具体文件系统提供统一抽象接口的子系统 |
| 设备驱动 | Device Driver | 操作系统中控制特定硬件设备的软件模块 |
| 死锁 | Deadlock | 多个进程因循环等待资源而无法继续执行的状态 |

---

## 5. 国际来源映射

| 概念 | 来源类型 | 来源 | 位置 | 状态 |
|------|----------|------|------|------|
| 进程抽象 | Textbook | OSTEP | Ch. 4 The Abstraction: The Process | 已覆盖 |
| CPU 调度 | Textbook | OSTEP | Ch. 7~9 Scheduling | 已覆盖 |
| 地址空间 | Textbook | OSTEP | Ch. 13~22 Memory Virtualization | 已覆盖 |
| 并发与锁 | Textbook | OSTEP | Ch. 26~32 Concurrency | 已覆盖 |
| 文件系统 | Textbook | OSTEP | Ch. 37~43 Persistence | 已覆盖 |
| OS 知识体系 | Standard | ACM/IEEE CS Curricula 2023 | OS Knowledge Areas | 已覆盖 |
| xv6 实现 | Course | MIT 6.S081 / IITBombay OS | xv6 book & lectures | 已覆盖 |

---

## 6. 相关文件

- [属性-关系映射 OS](./attribute-relationship-map-os.md)
- [机制组合树 OS](./mechanism-composition-tree-os.md)
- [依赖树 OS](./dependency-tree-os.md)
- [场景分析树 OS](./scenario-analysis-tree-os.md)
- [Linux 内核源码映射](../05-linux-kernel/linux-source-map.md)
