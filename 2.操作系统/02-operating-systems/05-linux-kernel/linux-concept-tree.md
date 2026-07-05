<!-- 创建理由：Linux 内核实现层需要独立的概念树，将通用 OS 概念映射到 Linux 专有数据结构、子系统和源码目录。 -->

# Linux 内核概念树（Linux Kernel Concept Tree）

<!-- TOC START -->

- [Linux 内核概念树（Linux Kernel Concept Tree）](#linux-内核概念树linux-kernel-concept-tree)
  - [1. 顶层概念树](#1-顶层概念树)
  - [2. 进程管理子树](#2-进程管理子树)
  - [3. 内存管理子树](#3-内存管理子树)
  - [4. 文件系统子树](#4-文件系统子树)
  - [5. 网络子树](#5-网络子树)
  - [6. 设备与驱动子树](#6-设备与驱动子树)
  - [7. 安全与隔离子树](#7-安全与隔离子树)
  - [8. 国际来源映射](#8-国际来源映射)
  - [9. 相关文件](#9-相关文件)

<!-- TOC END -->

> **权威来源**：Linux Kernel Documentation, The Linux man-pages Project, Michael Kerrisk *The Linux Programming Interface*, Robert Love *Linux Kernel Development*。
>
> **目标**：建立 Linux 内核实现层的概念体系，将通用 OS 概念落地为 Linux 专有数据结构、子系统和源码目录。

---

## 1. 顶层概念树

```mermaid
graph TD
    LK[Linux Kernel] -->|is-a| OS[Operating System Kernel]
    LK -->|part-of| PM[进程管理 Process Management]
    LK -->|part-of| MM[内存管理 Memory Management]
    LK -->|part-of| FS[文件系统 File Systems]
    LK -->|part-of| NET[网络 Networking]
    LK -->|part-of| DEV[设备与驱动 Devices & Drivers]
    LK -->|part-of| SEC[安全与隔离 Security & Isolation]
    LK -->|part-of| INIT[初始化与启动 Initialization]

    PM -->|core-data| TS[task_struct]
    MM -->|core-data| MMS[mm_struct / VMA]
    FS -->|core-data| VFS[VFS: inode/dentry/superblock]
    NET -->|core-data| SKB[sk_buff / struct sock]
    DEV -->|core-data| DEVICE[struct device / device_driver]
    SEC -->|core-data| CRED[struct cred / security_hook_list]
    INIT -->|core-data| DTB[Device Tree / ACPI]
```

---

## 2. 进程管理子树

```mermaid
graph TD
    PM[进程管理] -->|has| TS[task_struct]
    TS -->|contains| PID[pid/tgid/pgrp/session]
    TS -->|contains| STATE[task_state: RUNNING/INTERRUPTIBLE/UNINTERRUPTIBLE/ZOMBIE]
    TS -->|has| SCHED[sched_entity / sched_class]

    SCHED -->|class| CFS[CFS: fair_sched_class]
    SCHED -->|class| RT[RT: rt_sched_class]
    SCHED -->|class| DL[DL: dl_sched_class]
    SCHED -->|class| IDLE[IDLE: idle_sched_class]

    TS -->|has| NS[nsproxy: namespaces]
    NS -->|type| PID_NS[PID namespace]
    NS -->|type| NET_NS[Network namespace]
    NS -->|type| MNT_NS[Mount namespace]
    NS -->|type| USER_NS[User namespace]

    TS -->|has| CG[cgroup: css_set]
    CG -->|controller| CPUSET[cpuset]
    CG -->|controller| CPU[cpu]
    CG -->|controller| MEMORY[memory]
    CG -->|controller| IO[io]
    CG -->|controller| PIDS[pids]
```

---

## 3. 内存管理子树

```mermaid
graph TD
    MM[内存管理] -->|has| VMA[VMA: vm_area_struct]
    MM -->|has| PGD[pgd_t / 页表层次]
    MM -->|has| BUDDY[Buddy System]
    MM -->|has| SLAB[SLUB / SLOB]

    VMA -->|type| ANON[匿名映射 anon]
    VMA -->|type| FILE[文件映射 file]
    VMA -->|type| STACK[栈 stack]
    VMA -->|type| HEAP[堆 heap]

    PGD -->|hierarchy| P4D[P4D]
    PGD -->|hierarchy| PUD[PUD]
    PGD -->|hierarchy| PMD[PMD]
    PGD -->|hierarchy| PTE[PTE]

    BUDDY -->|unit| PAGE[struct page / page frame]
    SLAB -->|object| KOBJ[kernel objects]

    MM -->|cache| PCACHE[Page Cache]
    MM -->|cache| SWAPPER[Swap / Zswap]
    MM -->|mechanism| COW[Copy-On-Write]
```

---

## 4. 文件系统子树

```mermaid
graph TD
    FS[文件系统] -->|abstraction| VFS[VFS]
    VFS -->|data| INODE[struct inode]
    VFS -->|data| DENTRY[struct dentry]
    VFS -->|data| SB[struct super_block]
    VFS -->|ops| FOP[file_operations]
    VFS -->|ops| IOP[inode_operations]

    FS -->|instance| EXT4[ext4]
    FS -->|instance| XFS[XFS]
    FS -->|instance| BTRFS[Btrfs]
    FS -->|instance| TMPFS[tmpfs]
    FS -->|instance| OVERLAY[overlayfs]

    FS -->|block-layer| BIO[struct bio]
    BIO -->|submit| BL[Block Layer]
    BL -->|driver| NVME[NVMe driver]
    BL -->|driver| SCSI[SCSI driver]
    BL -->|driver| MMC[MMC driver]
```

---

## 5. 网络子树

```mermaid
graph TD
    NET[网络] -->|socket| SOCK[struct socket]
    SOCK -->|protocol| SK[struct sock]
    SK -->|instance| TCP[TCP]
    SK -->|instance| UDP[UDP]
    SK -->|instance| RAW[RAW]

    NET -->|packet| SKB[sk_buff]
    SKB -->|layer| DEV[net_device]
    DEV -->|ops| NDO[net_device_ops]

    NET -->|framework| NETFILTER[netfilter]
    NETFILTER -->|backend| NFTABLES[nftables]
    NETFILTER -->|backend| IPTABLES[iptables]
    NET -->|framework| EBPF[eBPF / XDP]
    NET -->|framework| TC[Traffic Control]
```

---

## 6. 设备与驱动子树

```mermaid
graph TD
    DEV[设备与驱动] -->|model| BUS[struct bus_type]
    BUS -->|instance| PCI[PCIe]
    BUS -->|instance| USB[USB]
    BUS -->|instance| I2C[I2C]
    BUS -->|instance| SPI[SPI]
    BUS -->|instance| PLATFORM[platform]

    DEV -->|core| DEVICE2[struct device]
    DEV -->|core| DRIVER[struct device_driver]
    DRIVER -->|lifecycle| PROBE[probe]
    DRIVER -->|lifecycle| REMOVE[remove]

    DEV -->|discovery| DT[Device Tree]
    DEV -->|discovery| ACPI2[ACPI]
    DEV -->|interrupt| IRQ2[IRQ subsystem]
    DEV -->|dma| DMA2[DMA subsystem]
```

---

## 7. 安全与隔离子树

```mermaid
graph TD
    SEC[安全与隔离] -->|identity| CRED2[struct cred]
    CRED2 -->|fields| UID[uid/gid/suid/euid/fsuid]
    CRED2 -->|cap| CAPS[capability set]

    SEC -->|mandatory| LSM[LSM framework]
    LSM -->|module| SELINUX[SELinux]
    LSM -->|module| APPARMOR[AppArmor]
    LSM -->|module| SMACK2[Smack]
    LSM -->|module| TOMOYO2[Tomoyo]

    SEC -->|syscall-filter| SECCOMP2[seccomp]
    SEC -->|namespace| NS2[namespaces]
    SEC -->|resource| CG2[cgroups]
    SEC -->|integrity| IMA[IMA/EVM]
    SEC -->|crypto| KEYS[Kernel Key Retention Service]
```

---

## 8. 国际来源映射

| 概念域 | 来源类型 | 来源 | 位置 | 状态 |
|--------|----------|------|------|------|
| task_struct / 调度类 | SourceCode | Linux Kernel | include/linux/sched.h, kernel/sched/ | 已覆盖 |
| 内存管理 / VMA / 页表 | SourceCode | Linux Kernel | include/linux/mm_types.h, mm/ | 已覆盖 |
| VFS | SourceCode | Linux Kernel | fs/ | 已覆盖 |
| 网络子系统 | SourceCode | Linux Kernel | net/ | 已覆盖 |
| 设备模型 | SourceCode | Linux Kernel | drivers/base/ | 已覆盖 |
| LSM / capabilities | SourceCode | Linux Kernel | security/, include/linux/cred.h | 已覆盖 |
| 系统调用语义 | Reference | Linux man-pages | Section 2/3 | 已覆盖 |
| 内核开发 | Textbook | Robert Love, *Linux Kernel Development* | 3rd Ed. | 已覆盖 |

---

## 9. 相关文件

- [Linux 属性-关系映射](./linux-attribute-relationship-map.md)
- [Linux 机制组合树](./linux-mechanism-composition-tree.md)
- [Linux 依赖树](./linux-dependency-tree.md)
- [Linux 场景分析树](./linux-scenario-analysis-tree.md)
- [Linux 源码地图](./linux-source-map.md)
- [通用 OS 概念树](../00-concept-atlas/concept-tree-os.md)
