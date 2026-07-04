# Linux 内存管理


<!-- TOC START -->

- [Linux 内存管理](#linux-内存管理)
  - [1. 核心数据结构](#1-核心数据结构)
  - [2. 物理页分配](#2-物理页分配)
    - [2.1 伙伴系统（Buddy System）](#21-伙伴系统buddy-system)
    - [2.2 内存区](#22-内存区)
  - [3. Slab / SLUB 分配器](#3-slab--slub-分配器)
  - [4. 虚拟内存](#4-虚拟内存)
    - [4.1 缺页处理](#41-缺页处理)
    - [4.2 页表](#42-页表)
    - [4.3 请求调页与写时复制](#43-请求调页与写时复制)
  - [5. 页缓存与 Swap](#5-页缓存与-swap)
    - [5.1 页缓存（Page Cache）](#51-页缓存page-cache)
    - [5.2 Swap](#52-swap)
    - [5.3 页面回收算法](#53-页面回收算法)
  - [6. 大页与 NUMA](#6-大页与-numa)
    - [6.1 大页](#61-大页)
    - [6.2 NUMA](#62-numa)
  - [7. 内存管理工具](#7-内存管理工具)
  - [8. 场景分析](#8-场景分析)
  - [9. 术语表](#9-术语表)
  - [10. 国际来源映射](#10-国际来源映射)
  - [11. 相关文件](#11-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：Linux Kernel Development (Love), OSTEP Ch. 13~22, kernel.org `Documentation/mm/`, LWN.net。
>
> **目标**：深入 Linux 内存管理子系统：物理页分配、slab、虚拟内存、页缓存、swap、大页、NUMA。

---

## 1. 核心数据结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct page` | `include/linux/mm_types.h` | 物理页描述符 |
| `struct mm_struct` | `include/linux/mm_types.h` | 进程地址空间 |
| `struct vm_area_struct` | `include/linux/mm_types.h` | 虚拟内存区域 |
| `struct zone` | `include/linux/mmzone.h` | 内存区（DMA/Normal/HighMem/Movable） |
| `struct pglist_data` | `include/linux/mmzone.h` | NUMA 节点 |
| `struct kmem_cache` | `include/linux/slab.h` | slab 缓存 |

---

## 2. 物理页分配

### 2.1 伙伴系统（Buddy System）

| 函数 | 说明 | 源码 |
|------|------|------|
| `alloc_pages()` | 分配 2^order 个连续页 | `mm/page_alloc.c` |
| `__alloc_pages()` | 核心分配函数 | `mm/page_alloc.c` |
| `free_pages()` | 释放并尝试合并伙伴块 | `mm/page_alloc.c` |

### 2.2 内存区

| Zone | 说明 |
|------|------|
| ZONE_DMA | 用于 DMA 的低端内存（x86 遗留） |
| ZONE_DMA32 | 32-bit 设备可访问内存 |
| ZONE_NORMAL | 常规可直接映射内存 |
| ZONE_HIGHMEM | 高端内存（32-bit 架构） |
| ZONE_MOVABLE | 可移动页，用于内存规整 |

---

## 3. Slab / SLUB 分配器

| 函数 | 说明 | 源码 |
|------|------|------|
| `kmalloc()` | 分配小块内核内存 | `mm/slub.c` |
| `kmem_cache_alloc()` | 从指定缓存分配 | `mm/slub.c` |
| `kfree()` | 释放 | `mm/slub.c` |

- SLUB 是 Linux 当前默认分配器，替代 SLAB。
- 减少元数据开销，更好的调试支持。

---

## 4. 虚拟内存

### 4.1 缺页处理

```text
用户访问未映射地址
  ↓ 触发 page fault
  ↓ do_page_fault() (arch specific)
    ↓ handle_mm_fault()
      ↓ __handle_mm_fault()
        ↓ 遍历页表层级
        ↓ 分配/读取页
```

| 函数 | 说明 | 源码 |
|------|------|------|
| `do_page_fault()` | x86 缺页入口 | `arch/x86/mm/fault.c` |
| `handle_mm_fault()` | 通用缺页处理 | `mm/memory.c` |
| `do_anonymous_page()` | 匿名页分配 | `mm/memory.c` |
| `do_fault()` | 文件映射页处理 | `mm/memory.c` |

### 4.2 页表

| 类型 | 说明 |
|------|------|
| `pgd_t` | Page Global Directory |
| `p4d_t` | Page 4th Level Directory |
| `pud_t` | Page Upper Directory |
| `pmd_t` | Page Middle Directory |
| `pte_t` | Page Table Entry |

### 4.3 请求调页与写时复制

- `MAP_PRIVATE` + 写操作 → COW 异常 → 复制私有页。
- `fork()` 时复制页表但不复制物理页，标记只读。

---

## 5. 页缓存与 Swap

### 5.1 页缓存（Page Cache）

| 概念 | 说明 |
|------|------|
| `address_space` | 文件 ↔ 页缓存映射 |
| `radix_tree` / `xarray` | 缓存页索引结构 |
| `read_cache_page()` | 读取页缓存 |
| `write_cache_pages()` | 回写脏页 |

### 5.2 Swap

| 函数 | 说明 | 源码 |
|------|------|------|
| `swap_readpage()` | 换入 | `mm/page_io.c` |
| `swap_writepage()` | 换出 | `mm/page_io.c` |
| `shrink_lruvec()` | 回收 LRU 页 | `mm/vmscan.c` |

### 5.3 页面回收算法

- 活跃 LRU / 非活跃 LRU。
- `kswapd` 后台回收。
- `direct reclaim` 直接回收（进程上下文）。

---

## 6. 大页与 NUMA

### 6.1 大页

| 类型 | 说明 |
|------|------|
| hugetlbfs | 预分配大页文件系统 |
| Transparent Huge Pages (THP) | 透明大页，自动合并 |

### 6.2 NUMA

| 概念 | 说明 |
|------|------|
| `pglist_data` | NUMA 节点描述 |
| `numa_node_id()` | 当前 CPU 所属节点 |
| NUMA balancing | 自动页迁移平衡 |
| `mpol_*` | 内存策略 API |

---

## 7. 内存管理工具

| 工具 | 用途 |
|------|------|
| `free` | 查看内存使用 |
| `vmstat` | 虚拟内存统计 |
| `sar -B` | 分页统计 |
| `/proc/meminfo` | 详细内存信息 |
| `/proc/<pid>/maps` | 进程地址空间 |
| `/proc/<pid>/smaps` | 详细内存映射 |
| `numactl` | NUMA 控制 |

---

## 8. 场景分析

| 场景 | 关键机制 | 关键参数 | 验证指标 |
|------|----------|----------|----------|
| 数据库大内存 | hugepages / THP | `vm.nr_hugepages`, `transparent_hugepage` | TLB miss |
| 高并发服务 | slab tuning / page cache | `slab_*`, `vfs_cache_pressure` | 内存碎片 |
| 内存不足 | OOM killer / swap | `vm.swappiness`, `oom_score_adj` | OOM 频率 |
| NUMA 数据库 | NUMA policy / hugepages | `numactl --interleave` | 本地内存命中率 |

---

## 9. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| 伙伴系统 | Buddy System | 按 2 的幂分配连续物理页的算法 |
| SLUB | SLUB Allocator | Linux 默认的小对象内核分配器 |
| VMA | Virtual Memory Area | 进程地址空间中的连续虚拟内存区域 |
| Page Cache | 页缓存 | 文件数据在内存中的缓存 |
| Swap | 交换 | 将不活跃页换出到磁盘 |
| THP | Transparent Huge Pages | 透明大页机制 |
| NUMA | Non-Uniform Memory Access | 非一致内存访问架构 |
| OOM | Out of Memory | 内存耗尽时的处理机制 |

---

## 10. 国际来源映射

| 概念 | 来源类型 | 来源 | 位置 |
|------|----------|------|------|
| 内存管理 | Textbook | OSTEP | Ch. 13~22 |
| Linux 内存 | SourceCode | Linux Kernel | `mm/` |
| 伙伴系统 | SourceCode | Linux Kernel | `mm/page_alloc.c` |
| SLUB | SourceCode | Linux Kernel | `mm/slub.c` |
| NUMA | SourceCode | Linux Kernel | `mm/mempolicy.c` |

---

## 11. 相关文件

- [Linux 内核源码映射](./linux-source-map.md)
- [进程调度](./process-scheduling-linux.md)
- [VFS 与文件系统](./vfs-filesystems-linux.md)
- [操作系统机制组合树](../00-concept-atlas/mechanism-composition-tree-os.md)

## 国际权威来源链接 / Authoritative Sources

- [Linux Kernel - Memory Management documentation](https://docs.kernel.org/mm/)
- [Linux Kernel - Page Allocator](https://docs.kernel.org/mm/page_owner.html)
- [Linux Kernel - SLUB](https://docs.kernel.org/mm/slub.html)
- [Understanding the Linux Kernel (Bovet & Cesati)](https://www.amazon.com/Understanding-Linux-Kernel-Third-Daniel/dp/0596005652)
