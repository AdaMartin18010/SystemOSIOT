# OS / 网络 / 外设 / 接口 跨域术语对照表


<!-- TOC START -->

- [OS / 网络 / 外设 / 接口 跨域术语对照表](#os--网络--外设--接口-跨域术语对照表)
  - [1. 执行单元](#1-执行单元)
  - [2. 调度](#2-调度)
  - [3. 内存](#3-内存)
  - [4. 网络](#4-网络)
  - [5. 外设与总线](#5-外设与总线)
  - [6. 接口与抽象](#6-接口与抽象)
  - [7. 安全](#7-安全)
  - [8. 相关文件](#8-相关文件)

<!-- TOC END -->

> **目标**：统一 `2.操作系统/`、`3.物联网嵌入式系统/`、`8.网络系统/` 三大领域中容易混淆的术语，避免同名异义或异名同义。

---

## 1. 执行单元

| 中文 | 通用 OS | Linux | RTOS/嵌入式 |
|------|---------|-------|-------------|
| 进程 | Process | `task_struct` (with mm) | — |
| 线程 | Thread | `task_struct` (共享 mm) | Task |
| 任务 | Task | `task_struct` / `work_struct` | Task / Thread |
| 协程 | Coroutine | 用户态实现（e.g., ucontext） | — |

---

## 2. 调度

| 中文 | 通用 OS | Linux | RTOS |
|------|---------|-------|------|
| 调度器 | Scheduler | CFS / RT / DL / Idle | Fixed Priority / EDF |
| 调度实体 | Schedulable Entity | `sched_entity` / `rt_rq` | TCB |
| 时间片 | Time Quantum / Slice | `sched_min_granularity_ns` | Tick |
| 抢占 | Preemption | `CONFIG_PREEMPT` | 默认可抢占 |

---

## 3. 内存

| 中文 | 通用 OS | Linux | 嵌入式 |
|------|---------|-------|--------|
| 虚拟地址 | Virtual Address | `mm_struct` / page table | MPU region |
| 物理页 | Physical Page | `struct page` | — |
| 页表 | Page Table | `pgd`/`pud`/`pmd`/`pte` | — |
| 内存保护 | Memory Protection | MMU + page flags | MPU / MMU |
| 缓存 | Cache | page cache / slab | — |

---

## 4. 网络

| 中文 | OSI/通用 | Linux 实现 | 嵌入式 |
|------|----------|------------|--------|
| 套接字 | Socket | `struct socket` → `struct sock` | lwIP socket API |
| 数据包 | Packet / PDU | `struct sk_buff` | pbuf |
| 协议栈 | Protocol Stack | `net/` 子系统 | lwIP / FreeRTOS+TCP |
| 网卡 | NIC | `struct net_device` | 以太 MAC |
| 多路复用 | Multiplexing | epoll / io_uring | select / poll |
| 数据面卸载 | Offload | NAPI / GRO / GSO / TSO | — |

---

## 5. 外设与总线

| 中文 | 通用 | Linux | 嵌入式/RTOS |
|------|------|-------|-------------|
| 总线 | Bus | `struct bus_type` | 片上总线 |
| 设备 | Device | `struct device` | Device Object |
| 驱动 | Driver | `struct device_driver` | HAL driver |
| 中断 | Interrupt / IRQ | `irq_desc` / `request_irq()` | ISR / NVIC |
| DMA | Direct Memory Access | `dmaengine` / `dma_map_*` | DMA controller |
| I2C | Inter-Integrated Circuit | `i2c_adapter` / `i2c_client` | I2C HAL |
| SPI | Serial Peripheral Interface | `spi_master` / `spi_device` | SPI HAL |
| UART | Universal Asynchronous Receiver-Transmitter | `uart_driver` / `uart_port` | UART HAL |
| GPIO | General Purpose I/O | `gpiochip` / `gpiod` | GPIO HAL |
| CAN | Controller Area Network | `socketcan` / `can_dev` | CAN HAL |
| PCIe | PCI Express | `pci_dev` / `pci_driver` | — |

---

## 6. 接口与抽象

| 中文 | 通用 | Linux | 嵌入式 |
|------|------|-------|--------|
| 系统调用 | System Call | `SYSCALL_DEFINE*` | SVC / ecall |
| ABI | Application Binary Interface | System V AMD64 ABI | EABI / AAPCS |
| API | Application Programming Interface | POSIX / glibc | CMSIS / HAL API |
| HAL | Hardware Abstraction Layer | 厂商 BSP / device tree | CMSIS / Zephyr driver API |
| BSP | Board Support Package | `arch/arm/boot/dts` / `board/` | 板级初始化代码 |
| 设备树 | Device Tree | DTB / DTS / bindings | Device Tree |

---

## 7. 安全

| 中文 | Linux | RTOS/嵌入式 |
|------|-------|-------------|
| 隔离 | namespace / cgroup / LSM | MPU / TrustZone |
| 强制访问控制 | SELinux / AppArmor / Smack | — |
| 能力 | capabilities | — |
| 系统调用过滤 | seccomp | — |
| 安全启动 | secure boot | secure boot |

---

## 8. 相关文件

- [操作系统概念树](../2.操作系统/02-operating-systems/00-concept-atlas/concept-tree-os.md)
- [跨域映射](../Analysis/操作系统-网络-嵌入式-接口跨域映射.md)
