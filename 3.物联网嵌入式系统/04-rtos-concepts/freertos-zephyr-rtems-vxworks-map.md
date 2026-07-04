# FreeRTOS / Zephyr / RTEMS / VxWorks 对比映射

> **权威来源**：FreeRTOS Docs, Zephyr Docs, RTEMS Docs, VxWorks Docs。
>
> **目标**：对比主流 RTOS 的任务模型、调度器、同步原语、内存、中断、安全、适用场景。

---

## 1. 总体对比

| 特性 | FreeRTOS | Zephyr | RTEMS | VxWorks |
|------|----------|--------|-------|---------|
| 许可证 | MIT | Apache 2.0 | BSD/GPL | 商业 |
| 首次发布 | 2003 | 2016 | 1988 | 1987 |
| 内核大小 | 4~9 KB RAM | 8~50 KB | 数十 KB~MB | 较大 |
| 架构支持 | 35+ | ARM/x86/RISC-V/ARC/... | 大量 | 大量 |
| 调度器 | 优先级抢占 + 可选时间片 | 优先级抢占 + 时间片 | 多种调度器 | 多种调度器 |
| POSIX | 部分 | 部分 | 完整 | 完整 |
| 网络协议栈 | FreeRTOS+TCP / lwIP | 原生 + lwIP | RTEMS 网络 | WindNet |
| 文件系统 | FreeRTOS-Plus-FAT | 原生/NVS/littlefs | IMFS/... | HRFS/... |
| 安全认证 | 安全相关扩展 | 发展中 | 航天/航空认证 | DO-178C, IEC 61508 |

---

## 2. 任务/线程模型

| RTOS | 任务结构 | 上下文切换 |
|------|----------|------------|
| FreeRTOS | `TaskHandle_t` | 基于优先级就绪列表 |
| Zephyr | `k_thread` | 基于优先级就绪队列 |
| RTEMS | `rtems_task` | 可配置调度类 |
| VxWorks | `TASK_ID` |  Wind 内核调度 |

---

## 3. 调度器对比

| RTOS | 默认调度 | 可选调度 |
|------|----------|----------|
| FreeRTOS | 固定优先级抢占 | EDF（FreeRTOS-Plus） |
| Zephyr | 固定优先级抢占 + 时间片 | 合作式 |
| RTEMS | 固定优先级 | EDF、常量带宽服务器 |
| VxWorks | 固定优先级抢占 | 时间片、EDF |

---

## 4. 同步原语对比

| 原语 | FreeRTOS | Zephyr | RTEMS | VxWorks |
|------|----------|--------|-------|---------|
| 互斥锁 | `xSemaphoreTake(Mutex)` | `k_mutex_lock()` | `rtems_semaphore_obtain` | `semTake()` |
| 信号量 | `xSemaphoreGive/Take` | `k_sem_give/take()` | `rtems_semaphore_*` | `sem*()` |
| 队列 | `xQueueSend/Receive` | `k_msgq_*` | `rtems_message_queue_*` | `msgQ*()` |
| 事件 | `xEventGroupSetBits` | `k_poll_signal` | `rtems_event_*` | `event*()` |
| 互斥锁优先级继承 | 可选 | 支持 | 支持 | 支持 |

---

## 5. 中断与内存

| 特性 | FreeRTOS | Zephyr | RTEMS | VxWorks |
|------|----------|--------|-------|---------|
| 中断延迟 | 极低 | 低 | 低 | 极低 |
| Tickless | 支持 | 支持 | 支持 | 支持 |
| 静态分配 | 支持 | 原生支持 | 支持 | 支持 |
| 动态堆 | `pvPortMalloc` | `k_malloc` | `malloc` | `memPartAlloc` |
| MPU/MMU | FreeRTOS-MPU | 支持 | 支持 | 支持 |

---

## 6. 设备树与 HAL

| RTOS | 设备描述 | HAL |
|------|----------|-----|
| FreeRTOS | 板级文件 / CMSIS | 厂商 HAL |
| Zephyr | Device Tree | 统一设备驱动 API |
| RTEMS | Device Tree / BSP | BSP + libbsd |
| VxWorks | Device Tree / BSP | vxBus |

---

## 7. 场景选择

| 场景 | 推荐 RTOS | 原因 |
|------|-----------|------|
| 低成本 MCU | FreeRTOS | 极简，生态广 |
| 物联网/边缘 | Zephyr | 现代，安全，统一 API |
| 航天/航空 | RTEMS / VxWorks | 认证，高可靠 |
| 汽车电子 | VxWorks / FreeRTOS | 安全认证，实时性 |
| 工业控制 | VxWorks / RTEMS | 确定性，长周期支持 |
| 开源社区项目 | Zephyr / FreeRTOS | 活跃社区 |

---

## 8. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| Tickless | 无节拍 | 减少定时器中断以降低功耗 |
| MPU | Memory Protection Unit | 内存保护单元 |
| BSP | Board Support Package | 板级支持包 |
| HAL | Hardware Abstraction Layer | 硬件抽象层 |
| 静态分配 | Static Allocation | 编译时分配资源，避免运行时碎片 |

---

## 9. 相关文件

- [RTOS 概念树](./rtos-concept-tree.md)
- [Linux vs RTOS 决策树](../06-decision-trees/linux-vs-rtos.md)

## 国际权威来源链接 / Authoritative Sources

- [FreeRTOS Documentation](https://www.freertos.org/Documentation/RTOS-book)
- [Zephyr Project Documentation](https://docs.zephyrproject.org/)
- [RTEMS Documentation](https://docs.rtems.org/)
- [Wind River VxWorks Documentation](https://docs.windriver.com/)
