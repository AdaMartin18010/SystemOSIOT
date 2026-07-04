# Linux 进程调度


<!-- TOC START -->

- [Linux 进程调度](#linux-进程调度)
  - [1. 核心数据结构](#1-核心数据结构)
    - [1.1 task_struct](#11-task_struct)
    - [1.2 sched_entity（CFS）](#12-sched_entitycfs)
    - [1.3 sched_class](#13-sched_class)
  - [2. 调度类层次](#2-调度类层次)
  - [3. CFS 完全公平调度器](#3-cfs-完全公平调度器)
    - [3.1 核心思想](#31-核心思想)
    - [3.2 vruntime 计算](#32-vruntime-计算)
    - [3.3 关键函数](#33-关键函数)
    - [3.4 调度时延](#34-调度时延)
  - [4. 实时调度](#4-实时调度)
    - [4.1 SCHED_FIFO](#41-sched_fifo)
    - [4.2 SCHED_RR](#42-sched_rr)
    - [4.3 SCHED_DEADLINE](#43-sched_deadline)
    - [4.4 关键函数](#44-关键函数)
  - [5. 进程创建与退出](#5-进程创建与退出)
  - [6. cgroup 与 namespace](#6-cgroup-与-namespace)
    - [6.1 cgroup](#61-cgroup)
    - [6.2 namespace](#62-namespace)
  - [7. 调度相关系统调用与工具](#7-调度相关系统调用与工具)
  - [8. 场景分析](#8-场景分析)
  - [9. 术语表](#9-术语表)
  - [10. 国际来源映射](#10-国际来源映射)
  - [11. 相关文件](#11-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：Linux Kernel Development (Love), OSTEP Ch. 7~9, kernel.org `Documentation/scheduler/`, LWN.net。
>
> **目标**：深入 Linux 进程/线程描述符、调度类、CFS、实时调度、cgroup、namespace 的实现与源码映射。

---

## 1. 核心数据结构

### 1.1 task_struct

| 字段 | 说明 |
|------|------|
| `pid` | 进程 ID |
| `tgid` | 线程组 ID |
| `state` | 任务状态：TASK_RUNNING, TASK_INTERRUPTIBLE, TASK_UNINTERRUPTIBLE 等 |
| `mm` | 进程地址空间 `struct mm_struct` |
| `sched_class` | 调度类指针 |
| `se` | CFS 调度实体 `struct sched_entity` |
| `rt` | 实时调度实体 `struct sched_rt_entity` |
| `dl` | deadline 调度实体 `struct sched_dl_entity` |
| `files` | 打开文件表 |
| `signal` | 信号处理结构 |
| `cgroup` | cgroup 指针 |
| `nsproxy` | 命名空间代理 |

### 1.2 sched_entity（CFS）

| 字段 | 说明 |
|------|------|
| `vruntime` | 虚拟运行时间，CFS 选择最小 vruntime 运行 |
| `load` | 任务权重 |
| `run_node` | 红黑树节点 |
| `on_rq` | 是否在运行队列 |

### 1.3 sched_class

```c
struct sched_class {
    void (*enqueue_task) (...);
    void (*dequeue_task) (...);
    struct task_struct *(*pick_next_task) (...);
    void (*task_tick) (...);
    void (*update_curr) (...);
};
```

---

## 2. 调度类层次

```mermaid
graph TD
    SCHED[schedule()] -->|优先级最高| DL[SCHED_DEADLINE]
    SCHED -->|次高| RT[SCHED_FIFO / SCHED_RR]
    SCHED -->|默认| CFS[SCHED_NORMAL / SCHED_BATCH / SCHED_IDLE]

    DL -->|src| DL_SCHED[kernel/sched/deadline.c]
    RT -->|src| RT_SCHED[kernel/sched/rt.c]
    CFS -->|src| FAIR[kernel/sched/fair.c]
```

| 调度类 | 策略 | 适用场景 |
|--------|------|----------|
| CFS | `SCHED_NORMAL`, `SCHED_BATCH`, `SCHED_IDLE` | 普通任务、批处理、idle |
| RT | `SCHED_FIFO`, `SCHED_RR` | 实时任务 |
| DL | `SCHED_DEADLINE` | 显式 deadline 任务 |

---

## 3. CFS 完全公平调度器

### 3.1 核心思想

- 每个任务按权重分配 CPU 时间。
- 选择 `vruntime` 最小的任务运行。
- 使用红黑树维护可运行任务。

### 3.2 vruntime 计算

```text
vruntime += delta_exec * NICE_0_LOAD / se->load.weight
```

- nice 值越小，权重越大，vruntime 增长越慢。
- nice 范围：-20 ~ 19，对应权重见 `sched_prio_to_weight[]`。

### 3.3 关键函数

| 函数 | 说明 | 源码 |
|------|------|------|
| `pick_next_task_fair()` | 选择红黑树最左节点 | `kernel/sched/fair.c` |
| `enqueue_task_fair()` | 将任务加入红黑树 | `kernel/sched/fair.c` |
| `dequeue_task_fair()` | 将任务移出红黑树 | `kernel/sched/fair.c` |
| `update_curr()` | 更新当前任务 vruntime | `kernel/sched/fair.c` |
| `check_preempt_tick()` | 检查是否需要抢占 | `kernel/sched/fair.c` |

### 3.4 调度时延

| 参数 | 说明 | 默认值 |
|------|------|--------|
| `sched_latency_ns` | 目标调度延迟 | 6 ms |
| `sched_min_granularity_ns` | 最小时间片 | 0.75 ms |
| `sched_wakeup_granularity_ns` | 唤醒抢占粒度 | 1 ms |

---

## 4. 实时调度

### 4.1 SCHED_FIFO

- 同优先级任务先到先服务，高优先级任务可立即抢占。
- 没有时间片，一直运行到阻塞或主动放弃。

### 4.2 SCHED_RR

- 同优先级任务轮转，有时间片。
- 时间片耗尽后放到同优先级队列尾部。

### 4.3 SCHED_DEADLINE

- 基于 EDF（Earliest Deadline First）。
- 每个任务声明 runtime、period、deadline。

### 4.4 关键函数

| 函数 | 说明 | 源码 |
|------|------|------|
| `pick_next_task_rt()` | 选择最高优先级 RT 任务 | `kernel/sched/rt.c` |
| `enqueue_task_rt()` | 加入 RT 优先级队列 | `kernel/sched/rt.c` |
| `pick_next_task_dl()` | 选择最早 deadline 任务 | `kernel/sched/deadline.c` |

---

## 5. 进程创建与退出

| 系统调用 | 内核路径 | 说明 |
|----------|----------|------|
| `fork()` | `kernel/fork.c:_do_fork()` | 复制进程 |
| `clone()` | `kernel/fork.c:_do_fork()` | 创建线程/进程 |
| `execve()` | `fs/exec.c:do_execve()` | 加载新程序 |
| `exit()` | `kernel/exit.c:do_exit()` | 进程退出 |
| `wait()` | `kernel/exit.c:do_wait()` | 等待子进程 |

---

## 6. cgroup 与 namespace

### 6.1 cgroup

| 控制器 | 作用 |
|--------|------|
| cpu | CPU 时间分配 |
| cpuacct | CPU 使用统计 |
| cpuset | CPU/内存节点绑定 |
| memory | 内存限制 |
| blkio | 块 I/O 限制 |
| pids | 进程数限制 |

### 6.2 namespace

| 类型 | 隔离资源 |
|------|----------|
| PID | 进程 ID |
| Network | 网络设备、栈、端口 |
| Mount | 挂载点 |
| IPC | System V IPC / POSIX message queue |
| UTS | hostname/domainname |
| User | UID/GID |
| Cgroup | cgroup 视图 |
| Time | 系统时间视图 |

---

## 7. 调度相关系统调用与工具

| 系统调用/工具 | 作用 |
|---------------|------|
| `sched_setscheduler()` | 设置调度策略和优先级 |
| `nice()` | 调整 nice 值 |
| `sched_setaffinity()` | 设置 CPU 亲和性 |
| `sched_yield()` | 主动让出 CPU |
| `chrt` | 命令行设置实时调度 |
| `taskset` | 命令行设置 CPU 亲和性 |
| `schedtool` | 调度策略调试 |

---

## 8. 场景分析

| 场景 | 调度策略 | 关键参数 | 验证指标 |
|------|----------|----------|----------|
| Web 服务器 | CFS | nice, cgroup cpu.shares | 吞吐, P99 延迟 |
| 实时控制 | SCHED_FIFO + PREEMPT_RT | priority, cpu isolation | 最坏中断延迟 |
| 批处理 | SCHED_BATCH | 最低优先级 | 完成时间 |
| 视频渲染 | SCHED_DEADLINE | runtime/period | deadline 满足率 |

---

## 9. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| CFS | Completely Fair Scheduler | Linux 默认公平调度器 |
| vruntime | Virtual Runtime | CFS 用于公平调度的虚拟运行时间 |
| SCHED_FIFO | First-In-First-Out | 实时先进先出调度 |
| SCHED_RR | Round-Robin | 实时轮转调度 |
| SCHED_DEADLINE | Deadline Scheduling | 基于最早截止期限的调度 |
| cgroup | Control Group | Linux 资源限制与统计机制 |
| namespace | Namespace | Linux 资源隔离机制 |
| 任务组 | Task Group | CFS 中按组分配 CPU 时间 |

---

## 10. 国际来源映射

| 概念 | 来源类型 | 来源 | 位置 |
|------|----------|------|------|
| CFS | SourceCode | Linux Kernel | `kernel/sched/fair.c` |
| RT 调度 | SourceCode | Linux Kernel | `kernel/sched/rt.c` |
| Deadline | SourceCode | Linux Kernel | `kernel/sched/deadline.c` |
| 调度框架 | SourceCode | Linux Kernel | `kernel/sched/core.c` |
| 调度理论 | Textbook | OSTEP | Ch. 7~9 |
| 实时调度 | Paper | Liu & Layland | JACM 1973 |

---

## 11. 相关文件

- [Linux 内核源码映射](./linux-source-map.md)
- [内存管理](./memory-management-linux.md)
- [操作系统场景分析树](../00-concept-atlas/scenario-analysis-tree-os.md)

## 国际权威来源链接 / Authoritative Sources

- [Linux Kernel - Scheduler documentation](https://docs.kernel.org/scheduler/)
- [Linux Kernel - CFS Scheduler](https://docs.kernel.org/scheduler/sched-design-CFS.html)
- [Linux Kernel - Control Groups v2](https://docs.kernel.org/admin-guide/cgroup-v2.html)
- [Linux Kernel Development (Robert Love)](https://www.amazon.com/Linux-Kernel-Development-Robert-Love/dp/0672329468)
