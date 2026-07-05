# POSIX 与 Linux 实现条款映射


<!-- TOC START -->

- [POSIX 与 Linux 实现条款映射](#posix-与-linux-实现条款映射)
  - [1. POSIX §3 进程/线程控制](#1-posix-3-进程线程控制)
  - [2. POSIX §13 文件系统接口](#2-posix-13-文件系统接口)
  - [3. POSIX §16 网络 Socket](#3-posix-16-网络-socket)
  - [4. POSIX §17 实时扩展](#4-posix-17-实时扩展)
    - [4.1 实时调度](#41-实时调度)
    - [4.2 POSIX 实时 IPC / 同步 / I/O](#42-posix-实时-ipc--同步--io)
  - [5. pthread 同步](#5-pthread-同步)
  - [6. Linux 特有扩展](#6-linux-特有扩展)
  - [7. POSIX aio 与 Linux io\_uring 映射](#7-posix-aio-与-linux-io_uring-映射)
  - [8. 覆盖状态汇总](#8-覆盖状态汇总)
  - [9. 术语表](#9-术语表)
  - [10. 国际来源映射](#10-国际来源映射)
  - [11. 相关文件](#11-相关文件)
  - [12. 维护记录](#12-维护记录)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：POSIX.1-2024, Linux Standard Base 5.0, Linux Kernel Source, glibc Source。
>
> **目标**：将 POSIX.1-2024 关键条款映射到 Linux 内核实现、glibc 函数与源码路径。

---

## 1. POSIX §3 进程/线程控制

| POSIX 条款 | POSIX 函数/概念 | Linux 系统调用 | glibc 封装 | Linux 源码 |
|------------|-----------------|----------------|------------|------------|
| §3.1 Process Creation | `fork()` | `sys_clone()` / `sys_fork()` | `fork()` | `kernel/fork.c` |
| §3.2 exec Family | `execve()` | `sys_execve()` | `execve()` | `fs/exec.c` |
| §3.3 Process Termination | `exit()` / `_exit()` | `sys_exit_group()` / `sys_exit()` | `exit()` | `kernel/exit.c` |
| §3.4 wait | `waitpid()` | `sys_wait4()` | `waitpid()` | `kernel/exit.c` |
| §2.9 Threads | `pthread_create()` | `sys_clone()` | `pthread_create()` | `kernel/fork.c`, nptl |
| §3.5 Process Groups | `setpgid()` | `sys_setpgid()` | `setpgid()` | `kernel/sys.c` |

---

## 2. POSIX §13 文件系统接口

| POSIX 条款 | POSIX 函数 | Linux 系统调用 | glibc | Linux 源码 |
|------------|------------|----------------|-------|------------|
| §13.1 open | `open()` | `sys_openat()` | `open()` | `fs/open.c` |
| §13.2 close | `close()` | `sys_close()` | `close()` | `fs/open.c` |
| §13.3 read | `read()` | `sys_read()` | `read()` | `fs/read_write.c` |
| §13.4 write | `write()` | `sys_write()` | `write()` | `fs/read_write.c` |
| §13.5 lseek | `lseek()` | `sys_lseek()` | `lseek()` | `fs/read_write.c` |
| §13.6 stat | `stat()` | `sys_newfstatat()` | `stat()` | `fs/stat.c` |
| §13.7 mkdir | `mkdir()` | `sys_mkdirat()` | `mkdir()` | `fs/namei.c` |
| §13.8 link/unlink | `link()` / `unlink()` | `sys_linkat()` / `sys_unlinkat()` | `link()` / `unlink()` | `fs/namei.c` |
| §13.9 dup | `dup()` | `sys_dup()` | `dup()` | `fs/file.c` |
| §13.10 fcntl | `fcntl()` | `sys_fcntl()` | `fcntl()` | `fs/fcntl.c` |
| §13.11 mmap | `mmap()` | `sys_mmap()` | `mmap()` | `mm/mmap.c` |

---

## 3. POSIX §16 网络 Socket

| POSIX 条款 | POSIX 函数 | Linux 系统调用 | glibc | Linux 源码 |
|------------|------------|----------------|-------|------------|
| §16.1 socket | `socket()` | `sys_socket()` | `socket()` | `net/socket.c` |
| §16.2 bind | `bind()` | `sys_bind()` | `bind()` | `net/socket.c` |
| §16.3 listen | `listen()` | `sys_listen()` | `listen()` | `net/socket.c` |
| §16.4 accept | `accept()` | `sys_accept4()` | `accept()` | `net/socket.c` |
| §16.5 connect | `connect()` | `sys_connect()` | `connect()` | `net/socket.c` |
| §16.6 send/recv | `send()` / `recv()` | `sys_sendto()` / `sys_recvfrom()` | `send()` / `recv()` | `net/socket.c` |
| §16.7 shutdown | `shutdown()` | `sys_shutdown()` | `shutdown()` | `net/socket.c` |
| §16.8 setsockopt | `setsockopt()` | `sys_setsockopt()` | `setsockopt()` | `net/socket.c` |

---

## 4. POSIX §17 实时扩展

### 4.1 实时调度

| POSIX 函数/概念 | Linux 系统调用 | glibc | Linux 源码 | 说明 |
|-----------------|----------------|-------|------------|------|
| `SCHED_FIFO` | `sys_sched_setscheduler()` | `pthread_setschedparam()` | `kernel/sched/rt.c` | 先进先出实时调度 |
| `SCHED_RR` | `sys_sched_setscheduler()` | `pthread_setschedparam()` | `kernel/sched/rt.c` | 时间片轮转实时调度 |
| `SCHED_DEADLINE` | `sys_sched_setscheduler()` | `sched_setscheduler()` | `kernel/sched/deadline.c` | EDF 截止期限调度 |
| `sched_setscheduler()` | `sys_sched_setscheduler()` | `sched_setscheduler()` | `kernel/sched/core.c` | 设置调度策略与参数 |
| `sched_getscheduler()` | `sys_sched_getscheduler()` | `sched_getscheduler()` | `kernel/sched/core.c` | 获取调度策略 |
| `sched_setparam()` | `sys_sched_setparam()` | `sched_setparam()` | `kernel/sched/core.c` | 设置调度参数 |
| `sched_getparam()` | `sys_sched_getparam()` | `sched_getparam()` | `kernel/sched/core.c` | 获取调度参数 |
| `sched_yield()` | `sys_sched_yield()` | `sched_yield()` | `kernel/sched/core.c` | 主动让出 CPU |
| `sched_get_priority_min/max()` | `sys_sched_get_priority_min/max()` | — | `kernel/sched/core.c` | 获取优先级范围 |

### 4.2 POSIX 实时 IPC / 同步 / I/O

| POSIX 条款 | POSIX 函数 | Linux 实现 | 源码 |
|------------|------------|------------|------|
| §17.1 Real-time Signals | `sigqueue()` | 实时信号 32~64 | `kernel/signal.c` |
| §17.2 Message Queues | `mq_open()` / `mq_send()` / `mq_receive()` | POSIX message queue | `ipc/mqueue.c` |
| §17.3 Semaphores | `sem_init()` / `sem_wait()` / `sem_post()` | 无名/有名信号量 | nptl, `ipc/sem.c` |
| §17.4 Shared Memory | `shm_open()` / `mmap()` | POSIX shared memory | `ipc/shm.c`, `mm/shmem.c` |
| §17.5 Asynchronous I/O | `aio_read()` / `aio_write()` / `aio_error()` / `aio_return()` | Linux native aio / io_uring | `fs/aio.c`, `fs/io_uring.c` |
| §17.6 Memory Locking | `mlock()` / `mlockall()` | 锁定内存页 | `mm/mlock.c` |
| §17.7 Memory Advisory | `madvise()` / `posix_madvise()` | 内存使用建议 | `mm/madvise.c` |

---

## 5. pthread 同步

| POSIX 函数 | Linux 实现 | 源码 |
|------------|------------|------|
| `pthread_mutex_lock()` | futex + 用户态快速路径 | nptl, `kernel/futex.c` |
| `pthread_cond_wait()` | futex | nptl, `kernel/futex.c` |
| `pthread_rwlock_*()` | futex | nptl |
| `pthread_barrier_*()` | futex | nptl |

---

## 6. Linux 特有扩展

| 机制 | POSIX 状态 | Linux 系统调用 | 源码 |
|------|------------|----------------|------|
| epoll | 非 POSIX | `sys_epoll_create1()` / `epoll_ctl()` / `epoll_wait()` | `fs/eventpoll.c` |
| io_uring | 非 POSIX | `sys_io_uring_setup()` / `sys_io_uring_enter()` / `sys_io_uring_register()` | `fs/io_uring.c` |
| inotify | 非 POSIX | `sys_inotify_init()` | `fs/notify/inotify/` |
| signalfd / eventfd / timerfd | 非 POSIX | `sys_signalfd()` / `eventfd()` / `timerfd_create()` | `fs/signalfd.c`, `fs/eventfd.c`, `fs/timerfd.c` |
| memfd | 非 POSIX | `sys_memfd_create()` | `mm/memfd.c` |
| bpf | 非 POSIX | `sys_bpf()` | `kernel/bpf/syscall.c` |

---

## 7. POSIX aio 与 Linux io_uring 映射

| POSIX aio 函数 | Linux native aio 路径 | io_uring 对应 | 说明 |
|----------------|----------------------|---------------|------|
| `aio_read()` | `fs/aio.c: aio_read()` | `io_uring_enter()` with read op | io_uring 提供更低的系统调用开销 |
| `aio_write()` | `fs/aio.c: aio_write()` | `io_uring_enter()` with write op | 支持 buffered 和 direct I/O |
| `aio_error()` | `fs/aio.c: aio_error()` | 检查 CQ ring entry | 查询完成状态 |
| `aio_return()` | `fs/aio.c: aio_return()` | 读取 CQ ring res | 获取完成结果 |
| `aio_suspend()` | `fs/aio.c: aio_suspend()` | `io_uring_enter()` wait for CQ | 等待至少一个请求完成 |
| `aio_cancel()` | `fs/aio.c: aio_cancel()` | 不支持直接取消，可通过 sqe flags 控制 | io_uring 取消需使用 `IORING_OP_ASYNC_CANCEL` |

**关键数据结构**：

- POSIX aio：`struct kiocb` + `struct iocb` + `struct io_event`
- io_uring：`struct io_uring_sqe`（提交队列条目）、`struct io_uring_cqe`（完成队列条目）、`io_uring` 上下文

**源码路径**：

- `fs/aio.c` — Linux native AIO
- `fs/io_uring.c` — io_uring 核心实现
- `include/uapi/linux/aio_abi.h` — AIO 用户态 ABI
- `include/uapi/linux/io_uring.h` — io_uring 用户态 ABI

---

## 8. 覆盖状态汇总

| POSIX 章节 | 覆盖状态 | 缺口 |
|------------|----------|------|
| §3 进程/线程 | 完整 | 可补充 pthread 同步 futex 实现细节 |
| §13 文件系统 | 完整 | - |
| §16 网络 | 完整 | - |
| §17 实时 | 已规划/基本覆盖 | SCHED_DEADLINE 运行时语义、aio 与 io_uring 对比 |
| 非 POSIX 扩展 | 已列出 | 可继续扩展 io_uring 细节 |

---

## 9. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| POSIX | Portable Operating System Interface | 可移植操作系统接口标准 |
| LSB | Linux Standard Base | Linux 标准化规范 |
| futex | Fast Userspace muTEX | Linux 用户态/内核态混合互斥原语 |
| real-time signal | 实时信号 | 支持排队的扩展信号 |
| aio | Asynchronous I/O | POSIX 异步 I/O 接口 |

---

## 10. 国际来源映射

| 概念 | 来源类型 | 来源 | 位置 |
|------|----------|------|------|
| POSIX | Standard | IEEE | POSIX.1-2024 |
| LSB | Standard | Linux Foundation | LSB 5.0 Core |
| System V ABI | Standard | AMD / Intel | System V ABI |
| Linux Syscall Table | SourceCode | Linux Kernel | `arch/x86/entry/syscalls/syscall_64.tbl` |
| glibc | SourceCode | GNU | nptl, posix/ |

---

## 11. 相关文件

- [系统调用接口](./syscall-interface.md)
- [ABI/API](./abi-api.md)
- [Linux 网络协议栈](../06-networking/linux-network-stack.md)
- [Linux 内核源码映射](../05-linux-kernel/linux-source-map.md)

## 12. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 POSIX 到 Linux 实现映射 | Kimi Code CLI |
| 2026-07-05 | 补全 POSIX §17 实时调度函数到 Linux 源码映射；扩展 pthread 同步 futex 实现细节；新增 POSIX aio / io_uring 映射 | Kimi Code CLI |

## 国际权威来源链接 / Authoritative Sources

- [POSIX.1-2024 Base Definitions](https://pubs.opengroup.org/onlinepubs/9799919799/)
- [POSIX.1-2024 System Interfaces](https://pubs.opengroup.org/onlinepubs/9799919799/)
- [Linux Standard Base (LSB) 5.0](https://refspecs.linuxfoundation.org/lsb.shtml)
- [System V ABI x86-64](https://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf)
- [Linux man-pages project](https://www.kernel.org/doc/man-pages/)
- [glibc source repository](https://sourceware.org/git/?p=glibc.git)
