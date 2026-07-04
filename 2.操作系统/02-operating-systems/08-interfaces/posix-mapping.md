# POSIX 与 Linux 实现条款映射


<!-- TOC START -->

- [POSIX 与 Linux 实现条款映射](#posix-与-linux-实现条款映射)
  - [1. POSIX §3 进程/线程控制](#1-posix-3-进程线程控制)
  - [2. POSIX §13 文件系统接口](#2-posix-13-文件系统接口)
  - [3. POSIX §16 网络 Socket](#3-posix-16-网络-socket)
  - [4. POSIX §17 实时扩展](#4-posix-17-实时扩展)
  - [5. pthread 同步](#5-pthread-同步)
  - [6. Linux 特有扩展](#6-linux-特有扩展)
  - [7. 覆盖状态汇总](#7-覆盖状态汇总)
  - [8. 术语表](#8-术语表)
  - [9. 国际来源映射](#9-国际来源映射)
  - [10. 相关文件](#10-相关文件)
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

| POSIX 条款 | POSIX 函数 | Linux 实现 | 源码 |
|------------|------------|------------|------|
| §17.1 Real-time Signals | `sigqueue()` | 实时信号 32~64 | `kernel/signal.c` |
| §17.2 Message Queues | `mq_open()` | POSIX message queue | `ipc/mqueue.c` |
| §17.3 Semaphores | `sem_init()` | 无名/有名信号量 | nptl, `ipc/sem.c` |
| §17.4 Shared Memory | `shm_open()` | POSIX shared memory | `ipc/shm.c` |
| §17.5 Asynchronous I/O | `aio_read()` | Linux native aio | `fs/aio.c` |
| §17.6 Memory Locking | `mlock()` | 锁定内存页 | `mm/mlock.c` |

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
| io_uring | 非 POSIX | `sys_io_uring_setup()` / `enter()` | `fs/io_uring.c` |
| inotify | 非 POSIX | `sys_inotify_init()` | `fs/notify/inotify/` |
| signalfd / eventfd / timerfd | 非 POSIX | `sys_signalfd()` / `eventfd()` / `timerfd_create()` | `fs/signalfd.c`, `fs/eventfd.c`, `fs/timerfd.c` |
| memfd | 非 POSIX | `sys_memfd_create()` | `mm/memfd.c` |
| bpf | 非 POSIX | `sys_bpf()` | `kernel/bpf/syscall.c` |

---

## 7. 覆盖状态汇总

| POSIX 章节 | 覆盖状态 | 缺口 |
|------------|----------|------|
| §3 进程/线程 | 完整 | - |
| §13 文件系统 | 完整 | - |
| §16 网络 | 完整 | - |
| §17 实时 | 部分 | POSIX aio 深入机制 |
| 非 POSIX 扩展 | 已列出 | 可继续扩展 io_uring 细节 |

---

## 8. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| POSIX | Portable Operating System Interface | 可移植操作系统接口标准 |
| LSB | Linux Standard Base | Linux 标准化规范 |
| futex | Fast Userspace muTEX | Linux 用户态/内核态混合互斥原语 |
| real-time signal | 实时信号 | 支持排队的扩展信号 |
| aio | Asynchronous I/O | POSIX 异步 I/O 接口 |

---

## 9. 国际来源映射

| 概念 | 来源类型 | 来源 | 位置 |
|------|----------|------|------|
| POSIX | Standard | IEEE | POSIX.1-2024 |
| LSB | Standard | Linux Foundation | LSB 5.0 Core |
| System V ABI | Standard | AMD / Intel | System V ABI |
| Linux Syscall Table | SourceCode | Linux Kernel | `arch/x86/entry/syscalls/syscall_64.tbl` |
| glibc | SourceCode | GNU | nptl, posix/ |

---

## 10. 相关文件

- [系统调用接口](./syscall-interface.md)
- [ABI/API](./abi-api.md)
- [Linux 网络协议栈](../06-networking/linux-network-stack.md)
- [Linux 内核源码映射](../05-linux-kernel/linux-source-map.md)

## 国际权威来源链接 / Authoritative Sources

- [POSIX.1-2024 Base Definitions](https://pubs.opengroup.org/onlinepubs/9799919799/)
- [POSIX.1-2024 System Interfaces](https://pubs.opengroup.org/onlinepubs/9799919799/)
- [Linux man-pages project](https://www.kernel.org/doc/man-pages/)
