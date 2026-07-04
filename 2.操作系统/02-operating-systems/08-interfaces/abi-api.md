# ABI 与 API 接口层映射

> **目标**：区分 ABI（Application Binary Interface）与 API（Application Programming Interface），并映射到 Linux/POSIX 系统调用与库接口。

---

## 1. API vs ABI 对比

| 维度 | API | ABI |
|------|-----|-----|
| 层级 | 源代码/语言级别 | 二进制/机器码级别 |
| 内容 | 函数签名、数据结构、宏 | 调用约定、寄存器使用、内存布局、符号名 |
| 稳定性 | 通常较稳定 | 一旦发布必须严格保持 |
| 兼容性 | 源码兼容 | 二进制兼容 |
| 例子 | POSIX `open()` | System V AMD64 ABI、x86_64 syscall ABI |

---

## 2. Linux API 层次

```mermaid
graph LR
    APP[应用程序] -->|API| GLIBC[glibc]
    GLIBC -->|API| SYSCALL[系统调用封装]
    SYSCALL -->|ABI| KERNEL[Linux 内核]
    KERNEL -->|Driver ABI| DRIVER[设备驱动]
```

---

## 3. 系统调用 ABI（x86_64）

| 项目 | 约定 |
|------|------|
| 系统调用号 | `rax` |
| 参数 1~6 | `rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9` |
| 返回值 | `rax` |
| 调用指令 | `syscall` |
| 破坏寄存器 | `rcx`, `r11` |

### 3.1 示例：`write(1, buf, len)`

```asm
mov rax, 1      ; __NR_write
mov rdi, 1      ; fd
mov rsi, buf    ; buffer
mov rdx, len    ; count
syscall
```

---

## 4. POSIX API → 系统调用映射

| POSIX API | glibc 封装 | Linux 系统调用 |
|-----------|------------|----------------|
| `open()` | `__libc_open()` | `sys_openat()` |
| `read()` | `__libc_read()` | `sys_read()` |
| `write()` | `__libc_write()` | `sys_write()` |
| `close()` | `__close_nocancel()` | `sys_close()` |
| `mmap()` | `__mmap()` | `sys_mmap()` |
| `fork()` | `__libc_fork()` | `sys_clone()` |
| `pthread_create()` | `create_thread()` | `sys_clone3()` |
| `socket()` | `__socket()` | `sys_socket()` |

---

## 5. 内核与用户态 ABI

| ABI 类型 | 说明 |
|----------|------|
| System Call ABI | 寄存器约定、调用门 |
| Virtual Dynamic Shared Object (vDSO) | 用户态快速读取时间 |
| Signal ABI | 信号帧布局 |
| ELF ABI | 可执行文件格式、段布局 |
| Netlink ABI | 用户态与内核网络配置接口 |

---

## 6. 稳定性与兼容性

| 接口 | 稳定性 |
|------|--------|
| POSIX | 非常稳定 |
| Linux 系统调用 | 稳定（但新增） |
| glibc ABI | 向后兼容 |
| 内核模块 ABI | 不保证跨版本兼容 |
| `/proc`, `/sys` | 格式约定，但可能变化 |

---

## 7. 相关文件

- [系统调用接口](./syscall-interface.md)
- [POSIX 映射](./posix-mapping.md)
- [内核-用户边界](./kernel-user-boundary.md)
