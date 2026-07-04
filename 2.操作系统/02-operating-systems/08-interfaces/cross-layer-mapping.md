# 跨层映射图（Cross-Layer Mapping）

> **目标**：展示关键用户操作如何经过应用层、glibc、系统调用、内核子系统、驱动、硬件的完整路径。

---

## 1. `printf` → 屏幕/文件

```mermaid
graph LR
    A[printf] --> B[glibc 缓冲]
    B -->|行缓冲/全缓冲| C[write syscall]
    C --> D[vfs_write]
    D --> E[ext4_file_write_iter]
    E --> F[Page Cache]
    F --> G[Journal]
    G --> H[Block I/O Layer]
    H --> I[NVMe Driver]
    I --> J[DMA Ring]
    J --> K[SSD NAND]
```

| 层级 | 关键函数/结构 | 说明 |
|------|---------------|------|
| 应用层 | `printf()` | glibc 格式化输出 |
| glibc | `write()` wrapper | 行缓冲后触发系统调用 |
| 系统调用 | `sys_write()` | `SYSCALL_DEFINE3(write, ...)` |
| VFS | `vfs_write()` | 通用写入口 |
| 文件系统 | `ext4_file_write_iter()` | ext4 写处理 |
| 页缓存 | `generic_perform_write()` | 拷贝到 page cache |
| 日志 | `jbd2` | 事务日志 |
| 块层 | `submit_bio()` | 构造 bio |
| 驱动 | `nvme_queue_rq()` | NVMe 队列请求 |
| 硬件 | DMA + SSD | 物理写入 |

---

## 2. `socket()` + `send()` → 网络

```mermaid
graph LR
    A[send] --> B[glibc send]
    B --> C[sendto syscall]
    C --> D[sock_sendmsg]
    D --> E[tcp_sendmsg]
    E --> F[tcp_write_xmit]
    F --> G[tcp_transmit_skb]
    G --> H[ip_queue_xmit]
    H --> I[ip_local_out]
    I --> J[dev_queue_xmit]
    J --> K[ndo_start_xmit]
    K --> L[NIC Driver]
    L --> M[DMA Ring]
    M --> N[PHY/MAC]
```

| 层级 | 关键函数/结构 | 说明 |
|------|---------------|------|
| 应用层 | `send()` / `sendmsg()` | 用户态发送 |
| glibc | `sendto()` wrapper | - |
| 系统调用 | `sys_sendmsg()` | - |
| Socket 层 | `sock_sendmsg()` / `inet_sendmsg()` | BSD socket → INET |
| TCP | `tcp_sendmsg()` | 拷贝到 send buffer |
| TCP 输出 | `tcp_write_xmit()` | 拥塞控制、Nagle |
| IP | `ip_queue_xmit()` | 路由、分片 |
| 网络设备 | `dev_queue_xmit()` | qdisc 或直接发送 |
| 驱动 | `ndo_start_xmit()` | NIC 驱动发送 |
| 硬件 | DMA + PHY/MAC | 物理发送 |

---

## 3. 传感器读取 → I2C → 用户态

```mermaid
graph LR
    A[用户态 read] --> B[sys_read]
    B --> C[vfs_read]
    C --> D[iio_device_read]
    D --> E[i2c_transfer]
    E --> F[i2c_adapter]
    F --> G[I2C Controller Driver]
    G --> H[GPIO/I2C 硬件]
    H --> I[Sensor]
```

| 层级 | 关键函数/结构 | 说明 |
|------|---------------|------|
| 应用层 | `read()` / `sysfs` | 读取传感器数据 |
| 系统调用 | `sys_read()` | - |
| VFS | `vfs_read()` | - |
| IIO 子系统 | `iio_device_read()` / `iio_triggered_buffer_postenable()` | Industrial I/O |
| I2C 核心 | `i2c_transfer()` / `i2c_smbus_read_byte_data()` | 总线传输 |
| I2C 适配器 | `i2c_adapter` | 控制器抽象 |
| 驱动 | I2C controller driver | 控制 I2C 时序 |
| 硬件 | GPIO/SCL/SDA | 物理信号 |
| 传感器 | BME280/MPU6050 | 数据采集 |

---

## 4. 跨层接口映射表

| 用户操作 | 用户 API | 系统调用 | 内核子系统 | 驱动/硬件 |
|----------|----------|----------|------------|-----------|
| 写文件 | `write()` | `sys_write` | VFS → ext4 → block | NVMe/SATA → DMA → SSD |
| 发网络包 | `send()` | `sys_sendmsg` | socket → TCP → IP → net_device | NIC driver → DMA → PHY |
| 读传感器 | `read()` / sysfs | `sys_read` | IIO → I2C core | I2C controller → sensor |
| 控制 GPIO | `libgpiod` | `sys_ioctl` | GPIO chardev → gpiolib | gpiochip → GPIO 寄存器 |
| 打开串口 | `open()` | `sys_open` | tty core → uart driver | UART controller → 外设 |

---

## 5. 开销分析

| 路径 | 主要开销 | 优化方向 |
|------|----------|----------|
| `printf` → SSD | 系统调用 + 拷贝 + 块层 + DMA | 缓冲、O_DIRECT、io_uring |
| `send` → NIC | 系统调用 + TCP/IP 处理 + 拷贝 | GSO/TSO、zero-copy、DPDK |
| 传感器读取 | 系统调用 + I2C 时延 | batch 读取、中断触发、DMA |
| GPIO 控制 | 系统调用 + gpiolib | mmap GPIO 寄存器、内核事件 |

---

## 6. 国际来源映射

| 跨层主题 | 来源类型 | 来源 | 位置 |
|----------|----------|------|------|
| 文件 I/O 路径 | Textbook | OSTEP | Ch. 17~20 |
| 网络数据路径 | Book | Linux Kernel Networking | Ch. 3~4 |
| IIO 子系统 | SourceCode | Linux Kernel | `drivers/iio/` |
| GPIO 用户态接口 | SourceCode | Linux Kernel | `drivers/gpio/gpiolib.c` |

---

## 7. 相关文件

- [系统调用接口](./syscall-interface.md)
- [Linux 网络协议栈](../06-networking/linux-network-stack.md)
- [外设概念树](../07-peripherals/peripheral-concept-tree.md)
- [Linux 内核源码映射](../05-linux-kernel/linux-source-map.md)
