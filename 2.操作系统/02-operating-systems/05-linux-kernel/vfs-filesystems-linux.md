# Linux VFS 与文件系统

> **权威来源**：Linux Kernel Development (Love), OSTEP Ch. 37~43, kernel.org `Documentation/filesystems/`, LWN.net。
>
> **目标**：深入 Linux 虚拟文件系统 VFS、页缓存、具体文件系统 ext4/Btrfs/XFS/overlay 的实现映射。

---

## 1. VFS 核心数据结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct super_block` | `include/linux/fs.h` | 超级块，描述已挂载文件系统实例 |
| `struct inode` | `include/linux/fs.h` | 索引节点，描述文件元数据 |
| `struct dentry` | `include/linux/dcache.h` | 目录项，缓存路径名到 inode 的映射 |
| `struct file` | `include/linux/fs.h` | 打开文件描述，进程视角 |
| `struct file_operations` | `include/linux/fs.h` | 文件操作回调 |
| `struct inode_operations` | `include/linux/fs.h` | inode 操作回调 |
| `struct super_operations` | `include/linux/fs.h` | 超级块操作回调 |
| `struct address_space` | `include/linux/fs.h` | 文件页缓存映射 |

---

## 2. 打开文件流程

```text
openat()
  ↓ sys_openat()
    ↓ do_filp_open()
      ↓ path_openat()
        ↓ link_path_walk()      # 路径解析，查找/创建 dentry
        ↓ do_last()
          ↓ lookup_fast()       # dcache 快速查找
          ↓ lookup_real()       # 未命中则调用具体文件系统 lookup
        ↓ do_open()
          ↓ vfs_open()
            ↓ dentry_open()
              ↓ alloc_file()
              ↓ f_op->open()
```

---

## 3. 读文件流程

```text
read()
  ↓ vfs_read()
    ↓ file->f_op->read_iter()   # 默认 generic_file_read_iter()
      ↓ 检查 page cache
        ↓ 命中：直接拷贝到用户态
        ↓ 未命中：readpage() 发起 I/O
          ↓ submit_bio()
            ↓ 块层 → 驱动 → DMA → 磁盘
```

---

## 4. 页缓存（Page Cache）

| 概念 | 说明 |
|------|------|
| `address_space` | 文件 ↔ 缓存页的映射 |
| `radix_tree` / `xarray` | 缓存页索引结构（Linux 4.20+ 用 xarray） |
| `read_cache_page()` | 读取缓存页 |
| `add_to_page_cache_lru()` | 加入页缓存 LRU |
| `write_cache_pages()` | 回写脏页 |
| `pdflush` / `flusher threads` | 后台回写线程 |

---

## 5. 写文件与一致性

### 5.1 写路径

```text
write()
  ↓ vfs_write()
    ↓ file->f_op->write_iter()  # ext4_file_write_iter()
      ↓ generic_perform_write() # 写入 page cache
        ↓ ext4_write_end()      # 标记 dirty
      ↓ 日志提交（ext4）
      ↓ 后台 flusher 刷盘
```

### 5.2 日志模式（ext4）

| 模式 | 说明 | 性能/安全 |
|------|------|-----------|
| `data=journal` | 数据与元数据都日志 | 最安全，最慢 |
| `data=ordered` | 元数据日志，数据先刷盘 | 默认，平衡 |
| `data=writeback` | 元数据日志，数据不保证顺序 | 最快，最不安全 |

---

## 6. 具体文件系统

### 6.1 ext4

| 特性 | 说明 |
|------|------|
|  extents | 替代传统块映射，减少碎片 |
| 日志 | JBD2 日志 |
| 延迟分配 | 提高大文件性能 |
| 在线扩容 | `resize2fs` |

### 6.2 Btrfs

| 特性 | 说明 |
|------|------|
| COW | 写时复制 |
| 子卷/快照 | subvolume/snapshot |
| 校验和 | 数据与元数据校验 |
| RAID | 内置 RAID 0/1/10/5/6 |

### 6.3 XFS

| 特性 | 说明 |
|------|------|
| 大文件 | 适合大容量存储 |
| 分配组 | 并行分配 |
| 延迟日志 | 高性能日志 |

### 6.4 overlayfs

| 概念 | 说明 |
|------|------|
| lowerdir | 只读底层 |
| upperdir | 可写层 |
| workdir | 工作目录 |
| merged | 合并视图 |

---

## 7. procfs / sysfs / tmpfs / devtmpfs

| 文件系统 | 类型 | 用途 |
|----------|------|------|
| procfs | 伪文件系统 | 进程与内核信息 `/proc` |
| sysfs | 伪文件系统 | 设备与驱动信息 `/sys` |
| tmpfs | 内存文件系统 | 临时文件 `/tmp`, `/run` |
| devtmpfs | 伪文件系统 | 设备节点 `/dev` |

---

## 8. 文件系统挂载

| 系统调用 | 内核函数 | 说明 |
|----------|----------|------|
| `mount()` | `sys_mount()` → `do_mount()` | 挂载文件系统 |
| `umount()` | `sys_umount()` | 卸载 |
| `mount namespace` | `CLONE_NEWNS` | 隔离挂载点 |

---

## 9. 场景分析

| 场景 | 文件系统 | 关键参数 | 验证指标 |
|------|----------|----------|----------|
| 通用服务器根分区 | ext4 | journal=ordered | 稳定，fsck 时间 |
| 大数据/数据库 | XFS | inode64, allocsize | 大文件吞吐 |
| 容器镜像 | overlayfs | lowerdir/upperdir | 层数，启动时间 |
| 临时缓存 | tmpfs | size, nr_inodes | 访问延迟 |
| 高可靠存储 | Btrfs | checksums, RAID1 | 数据完整性 |

---

## 10. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| VFS | Virtual File System | 为不同文件系统提供统一接口的抽象层 |
| Inode | 索引节点 | 存储文件元数据的数据结构 |
| Dentry | 目录项 | 缓存路径分量到 inode 的映射 |
| Page Cache | 页缓存 | 文件数据在内存中的缓存 |
| Journaling | 日志 | 保证文件系统崩溃一致性的机制 |
| Extent | 区段 | ext4 中连续块的高效表示 |
| COW | Copy-on-Write | 写时复制，用于 Btrfs/overlayfs |

---

## 11. 相关文件

- [Linux 内核源码映射](./linux-source-map.md)
- [进程调度](./process-scheduling-linux.md)
- [内存管理](./memory-management-linux.md)

## 国际权威来源链接 / Authoritative Sources

- [Linux Kernel - Filesystems documentation](https://docs.kernel.org/filesystems/)
- [Linux Kernel - ext4](https://docs.kernel.org/filesystems/ext4/index.html)
- [Linux Kernel - VFS](https://docs.kernel.org/filesystems/vfs.html)
- [Linux Device Drivers - VFS and block layer](https://static.lwn.net/images/pdf/LDD3/ch12.pdf)
