# 05-linux-kernel / Linux 内核实现


<!-- TOC START -->

- [05-linux-kernel / Linux 内核实现](#05-linux-kernel--linux-内核实现)
  - [文件列表](#文件列表)
  - [返回](#返回)

<!-- TOC END -->

本目录聚焦 Linux 内核的工程实现，把操作系统通用概念映射到 `task_struct`、`mm_struct`、`VFS`、`net/`、`drivers/` 等真实源码结构。

## 文件列表

- [linux-source-map.md](./linux-source-map.md) — Linux 源码地图与子系统索引
- [linux-concept-tree.md](./linux-concept-tree.md) — Linux 内核概念树
- [linux-attribute-relationship-map.md](./linux-attribute-relationship-map.md) — Linux 内核属性-关系映射
- [linux-mechanism-composition-tree.md](./linux-mechanism-composition-tree.md) — Linux 内核机制组合树
- [linux-dependency-tree.md](./linux-dependency-tree.md) — Linux 内核依赖树
- [linux-scenario-analysis-tree.md](./linux-scenario-analysis-tree.md) — Linux 内核场景分析树
- [process-scheduling-linux.md](./process-scheduling-linux.md) — 进程调度：CFS / RT / DL / cgroup / namespace
- [memory-management-linux.md](./memory-management-linux.md) — 内存管理：伙伴系统、SLUB、页缓存、NUMA
- [vfs-filesystems-linux.md](./vfs-filesystems-linux.md) — VFS 与文件系统：ext4/Btrfs/XFS/overlay
- [devices-drivers-linux.md](./devices-drivers-linux.md) — 设备模型、sysfs/udev、驱动框架、设备树
- [security-linux.md](./security-linux.md) — capabilities、LSM、SELinux/AppArmor、seccomp、eBPF LSM

## 返回

- [返回操作系统总览](../README.md)
