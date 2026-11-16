# 08-interfaces / 接口与抽象层


<!-- TOC START -->

- [08-interfaces / 接口与抽象层](#08-interfaces--接口与抽象层)
  - [文件列表](#文件列表)
  - [返回](#返回)
  - [质量治理注记（2026-11）](#质量治理注记2026-11)

<!-- TOC END -->

本目录梳理用户程序与内核、硬件之间的接口层：系统调用、ABI/API、内核-用户边界、POSIX、HAL/BSP/设备树、跨层映射。

## 文件列表

- [syscall-interface.md](./syscall-interface.md) — 系统调用表、`SYSCALL_DEFINE*`、vDSO、seccomp
- [abi-api.md](./abi-api.md) — ABI 与 API 分层映射、调用约定、ELF
- [kernel-user-boundary.md](./kernel-user-boundary.md) — 特权级、系统调用开销、安全边界
- [posix-mapping.md](./posix-mapping.md) — POSIX 条款级映射到 Linux 实现
- [hal-bsp-device-tree.md](./hal-bsp-device-tree.md) — HAL、BSP、设备树、ACPI 对比
- [cross-layer-mapping.md](./cross-layer-mapping.md) — `printf`/socket/传感器 的完整跨层调用链

## 返回

- [返回操作系统总览](../README.md)

## 质量治理注记（2026-11）

本目录原 1 个内容文件经全库质量审计归类为模板填充（C 类），已整体归档至 `docs/Refactor/archive/2026-quality-audit/2.操作系统/02-operating-systems/08-interfaces/`（原相对路径不变，可恢复）。保留本 README 作为目录骨架。
