# SPIN / Promela 模型


<!-- TOC START -->

- [SPIN / Promela 模型](#spin--promela-模型)
  - [文件](#文件)
  - [依赖](#依赖)
  - [本地运行（Linux / WSL / macOS）](#本地运行linux--wsl--macos)
  - [CI 运行](#ci-运行)

<!-- TOC END -->

本目录包含用于 SPIN 模型检验器的 Promela 规范。

## 文件

| 文件 | 内容 | 运行方式 |
|---|---|---|
| `Mutex.pml` | 基于 turn 变量的两进程互斥协议 | `spin -a Mutex.pml && cc -o pan pan.c && ./pan -a` |

## 依赖

- SPIN 6.5+ (<http://spinroot.com/>)
- C 编译器（gcc / clang）

## 本地运行（Linux / WSL / macOS）

```bash
spin -a Mutex.pml
gcc -o pan pan.c
./pan -a
```

## CI 运行

见 `.github/workflows/formal-verification.yml`。
