# CVC5 / SMT-LIB 示例


<!-- TOC START -->

- [CVC5 / SMT-LIB 示例](#cvc5--smt-lib-示例)
  - [文件](#文件)
  - [依赖](#依赖)
  - [CI 运行](#ci-运行)

<!-- TOC END -->

本目录包含用于 CVC5 求解器的 SMT-LIB 示例，用于验证多求解器兼容性。

## 文件

| 文件 | 内容 | 运行方式 |
|---|---|---|
| `Scheduling_Constraints.smt2` | 任务调度到时间槽的约束满足问题 | `cvc5 Scheduling_Constraints.smt2` |

## 依赖

- CVC5 (<https://cvc5.github.io/>)

## CI 运行

见 `.github/workflows/formal-verification.yml`。
