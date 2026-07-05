# SMT-LIB / Z3 约束求解示例


<!-- TOC START -->

- [SMT-LIB / Z3 约束求解示例](#smt-lib--z3-约束求解示例)
  - [文件清单](#文件清单)
  - [运行方式](#运行方式)
  - [验证目标](#验证目标)
  - [与项目模块的关联](#与项目模块的关联)
  - [扩展计划](#扩展计划)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 位置：`tools/smt-examples/`
> 用途：为资源分配、调度、安全策略等提供约束求解示例。
> 工具：Z3 SMT Solver（<https://github.com/Z3Prover/z3）。>

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `Container_Resource_Allocation.smt2` | Kubernetes Pod 到 Node 的资源分配约束 | 已创建，待 Z3 验证 |

## 运行方式

```bash
cd tools/smt-examples
z3 Container_Resource_Allocation.smt2
```

## 验证目标

- 检查在给定节点容量下，是否可以同时调度所有 Pod。
- 输出一个满足 CPU/内存约束的放置方案。

## 与项目模块的关联

- 对应 `7.容器与微服务/7.7 运行时调度语义分析` 中的资源调度约束。
- 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 SMT-LIB / Z3 工件。

## 扩展计划

1. 增加多节点调度与负载均衡约束。
2. 增加网络策略（NetworkPolicy）可满足的约束。
3. 增加实时任务调度可行性约束。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建容器资源分配 SMT-LIB 示例 | Kimi Code CLI |
