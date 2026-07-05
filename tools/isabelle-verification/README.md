# Isabelle/HOL 形式化验证示例


<!-- TOC START -->

- [Isabelle/HOL 形式化验证示例](#isabellehol-形式化验证示例)
  - [文件清单](#文件清单)
  - [运行方式](#运行方式)
    - [前提](#前提)
    - [验证](#验证)
  - [新增工件说明](#新增工件说明)
    - [`RoutingTable.thy`](#routingtablethy)
  - [与项目模块的关联](#与项目模块的关联)
  - [扩展计划](#扩展计划)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 位置：`tools/isabelle-verification/`
> 用途：为 SystemOSIOT 项目提供 Isabelle/HOL 证明助手示例，覆盖命令式语言语义与网络协议形式化。
> 工具：Isabelle2024 + Isabelle/jEdit。

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `IMP_BigStep.thy` | IMP 语言大步操作语义与 big_step 确定性证明 | ✅ 已创建，待 Isabelle 构建验证 |
| `RoutingTable.thy` | 距离向量路由表更新单调性证明 | ✅ 待 Isabelle 构建验证 |

## 运行方式

### 前提

安装 Isabelle2024：<https://isabelle.in.tum.de/>

### 验证

```bash
cd tools/isabelle-verification
isabelle build -D .
# 或在 Isabelle/jEdit 中打开 IMP_BigStep.thy / RoutingTable.thy
```

## 新增工件说明

### `RoutingTable.thy`

- 形式化定义：
  - 地址与 metric 类型。
  - 路由表 `routing_table` 为 `(addr × metric) list`。
  - `lookup`：查询当前 metric，缺失返回 `INF`（RIP 风格不可达值 16）。
  - `update_route` / `update_table`：单条与批量路由更新，仅在新 metric 更小时替换。
  - `no_worse_than`（`⊑`）：逐地址 metric 不恶化。
- 证明定理：
  - `update_route_monotonic`：单条路由更新保持不恶化。
  - `update_table_monotonic`：批量路由更新保持不恶化。
  - `lookup_update_nonincreasing`：更新后任意地址的 metric 不大于更新前。

## 与项目模块的关联

- `RoutingTable.thy` 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 **网络协议相关 Isabelle/HOL 形式化** 工件。
- 可作为 `8.网络系统/8.4 形式化证明` 中路由协议（RIP/OSPF/BGP）形式化的参考模板。

## 扩展计划

1. 增加 IMP 的霍尔逻辑与部分正确性证明。
2. 增加一个小型命令式内存分配器，用分离逻辑验证。
3. 增加 TCP 连接建立状态机（3-way handshake）安全转移证明。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Isabelle/HOL IMP 语义示例 | Kimi Code CLI |
| 2026-07-05 | 新增 `RoutingTable.thy` 路由表单调性证明 | Kimi Code CLI |
