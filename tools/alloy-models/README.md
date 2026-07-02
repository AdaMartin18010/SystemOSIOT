# Alloy 架构一致性示例

> 位置：`tools/alloy-models/`
> 用途：为系统架构描述提供关系模型与一致性验证。
> 工具：Alloy Analyzer（<https://alloytools.org/）。>

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `Kubernetes_Architecture.als` | Kubernetes Pod/Node/Container/Service 架构约束 | 已创建，待 Alloy Analyzer 验证 |

## 运行方式

```bash
cd tools/alloy-models
alloy Kubernetes_Architecture.als
```

或在 Alloy Analyzer GUI 中打开并执行 `Execute`。

## 验证断言

| 断言 | 含义 |
|---|---|
| `NoDuplicatePodImagesOnSameNode` | 同一 Node 上的不同 Pod 不使用完全相同镜像集 |
| `ServiceHasTarget` | 每个 Service 至少 target 一个 Pod |

## 与项目模块的关联

- 对应 `7.容器与微服务/7.3 形式化结构` 中的架构形式化。
- 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 Alloy 工件。
- 对应 `ISO/IEC/IEEE 42010:2022` 架构视图一致性检查需求。

## 扩展计划

1. 增加网络策略（NetworkPolicy）与 Pod 标签约束。
2. 增加 RBAC 角色-绑定一致性。
3. 增加分布式系统节点拓扑约束。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Kubernetes 架构 Alloy 模型 | Kimi Code CLI |
