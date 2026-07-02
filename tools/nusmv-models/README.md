# NuSMV 模型检验示例

> 位置：`tools/nusmv-models/`
> 用途：为并发/分布式系统提供符号模型检验示例。
> 工具：NuSMV / nuXmv（<https://nusmv.fbk.eu/）。>

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `Mutex.smv` | 两进程互斥协议 + CTL 安全/活性/无饥饿性质 | 已创建，待 NuSMV 验证 |

## 运行方式

```bash
cd tools/nusmv-models
NuSMV Mutex.smv
# 或使用 nuXmv
nuXmv -source check.smv Mutex.smv
```

## 验证性质

| CTL 规格 | 含义 |
|---|---|
| `AG !(p1.state = critical & p2.state = critical)` | 两进程不会同时进入临界区（安全） |
| `AG (p1.state = waiting -> AF p1.state = critical)` | 等待的进程最终能进入临界区（活性） |
| `AG AF p1.state = critical` | 进程 p1 无限次进入临界区（无饥饿） |

## 与项目模块的关联

- 对应 `4.分布式系统/4.6 形式语义` 与 `7.8 形式语义与递归语义分析` 中 CTL/LTL 验证章节。
- 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 NuSMV 工件。

## 扩展计划

1. 增加 Raft/Paxos 协议高层状态机模型。
2. 增加 Kubernetes 控制器循环模型。
3. 增加物联网节点并发访问共享资源模型。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建互斥协议 NuSMV 模型 | Kimi Code CLI |
