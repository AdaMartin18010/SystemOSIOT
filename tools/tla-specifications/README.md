# TLA+ 形式化规范集合

> 位置：`tools/tla-specifications/`
> 用途：为分布式系统、容器编排、网络协议等关键模块提供可机器检查的时序逻辑规范。
> 工具：TLA+ Toolbox / TLC Model Checker / SANY 语法检查器。

## 文件清单

| 文件 | 内容 | 对应模块 | 验证状态 |
|---|---|---|---|
| `Raft.tla` | Raft 共识算法简化模型（Leader 选举、日志复制、安全性质） | `4.分布式系统` | 待 TLC 运行验证 |
| `Raft.cfg` | Raft 模型检查配置（3 节点、2 值、最大任期 3） | `4.分布式系统` | 待 TLC 运行验证 |
| `Kubernetes.tla` | Kubernetes Pod 生命周期与 Deployment 滚动更新模型 | `7.容器与微服务` | 待 TLC 运行验证 |
| `Kubernetes.cfg` | Kubernetes 模型检查配置 | `7.容器与微服务` | 待 TLC 运行验证 |
| `QUIC.tla` | QUIC/TCP 传输层握手状态机与安全性质 | `8.网络系统` | 待 TLC 运行验证 |
| `QUIC.cfg` | QUIC 模型检查配置 | `8.网络系统` | 待 TLC 运行验证 |

## 运行方式

### 使用 TLA+ Toolbox（图形界面）

1. 下载并安装 TLA+ Toolbox：<https://lamport.azurewebsites.net/tla/toolbox.html>
2. 导入 `tools/tla-specifications/` 目录。
3. 打开 `.tla` 文件，使用对应的 `.cfg` 运行 TLC。

### 使用命令行 TLC

```bash
# 需要 tla2tools.jar
cd tools/tla-specifications
java -cp /path/to/tla2tools.jar tlc2.TLC Raft
java -cp /path/to/tla2tools.jar tlc2.TLC Kubernetes
```

## 与项目模块的关联

- `Raft.tla` 对应 `4.分布式系统/4.0 国际标准映射/4.0.1 分布式共识与一致性模型.md` 中提出的形式化工件建议。
- `Kubernetes.tla` 对应 `7.容器与微服务/7.0 国际标准映射/7.0.2 Kubernetes-v1.33.md` 中提出的 TLA+ 规范建议。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Raft / Kubernetes TLA+ 规范 | Kimi Code CLI |
