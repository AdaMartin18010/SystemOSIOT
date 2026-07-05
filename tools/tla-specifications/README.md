# TLA+ 形式化规范集合


<!-- TOC START -->

- [TLA+ 形式化规范集合](#tla-形式化规范集合)
  - [文件清单](#文件清单)
  - [运行方式](#运行方式)
    - [使用命令行 TLC（推荐）](#使用命令行-tlc推荐)
    - [使用 TLA+ Toolbox（图形界面）](#使用-tla-toolbox图形界面)
  - [与项目模块的关联](#与项目模块的关联)
  - [验证日志](#验证日志)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 位置：`tools/tla-specifications/`
> 用途：为分布式系统、容器编排、网络协议等关键模块提供可机器检查的时序逻辑规范。
> 工具：TLC Model Checker（随附 `tla2tools.jar`）。

## 文件清单

| 文件 | 内容 | 对应模块 | 验证状态 |
|---|---|---|---|
| `Raft.tla` | Raft 共识算法简化模型（Leader 选举、日志复制、安全性质） | `4.分布式系统` | ✅ TLC 通过（102679 / 22977 states） |
| `Raft.cfg` | Raft 模型检查配置（3 节点、1 值、最大任期 2） | `4.分布式系统` | ✅ TLC 通过 |
| `Kubernetes.tla` | Kubernetes Pod 生命周期与 Deployment 滚动更新模型 | `7.容器与微服务` | ✅ TLC 通过（3322 / 594 states） |
| `Kubernetes.cfg` | Kubernetes 模型检查配置 | `7.容器与微服务` | ✅ TLC 通过 |
| `QUIC.tla` | QUIC/TCP 传输层握手状态机与安全性质 | `8.网络系统` | ✅ TLC 通过（5 / 5 states） |
| `QUIC.cfg` | QUIC 模型检查配置 | `8.网络系统` | ✅ TLC 通过 |
| `TCP_CongestionControl.tla` | TCP Reno/CUBIC 拥塞控制状态机 | `8.网络系统` | ✅ TLC 通过（1737 / 592 states） |
| `TCP_CongestionControl.cfg` | TCP 拥塞控制模型检查配置 | `8.网络系统` | ✅ TLC 通过 |
| `BGP_PathSelection.tla` | 3 路由器 BGP 路径选择与收敛模型 | `8.网络系统` | ✅ TLC 通过（49078 / 8186 states） |
| `BGP_PathSelection.cfg` | BGP 路径选择模型检查配置 | `8.网络系统` | ✅ TLC 通过 |
| `OSPF_LinkState.tla` | OSPF 链路状态协议邻居状态机 / LSA 泛洪 / LSDB 同步 / SPF 计算 | `8.网络系统` | ✅ TLC 通过（1132793 / 168844 states） |
| `OSPF_LinkState.cfg` | OSPF 链路状态模型检查配置 | `8.网络系统` | ✅ TLC 通过 |

## 运行方式

### 使用命令行 TLC（推荐）

`tools/tla-specifications/` 目录已包含 `tla2tools.jar`，无需额外下载。

```bash
cd tools/tla-specifications

java -cp tla2tools.jar tlc2.TLC Raft -config Raft.cfg -nowarning
java -cp tla2tools.jar tlc2.TLC Kubernetes -config Kubernetes.cfg -nowarning
java -cp tla2tools.jar tlc2.TLC QUIC -config QUIC.cfg -nowarning
java -cp tla2tools.jar tlc2.TLC TCP_CongestionControl -config TCP_CongestionControl.cfg -nowarning
java -cp tla2tools.jar tlc2.TLC BGP_PathSelection -config BGP_PathSelection.cfg -nowarning
java -cp tla2tools.jar tlc2.TLC OSPF_LinkState -config OSPF_LinkState.cfg -nowarning
```

> 说明：
>
> - 在 Windows（Git Bash / MSYS2 / WSL）下均可使用上述命令；路径中的 jar 为本地相对路径，不会污染系统目录。
> - `OSPF_LinkState` 状态空间较大，完整验证约需 3–5 分钟（视硬件而定）。
> - 若出现 `UseParallelGC` 警告，可追加 `-XX:+UseParallelGC` 到 `java` 参数。

### 使用 TLA+ Toolbox（图形界面）

1. 下载并安装 TLA+ Toolbox：<https://lamport.azurewebsites.net/tla/toolbox.html>
2. 导入 `tools/tla-specifications/` 目录。
3. 打开 `.tla` 文件，使用对应的 `.cfg` 运行 TLC。

## 与项目模块的关联

- `Raft.tla` 对应 `4.分布式系统/4.0 国际标准映射/4.0.1 分布式共识与一致性模型.md` 中提出的形式化工件建议。
- `Kubernetes.tla` 对应 `7.容器与微服务/7.0 国际标准映射/7.0.2 Kubernetes-v1.33.md` 中提出的 TLA+ 规范建议。
- `QUIC.tla`、`TCP_CongestionControl.tla`、`BGP_PathSelection.tla`、`OSPF_LinkState.tla` 对应 `8.网络系统/8.0 国际标准映射/` 与 `8.8 综合专题与前沿展望/` 中网络协议深度分析的形式化补充。

## 验证日志

本次 Phase 9 验证日志保存在：

```
validation/verification-results/tla-phase9/
├── BGP_PathSelection.log
├── Kubernetes.log
├── OSPF_LinkState.log
├── QUIC.log
├── Raft.log
└── TCP_CongestionControl.log
```

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Raft / Kubernetes TLA+ 规范 | Kimi Code CLI |
| 2026-07-05 | 新增 QUIC / TCP 拥塞控制 / BGP / OSPF TLA+ 规范并完成 TLC 验证 | Kimi Code CLI |
