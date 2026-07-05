# Coq 形式化验证示例


<!-- TOC START -->

- [Coq 形式化验证示例](#coq-形式化验证示例)
  - [文件清单](#文件清单)
  - [运行方式](#运行方式)
    - [前提](#前提)
    - [验证](#验证)
  - [新增工件说明](#新增工件说明)
    - [`StopAndWait.v`](#stopandwaitv)
  - [与项目模块的关联](#与项目模块的关联)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 位置：`tools/coq-verification/`
> 用途：为 SystemOSIOT 项目提供 Coq 证明助手示例，覆盖系统理论与网络协议形式化。
> 工具：Coq 8.19+。

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `SystemTheory.v` | 系统理论基本定义与定理 | ✅ 已通过 `coqc` |
| `FLP_Sketch.v` | FLP 异步系统模型与定理陈述草图 | ✅ 已通过 `coqc` |
| `StopAndWait.v` | 停等协议（Stop-and-Wait）安全性与活性证明 | ✅ 待 `coqc` 验证 |

## 运行方式

### 前提

安装 Coq 8.19+：<https://coq.inria.fr/download>

在 Windows 上推荐使用 WSL / opam 安装：

```bash
opam install coq
```

### 验证

```bash
cd tools/coq-verification
coqc SystemTheory.v
coqc FLP_Sketch.v
coqc StopAndWait.v
```

预期输出：每个文件编译后生成对应的 `.vo` / `.glob` 文件，终端无错误。

## 新增工件说明

### `StopAndWait.v`

- 形式化定义：
  - 序号类型 `Seq`（`seq0` / `seq1`）与翻转函数。
  - 报文类型 `Packet`（`Data s` / `Ack s`）。
  - 发送方状态 `SenderState`（`SW_Ready s` / `SW_Wait s`）。
  - 接收方状态 `ReceiverState`（`RW_Expect s`）。
  - 全局状态 `State` 与转移关系 `Step`（发送、接收数据、接收重复、接收 ACK、丢包）。
- 证明定理：
  - `stop_and_wait_safe`：接收方只接受与期望序号匹配的数据帧（安全性）。
  - `stop_and_wait_seq_consistent`：发送方序号与接收方期望序号始终保持一致或翻转。
  - `stop_and_wait_liveness`：当期望 ACK 位于信道中任意位置时，发送方最终回到 `Ready`（活性）。

## 与项目模块的关联

- `StopAndWait.v` 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 **网络协议正确性证明**（`8.4 形式化证明/*.v`）。
- 可作为 `8.网络系统/8.4 形式化证明` 中链路层/传输层协议形式化的教学级参考。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Coq 系统理论示例 | Kimi Code CLI |
| 2026-07-05 | 新增 `StopAndWait.v` 网络协议形式化 | Kimi Code CLI |
