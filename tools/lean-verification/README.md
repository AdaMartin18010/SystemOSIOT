# Lean 4 形式化验证示例


<!-- TOC START -->

- [Lean 4 形式化验证示例](#lean-4-形式化验证示例)
  - [文件清单](#文件清单)
  - [运行方式](#运行方式)
    - [前提](#前提)
    - [验证](#验证)
  - [新增工件说明](#新增工件说明)
    - [`PacketSeqMonotonicity.lean`](#packetseqmonotonicitylean)
  - [与项目模块的关联](#与项目模块的关联)
  - [扩展计划](#扩展计划)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 位置：`tools/lean-verification/`
> 用途：为 SystemOSIOT 项目提供 Lean 4 证明助手示例，覆盖类型论与网络协议形式化。
> 工具：Lean 4 / Lake。

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `SimpleTypeTheory.lean` | 简单算术表达式语言、大步语义、类型系统、Progress/Preservation | ✅ 已通过 `lean` 编译 |
| `PacketSeqMonotonicity.lean` | 数据包序列号单调性与网络不变式证明 | ✅ 已通过 `lake build` 验证 |

## 运行方式

### 前提

安装 Lean 4：<https://leanprover.github.io/lean4/doc/quickstart.html>

### 验证

```bash
cd tools/lean-verification
lean SimpleTypeTheory.lean
lean PacketSeqMonotonicity.lean
# 或使用 Lake 构建
lake build
```

## 新增工件说明

### `PacketSeqMonotonicity.lean`

- 形式化定义：
  - `Packet`：携带自然数序列号。
  - `SenderState`：下一待发序号 `nextSeq`。
  - `NetworkState`：发送方 + FIFO 信道。
  - `Step`：发送方将当前序号报文放入信道并递增 `nextSeq`。
  - `Reachable`：多步可达关系。
- 证明定理：
  - `strong_invariant_initial`：初始状态满足强不变式。
  - `step_preserves_strong`：发送一步保持强不变式。
  - `strong_invariant_reachable`：任意可达状态满足强不变式。
  - `seqs_nondecreasing_invariant`：信道中序列号始终保持非递减。

## 与项目模块的关联

- `PacketSeqMonotonicity.lean` 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 **系统理论 / 网络协议相关 Lean 4 形式化** 工件。
- 可作为 `8.网络系统/8.4 形式化证明` 与 `8.7 系统运行时语义` 中传输层序列号管理的参考。

## 扩展计划

1. 增加 STLC（Simply Typed Lambda Calculus）小步语义与类型安全证明。
2. 增加 System F / 多态类型示例。
3. 与 `tools/coq-verification/StopAndWait.v` 对比，展示 Coq 与 Lean 在网络协议形式化上的差异。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Lean 4 类型论示例 | Kimi Code CLI |
| 2026-07-05 | 新增 `PacketSeqMonotonicity.lean` 序列号单调性证明 | Kimi Code CLI |
| 2026-07-05 | 通过 `lake build` 验证全部 Lean 工件 | Kimi Code CLI |
