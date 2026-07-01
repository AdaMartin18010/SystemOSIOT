# Lean 4 形式化验证示例

> 位置：`tools/lean-verification/`
> 用途：为项目提供 Lean 4 证明助手示例，展示类型论、程序语义与类型安全证明。
> 工具：Lean 4 / Lake。

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `SimpleTypeTheory.lean` | 简单算术表达式语言、大步语义、类型系统、Progress/Preservation | 待 `lean` 命令验证 |

## 运行方式

### 前提

安装 Lean 4：<https://leanprover.github.io/lean4/doc/quickstart.html>

### 验证

```bash
cd tools/lean-verification
lean SimpleTypeTheory.lean
```

## 与项目模块的关联

- `SimpleTypeTheory.lean` 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 Lean 工件。
- 该示例可作为 `1.系统理论/1.4 形式化证明` 和 `1.系统理论/1.6 形式语义` 的教学级形式化参考。

## 扩展计划

1. 增加 STLC（Simply Typed Lambda Calculus）小步语义与类型安全证明。
2. 增加 System F / 多态类型示例。
3. 与 `tools/coq-verification/SystemTheory.v` 对比，展示 Coq 与 Lean 在系统理论形式化上的差异。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Lean 4 类型论示例 | Kimi Code CLI |
