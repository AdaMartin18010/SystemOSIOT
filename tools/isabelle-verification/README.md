# Isabelle/HOL 形式化验证示例

> 位置：`tools/isabelle-verification/`  
> 用途：为项目提供 Isabelle/HOL 证明助手示例，展示命令式语言操作语义与确定性证明。  
> 工具：Isabelle2024 + Isabelle/jEdit。

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `IMP_BigStep.thy` | IMP 语言大步操作语义与 big_step 确定性证明 | 待 Isabelle 构建验证 |

## 运行方式

### 前提

安装 Isabelle2024：https://isabelle.in.tum.de/

### 验证

```bash
cd tools/isabelle-verification
isabelle build -D .
# 或在 Isabelle/jEdit 中打开 IMP_BigStep.thy
```

## 与项目模块的关联

- `IMP_BigStep.thy` 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 Isabelle/HOL 工件。
- 该示例可作为 `2.操作系统/2.7 形式证明` 中命令式代码语义形式化的参考模板。
- 后续可扩展至霍尔逻辑（Hoare Logic）与分离逻辑（Separation Logic）小例。

## 扩展计划

1. 增加 IMP 的霍尔逻辑与部分正确性证明。
2. 增加一个小型命令式内存分配器，用分离逻辑验证。
3. 与 `tools/coq-verification/SystemTheory.v` 对比，展示 Isabelle 与 Coq 在系统形式化上的差异。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 Isabelle/HOL IMP 语义示例 | Kimi Code CLI |
