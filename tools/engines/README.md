# 验证引擎目录

本目录集中存放 SystemOSIOT 形式化验证所需的外部验证器二进制包与源码。所有工具均按“Windows 本地可用”或“WSL (Ubuntu-24.04)”策略部署。

## 目录布局

| 子目录/文件 | 工具 | 平台 | 说明 |
|---|---|---|---|
| `z3-4.13.0-x64-win/` | Z3 4.13.0 | Windows | SMT 求解器，用于 `tools/smt-examples/` |
| `NuSMV-2.6.0-win64/` | NuSMV 2.6.0 | Windows | 符号模型检验器，用于 `tools/nusmv-models/` |
| `tla2tools.jar` | TLA+ Toolbox / TLC 1.7.4 | Windows (Java) | TLA+ 模型检验器，用于 `tools/tla-specifications/` |
| `alloy.jar` | Alloy 6.2.0 | Windows (Java) | 关系模型查找器，用于 `tools/alloy-models/` |
| `prism-4.10.1-linux64-x86/` | PRISM 4.10.1 | WSL | 概率模型检验器，用于 `tools/prism-models/` |
| `uppaal-5.0.0-linux64/` | UPPAAL 5.0.0 | WSL | 时间自动机模型检验器，用于 `tools/uppaal-models/`（需学术 license） |
| `cvc5-Linux-x86_64-static/` | CVC5 1.3.4 | WSL | SMT 求解器，用于 `tools/smt-examples/` |
| `Spin-master/` | SPIN 6.5+ 源码 | WSL | 待编译后生成 `spin` 二进制，用于 `tools/spin-models/` |
| `Isabelle2025-2/` | Isabelle/HOL 2025-2 | WSL | 高阶逻辑证明助手，用于 `tools/isabelle-verification/`（Isabelle2024 官方已下架，改用 2025-2） |

## 环境变量参考

```bash
# Windows (PowerShell)
$env:PATH += ";E:\_src\SystemOSIOT\tools\engines\z3-4.13.0-x64-win"
$env:PATH += ";E:\_src\SystemOSIOT\tools\engines\NuSMV-2.6.0-win64\bin"

# WSL (bash)
export PATH="/mnt/e/_src/SystemOSIOT/tools/engines/cvc5-Linux-x86_64-static/bin:$PATH"
export PATH="/mnt/e/_src/SystemOSIOT/tools/engines/prism-4.10.1-linux64-x86/bin:$PATH"
export PATH="/mnt/e/_src/SystemOSIOT/tools/engines/Spin-master/bin:$PATH"
export PATH="/mnt/e/_src/SystemOSIOT/tools/engines/Isabelle2025-2/bin:$PATH"
```

## 下载脚本

各工具的下载与解压过程已记录在 `validation/formal-artifacts-gap-audit.md` 与 CI 工作流中。本目录本身不存放下载脚本，以避免误触发大文件提交。
