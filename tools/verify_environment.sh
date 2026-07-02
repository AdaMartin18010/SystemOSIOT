#!/usr/bin/env bash
# SystemOSIOT 验证环境检查脚本
# 本脚本仅做“存在性”检查，不执行长时间模型检验。

set -euo pipefail

check_cmd() {
  if command -v "$1" >/dev/null 2>&1; then
    echo "✓ $1: $(command -v "$1")"
  else
    echo "✗ $1 not found"
    return 1
  fi
}

echo "=== SystemOSIOT 验证环境检查 ==="

fail=0

check_cmd java || fail=1
check_cmd coqc || fail=1
check_cmd lean || fail=1
check_cmd z3 || fail=1
check_cmd cvc5 || fail=1

# 可选：仅当目录存在时检查
[ -d tools/engines/Isabelle2025-2 ] && check_cmd tools/engines/Isabelle2025-2/bin/isabelle || true
[ -d tools/engines/prism-4.10.1-linux64-x86 ] && check_cmd tools/engines/prism-4.10.1-linux64-x86/bin/prism || true
[ -f tools/engines/spin ] && check_cmd tools/engines/spin || true
[ -d tools/engines/NuSMV-2.6.0-win64 ] && echo "✓ NuSMV (Windows)" || true
[ -f tools/engines/alloy.jar ] && echo "✓ Alloy jar" || true

if [ $fail -eq 0 ]; then
  echo "=== 核心环境检查通过 ==="
else
  echo "=== 核心环境检查存在缺失，请按 tools/engines/README.md 安装 ==="
  exit 1
fi
