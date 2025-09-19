#!/bin/bash

# SystemOSIOT 环境验证脚本
# 用途: 验证构建环境的完整性和一致性
# 版本: 1.0.0
# 日期: 2025-01-27

set -euo pipefail

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 检查命令是否存在
check_command() {
    local cmd=$1
    local version_flag=${2:-"--version"}
    
    if command -v "$cmd" >/dev/null 2>&1; then
        local version=$(eval "$cmd $version_flag" 2>/dev/null | head -n1 || echo "unknown")
        log_success "$cmd: $version"
        return 0
    else
        log_error "$cmd: not found"
        return 1
    fi
}

# 检查文件是否存在
check_file() {
    local file=$1
    local description=${2:-"file"}
    
    if [ -f "$file" ]; then
        log_success "$description: $file exists"
        return 0
    else
        log_error "$description: $file not found"
        return 1
    fi
}

# 检查目录是否存在
check_directory() {
    local dir=$1
    local description=${2:-"directory"}
    
    if [ -d "$dir" ]; then
        log_success "$description: $dir exists"
        return 0
    else
        log_error "$description: $dir not found"
        return 1
    fi
}

# 验证环境锁定文件
verify_env_lock() {
    log_info "Verifying environment lock file..."
    
    if [ ! -f "validation/env.lock" ]; then
        log_error "env.lock file not found"
        return 1
    fi
    
    # 检查关键版本信息
    local required_vars=("COQ_VERSION" "ISABELLE_VERSION" "LEAN_VERSION" "Z3_VERSION" "CVC5_VERSION")
    
    for var in "${required_vars[@]}"; do
        if grep -q "^${var}=" validation/env.lock; then
            local value=$(grep "^${var}=" validation/env.lock | cut -d'=' -f2)
            log_success "$var: $value"
        else
            log_error "$var not found in env.lock"
            return 1
        fi
    done
    
    log_success "Environment lock file verification completed"
}

# 验证证明助手工具链
verify_proof_assistants() {
    log_info "Verifying proof assistant toolchain..."
    
    local tools=("coqc" "isabelle" "lean" "lake")
    local failed=0
    
    for tool in "${tools[@]}"; do
        if ! check_command "$tool"; then
            failed=1
        fi
    done
    
    if [ $failed -eq 0 ]; then
        log_success "Proof assistant toolchain verification completed"
    else
        log_error "Proof assistant toolchain verification failed"
        return 1
    fi
}

# 验证SMT求解器
verify_smt_solvers() {
    log_info "Verifying SMT solvers..."
    
    local solvers=("z3" "cvc5")
    local failed=0
    
    for solver in "${solvers[@]}"; do
        if ! check_command "$solver"; then
            failed=1
        fi
    done
    
    if [ $failed -eq 0 ]; then
        log_success "SMT solvers verification completed"
    else
        log_error "SMT solvers verification failed"
        return 1
    fi
}

# 验证TLA+工具链
verify_tla_tools() {
    log_info "Verifying TLA+ tools..."
    
    if [ -f "tla2tools.jar" ]; then
        log_success "TLA+ tools: tla2tools.jar found"
    else
        log_warning "TLA+ tools: tla2tools.jar not found (optional)"
    fi
    
    log_success "TLA+ tools verification completed"
}

# 验证项目结构
verify_project_structure() {
    log_info "Verifying project structure..."
    
    local required_dirs=("research" "tools" "validation")
    local required_files=("README.md" "LICENSE")
    
    local failed=0
    
    for dir in "${required_dirs[@]}"; do
        if ! check_directory "$dir"; then
            failed=1
        fi
    done
    
    for file in "${required_files[@]}"; do
        if ! check_file "$file"; then
            failed=1
        fi
    done
    
    if [ $failed -eq 0 ]; then
        log_success "Project structure verification completed"
    else
        log_error "Project structure verification failed"
        return 1
    fi
}

# 验证可复现性工件
verify_artifacts() {
    log_info "Verifying reproducibility artifacts..."
    
    local artifacts=("validation/artifact.json" "validation/repro-checklist.md")
    local failed=0
    
    for artifact in "${artifacts[@]}"; do
        if ! check_file "$artifact"; then
            failed=1
        fi
    done
    
    if [ $failed -eq 0 ]; then
        log_success "Reproducibility artifacts verification completed"
    else
        log_error "Reproducibility artifacts verification failed"
        return 1
    fi
}

# 生成环境报告
generate_environment_report() {
    log_info "Generating environment report..."
    
    local report_file="validation/verification-results/environment_report.md"
    mkdir -p "$(dirname "$report_file")"
    
    cat > "$report_file" << EOF
# Environment Verification Report

Generated: $(date)
Host: $(hostname)
OS: $(uname -a)
User: $(whoami)

## System Information

- **OS**: $(uname -s) $(uname -r)
- **Architecture**: $(uname -m)
- **Shell**: $SHELL
- **Python**: $(python3 --version 2>/dev/null || echo "not found")
- **Node.js**: $(node --version 2>/dev/null || echo "not found")
- **Java**: $(java -version 2>&1 | head -n1 || echo "not found")

## Toolchain Versions

EOF

    # 添加工具版本信息
    local tools=("coqc" "isabelle" "lean" "lake" "z3" "cvc5")
    for tool in "${tools[@]}"; do
        if command -v "$tool" >/dev/null 2>&1; then
            local version=$(eval "$tool --version" 2>/dev/null | head -n1 || echo "unknown")
            echo "- **$tool**: $version" >> "$report_file"
        else
            echo "- **$tool**: not found" >> "$report_file"
        fi
    done
    
    cat >> "$report_file" << EOF

## Verification Results

- Environment Lock File: $(if [ -f "validation/env.lock" ]; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Proof Assistants: $(if verify_proof_assistants >/dev/null 2>&1; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- SMT Solvers: $(if verify_smt_solvers >/dev/null 2>&1; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Project Structure: $(if verify_project_structure >/dev/null 2>&1; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)
- Reproducibility Artifacts: $(if verify_artifacts >/dev/null 2>&1; then echo "✅ PASSED"; else echo "❌ FAILED"; fi)

## Recommendations

1. Ensure all required tools are installed and accessible
2. Verify environment lock file is up to date
3. Run full verification suite before committing changes
4. Maintain consistency across development environments

EOF

    log_success "Environment report generated: $report_file"
}

# 主函数
main() {
    log_info "Starting SystemOSIOT environment verification..."
    
    local failed=0
    
    # 执行所有验证步骤
    verify_env_lock || failed=1
    verify_proof_assistants || failed=1
    verify_smt_solvers || failed=1
    verify_tla_tools || failed=1
    verify_project_structure || failed=1
    verify_artifacts || failed=1
    
    # 生成环境报告
    generate_environment_report
    
    # 总结
    if [ $failed -eq 0 ]; then
        log_success "All environment verifications passed!"
        log_info "Environment is ready for formal verification"
        exit 0
    else
        log_error "Some environment verifications failed!"
        log_info "Please fix the issues above before proceeding"
        exit 1
    fi
}

# 脚本入口点
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
