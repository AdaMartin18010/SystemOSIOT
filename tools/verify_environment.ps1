<#
 SystemOSIOT 环境验证脚本 (PowerShell 版)
 用途: 在 Windows/PowerShell 环境下验证构建环境的完整性与一致性
 版本: 1.0.0
 日期: 2025-01-27
#>

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Write-Info($msg)    { Write-Host "[INFO]    $msg" -ForegroundColor Cyan }
function Write-Ok($msg)      { Write-Host "[SUCCESS] $msg" -ForegroundColor Green }
function Write-Warn($msg)    { Write-Host "[WARNING] $msg" -ForegroundColor Yellow }
function Write-Err($msg)     { Write-Host "[ERROR]   $msg" -ForegroundColor Red }

function Test-Command {
  param(
    [Parameter(Mandatory)] [string] $Name,
    [string] $VersionArg = '--version'
  )
  $cmd = Get-Command $Name -ErrorAction SilentlyContinue
  if ($null -ne $cmd) {
    try {
      $ver = & $Name $VersionArg 2>$null | Select-Object -First 1
    } catch { $ver = 'unknown' }
    Write-Ok "${Name}: $ver"
    return $true
  } else {
    Write-Err "${Name}: not found"
    return $false
  }
}

function Test-File {
  param([Parameter(Mandatory)][string] $Path, [string] $Desc = 'file')
  if (Test-Path -LiteralPath $Path -PathType Leaf) { Write-Ok "${Desc}: $Path exists"; return $true }
  Write-Err "${Desc}: $Path not found"; return $false
}

function Test-Directory {
  param([Parameter(Mandatory)][string] $Path, [string] $Desc = 'directory')
  if (Test-Path -LiteralPath $Path -PathType Container) { Write-Ok "${Desc}: $Path exists"; return $true }
  Write-Err "${Desc}: $Path not found"; return $false
}

function Test-EnvLock {
  Write-Info 'Verifying environment lock file...'
  if (-not (Test-File -Path 'validation/env.lock' -Desc 'env.lock')) { return $false }
  $required = 'COQ_VERSION','ISABELLE_VERSION','LEAN_VERSION','Z3_VERSION','CVC5_VERSION'
  foreach ($k in $required) {
    $hit = Select-String -Path 'validation/env.lock' -Pattern ("^$k=") -SimpleMatch:$false -CaseSensitive:$false | Select-Object -First 1
    if (-not $hit) { Write-Err "$k not found in env.lock"; return $false }
    else { Write-Ok $hit.Line }
  }
  Write-Ok 'Environment lock file verification completed'
  return $true
}

function Test-ProofAssistants {
  Write-Info 'Verifying proof assistant toolchain...'
  $ok = $true
  foreach ($t in 'coqc','isabelle','lean','lake') {
    if (-not (Test-Command -Name $t)) { $ok = $false }
  }
  if ($ok) { Write-Ok 'Proof assistant toolchain verification completed' } else { Write-Err 'Proof assistant toolchain verification failed' }
  return $ok
}

function Test-SMTSolvers {
  Write-Info 'Verifying SMT solvers...'
  $ok = $true
  foreach ($t in 'z3','cvc5') { if (-not (Test-Command -Name $t)) { $ok = $false } }
  if ($ok) { Write-Ok 'SMT solvers verification completed' } else { Write-Err 'SMT solvers verification failed' }
  return $ok
}

function Test-TLATools {
  Write-Info 'Verifying TLA+ tools...'
  if (Test-Path -LiteralPath 'tla2tools.jar' -PathType Leaf) { Write-Ok 'TLA+ tools: tla2tools.jar found' } else { Write-Warn 'TLA+ tools: tla2tools.jar not found (optional)' }
  Write-Ok 'TLA+ tools verification completed'
  return $true
}

function Test-ProjectStructure {
  Write-Info 'Verifying project structure...'
  $ok = $true
  foreach ($d in 'research','tools','validation') { if (-not (Test-Directory -Path $d)) { $ok = $false } }
  foreach ($f in 'README.md','LICENSE') { if (-not (Test-File -Path $f)) { $ok = $false } }
  if ($ok) { Write-Ok 'Project structure verification completed' } else { Write-Err 'Project structure verification failed' }
  return $ok
}

function Test-Artifacts {
  Write-Info 'Verifying reproducibility artifacts...'
  $ok = $true
  foreach ($f in 'validation/artifact.json','validation/repro-checklist.md') { if (-not (Test-File -Path $f)) { $ok = $false } }
  if ($ok) { Write-Ok 'Reproducibility artifacts verification completed' } else { Write-Err 'Reproducibility artifacts verification failed' }
  return $ok
}

function New-EnvironmentReport {
  Write-Info 'Generating environment report...'
  $report = 'validation/verification-results/environment_report.md'
  $dir = Split-Path -Parent $report
  if (-not (Test-Path $dir)) { New-Item -ItemType Directory -Force -Path $dir | Out-Null }

  $sysInfo = @()
  $sysInfo += "# Environment Verification Report"
  $sysInfo += ''
  $sysInfo += "Generated: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
  $sysInfo += "Host: $env:COMPUTERNAME"
  $sysInfo += "OS: $(Get-CimInstance Win32_OperatingSystem | ForEach-Object { $_.Caption + ' ' + $_.Version })"
  $sysInfo += "User: $env:USERNAME"
  $sysInfo += ''
  $sysInfo += '## Toolchain Versions'
  foreach ($t in 'coqc','isabelle','lean','lake','z3','cvc5','python','node','java') {
    $found = Get-Command $t -ErrorAction SilentlyContinue
    if ($found) {
      try { $ver = & $t --version 2>$null | Select-Object -First 1 } catch { $ver = 'unknown' }
      $sysInfo += "- **$t**: $ver"
    } else {
      $sysInfo += "- **$t**: not found"
    }
  }
  $sysInfo += ''
  $sysInfo += '## Verification Results'
  $sysInfo += "- Environment Lock File: $(if (Test-EnvLock) { '✅ PASSED' } else { '❌ FAILED' })"
  $sysInfo += "- Proof Assistants: $(if (Test-ProofAssistants) { '✅ PASSED' } else { '❌ FAILED' })"
  $sysInfo += "- SMT Solvers: $(if (Test-SMTSolvers) { '✅ PASSED' } else { '❌ FAILED' })"
  $sysInfo += "- Project Structure: $(if (Test-ProjectStructure) { '✅ PASSED' } else { '❌ FAILED' })"
  $sysInfo += "- Reproducibility Artifacts: $(if (Test-Artifacts) { '✅ PASSED' } else { '❌ FAILED' })"

  $sysInfo -join "`n" | Set-Content -LiteralPath $report -Encoding UTF8
  Write-Ok "Environment report generated: $report"
}

function Invoke-Main {
  Write-Info 'Starting SystemOSIOT environment verification (PowerShell)...'
  $failed = $false
  if (-not (Test-EnvLock)) { $failed = $true }
  if (-not (Test-ProofAssistants)) { $failed = $true }
  if (-not (Test-SMTSolvers)) { $failed = $true }
  if (-not (Test-TLATools)) { $failed = $true }
  if (-not (Test-ProjectStructure)) { $failed = $true }
  if (-not (Test-Artifacts)) { $failed = $true }
  New-EnvironmentReport
  if (-not $failed) { Write-Ok 'All environment verifications passed!'; exit 0 } else { Write-Err 'Some environment verifications failed!'; exit 1 }
}

Invoke-Main


