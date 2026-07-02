# PRISM 概率模型

本目录包含用于概率模型检验的 PRISM 规范。

## 文件

| 文件 | 内容 | 运行方式 |
|---|---|---|
| `IoT_Reliability.prism` | 物联网传感器节点电池耗尽 / 成功采样 / 失败重试的 DTMC 模型 | `prism IoT_Reliability.prism -pf "P=? [ F state=dead ]"` |
| `Mutex.pm` | 基于 MDP 的两进程互斥协议（安全 + 活性） | `prism Mutex.pm -pf 'filter(forall, G !(s1=2 & s2=2))'` |

## 依赖

- PRISM Model Checker 4.10.1+ (<https://www.prismmodelchecker.org/>)
- Java 17+（WSL 中已安装 `default-jre`）

## 本地运行（WSL / Linux）

```bash
export PATH="/mnt/e/_src/SystemOSIOT/tools/engines/prism-4.10.1-linux64-x86/bin:$PATH"
cd /mnt/e/_src/SystemOSIOT/tools/prism-models

# IoT 可靠性
prism IoT_Reliability.prism -pf 'P=? [ F state=dead ]'

# 互斥安全
prism Mutex.pm -pf 'filter(forall, G !(s1=2 & s2=2))'

# 互斥活性（Pmax=? 表示在所有调度下最大概率）
prism Mutex.pm -pf 'Pmax=? [ G (s1=1 -> F s1=2) ]'
```

## CI 运行

见 `.github/workflows/formal-verification.yml`。
