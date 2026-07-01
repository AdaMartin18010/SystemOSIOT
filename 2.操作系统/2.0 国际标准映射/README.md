# 2.0 操作系统 — 国际标准映射

## 1. 主要对标标准

| 标准/论文/产品 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| POSIX.1 / IEEE Std 1003.1 | 2024 (Issue 8) | <https://pubs.opengroup.org/onlinepubs/9799919799/> | 2.1, 2.3, 2.6 |
| Linux Standard Base (LSB) | ISO/IEC 23360-1-x:2021 | <https://webstore.iec.ch/en/publication/71478> | 2.1, 2.3 |
| Common Criteria | ISO/IEC 15408:2022 | <https://www.iso.org/standard/72891.html> | 2.2, 2.4 |
| seL4 formal verification | SOSP 2009 | DOI: 10.1145/1629575.1629596 | 2.1, 2.4, 2.6 |
| Fiasco.OC / L4Re | 最新 | <https://l4re.org/> | 2.1, 2.6 |

## 2. 标准条款映射表

| 标准条款 | 条款标题 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| POSIX.1-2024 第3章 | Definitions | 2.1 知识梳理 | 待补充 | 部分覆盖 |
| POSIX.1-2024 第11章 | General Terminal Interface | — | 待补充 | 未覆盖 |
| POSIX.1-2024 第16章 | Networking Interfaces | 2.1, 2.6 | 待补充 | 部分覆盖 |
| POSIX.1-2024 第17章 | Realtime | 2.1, 2.8 | 待补充 | 未覆盖 |
| seL4 SOSP 2009 | Functional Correctness Proof | 2.4 形式化证明 | 待补充 | 未覆盖 |
| ISO/IEC 15408:2022 APE | Security Targets evaluation | 2.2 批判分析 | 待补充 | 未覆盖 |

## 3. 覆盖缺口与补齐计划

1. 建立 POSIX.1-2024 关键条款与进程/线程/调度/内存/文件系统章节的逐条映射。
2. 增加 seL4 capability model、 Isabelle/HOL 形式化证明、binary verification 的分析。
3. 增加 C11 / Linux Kernel Memory Model (LKMM) 内存模型形式化。

## 4. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
