# 4.0 分布式系统 — 国际标准映射

## 1. 主要对标论文与标准

| 论文/标准 | 年份 | DOI/链接 | 对应项目章节 |
|---|---|---|---|
| CAP Theorem (Brewer) | 2000 | DOI: 10.1145/343477.343502 | 4.1, 4.3, 4.4 |
| CAP Theorem (Gilbert & Lynch) | 2002 | DOI: 10.1145/564585.564601 | 4.1, 4.3, 4.4 |
| FLP Impossibility | 1985 | DOI: 10.1145/3149.214121 | 4.1, 4.3, 4.4 |
| Paxos (Lamport) | 1998/2001 | DOI: 10.1145/279227.279229 | 4.1, 4.3, 4.6 |
| Raft (Ongaro & Ousterhout) | 2014 | https://www.usenix.org/conference/atc14/technical-sessions/presentation/ongaro | 4.1, 4.3, 4.6, 4.7 |
| Linearizability (Herlihy & Wing) | 1990 | DOI: 10.1145/78969.78972 | 4.1, 4.6, 4.7 |
| PBFT (Castro & Liskov) | 1999 | DOI: 10.1145/319155.319168 | 4.1, 4.2, 4.4 |
| PACELC (Abadi) | 2010 | https://doi.org/10.1145/1835698.1835701 | 4.1, 4.2 |

## 2. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [4.0.1 分布式共识与一致性模型](4.0.1%20分布式共识与一致性模型.md) | CAP/PACELC/FLP/Paxos/Raft/BFT/一致性模型光谱 |

## 3. 标准/论文映射表

| 来源 | 核心结论/条款 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| Gilbert & Lynch 2002 | CAP 严格形式化（C=linearizability, A=所有非故障节点响应） | 4.1 | 待补充 | 需修正简化表述 |
| Fischer, Lynch, Paterson 1985 | 异步系统单故障共识不可能 | 4.1, 4.3 | 待补充 | 未覆盖形式化证明 |
| Lamport 2001 | Paxos Made Simple | 4.1, 4.3 | 待补充 | 部分覆盖 |
| Ongaro & Ousterhout 2014 | Raft safety & liveness invariants | 4.1, 4.7 | 待补充 | 部分覆盖 |
| Herlihy & Wing 1990 | Linearizability formal definition | 4.6, 4.7 | 待补充 | 部分覆盖 |
| Castro & Liskov 1999 | Byzantine fault tolerance | 4.1, 4.2 | 待补充 | 未覆盖 |

## 4. 覆盖缺口与补齐计划

1. **修正 CAP 表述**：已完成全项目扫描，修正了 `4.1.1`、`4.1.4`、`4.2.1`、`4.3.1`、`4.4.1`、`4.5.1`、`4.6.x` 以及 `7.容器与微服务` 中多个文件的错误表述。  
2. **新增 PACELC 定理**：补充到 `4.1 知识梳理/一致性模型.md`。  
3. **新增 FLP 形式化证明**：用 Coq/Lean 对异步系统模型建模。  
4. **新增 Raft TLA+ 规范**：与论文不变式逐项对照。  
5. **新增 BFT 章节**：PBFT、HotStuff、Tendermint/Cosmos。

## 6. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| Raft TLA+ 规范 | `tools/tla-specifications/Raft.tla` + `Raft.cfg` | Raft 共识简化模型 |
| FLP 草图 | `tools/coq-verification/FLP_Sketch.v` | 异步系统共识不可能性模型 |

## 7. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-02 | 补充 CAP/PACELC/FLP/Raft/BFT 详细映射 | Kimi Code CLI |
