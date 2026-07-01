# SystemOSIOT 国际化权威标准基线

> 版本：1.0.0
> 更新日期：2026-07-02
> 用途：定义项目各模块必须对齐的国际权威来源，作为引用、映射与审计的基线。

## 1. 系统理论

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 国际标准 | ISO/IEC/IEEE 15288:2023 | 2023 | <https://www.iso.org/standard/81702.html> |
| 知识体系 | INCOSE Systems Engineering Handbook | 5th Ed., 2023 | <https://www.incose.org/products-and-publications/se-handbook> |
| 知识体系 | SEBoK | v2.13 (2025) | <https://sebokwiki.org/> |
| 建模语言 | OMG SysML v2 / KerML v1.0 | v2.0 (2025) | <https://www.omg.org/spec/SysML/> |
| 国际标准 | ISO/IEC/IEEE 24641:2023 | 2023 | <https://www.iso.org/standard/79111.html> |
| 国际标准 | ISO/IEC/IEEE 42010:2022 | 2022 | <https://www.iso.org/standard/77394.html> |

## 2. 操作系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 国际标准 | POSIX.1 / IEEE Std 1003.1 | 2024 (Issue 8) | <https://pubs.opengroup.org/onlinepubs/9799919799/> |
| 国际标准 | Linux Standard Base (LSB) | ISO/IEC 23360-1-x:2021 | <https://webstore.iec.ch/en/publication/71478> |
| 安全标准 | Common Criteria | ISO/IEC 15408:2022 | <https://www.iso.org/standard/72891.html> |
| 形式化 OS | seL4 | SOSP 2009 | DOI: 10.1145/1629575.1629596 |
| 微内核 | Fiasco.OC / L4Re | 最新 | <https://l4re.org/> |

## 3. 物联网嵌入式系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 国际标准 | ISO/IEC 30141 | 2024 (Edition 2) | <https://www.iso.org/standard/88800.html> |
| 安全标准 | IEC 62443-2-1 | 2024 | <https://webstore.iec.ch/en/publication/62883> |
| 安全指南 | NIST SP 800-213 / 800-213A | 2024 | <https://csrc.nist.gov/publications/detail/sp/800/213/final> |
| 协议 | MQTT | v5.0 (OASIS) | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> |
| 协议 | CoAP | RFC 7252/8323 | <https://doi.org/10.17487/RFC7252> |
| 协议 | LwM2M | 1.2 | <https://omaspecworks.org/> |
| 标准 | Matter / Thread | 1.4 / 1.4 | <https://csa-iot.org/all-solutions/matter/> |

## 4. 分布式系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 定理 | CAP Theorem (Brewer) | PODC 2000 | DOI: 10.1145/343477.343502 |
| 定理 | CAP Theorem (Gilbert & Lynch) | SIGACT News 2002 | DOI: 10.1145/564585.564601 |
| 定理 | FLP Impossibility | JACM 1985 | DOI: 10.1145/3149.214121 |
| 算法 | Paxos (Lamport) | TOCS 1998 / 2001 | DOI: 10.1145/279227.279229 |
| 算法 | Raft (Ongaro & Ousterhout) | USENIX ATC 2014 | <https://www.usenix.org/conference/atc14/technical-sessions/presentation/ongaro> |
| 算法 | PBFT (Castro & Liskov) | OSDI 1999 | DOI: 10.1145/319155.319168 |
| 一致性 | Linearizability (Herlihy & Wing) | TOPLAS 1990 | DOI: 10.1145/78969.78972 |
| 权衡 | PACELC (Abadi) | 2010 | <https://doi.org/10.1145/1835698.1835701> |
| 教材 | Designing Data-Intensive Applications | 2017 | <https://dataintensive.net/> |

## 5. 集群系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 标准 | MPI Standard | 4.1 (2023) | <https://www.mpi-forum.org/docs/mpi-4.1/mpi41-report.pdf> |
| 软件 | Slurm Workload Manager | 24.11 / 25.05 | <https://slurm.schedmd.com/> |
| 基准 | TOP500 / Green500 | 2025-06 | <https://top500.org/> |
| 能耗 | Energy Aware Runtime (EAR) | v7.0 | <https://www.ear.energy/> |

## 6. P2P 系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 协议 | BitTorrent / BEP 52 | v2 | <http://bittorrent.org/beps/bep_0052.html> |
| 算法 | Chord (Stoica et al.) | SIGCOMM 2001 | DOI: 10.1145/383059.383071 |
| 算法 | Kademlia (Maymounkov & Mazieres) | IPTPS 2002 | DOI: 10.1007/3-540-45748-8_5 |
| 协议栈 | libp2p / IPFS | 持续更新 | <https://docs.libp2p.io/> |
| 论文 | Bitcoin Whitepaper (Nakamoto) | 2008 | <https://bitcoin.org/bitcoin.pdf> |
| 算法 | HotStuff (Yin et al.) | 2019 | <https://doi.org/10.1145/3293611.3331591> |

## 7. 容器与微服务

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 标准 | OCI Runtime Spec | v1.3.0 | <https://github.com/opencontainers/runtime-spec/releases/tag/v1.3.0> |
| 标准 | OCI Image Spec | v1.1.0 | <https://github.com/opencontainers/image-spec/releases/tag/v1.1.0> |
| 标准 | OCI Distribution Spec | v1.1.0 | <https://github.com/opencontainers/distribution-spec/releases/tag/v1.1.0> |
| 编排 | Kubernetes | v1.33 (2025) | <https://v1-33.docs.kubernetes.io/> |
| 接口 | CNI Spec | v1.1.0 | <https://www.cni.dev/docs/spec/> |
| 接口 | CSI / CRI | 最新 | <https://kubernetes.io/docs/concepts/> |
| RPC | gRPC | v1.71.0 | <https://github.com/grpc/grpc/releases/tag/v1.71.0> |
| 事件 | CloudEvents | v1.0.2 | <https://github.com/cloudevents/spec/blob/v1.0.2/cloudevevents/spec.md> |
| 接口 | SMI | v0.7+ | <https://smi-spec.io/> |

## 8. 网络系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| RFC | TCP/IP Host Requirements | RFC 1122/1123 | DOI: 10.17487/RFC1122 |
| RFC | QUIC | RFC 9000/9001/9002/9114 | DOI: 10.17487/RFC9000 |
| RFC | BGP | RFC 4271 及扩展 | DOI: 10.17487/RFC4271 |
| RFC | OSPF | RFC 2328/5340 | DOI: 10.17487/RFC2328 |
| 标准 | IEEE 802.11 | IEEE 802.11-2024 | <https://standards.ieee.org/standard/802.11-2024.html> |
| 协议 | OpenFlow | 1.5.1 | <https://opennetworking.org/software-defined-standards/> |
| 语言 | P4 / P4Runtime | P4-16 / v1.4.1 | <https://p4.org/> |
| 标准 | 3GPP 5G-Advanced | Release 18 | <https://www.3gpp.org/specifications> |
| 框架 | NIST SP 800-207 | Zero Trust Architecture | <https://csrc.nist.gov/publications/detail/sp/800-207/final> |

## 9. 形式化方法通用基准

| 类别 | 权威资料 | 链接/DOI |
|---|---|---|
| 形式语义 | Winskel, *The Formal Semantics of Programming Languages* | MIT Press, 1993 |
| 形式语义 | Nielson & Nielson, *Semantics with Applications* | Springer, 2007 |
| SOS | Plotkin, *A Structural Approach to Operational Semantics* | DOI: 10.1016/j.jlap.2004.05.001 |
| 类型论 | Pierce, *Types and Programming Languages* | <https://www.cis.upenn.edu/~bcpierce/tapl/> |
| Coq 教材 | Pierce et al., *Software Foundations* | <https://softwarefoundations.cis.upenn.edu/> |
| Isabelle 教材 | Nipkow & Klein, *Concrete Semantics* | <http://concrete-semantics.org/> |
| Lean 教材 | Avigad et al., *Theorem Proving in Lean 4* | <https://leanprover.github.io/theorem_proving_in_lean4/> |
| 模型检验 | Baier & Katoen, *Principles of Model Checking* | MIT Press, 2008 |
| TLA+ | Lamport, *Specifying Systems* | <https://lamport.azurewebsites.net/tla/book.html> |
| 霍尔逻辑 | Hoare, *An Axiomatic Basis for Computer Programming* | DOI: 10.1145/363235.363259 |
| 分离逻辑 | Reynolds, *Separation Logic* | DOI: 10.1109/LICS.2002.1029817 |
| 并发 | Herlihy & Wing, *Linearizability* | DOI: 10.1145/78969.78972 |

## 10. 更新策略

- 每季度检索 ISO/IEC/IEEE/3GPP/IETF 官方站点，更新本基线。
- 新增模块或子主题前，必须先在本基线中确认权威来源。
