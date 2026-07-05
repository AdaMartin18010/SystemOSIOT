# 6.0 P2P 系统 — 国际标准映射


<!-- TOC START -->

- [6.0 P2P 系统 — 国际标准映射](#60-p2p-系统--国际标准映射)
  - [1. 主要对标标准](#1-主要对标标准)
  - [2. 详细映射子文档](#2-详细映射子文档)
  - [3. 标准条款映射表](#3-标准条款映射表)
  - [4. 覆盖缺口与补齐计划](#4-覆盖缺口与补齐计划)
  - [5. 形式化工件链接](#5-形式化工件链接)
  - [6. 维护记录](#6-维护记录)

<!-- TOC END -->

## 1. 主要对标标准

| 标准/规范 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| BitTorrent BEP Index | BEP 0000–0052+ | <https://www.bittorrent.org/beps/bep_0000.html> | 6.1, 6.3, 6.6 |
| Kademlia DHT | 2002 (LNCS) | <https://pdos.csail.mit.edu/~petar/papers/maymounkov-kademlia-lncs.pdf> | 6.1, 6.3, 6.4 |
| IPFS Specs | 2024/当前 | <https://specs.ipfs.tech/> | 6.1, 6.3, 6.5 |
| libp2p Specs | 当前 | <https://specs.libp2p.io/> | 6.1, 6.3, 6.6 |
| WebRTC Overview | RFC 8825 | <https://www.rfc-editor.org/rfc/rfc8825.html> | 6.1, 6.6 |
| WebRTC Data Channel | RFC 8838 / RFC 8863 | <https://www.rfc-editor.org/rfc/rfc8838.html> / <https://www.rfc-editor.org/rfc/rfc8863.html> | 6.1, 6.6 |
| WebRTC Security | RFC 8833 | <https://www.rfc-editor.org/rfc/rfc8833.html> | 6.1, 6.2, 6.6 |
| WebRTC JSEP | RFC 8829 | <https://www.rfc-editor.org/rfc/rfc8829.html> | 6.1, 6.6 |
| PPSP (Peer-to-Peer Streaming Protocol) | RFC 7574 / RFC 7656 | <https://www.rfc-editor.org/rfc/rfc7574.html> / <https://www.rfc-editor.org/rfc/rfc7656.html> | 6.1, 6.3 |
| Dat Protocol / Hypercore | 当前 | <https://dat-ecosystem.org/> / <https://github.com/datprotocol> | 6.1, 6.3 |
| ActivityPub | W3C REC (2018/当前) | <https://www.w3.org/TR/activitypub/> | 6.1, 6.5 |
| Matrix Specification | 当前 | <https://spec.matrix.org/> | 6.1, 6.3 |
| W3C DID Core | W3C REC (2022/当前) | <https://www.w3.org/TR/did-core/> | 6.1, 6.2, 6.3 |
| W3C Verifiable Credentials Data Model | v2.0 W3C REC (当前) | <https://www.w3.org/TR/vc-data-model-2.0/> | 6.1, 6.2 |
| NIST Decentralized Identity | 当前 | <https://pages.nist.gov/DeIdent/> | 6.1, 6.2 |
| EU eIDAS | Regulation (EU) No 910/2014 / 2024 修订 | <https://digital-strategy.ec.europa.eu/en/policies/eidas-regulation> | 6.1, 6.2 |
| GDPR | Regulation (EU) 2016/679 | <https://gdpr-info.eu/> / <https://eur-lex.europa.eu/eli/reg/2016/679/oj> | 6.1, 6.2 |

## 2. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [6.0.1 BitTorrent 与 DHT 协议标准映射](6.0.1%20BitTorrent%20与%20DHT%20协议标准映射.md) | BitTorrent BEP、Kademlia DHT、libp2p、IPFS 内容寻址条款级映射 |
| [6.0.2 P2P 安全与隐私标准映射](6.0.2%20P2P%20安全与隐私标准映射.md) | WebRTC 安全、DID/VC、GDPR/eIDAS、NIST 去中心化身份条款级映射 |

## 3. 标准条款映射表

| 标准/来源 | 核心条款/内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| BitTorrent BEP 3 | Peer Wire Protocol、pieces、choking/unchoking、interested 状态机 | 6.1, 6.3 | 6.1.1 基本概念、6.1.3 主要流派与理论 | 部分覆盖 |
| BitTorrent BEP 5 | DHT Protocol、infohash 路由、节点 ID、KRPC（ping/find_node/get_peers/announce_peer） | 6.1, 6.3 | 6.1.1 基本概念、6.3.1 形式化定义 | 部分覆盖 |
| Kademlia (Maymounkov & Mazières, 2002) | XOR 距离、k-buckets、并行异步查找、O(log n) 路由 | 6.1, 6.3, 6.4 | 6.1.1 基本概念、6.3.1 形式化定义 | 部分覆盖 |
| libp2p specs | multiaddr、peer ID、swarm、NAT traversal、pubsub、gossipsub | 6.1, 6.3 | 6.1.1 基本概念 | 未覆盖 |
| IPFS specs | CID、MerkleDAG、bitswap、内容寻址、不可变命名 | 6.1, 6.3 | 6.1.3 主要流派与理论 | 未覆盖 |
| WebRTC RFC 8833 / RFC 8829 | DTLS/SRTP、ICE、STUN/TURN、SDP offer/answer | 6.1, 6.2 | 6.1.1 基本概念 | 未覆盖 |
| PPSP RFC 7574 | Peer Protocol、chunk scheduling、peer discovery、content authentication | 6.1 | 6.1.5 相关案例 | 未覆盖 |
| PPSP RFC 7656 | RTP 拓扑与报文分类、P2P streaming 术语 | 6.1 | 6.1.1 基本概念 | 未覆盖 |
| W3C DID Core | DID、DID document、DID method、verification method、service endpoint | 6.1, 6.2, 6.3 | 6.1.1 基本概念 | 未覆盖 |
| W3C VC Data Model 2.0 | Verifiable credential、verifiable presentation、issuer、holder、verifier | 6.1, 6.2 | 6.1.1 基本概念 | 未覆盖 |
| GDPR Art. 5 / Art. 25 / Art. 32 | 数据最小化、Privacy by Design、技术与组织安全措施 | 6.1, 6.2 | 6.1.1 基本概念 | 未覆盖 |
| EU eIDAS | 电子身份与信任服务、合格证书、电子签名 | 6.1, 6.2 | 6.1.1 基本概念 | 未覆盖 |

## 4. 覆盖缺口与补齐计划

1. **BitTorrent 协议细节补齐**：在 `6.1 知识梳理` 中补充 BEP 3 的 choking/unchoking 状态机、BEP 5 的 KRPC 消息格式与 DHT 路由表维护细节。
2. **libp2p / IPFS 现代 P2P 栈**：新增 `6.1 知识梳理/libp2p 与 IPFS 协议栈.md`，覆盖 multiaddr、CID、bitswap、gossipsub、NAT hole punching。
3. **WebRTC 安全与 NAT 穿透**：在 `6.2 批判分析` 中补充 WebRTC ICE/STUN/TURN/DTLS 的安全边界与隐私风险分析。
4. **去中心化身份（DID/VC/eIDAS）**：新增 `6.1 知识梳理/去中心化身份与可验证凭证.md`，建立与 W3C DID Core、VC 2.0、EU eIDAS 的条款级映射。
5. **形式化模型扩展**：为 Kademlia 查找过程、BitTorrent 片段交换状态机建立 TLA+/PlusCal 规范，并补充可运行配置。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| Raft TLA+ 规范 | `tools/tla-specifications/Raft.tla` + `Raft.cfg` | 共识机制通用模型，可用于 P2P 区块链共识分析 |
| QUIC TLA+ 规范 | `tools/tla-specifications/QUIC.tla` + `QUIC.cfg` | 现代 P2P 传输层（如 libp2p QUIC）的握手与流控参考 |
| FLP 异步共识草图 | `tools/coq-verification/FLP_Sketch.v` | 异步系统共识不可能性证明，用于 P2P BFT 场景边界说明 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 P2P 系统国际标准映射骨架 | Kimi Code CLI |
| 2026-07-02 | 补充 BitTorrent/DHT 与 P2P 安全隐私详细映射子文档 | Kimi Code CLI |
