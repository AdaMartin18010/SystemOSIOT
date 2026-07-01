# 6.0 P2P 系统 — 国际标准映射

## 1. 主要对标论文与协议

| 论文/协议 | 年份 | DOI/链接 | 对应项目章节 |
|---|---|---|---|
| BitTorrent Protocol / BEP 52 | v2 | <http://bittorrent.org/beps/bep_0052.html> | 6.1, 6.3, 6.6 |
| Chord (Stoica et al.) | 2001 | DOI: 10.1145/383059.383071 | 6.1, 6.3, 6.4 |
| Kademlia (Maymounkov & Mazieres) | 2002 | DOI: 10.1007/3-540-45748-8_5 | 6.1, 6.3, 6.4 |
| libp2p / IPFS | 持续更新 | <https://docs.libp2p.io/> | 6.1, 6.3, 6.6, 6.7 |
| Bitcoin Whitepaper (Nakamoto) | 2008 | <https://bitcoin.org/bitcoin.pdf> | 6.1, 6.2, 6.4 |
| HotStuff (Yin et al.) | 2019 | <https://doi.org/10.1145/3293611.3331591> | 6.2, 6.4 |

## 2. 论文/协议映射表

| 来源 | 核心内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| Stoica et al. 2001 | Chord DHT routing & consistency | 6.1, 6.3 | 待补充 | 部分覆盖 |
| Maymounkov & Mazieres 2002 | Kademlia XOR metric & lookup | 6.1, 6.3 | 待补充 | 部分覆盖 |
| BEP 52 | BitTorrent v2 Merkle tree pieces | 6.1, 6.3 | 待补充 | 未覆盖 |
| libp2p specs | Multiaddr, Kademlia DHT, GossipSub | 6.1, 6.3, 6.6 | 待补充 | 未覆盖 |
| Nakamoto 2008 | PoW consensus & incentive | 6.1, 6.2 | 待补充 | 部分覆盖 |

## 3. 覆盖缺口与补齐计划

1. 扩充 P2P 模块至与集群系统相当规模（目标 80–100 文件）。
2. 为 Chord/Kademlia 提供 TLA+/进程代数路由正确性规范。
3. 新增 BitTorrent v2、libp2p、IPFS 内容寻址章节。
4. 增加区块链共识（PoW/PoS/PBFT/HotStuff）与激励机制形式化。

## 4. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
