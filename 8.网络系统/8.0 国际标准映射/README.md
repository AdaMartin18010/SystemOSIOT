# 8.0 网络系统 — 国际标准映射

## 1. 主要对标标准与 RFC

| 标准/RFC | 版本 | DOI/链接 | 对应项目章节 |
|---|---|---|---|
| IP / TCP / Host Requirements | RFC 791/793/1122/1123 | DOI: 10.17487/RFC1122 | 8.1, 8.6, 8.7 |
| QUIC | RFC 9000/9001/9002/9114 | DOI: 10.17487/RFC9000 | 8.1, 8.6, 8.7 |
| BGP | RFC 4271/4456/4760/7752/9107/9552 | DOI: 10.17487/RFC4271 | 8.1, 8.3, 8.6 |
| OSPF | RFC 2328/5340 | DOI: 10.17487/RFC2328 | 8.1, 8.3, 8.6 |
| IEEE 802.11 | IEEE 802.11-2024 | <https://standards.ieee.org/standard/802.11-2024.html> | 8.1, 8.5, 8.8 |
| OpenFlow | 1.5.1 | <https://opennetworking.org/software-defined-standards/> | 8.8 |
| P4 / P4Runtime | P4-16 / v1.4.1 | <https://p4.org/> | 8.8 |
| 3GPP 5G-Advanced | Release 18 | <https://www.3gpp.org/specifications> | 8.8 |
| NIST SP 800-207 | Zero Trust Architecture | <https://csrc.nist.gov/publications/detail/sp/800-207/final> | 8.2, 8.8 |

## 2. 标准/RFC 映射表

| 来源 | 核心内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| RFC 1122 | Host requirements (link, IP, TCP) | 8.1, 8.6 | 待补充 | 部分覆盖 |
| RFC 9000 | QUIC transport protocol | 8.1, 8.6, 8.7 | 待补充 | 需增强 |
| RFC 4271 | BGP-4 path selection | 8.1, 8.3 | 待补充 | 部分覆盖 |
| RFC 2328 | OSPFv2 Dijkstra/LSA | 8.1, 8.3 | 待补充 | 部分覆盖 |
| IEEE 802.11-2024 | WLAN MAC/PHY | 8.1, 8.5 | 待补充 | 需升级版本 |
| P4-16 Language Spec | Protocol-independent packet processing | 8.8 | 待补充 | 未覆盖 |
| NIST SP 800-207 | Zero Trust principles | 8.2, 8.8 | 待补充 | 未覆盖 |

## 3. 覆盖缺口与补齐计划

1. **RFC 引用规范化**：全模块知识点标注 RFC 编号/DOI/版本，删除无来源推测。
2. **QUIC 独立专章**：按 RFC 9000 条款建立形式化分析。
3. **BGP 安全**：新增 RPKI、ROV、BGPsec 章节。
4. **可编程网络**：新增 P4/P4Runtime、OpenFlow 1.5.1 形式化语义。
5. **零信任架构**：增加 NIST SP 800-207 映射。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| QUIC/TCP 握手 TLA+ | `tools/tla-specifications/QUIC.tla` + `QUIC.cfg` | 传输层握手状态机与安全性质 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
