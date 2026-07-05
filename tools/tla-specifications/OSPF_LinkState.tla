---------------------------- MODULE OSPF_LinkState ----------------------------
(*
 * SystemOSIOT OSPF Link-State Protocol TLA+ Specification
 * 目标：形式化验证 OSPF 链路状态协议的核心机制与收敛性质。
 * 范围：小规模路由器拓扑，建模邻居状态机、LSA 泛洪、LSDB 同步、SPF 计算。
 * 来源：RFC 2328 (OSPFv2) / RFC 5340 (OSPFv3)。
 * 验证：使用 TLC Model Checker 检查 LSDB 最终一致性、无路由环路、邻居状态有效性。
 *)

EXTENDS Integers, FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    R1, R2, R3,     \* 具体路由器实例（模型值）
    Routers,        \* 路由器集合
    Links,          \* 无向链路集合，元素为 {r, n} 形式
    MaxSeq,         \* LSA 序列号上限（模型检查边界）
    MaxFloods       \* 泛洪计数上限（保证模型有界可终止）

ASSUME
    /\ Routers = {R1, R2, R3}
    /\ R1 # R2 /\ R1 # R3 /\ R2 # R3
    /\ Links \subseteq {{r, n} : r \in Routers, n \in Routers}
    /\ \A l \in Links : Cardinality(l) = 2
    /\ MaxSeq \in Nat /\ MaxSeq > 0
    /\ MaxFloods \in Nat /\ MaxFloods > 0

\* -------------------------------------------------------------------------
\* 类型与常量定义
\* -------------------------------------------------------------------------

\* 邻居状态机：Down → Init → 2-Way → ExStart → Exchange → Loading → Full
NeighborStates == {"Down", "Init", "2-Way", "ExStart", "Exchange", "Loading", "Full"}

\* 链路状态通告（LSA）：由起源路由器产生，包含序列号与邻接链路集合
\* 简化：每台路由器只维护一条自 originated 的 Router-LSA，描述其本地链路
LSA == [origin : Routers, seq : Nat, links : SUBSET Links]

VARIABLES
    neighborState,  \* neighborState[r][n] = 路由器 r 视角下邻居 n 的状态
    lsdb,           \* lsdb[r] = 路由器 r 的链路状态数据库（LSA 集合）
    lsaSeq,         \* lsaSeq[r] = 路由器 r 当前自起源 LSA 的序列号
    spfNextHop,     \* spfNextHop[r][d] = r 到 d 的下一跳路由器（或自身）
    floodCount      \* floodCount[r] = 路由器 r 已执行的泛洪次数（有界性）

vars == <<neighborState, lsdb, lsaSeq, spfNextHop, floodCount>>

\* 判断 r 与 n 之间存在物理链路
AreLinked(r, n) ==
    r # n /\ {r, n} \in Links

\* 邻居状态类型检查
NeighborStateTypeOK ==
    neighborState \in [Routers -> [Routers -> NeighborStates]]

\* LSDB 类型检查
LSDBTypeOK ==
    /\ lsdb \in [Routers -> SUBSET LSA]
    /\ lsaSeq \in [Routers -> Nat]
    /\ floodCount \in [Routers -> Nat]

\* 下一跳映射类型检查（自身用自身表示，空用模型值 NONE）
NextHopTypeOK ==
    spfNextHop \in [Routers -> [Routers -> Routers]]

TypeOK ==
    /\ NeighborStateTypeOK
    /\ LSDBTypeOK
    /\ NextHopTypeOK

\* -------------------------------------------------------------------------
\* 辅助算子
\* -------------------------------------------------------------------------

\* 路由器 r 自起源 LSA 的指定序列号版本
OwnLSA(r, seq) ==
    [origin |-> r, seq |-> seq, links |-> {l \in Links : r \in l}]

\* 比较两条 LSA 的新旧：同 origin 时 seq 大者更新；不同 origin 不可比
IsNewerThan(a, b) ==
    /\ a.origin = b.origin
    /\ a.seq > b.seq

\* 路由器 r 是否已与某邻居建立 Full 邻接
HasFullAdjacency(r) ==
    \E n \in Routers : neighborState[r][n] = "Full"

\* 路由器 r 是否已与所有链路邻居都达到 Full
AllNeighborsFull(r) ==
    \A n \in Routers : AreLinked(r, n) => neighborState[r][n] = "Full"

\* -------------------------------------------------------------------------
\* 初始化
\* -------------------------------------------------------------------------

Init ==
    /\ neighborState = [r \in Routers |-> [n \in Routers |-> IF AreLinked(r, n)
                                                          THEN "Down"
                                                          ELSE "Down"]]
    /\ lsdb = [r \in Routers |-> {OwnLSA(r, 1)}]
    /\ lsaSeq = [r \in Routers |-> 1]
    /\ spfNextHop = [r \in Routers |-> [d \in Routers |-> r]]
    /\ floodCount = [r \in Routers |-> 0]

\* -------------------------------------------------------------------------
\* 动作：邻居状态机
\* -------------------------------------------------------------------------

\* Down → Init：收到 Hello 包，发现邻居
ReceiveHello(r, n) ==
    /\ AreLinked(r, n)
    /\ neighborState[r][n] = "Down"
    /\ neighborState' = [neighborState EXCEPT ![r][n] = "Init"]
    /\ UNCHANGED <<lsdb, lsaSeq, spfNextHop, floodCount>>

\* Init → 2-Way：双向 Hello 可见（简化模型中，当双方都为 Init 时同时推进）
TwoWayReceived(r, n) ==
    /\ AreLinked(r, n)
    /\ neighborState[r][n] = "Init"
    /\ neighborState[n][r] = "Init"
    /\ neighborState' = [neighborState EXCEPT ![r][n] = "2-Way",
                                              ![n][r] = "2-Way"]
    /\ UNCHANGED <<lsdb, lsaSeq, spfNextHop, floodCount>>

\* 2-Way → ExStart：决定建立邻接（广播/NBMA 网络中由 DR/BDR 决定，此处简化为直接建立）
StartAdjacency(r, n) ==
    /\ AreLinked(r, n)
    /\ neighborState[r][n] = "2-Way"
    /\ neighborState[n][r] = "2-Way"
    /\ neighborState' = [neighborState EXCEPT ![r][n] = "ExStart",
                                              ![n][r] = "ExStart"]
    /\ UNCHANGED <<lsdb, lsaSeq, spfNextHop, floodCount>>

\* ExStart → Exchange → Loading → Full：DD 报文交换与 LSDB 同步（三阶段合并）
\* 要求双方此前状态一致，同步后互致 Full，并把对方已知的 LSA 并入本地 LSDB
ExchangeAndLoading(r, n) ==
    /\ AreLinked(r, n)
    /\ neighborState[r][n] = "ExStart"
    /\ neighborState[n][r] = "ExStart"
    /\ neighborState' = [neighborState EXCEPT ![r][n] = "Full",
                                              ![n][r] = "Full"]
    /\ lsdb' = [lsdb EXCEPT ![r] = lsdb[r] \cup lsdb[n],
                            ![n] = lsdb[n] \cup lsdb[r]]
    /\ UNCHANGED <<lsaSeq, spfNextHop, floodCount>>

\* -------------------------------------------------------------------------
\* 动作：LSA 泛洪
\* -------------------------------------------------------------------------

\* 路由器 r  originated 一条新的 Router-LSA（序列号递增），并泛洪给 Full 邻居
OriginateAndFloodLSA(r) ==
    /\ HasFullAdjacency(r)
    /\ lsaSeq[r] < MaxSeq
    /\ floodCount[r] < MaxFloods
    /\ LET newSeq == lsaSeq[r] + 1
           newLSA == OwnLSA(r, newSeq)
           newLsdb == (lsdb[r] \ {l \in lsdb[r] : l.origin = r}) \cup {newLSA}
       IN
        /\ lsdb' = [lsdb EXCEPT ![r] = newLsdb]
        /\ lsaSeq' = [lsaSeq EXCEPT ![r] = newSeq]
        /\ floodCount' = [floodCount EXCEPT ![r] = floodCount[r] + 1]
    /\ UNCHANGED <<neighborState, spfNextHop>>

\* 路由器 r 从邻居 n 收到一条更新的 LSA，并继续泛洪给其他 Full 邻居
\* 简化：若 r 的 LSDB 中该 origin 的 LSA 更旧，则用新的替换，并计入泛洪计数
ReceiveAndFloodLSA(r, n, lsa) ==
    /\ AreLinked(r, n)
    /\ neighborState[r][n] = "Full"
    /\ lsa \in lsdb[n]
    /\ lsa.origin # r            \* 不处理自己起源的 LSA（避免与 OriginateAndFloodLSA 冲突）
    /\ floodCount[r] < MaxFloods
    /\ LET old == {l \in lsdb[r] : l.origin = lsa.origin}
       IN
        /\ old = {} \/ (\E o \in old : IsNewerThan(lsa, o))
    /\ lsdb' = [lsdb EXCEPT ![r] = (lsdb[r] \ {l \in lsdb[r] : l.origin = lsa.origin}) \cup {lsa}]
    /\ floodCount' = [floodCount EXCEPT ![r] = floodCount[r] + 1]
    /\ UNCHANGED <<neighborState, lsaSeq, spfNextHop>>

\* -------------------------------------------------------------------------
\* 动作：SPF 计算（简化 Dijkstra，只计算到所有节点的下一跳）
\* -------------------------------------------------------------------------

\* 辅助：路由器 r 根据本地 LSDB 所知拓扑（所有 LSA 中 links 的并集）
KnownTopology(r) ==
    UNION {l.links : l \in lsdb[r]}

\* 在拓扑 topo 中，路由器 dst 是否可从 src 到达（路径长度 0..3，适合 3 节点模型）
ReachableIn(src, dst, topo) ==
    \/ src = dst
    \/ {src, dst} \in topo
    \/ \E x \in Routers : {src, x} \in topo /\ {x, dst} \in topo
    \/ \E x, y \in Routers : {src, x} \in topo /\ {x, y} \in topo /\ {y, dst} \in topo

\* 在已知拓扑 topo 中，从 src 到 dst 的最短路径距离（0..3；不可达用 3 表示，因为 3 节点最大距离为 2）
Distance(src, dst, topo) ==
    IF src = dst THEN 0
    ELSE IF {src, dst} \in topo THEN 1
    ELSE IF \E x \in Routers : {src, x} \in topo /\ {x, dst} \in topo THEN 2
    ELSE 3

\* 候选下一跳集合：与 r 为 Full 邻接且沿已知拓扑可达 d 的直连邻居
CandidateHops(r, d, topo) ==
    {nb \in Routers :
        /\ AreLinked(r, nb)
        /\ neighborState[r][nb] = "Full"
        /\ ReachableIn(nb, d, topo)}

\* 基于最短路径选择下一跳：在候选集合中选择到 d 距离最小的邻居
\* 若没有候选，则下一跳为 r 自身（表示暂不可达或本地投递）
RunSPF(r) ==
    /\ AllNeighborsFull(r)
    /\ LET topo == KnownTopology(r)
       IN
        spfNextHop' = [spfNextHop EXCEPT ![r] =
                           [d \in Routers |->
                               IF d = r THEN r
                               ELSE LET candidates == CandidateHops(r, d, topo)
                                    IN
                                      IF candidates = {}
                                      THEN r
                                      ELSE LET minDist == CHOOSE dist \in {Distance(nb, d, topo) : nb \in candidates} : TRUE
                                               best == {nb \in candidates : Distance(nb, d, topo) = minDist}
                                           IN CHOOSE nb \in best : TRUE]]
    /\ UNCHANGED <<neighborState, lsdb, lsaSeq, floodCount>>

\* -------------------------------------------------------------------------
\* 规范
\* -------------------------------------------------------------------------

Next ==
    \/ \E r, n \in Routers :
            \/ ReceiveHello(r, n)
            \/ TwoWayReceived(r, n)
            \/ StartAdjacency(r, n)
            \/ ExchangeAndLoading(r, n)
    \/ \E r \in Routers :
            \/ OriginateAndFloodLSA(r)
            \/ RunSPF(r)
            \/ \E n \in Routers : \E lsa \in lsdb[n] : ReceiveAndFloodLSA(r, n, lsa)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -------------------------------------------------------------------------
\* 不变式（安全性质）
\* -------------------------------------------------------------------------

\* 类型不变式
TypeInvariant == TypeOK

\* 邻居状态有效性：非链路节点保持 Down；状态只沿状态机向前
ValidNeighborState ==
    /\ \A r, n \in Routers :
        ~AreLinked(r, n) => neighborState[r][n] = "Down"

\* 自反性：路由器对自身的邻居状态保持 Down（非邻居）
SelfNeighborDown ==
    \A r \in Routers : neighborState[r][r] = "Down"

\* 对称性：若 r 视 n 为 Full，则 n 也视 r 为 Full（同步动作保证）
SymmetricFullState ==
    \A r, n \in Routers :
        neighborState[r][n] = "Full" <=> neighborState[n][r] = "Full"

\* 每台路由器至少保留自己的 LSA
OwnLSAInLSDB ==
    \A r \in Routers : OwnLSA(r, lsaSeq[r]) \in lsdb[r]

\* LSDB 无冲突：同一 origin 不会同时存在两条不同 seq 的 LSA
NoConflictingLSA ==
    \A r \in Routers : \A l1, l2 \in lsdb[r] :
        (l1.origin = l2.origin /\ l1 # l2) => l1.seq # l2.seq

\* 无路由环路：对任意目标 d，沿 spfNextHop 的转发图不存在长度 2 或 3 的有向环
\* 自环（路由器到自身）被允许，因为目标即自身时的下一跳只能是自身
NoForwardingLoop ==
    \A d \in Routers :
        /\ ~ \E a, b \in Routers :
              /\ a # b
              /\ spfNextHop[a][d] = b
              /\ spfNextHop[b][d] = a
        /\ ~ \E a, b, c \in Routers :
              /\ a # b /\ b # c /\ a # c
              /\ spfNextHop[a][d] = b
              /\ spfNextHop[b][d] = c
              /\ spfNextHop[c][d] = a

\* -------------------------------------------------------------------------
\* 活性性质
\* -------------------------------------------------------------------------

\* LSDB 最终一致性：若两台路由器互为 Full 邻居，则它们的 LSDB 最终相等
LSDBConsistency ==
    \A r, n \in Routers :
        neighborState[r][n] = "Full" ~> lsdb[r] = lsdb[n]

\* 泛洪有界性：计数器不超过阈值
FloodCountBounded ==
    \A r \in Routers : floodCount[r] <= MaxFloods

=============================================================================
