---------------------------- MODULE BGP_PathSelection ----------------------------
(*
 * SystemOSIOT BGP Path Selection / Route Flap Damping TLA+ Specification
 * 目标：形式化验证小规模 BGP 网络的路径选择与收敛性质。
 * 范围：3 个路由器组成的 AS 拓扑，按 LOCAL_PREF 与 AS_PATH 长度选路，
 *       检测路由振荡或最终收敛。
 * 来源：RFC 4271 (BGP-4) / RFC 2439 (Route Flap Damping)。
 * 验证：使用 TLC Model Checker 检查收敛与一致性。
 *)

EXTENDS Integers, FiniteSets, Naturals, Sequences

CONSTANTS
    R1, R2, R3,     \* 具体路由器实例（模型值）
    Routers,        \* 路由器集合
    Destinations,   \* 目标前缀集合
    MaxPathLength,  \* 模型检查时的最大 AS_PATH 长度
    MaxChanges      \* 允许的最大路由变化次数（用于检测振荡）

ASSUME
    /\ Routers = {R1, R2, R3}
    /\ R1 # R2 /\ R1 # R3 /\ R2 # R3
    /\ Destinations # {}
    /\ MaxPathLength \in Nat /\ MaxPathLength > 0
    /\ MaxChanges \in Nat /\ MaxChanges > 0

VARIABLES
    rib,            \* rib[r][d] = 当前为路由器 r 到 d 选择的最佳路由
    routes,         \* routes[r][d] = 路由器 r 到 d 学到的所有候选路由集合
    changes         \* changes[r][d] = 路由器 r 到 d 的路由变化次数

\* 路由属性：来源路由器、LOCAL_PREF、AS_PATH 长度、下一跳
Route == [origin : Routers, localPref : Nat, asPathLen : Nat, nextHop : Routers]

\* 空路由标记
NoRoute == [origin |-> "", localPref |-> 0, asPathLen |-> 0, nextHop |-> ""]

TypeOK ==
    /\ rib \in [Routers -> [Destinations -> Route \cup {NoRoute}]]
    /\ routes \in [Routers -> [Destinations -> SUBSET Route]]
    /\ changes \in [Routers -> [Destinations -> Nat]]

vars == <<rib, routes, changes>>

\* 路由器 r 自己产生到 d 的直连路由；不同起源者的初始 LOCAL_PREF 不同，避免平局
OriginateRoute(r, d) ==
    /\ rib[r][d] = NoRoute
    /\ LET pref == CASE r = R1 -> 300
                     [] r = R2 -> 200
                     [] r = R3 -> 100
                     [] OTHER -> 50
       direct == [origin |-> r, localPref |-> pref, asPathLen |-> 0, nextHop |-> r]
       IN
        /\ routes' = [routes EXCEPT ![r][d] = routes[r][d] \cup {direct}]
        /\ rib' = [rib EXCEPT ![r][d] = direct]
        /\ changes' = [changes EXCEPT ![r][d] = changes[r][d] + 1]

\* 从候选集中选择最佳路由：优先 LOCAL_PREF，其次 AS_PATH 长度短
BetterRoute(a, b) ==
    /\ a # NoRoute
    /\ (b = NoRoute
        \/ a.localPref > b.localPref
        \/ (a.localPref = b.localPref /\ a.asPathLen < b.asPathLen))

\* 从邻居 n 学到一条到 d 的路由并加入候选集；若新路由更优则立即更新 RIB
LearnRoute(r, n, d) ==
    /\ r # n
    /\ rib[n][d] # NoRoute
    /\ LET learned == [origin |-> rib[n][d].origin,
                       localPref |-> rib[n][d].localPref - 10,
                       asPathLen |-> rib[n][d].asPathLen + 1,
                       nextHop |-> n]
       IN
        /\ learned.asPathLen <= MaxPathLength
        /\ learned.localPref > 0
        /\ routes' = [routes EXCEPT ![r][d] = routes[r][d] \cup {learned}]
        /\ LET update == (rib[r][d] = NoRoute \/ BetterRoute(learned, rib[r][d]))
           IN
            /\ update => (rib' = [rib EXCEPT ![r][d] = learned]
                          /\ changes' = [changes EXCEPT ![r][d] = changes[r][d] + 1])
            /\ ~update => UNCHANGED <<rib, changes>>

SelectBestRoute(r, d) ==
    /\ routes[r][d] # {}
    /\ LET candidates == routes[r][d] \cup (IF rib[r][d] = NoRoute THEN {} ELSE {rib[r][d]})
           best == CHOOSE c \in candidates :
                       \A o \in candidates : o = c \/ BetterRoute(c, o)
       IN
        /\ best # rib[r][d]
        /\ rib' = [rib EXCEPT ![r][d] = best]
        /\ changes' = [changes EXCEPT ![r][d] = changes[r][d] + 1]
        /\ UNCHANGED <<routes>>

\* 注：为保持模型可终止，本简化模型未显式建模路由撤销与 flap-damping 的惩罚机制；
\*      重点验证路径选择与收敛性质。路由振荡检测可通过扩展 changes 阈值实现。

Init ==
    /\ rib = [r \in Routers |-> [d \in Destinations |-> NoRoute]]
    /\ routes = [r \in Routers |-> [d \in Destinations |-> {}]]
    /\ changes = [r \in Routers |-> [d \in Destinations |-> 0]]

Next ==
    \E r \in Routers, d \in Destinations :
        \/ OriginateRoute(r, d)
        \/ \E n \in Routers : LearnRoute(r, n, d)
        \/ SelectBestRoute(r, d)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------
(* 安全性质 *)

\* 类型不变式
TypeInvariant == TypeOK

\* 所选路由必须来自候选集或为空
SelectedRouteInCandidates ==
    \A r \in Routers, d \in Destinations :
        rib[r][d] # NoRoute => rib[r][d] \in routes[r][d]

\* 最佳路由一致性：若 r 已选路由，则候选集中不存在更优路由
BestRouteConsistency ==
    \A r \in Routers, d \in Destinations :
        \A rt \in routes[r][d] :
            rib[r][d] # NoRoute => ~BetterRoute(rt, rib[r][d])

-------------------------------------------------------------------------
(* 活性性质 *)

\* 收敛性：若路由变化次数未超过阈值，则最终必然获得一条有效路由
Convergence ==
    \A r \in Routers, d \in Destinations :
        changes[r][d] < MaxChanges ~> rib[r][d] # NoRoute

=============================================================================
