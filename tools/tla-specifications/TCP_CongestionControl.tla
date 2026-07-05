---------------------------- MODULE TCP_CongestionControl ----------------------------
(*
 * SystemOSIOT TCP Congestion Control TLA+ Specification
 * 目标：形式化验证 TCP Reno/CUBIC 拥塞控制状态机的核心性质。
 * 范围：简化模型，覆盖慢启动、拥塞避免、快速重传/恢复、超时四个状态。
 * 来源：RFC 5681 (TCP Congestion Control) / RFC 8312 (CUBIC)。
 * 验证：使用 TLC Model Checker 检查安全性与活性。
 *)

EXTENDS Integers, Naturals

CONSTANTS
    InitialCwnd,    \* 初始拥塞窗口（段数）
    SsthreshInit,   \* 初始慢启动阈值
    MaxCwnd,        \* 模型检查时的最大 cwnd
    DupAckThreshold \* 触发快速重传的重复 ACK 阈值

ASSUME
    /\ InitialCwnd \in Nat /\ InitialCwnd > 0
    /\ SsthreshInit \in Nat /\ SsthreshInit > InitialCwnd
    /\ MaxCwnd \in Nat /\ MaxCwnd >= SsthreshInit
    /\ DupAckThreshold \in Nat /\ DupAckThreshold > 0

VARIABLES
    state,          \* 发送端拥塞控制状态
    cwnd,           \* 拥塞窗口
    ssthresh,       \* 慢启动阈值
    dupAckCount     \* 重复 ACK 计数

\* 发送端状态
SlowStart           == "SlowStart"
CongestionAvoidance == "CongestionAvoidance"
FastRecovery        == "FastRecovery"

vars == <<state, cwnd, ssthresh, dupAckCount>>

Init ==
    /\ state        = SlowStart
    /\ cwnd         = InitialCwnd
    /\ ssthresh     = SsthreshInit
    /\ dupAckCount  = 0

\* 慢启动：收到新 ACK 且 cwnd < ssthresh，cwnd 指数增长
SlowStartAck ==
    /\ state = SlowStart
    /\ cwnd < ssthresh
    /\ cwnd < MaxCwnd
    /\ cwnd' = cwnd + 1
    /\ UNCHANGED <<state, ssthresh, dupAckCount>>

\* 慢启动 → 拥塞避免：cwnd 达到 ssthresh
EnterCongestionAvoidance ==
    /\ state = SlowStart
    /\ cwnd >= ssthresh
    /\ state' = CongestionAvoidance
    /\ UNCHANGED <<cwnd, ssthresh, dupAckCount>>

\* 拥塞避免：收到新 ACK，cwnd 线性增长
CongestionAvoidanceAck ==
    /\ state = CongestionAvoidance
    /\ cwnd < MaxCwnd
    /\ cwnd' = cwnd + 1
    /\ UNCHANGED <<state, ssthresh, dupAckCount>>

\* 收到重复 ACK，增加计数
DupAckArrives ==
    /\ state \in {SlowStart, CongestionAvoidance}
    /\ dupAckCount < DupAckThreshold
    /\ dupAckCount' = dupAckCount + 1
    /\ UNCHANGED <<state, cwnd, ssthresh>>

\* 快速重传/恢复：重复 ACK 达到阈值
FastRetransmit ==
    /\ state \in {SlowStart, CongestionAvoidance}
    /\ dupAckCount >= DupAckThreshold
    /\ state' = FastRecovery
    /\ ssthresh' = IF cwnd \div 2 > 1 THEN cwnd \div 2 ELSE 1
    /\ cwnd' = ssthresh' + DupAckThreshold
    /\ dupAckCount' = 0

\* 快速恢复期间收到部分 ACK，cwnd 膨胀（简化）
FastRecoveryAck ==
    /\ state = FastRecovery
    /\ cwnd < MaxCwnd
    /\ cwnd' = cwnd + 1
    /\ UNCHANGED <<state, ssthresh, dupAckCount>>

\* 快速恢复完成，回到拥塞避免
FastRecoveryComplete ==
    /\ state = FastRecovery
    /\ cwnd >= ssthresh
    /\ state' = CongestionAvoidance
    /\ cwnd' = ssthresh
    /\ dupAckCount' = 0
    /\ UNCHANGED <<ssthresh>>

\* 超时：重置为慢启动，cwnd 回到 InitialCwnd
Timeout ==
    /\ state \in {SlowStart, CongestionAvoidance, FastRecovery}
    /\ state' = SlowStart
    /\ ssthresh' = IF cwnd \div 2 > 1 THEN cwnd \div 2 ELSE 1
    /\ cwnd' = InitialCwnd
    /\ dupAckCount' = 0

Next ==
    /\ SlowStartAck
    \/ EnterCongestionAvoidance
    \/ CongestionAvoidanceAck
    \/ DupAckArrives
    \/ FastRetransmit
    \/ FastRecoveryAck
    \/ FastRecoveryComplete
    \/ Timeout

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------
(* 安全性质 *)

\* 类型不变式
TypeInvariant ==
    /\ state \in {SlowStart, CongestionAvoidance, FastRecovery}
    /\ cwnd \in 1..MaxCwnd
    /\ ssthresh \in 1..MaxCwnd
    /\ dupAckCount \in 0..DupAckThreshold

\* cwnd 始终非负且不超过上限
CwndBounds ==
    /\ cwnd >= 1
    /\ cwnd <= MaxCwnd

\* ssthresh 始终非负
SsthreshNonNegative ==
    ssthresh >= 1

\* 发送端状态一致性：慢启动时 cwnd < ssthresh 是允许的（进入 CA 的条件）
StateConsistency ==
    /\ state = CongestionAvoidance => cwnd >= ssthresh
    /\ state = FastRecovery => cwnd > ssthresh

\* 重复 ACK 计数只在非恢复状态累积
DupAckOnlyInOpenStates ==
    dupAckCount > 0 => state \in {SlowStart, CongestionAvoidance}

-------------------------------------------------------------------------
(* 活性性质 *)

\* 一旦进入快速恢复，最终必然离开（完成恢复或超时）
RecoveryEventually ==
    state = FastRecovery ~> state # FastRecovery

=============================================================================
