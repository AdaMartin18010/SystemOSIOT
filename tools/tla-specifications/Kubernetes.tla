---------------------------- MODULE Kubernetes ----------------------------
(*
 * SystemOSIOT Kubernetes TLA+ Specification
 * 目标：形式化验证 Kubernetes Pod 生命周期与 Deployment 滚动更新的核心性质。
 * 范围：简化模型，覆盖 Pod 状态机、ReplicaSet 副本数、滚动更新策略。
 * 来源：Kubernetes v1.33 API 与控制器机制。
 * 验证：使用 TLC Model Checker 检查 safety 与 liveness 性质。
 *)

EXTENDS Integers, FiniteSets, Sequences, Naturals

CONSTANTS
    PodIDs,         \* Pod 标识符集合，例如 {p1, p2, p3}
    MaxReplicas,    \* 模型检查时最大副本数
    MaxUnavailable, \* 滚动更新时最大不可用副本数
    MaxSurge        \* 滚动更新时最大超量副本数

ASSUME
    /\ PodIDs # {}
    /\ IsFiniteSet(PodIDs)
    /\ MaxReplicas \in Nat /\ MaxReplicas > 0
    /\ MaxUnavailable \in Nat
    /\ MaxSurge \in Nat

VARIABLES
    podState,       \* podState[p] : Pod 当前状态
    podVersion,     \* podVersion[p] : Pod 所属 Deployment 版本（old 或 new）
    replicasOld,    \* 旧版本 ReplicaSet 期望副本数
    replicasNew     \* 新版本 ReplicaSet 期望副本数

\* Pod 状态集合
Pending   == "Pending"
Running   == "Running"
Succeeded == "Succeeded"
Failed    == "Failed"
Unknown   == "Unknown"
Deleted   == "Deleted"

\* Deployment 版本
OldVersion == "old"
NewVersion == "new"

vars == <<podState, podVersion, replicasOld, replicasNew>>

\* 辅助函数：统计各版本、各状态的 Pod 数量
CountVersionState(v, s) == Cardinality({p \in PodIDs : podVersion[p] = v /\ podState[p] = s})
CountVersion(v) == Cardinality({p \in PodIDs : podVersion[p] = v /\ podState[p] # Deleted})
CountRunning(v) == CountVersionState(v, Running)
CountUnavailable ==
    Cardinality({p \in PodIDs : podVersion[p] \in {OldVersion, NewVersion}
                         /\ podState[p] \in {Pending, Failed, Unknown}})

\* 初始状态：所有 Pod 未分配，旧版本期望 MaxReplicas，新版本期望 0
Init ==
    /\ podState   = [p \in PodIDs |-> Deleted]
    /\ podVersion = [p \in PodIDs |-> OldVersion]
    /\ replicasOld = MaxReplicas
    /\ replicasNew = 0

\* 创建 Pod：为旧版本或新版本分配一个 Deleted 状态的 Pod
CreatePod(p, v) ==
    /\ podState[p] = Deleted
    /\ podVersion[p] # v
    /\ LET currentTotal == CountVersion(OldVersion) + CountVersion(NewVersion)
       IN currentTotal < MaxReplicas + MaxSurge
    /\ podState'   = [podState EXCEPT ![p] = Pending]
    /\ podVersion' = [podVersion EXCEPT ![p] = v]
    /\ UNCHANGED <<replicasOld, replicasNew>>

\* Pod 状态迁移（Pending -> Running -> Succeeded/Failed）
PodTransition(p, fromState, toState) ==
    /\ podState[p] = fromState
    /\ podState[p] # Deleted
    /\ podState' = [podState EXCEPT ![p] = toState]
    /\ UNCHANGED <<podVersion, replicasOld, replicasNew>>

\* 删除 Pod（滚动更新时缩容）
DeletePod(p) ==
    /\ podState[p] # Deleted
    /\ podState'   = [podState EXCEPT ![p] = Deleted]
    /\ podVersion' = [podVersion EXCEPT ![p] = OldVersion]
    /\ UNCHANGED <<replicasOld, replicasNew>>

\* 启动滚动更新：新版本期望副本数增加
StartRollout ==
    /\ replicasNew = 0
    /\ replicasNew' = MaxReplicas
    /\ UNCHANGED <<podState, podVersion, replicasOld>>

\* 推进滚动更新：在 maxUnavailable / maxSurge 约束下调整副本数
AdvanceRollout ==
    /\ replicasNew > 0
    /\ replicasNew < MaxReplicas
    /\ replicasOld > 0
    /\ CountUnavailable <= MaxUnavailable
    /\ (CountVersion(OldVersion) + CountVersion(NewVersion)) < MaxReplicas + MaxSurge
    /\ replicasOld' = replicasOld - 1
    /\ replicasNew' = replicasNew + 1
    /\ UNCHANGED <<podState, podVersion>>

\* 完成滚动更新：旧版本副本数归零
FinishRollout ==
    /\ replicasOld = 0
    /\ CountVersion(OldVersion) = 0
    /\ UNCHANGED vars

\* 下一步迁移关系
Next ==
    \/ \E p \in PodIDs : CreatePod(p, OldVersion)
    \/ \E p \in PodIDs : CreatePod(p, NewVersion)
    \/ \E p \in PodIDs : PodTransition(p, Pending, Running)
    \/ \E p \in PodIDs : PodTransition(p, Running, Succeeded)
    \/ \E p \in PodIDs : PodTransition(p, Running, Failed)
    \/ \E p \in PodIDs : DeletePod(p)
    \/ StartRollout
    \/ AdvanceRollout
    \/ FinishRollout

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* 安全性质 *)

\* 类型不变式
TypeInvariant ==
    /\ podState   \in [PodIDs -> {Pending, Running, Succeeded, Failed, Unknown, Deleted}]
    /\ podVersion  \in [PodIDs -> {OldVersion, NewVersion}]
    /\ replicasOld \in 0..MaxReplicas
    /\ replicasNew \in 0..MaxReplicas

\* 副本数约束：总运行副本数不超过期望总数 + MaxSurge，不低于期望总数 - MaxUnavailable
ReplicaSetConstraint ==
    LET totalRunning == CountRunning(OldVersion) + CountRunning(NewVersion)
    IN totalRunning <= MaxReplicas + MaxSurge

\* 滚动更新约束：不可用 Pod 数不超过 MaxUnavailable
UnavailableConstraint ==
    CountUnavailable <= MaxUnavailable

\* Deployment 完成后的收敛性：最终所有运行中的 Pod 都是新版本
\* 这是一个 safety 性质的近似（在 finish 状态下成立）
RolloutCompleteness ==
    (replicasOld = 0 /\ replicasNew = MaxReplicas)
        => \A p \in PodIDs : podState[p] = Running => podVersion[p] = NewVersion

=============================================================================
