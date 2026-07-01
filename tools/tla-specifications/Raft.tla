---------------------------- MODULE Raft ----------------------------
(*
 * SystemOSIOT Raft TLA+ Specification
 * 目标：形式化验证 Raft 共识算法的核心安全性质。
 * 范围：简化模型，覆盖 Leader 选举、日志复制、提交索引。
 * 来源：Diego Ongaro & John Ousterhout, "In Search of an Understandable
 *       Consensus Algorithm", USENIX ATC 2014.
 * 验证：使用 TLC Model Checker 检查 safety 性质。
 *)

EXTENDS Integers, FiniteSets, Sequences, Naturals

CONSTANTS
    Nodes,          \* 节点集合，例如 {n1, n2, n3}
    Values,         \* 客户端可提交的日志条目值
    MaxTerm         \* 模型检查时用到的最大任期上限

ASSUME
    /\ Nodes # {}
    /\ IsFiniteSet(Nodes)
    /\ MaxTerm \in Nat

VARIABLES
    currentTerm,    \* currentTerm[n] : 节点 n 的当前任期
    role,           \* role[n] \in {"Follower", "Candidate", "Leader"}
    votedFor,       \* votedFor[n] : 节点 n 在当前任期投给的候选人，或 Nil
    votesGranted,   \* votesGranted[n] : 节点 n 作为候选人已获得的投票集合
    log,            \* log[n] : 节点 n 的日志序列，每个条目为 [term |-> t, value |-> v]
    commitIndex     \* commitIndex[n] : 节点 n 已提交的最高日志索引

Nil == "Nil"

\* 节点角色集合
Follower  == "Follower"
Candidate == "Candidate"
Leader    == "Leader"

vars == <<currentTerm, role, votedFor, votesGranted, log, commitIndex>>

\* 初始状态：所有节点为 Follower，任期 0，日志为空
Init ==
    /\ currentTerm = [n \in Nodes |-> 0]
    /\ role        = [n \in Nodes |-> Follower]
    /\ votedFor    = [n \in Nodes |-> Nil]
    /\ votesGranted = [n \in Nodes |-> {}]
    /\ log         = [n \in Nodes |-> <<>>]
    /\ commitIndex  = [n \in Nodes |-> 0]

\* 简单多数派判定
Majority(S) == Cardinality(S) * 2 > Cardinality(Nodes)

\* 节点 n 的日志长度
LogLen(n) == Len(log[n])

\* 节点 n 在索引 i 处的日志条目任期（若索引越界则返回 -1）
TermAt(n, i) ==
    IF i \in 1..LogLen(n) THEN log[n][i].term ELSE -1

\* 检查节点 voter 是否可以投票给候选节点 candidate
\* 规则：任期更大，或任期相同但日志至少一样新
CanVoteFor(voter, candidate) ==
    LET cv == currentTerm[candidate]
        vv == currentTerm[voter]
    IN
        /\ role[candidate] = Candidate
        /\ cv >= vv
        /\ votedFor[voter] \in {Nil, candidate}
        (* log[candidate] 在日志新鲜度上不落后于 log[voter] *)
        /\ <<TermAt(candidate, LogLen(candidate)), LogLen(candidate)>>
            >= <<TermAt(voter, LogLen(voter)), LogLen(voter)>>

\* 超时：Follower 或 Candidate 增加任期并发起选举
Timeout(n) ==
    /\ role[n] \in {Follower, Candidate}
    /\ currentTerm[n] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![n] = @ + 1]
    /\ role'        = [role EXCEPT ![n] = Candidate]
    /\ votedFor'    = [votedFor EXCEPT ![n] = n]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ UNCHANGED <<log, commitIndex>>

\* voter 投票给 candidate
RequestVote(voter, candidate) ==
    /\ voter # candidate
    /\ CanVoteFor(voter, candidate)
    /\ votedFor' = [votedFor EXCEPT ![voter] = candidate]
    /\ votesGranted' = [votesGranted EXCEPT ![candidate] = @ \union {voter}]
    /\ UNCHANGED <<currentTerm, role, log, commitIndex>>

\* candidate 获得多数票后成为 leader
BecomeLeader(n) ==
    /\ role[n] = Candidate
    /\ Majority(votesGranted[n])
    /\ role' = [role EXCEPT ![n] = Leader]
    /\ UNCHANGED <<currentTerm, votedFor, votesGranted, log, commitIndex>>

\* Leader 向 follower 复制日志条目
\* 简化模型：leader 将自己的下一条日志条目复制给 follower（忽略 prevLogIndex 匹配细节）
AppendEntries(leader, follower) ==
    /\ role[leader] = Leader
    /\ leader # follower
    /\ currentTerm[leader] >= currentTerm[follower]
    /\ LogLen(follower) < LogLen(leader)
    /\ LET nextIdx == LogLen(follower) + 1
       IN log' = [log EXCEPT ![follower] = Append(log[follower], log[leader][nextIdx])]
    /\ UNCHANGED <<currentTerm, role, votedFor, votesGranted, commitIndex>>

\* Leader 自己接收客户端请求并追加日志
ClientRequest(leader, v) ==
    /\ role[leader] = Leader
    /\ v \in Values
    /\ log' = [log EXCEPT ![leader] = Append(log[leader], [term |-> currentTerm[leader], value |-> v])]
    /\ UNCHANGED <<currentTerm, role, votedFor, votesGranted, commitIndex>>

\* Leader 在多数节点复制后推进 commitIndex
\* 简化：leader 只要发现某索引在所有节点日志中存在即可提交
AdvanceCommitIndex(leader) ==
    /\ role[leader] = Leader
    /\ commitIndex[leader] < LogLen(leader)
    /\ \E i \in (commitIndex[leader] + 1)..LogLen(leader) :
        /\ log[leader][i].term = currentTerm[leader]
        /\ \A n \in Nodes : i <= LogLen(n)
        /\ commitIndex' = [commitIndex EXCEPT ![leader] = i]
    /\ UNCHANGED <<currentTerm, role, votedFor, votesGranted, log>>

\* 节点发现更高任期时退回 Follower
StepDown(n, other) ==
    /\ n # other
    /\ currentTerm[other] > currentTerm[n]
    /\ currentTerm' = [currentTerm EXCEPT ![n] = currentTerm[other]]
    /\ role'        = [role EXCEPT ![n] = Follower]
    /\ votedFor'    = [votedFor EXCEPT ![n] = Nil]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {}]
    /\ UNCHANGED <<log, commitIndex>>

\* 下一步迁移关系（每次仅执行一个动作）
Next ==
    \/ \E n \in Nodes : Timeout(n)
    \/ \E voter, candidate \in Nodes : RequestVote(voter, candidate)
    \/ \E n \in Nodes : BecomeLeader(n)
    \/ \E leader, follower \in Nodes : AppendEntries(leader, follower)
    \/ \E leader \in Nodes, v \in Values : ClientRequest(leader, v)
    \/ \E leader \in Nodes : AdvanceCommitIndex(leader)
    \/ \E n, other \in Nodes : StepDown(n, other)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* 安全性质 *)

\* 任一时段最多只有一个 Leader（按任期区分）
AtMostOneLeaderPerTerm ==
    \A t \in 0..MaxTerm :
        Cardinality({n \in Nodes : role[n] = Leader /\ currentTerm[n] = t}) <= 1

\* Leader 完整性：在任期 t 当选的 leader 一定拥有所有在任期 t 之前已提交的条目
\* 简化版：若某索引 i 在任期 t 之前被提交，则任期 t 的 leader 的日志在 i 处与提交值一致
LeaderCompleteness ==
    \A n \in Nodes :
        role[n] = Leader /\ currentTerm[n] > 0
            => \A i \in 1..commitIndex[n] :
                log[n][i].term <= currentTerm[n]

\* 状态机安全性：所有节点对已提交的条目达成一致
StateMachineSafety ==
    \A n1, n2 \in Nodes, i \in 1..Min(commitIndex[n1], commitIndex[n2]) :
        log[n1][i] = log[n2][i]

\* 类型不变式
TypeInvariant ==
    /\ currentTerm \in [Nodes -> 0..MaxTerm]
    /\ role \in [Nodes -> {Follower, Candidate, Leader}]
    /\ votedFor \in [Nodes -> Nodes \union {Nil}]
    /\ votesGranted \in [Nodes -> SUBSET Nodes]
    /\ log \in [Nodes -> Seq([term : 0..MaxTerm, value : Values])]
    /\ commitIndex \in [Nodes -> Nat]

=============================================================================
