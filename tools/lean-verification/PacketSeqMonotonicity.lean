/-
SystemOSIOT Lean 4 网络协议形式化示例
目标：验证数据包序列号单调性与简单网络不变式。
内容：发送方状态机、FIFO 信道、序列号单调不变式。
参考：TCP / QUIC 报文序列号非递减性质。
-/ 

-- 数据包：携带单调递增的序列号
structure Packet where
  seq : Nat
  deriving Repr, BEq, Inhabited

-- 发送方状态：下一待发序号
structure SenderState where
  nextSeq : Nat
  deriving Repr, Inhabited

-- 网络状态：发送方 + FIFO 信道
structure NetworkState where
  sender  : SenderState
  channel : List Packet
  deriving Repr, Inhabited

-- 转移关系：发送方将当前序号的数据包放入信道，并将 nextSeq 加 1
inductive Step : NetworkState → NetworkState → Prop where
  | send (n : Nat) (s : SenderState) (ch : List Packet) :
      s.nextSeq = n →
      Step { sender := s, channel := ch }
           { sender := { nextSeq := n + 1 }, channel := ch ++ [⟨n⟩] }

-- 可达关系
inductive Reachable : NetworkState → NetworkState → Prop where
  | refl (s : NetworkState) : Reachable s s
  | trans (s1 s2 s3 : NetworkState) : Step s1 s2 → Reachable s2 s3 → Reachable s1 s3

-- 序列号列表非递减（归纳定义）
def nondecreasing : List Nat → Prop
  | []        => True
  | [_]       => True
  | x :: y :: xs => x ≤ y ∧ nondecreasing (y :: xs)

-- 从信道提取序列号列表
def seqs (ch : List Packet) : List Nat :=
  ch.map Packet.seq

-- 不变式：信道中所有已发数据包的序列号非递减
def SeqInvariant (st : NetworkState) : Prop :=
  nondecreasing (seqs st.channel)

-- 辅助引理：在末尾追加一个不小于原列表所有元素的数，保持非递减
theorem nondecreasing_snoc {xs : List Nat} {x : Nat}
    (h : nondecreasing xs)
    (hbound : ∀ y, y ∈ xs → y ≤ x) :
    nondecreasing (xs ++ [x]) := by
  induction xs with
  | nil => simp [nondecreasing]
  | cons y ys ih =>
      cases ys with
      | nil =>
          simp [nondecreasing]
          exact hbound y (by simp)
      | cons z zs =>
          simp [nondecreasing] at h ⊢
          cases h with
          | intro hle hnd =>
              constructor
              · exact hle
              · apply ih
                · exact hnd
                · intro w hw
                  apply hbound
                  simp [hw]

-- 更强的不变式：nextSeq 严格大于所有已发送报文的序列号
def StrongInvariant (st : NetworkState) : Prop :=
  SeqInvariant st ∧
  ∀ p, p ∈ st.channel → p.seq < st.sender.nextSeq

-- 强不变式在初始状态成立
theorem strong_invariant_initial :
    StrongInvariant { sender := ⟨0⟩, channel := [] } := by
  constructor
  · unfold SeqInvariant nondecreasing seqs
    simp
  · intro p hp
    simp at hp

-- 发送一步保持强不变式
theorem step_preserves_strong {s1 s2 : NetworkState}
    (hstep : Step s1 s2) (hinv : StrongInvariant s1) : StrongInvariant s2 := by
  cases hstep with
  | send n s ch hn =>
      cases hinv with
      | intro hseq hmax =>
          constructor
          · -- 保持 SeqInvariant
            unfold SeqInvariant at hseq ⊢
            simp [seqs]
            apply nondecreasing_snoc
            · exact hseq
            · intro y hy
              rw [List.mem_map] at hy
              cases hy with
              | intro p hp_eq =>
                  cases hp_eq with
                  | intro hp hyseq =>
                      have h_lt : p.seq < s.nextSeq := hmax p hp
                      rw [hyseq] at h_lt
                      rw [hn] at h_lt
                      exact Nat.le_of_lt h_lt
          · -- 保持 nextSeq 大于所有已发 seq
            intro p hp
            simp at hp
            cases hp with
            | inl hp_old =>
                have h_lt : p.seq < s.nextSeq := hmax p hp_old
                rw [hn] at h_lt
                simp at *
                omega
            | inr hp_new =>
                cases hp_new
                simp at *

-- 主定理：强不变式在任意可达状态成立
theorem strong_invariant_reachable {s0 s : NetworkState}
    (hreach : Reachable s0 s) (hinit : StrongInvariant s0) :
    StrongInvariant s := by
  induction hreach with
  | refl => exact hinit
  | trans s1 s2 s3 hstep _ ih =>
      exact ih (step_preserves_strong hstep hinit)

-- 推论：信道中序列号非递减
theorem seqs_nondecreasing_invariant {s0 s : NetworkState}
    (hreach : Reachable s0 s) (hinit : StrongInvariant s0) :
    SeqInvariant s := by
  have h := strong_invariant_reachable hreach hinit
  exact h.left

-- 本地验证命令
/-
cd tools/lean-verification
lean PacketSeqMonotonicity.lean
预期输出：无错误、无未闭合子目标。
-/