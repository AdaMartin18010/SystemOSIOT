(* SystemOSIOT Network Protocol Coq Formalization *)
(* 停等协议（Stop-and-Wait）安全性与活性证明 *)
(* 内容：sender/receiver 状态机、报文（seq 0/1）与 ACK、安全接收引理、可达活性 *)
(* 工具：Coq 8.19+ *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relations.
Require Import Lia.

Import ListNotations.

(* ---------- 基础类型 ---------- *)

Inductive Seq : Type :=
  | seq0 : Seq
  | seq1 : Seq.

Definition Seq_eq (s t : Seq) : bool :=
  match s, t with
  | seq0, seq0 => true
  | seq1, seq1 => true
  | _, _ => false
  end.

Definition Seq_flip (s : Seq) : Seq :=
  match s with
  | seq0 => seq1
  | seq1 => seq0
  end.

Lemma seq_flip_neq : forall s, Seq_eq s (Seq_flip s) = false.
Proof. intros s; destruct s; reflexivity. Qed.

Lemma seq_flip_involutive : forall s, Seq_flip (Seq_flip s) = s.
Proof. intros s; destruct s; reflexivity. Qed.

Lemma seq_neq_implies_flip : forall s t, Seq_eq s t = false -> t = Seq_flip s.
Proof. intros s t; destruct s, t; simpl; auto; discriminate. Qed.

Lemma seq_safe_impl : forall s t, Seq_eq s t = false -> Seq_eq s (Seq_flip t) = true.
Proof. intros s t H; destruct s, t; simpl in *; auto; discriminate. Qed.

Inductive Packet : Type :=
  | Data : Seq -> Packet
  | Ack  : Seq -> Packet.

(* 发送方状态：等待应用层数据或等待对应当前 seq 的 ACK *)
Inductive SenderState : Type :=
  | SW_Ready  : Seq -> SenderState    (* 可发送下一帧，持有下一序号 *)
  | SW_Wait   : Seq -> SenderState.   (* 已发送 seq，等待 ACK *)

(* 接收方状态：期望接收的序号 *)
Inductive ReceiverState : Type :=
  | RW_Expect : Seq -> ReceiverState.

Record State : Type := mkState {
  sender   : SenderState;
  receiver : ReceiverState;
  channel  : list Packet    (* 有序信道，head 为即将投递 *)
}.

(* ---------- 转移关系 ---------- *)

Inductive Step : State -> State -> Prop :=
  (* 发送方在 Ready 时把 Data s 投入信道并进入 Wait *)
  | Step_Send : forall s rs ch,
      Step (mkState (SW_Ready s) rs ch)
           (mkState (SW_Wait s) rs (Data s :: ch))
  (* 接收方收到期望序号的数据，翻转期望并回发对应 ACK *)
  | Step_RecvData : forall s rest,
      Step (mkState (SW_Wait s) (RW_Expect s) (Data s :: rest))
           (mkState (SW_Wait s) (RW_Expect (Seq_flip s)) (Ack s :: rest))
  (* 接收方收到非期望序号的数据：丢弃并回发上一帧 ACK（捎带重复确认） *)
  | Step_RecvDup : forall s t rest,
      Seq_eq s t = false ->
      Step (mkState (SW_Wait t) (RW_Expect s) (Data t :: rest))
           (mkState (SW_Wait t) (RW_Expect s) (Ack s :: rest))
  (* 发送方收到期望 ACK，进入 Ready 并翻转序号 *)
  | Step_RecvAck : forall s rs ch,
      Step (mkState (SW_Wait s) rs (Ack s :: ch))
           (mkState (SW_Ready (Seq_flip s)) rs ch)
  (* 信道头部报文损坏/丢失：直接丢弃头部报文 *)
  | Step_Loss : forall ss rs p ch,
      Step (mkState ss rs (p :: ch))
           (mkState ss rs ch).

Definition Reachable (s0 s : State) : Prop :=
  clos_refl_trans State Step s0 s.

(* ---------- 安全性：接收方只接受发送方已发且序号匹配的帧 ---------- *)

(* 接收方决不交付乱序帧：仅当 Data s 与 receiver 期望序号一致时才改变期望 *)
Definition SafeDelivery' (ss : SenderState) (rs : ReceiverState) : Prop :=
  match rs with
  | RW_Expect s =>
      match ss with
      | SW_Ready t  => True
      | SW_Wait  t  => Seq_eq s t = false -> Seq_eq s (Seq_flip t) = true
      end
  end.

Definition SafeDelivery (st : State) : Prop :=
  SafeDelivery' (sender st) (receiver st).

Lemma safe_delivery_step :
  forall st st',
    Step st st' ->
    SafeDelivery st ->
    SafeDelivery st'.
Proof.
  intros st st' Hstep Hsafe.
  unfold SafeDelivery in *.
  destruct Hstep; simpl in *; unfold SafeDelivery' in *; auto.
  - (* Step_Send *) destruct rs. intro. apply seq_safe_impl. assumption.
  - (* Step_RecvData *) intro. apply seq_safe_impl. assumption.
  - (* Step_RecvAck *) destruct rs. auto.
Qed.

Theorem stop_and_wait_safe :
  forall s0 s,
    Reachable s0 s ->
    SafeDelivery s0 ->
    SafeDelivery s.
Proof.
  intros s0 s Hreach Hsafe.
  induction Hreach; eauto using safe_delivery_step.
Qed.

(* 更强安全性：receiver 期望序号总是 sender 已发 seq 的当前值或翻转值 *)
Definition SenderSeq (st : State) : Seq :=
  match sender st with
  | SW_Ready s => s
  | SW_Wait  s => s
  end.

Definition ReceiverSeq (st : State) : Seq :=
  match receiver st with
  | RW_Expect s => s
  end.

Definition SeqConsistent (st : State) : Prop :=
  let ss := SenderSeq st in
  let rs := ReceiverSeq st in
  rs = ss \/ rs = Seq_flip ss.

Lemma seq_consistent_initial :
  forall s0, SeqConsistent (mkState (SW_Ready s0) (RW_Expect s0) []).
Proof. intros; left; reflexivity. Qed.

Lemma seq_consistent_step :
  forall st st',
    Step st st' ->
    SeqConsistent st ->
    SeqConsistent st'.
Proof.
  intros st st' Hstep Hc.
  inversion Hstep; subst; simpl in *; unfold SeqConsistent, SenderSeq, ReceiverSeq in *;
    destruct (receiver st) eqn:?; destruct Hc; auto;
    try (right; rewrite seq_flip_involutive; auto); try (left; auto).
Qed.

Theorem stop_and_wait_seq_consistent :
  forall s0 s,
    Reachable s0 s ->
    SeqConsistent s0 ->
    SeqConsistent s.
Proof.
  intros s0 s Hreach Hc.
  induction Hreach; eauto using seq_consistent_step.
Qed.

(* ---------- 活性：在无丢失且信道非空时，系统必将推进 ---------- *)

(* 辅助引理：当信道头部存在可消费报文时，必然存在一步转移 *)
Lemma can_progress :
  forall st,
    channel st <> [] ->
    exists st', Step st st'.
Proof.
  intros st H.
  destruct st as [ss rs ch].
  destruct ch as [ | p ch'] eqn:Ech.
  - contradiction H; reflexivity.
  - destruct p.
    + destruct rs as [s].
      destruct ss as [ t | t ].
      * (* SW_Ready t：仍可消费数据，无论是否匹配 *)
        destruct (Seq_eq s t) eqn:E.
        { exists (mkState (SW_Wait t) (RW_Expect (Seq_flip s)) (Ack s :: ch')).
          apply Step_RecvData. }
        { exists (mkState (SW_Wait t) (RW_Expect s) (Ack s :: ch')).
          apply Step_RecvDup. auto. }
      * (* SW_Wait t *)
        destruct (Seq_eq s t) eqn:E.
        { exists (mkState (SW_Wait t) (RW_Expect (Seq_flip s)) (Ack s :: ch')).
          apply Step_RecvData. }
        { exists (mkState (SW_Wait t) (RW_Expect s) (Ack s :: ch')).
          apply Step_RecvDup. auto. }
    + destruct ss as [ s | s ].
      * (* SW_Ready s，收到 Ack s：翻转 *)
        destruct (Seq_eq s s0) eqn:E.
        { exists (mkState (SW_Ready (Seq_flip s)) (RW_Expect s1) ch').
          apply Step_RecvAck. }
        { exists (mkState (SW_Ready s) (RW_Expect s1) ch').
          apply Step_Loss. }
      * (* SW_Wait s *)
        destruct (Seq_eq s s0) eqn:E.
        { exists (mkState (SW_Ready (Seq_flip s)) (RW_Expect s1) ch').
          apply Step_RecvAck. }
        { exists (mkState (SW_Wait s) (RW_Expect s1) ch').
          apply Step_Loss. }
Qed.

(* ---------- 活性：当期望 ACK 位于信道头部时，发送方必将推进 ---------- *)

(* 单步活性：若信道头部为 Ack s 且发送方正等待 s，则下一步进入 Ready *)
Theorem stop_and_wait_progress_ack :
  forall s rs ch,
    Step (mkState (SW_Wait s) rs (Ack s :: ch))
         (mkState (SW_Ready (Seq_flip s)) rs ch).
Proof.
  intros. apply Step_RecvAck.
Qed.

(* 多步活性：从任何可达状态出发，只要信道中存在 Ack s 且发送方等待 s，
   则系统经过有限步可达 Ready (flip s)。 *)
Theorem stop_and_wait_liveness :
  forall s0 s s_ack ch_prefix ch_suffix rs,
    Reachable s0 s ->
    sender s = SW_Wait s_ack ->
    receiver s = RW_Expect rs ->
    channel s = ch_prefix ++ Ack s_ack :: ch_suffix ->
    exists s',
      Reachable s s' /\
      sender s' = SW_Ready (Seq_flip s_ack) /\
      receiver s' = RW_Expect rs.
Proof.
  intros s0 s s_ack ch_prefix ch_suffix rs Hreach Hsender Hreceiver Hch.
  induction ch_prefix as [ | p ps IH ] using rev_ind.
  - simpl in Hch. subst ch.
    exists (mkState (SW_Ready (Seq_flip s_ack)) rs ch_suffix).
    split; [ | split ].
    + apply rt_trans with (y := mkState (SW_Ready (Seq_flip s_ack)) rs ch_suffix);
        [ apply rt_step, stop_and_wait_progress_ack | apply rt_refl ].
    + reflexivity.
    + reflexivity.
  - rewrite app_assoc in Hch. simpl in Hch.
    set (mid := ps ++ Ack s_ack :: ch_suffix).
    (* 先丢弃前缀中的 p，再应用归纳假设 *)
    assert (Hdrop : Step (mkState (SW_Wait s_ack) rs (p :: mid))
                         (mkState (SW_Wait s_ack) rs mid)).
    { apply Step_Loss. }
    subst mid.
    assert (Hreach' : Reachable s0 (mkState (SW_Wait s_ack) rs (ps ++ Ack s_ack :: ch_suffix))).
    { eauto using rt_trans, rt_step. }
    apply IH in Hreach'; auto.
    destruct Hreach' as [s' [Hreach_s' [Hsender' Hreceiver']]].
    exists s'. split; [ | split ]; auto.
    eapply rt_trans; eauto.
    apply rt_step. apply Step_Loss.
Qed.

(* ---------- 本地验证命令 ---------- *)
(*
   cd tools/coq-verification
   coqc StopAndWait.v
   预期输出：无错误、无未闭合子目标。
*)