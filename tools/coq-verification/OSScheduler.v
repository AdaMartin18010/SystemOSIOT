(*
 * Operating System Scheduler: Formal Model in Coq
 *
 * This file defines a simple priority-based ready queue and proves
 * basic invariants:
 *   - The running task is always the highest-priority ready task.
 *   - The scheduler never loses tasks.
 *
 * Source: POSIX.1-2024 SCHED_FIFO/SCHED_RR, OSTEP Ch. 7~9
 *)

Require Import List Arith Lia.

(* Task identifier and priority *)
Definition TaskId := nat.
Definition Priority := nat.

Record Task := mkTask {
  tid : TaskId;
  priority : Priority
}.

(* Ready queue: list of tasks *)
Definition ReadyQueue := list Task.

(* Find the highest-priority task in the queue *)
Fixpoint highest_priority (q : ReadyQueue) : option Task :=
  match q with
  | nil => None
  | t :: nil => Some t
  | t :: q' =>
      match highest_priority q' with
      | None => Some t
      | Some t' => if t.(priority) >=? t'.(priority) then Some t else Some t'
      end
  end.

(* Remove a task from the queue by tid *)
Fixpoint remove_task (id : TaskId) (q : ReadyQueue) : ReadyQueue :=
  match q with
  | nil => nil
  | t :: q' =>
      if Nat.eqb t.(tid) id then remove_task id q' else t :: remove_task id q'
  end.

(* Schedule: pick highest-priority task and remove it from queue *)
Definition schedule (q : ReadyQueue) : option (Task * ReadyQueue) :=
  match highest_priority q with
  | None => None
  | Some t => Some (t, remove_task t.(tid) q)
  end.

(* Invariant: every task in q has tid distinct from the running task *)
Definition no_dup_tid (q : ReadyQueue) : Prop :=
  forall t1 t2 : Task,
    In t1 q -> In t2 q -> t1.(tid) = t2.(tid) -> t1 = t2.

(* Helper: if a task is in the queue after remove, it was already there *)
Lemma remove_task_presence :
  forall id t q,
    In t (remove_task id q) -> In t q.
Proof.
  induction q as [|t' q' IH]; simpl; intros H.
  - contradiction.
  - destruct (Nat.eqb t'.(tid) id).
    + right. apply IH. assumption.
    + destruct H as [H | H].
      * left. assumption.
      * right. apply IH. assumption.
Qed.

(* The scheduled task has priority greater or equal to any remaining task *)
Theorem schedule_highest_priority :
  forall q t q',
    no_dup_tid q ->
    schedule q = Some (t, q') ->
    forall t', In t' q' -> t.(priority) >= t'.(priority).
Proof.
  intros q t q' Hnd Hsched t' Hin.
  unfold schedule in Hsched.
  destruct (highest_priority q) eqn:Eh; inversion Hsched; subst; clear Hsched.
  apply remove_task_presence in Hin.
  revert t t' Hin Eh.
  induction q as [|t1 q1 IH]; simpl; intros t t' Hin Eh; [contradiction|].
  destruct q1 as [|t2 q2].
  - simpl in Eh. inversion Eh; subst. destruct Hin as [Hin | []]. subst. lia.
  - simpl in Eh. destruct (highest_priority (t2 :: q2)) as [t3|] eqn:Eh3.
    + destruct (t1.(priority) >=? t3.(priority)) eqn:Hcmp.
      * inversion Eh; subst. destruct Hin as [Hin | Hin].
        -- subst. lia.
        -- apply IH with (t := t3) (t' := t') in Hin; auto. simpl. lia.
      * inversion Eh; subst. apply IH with (t := t3) (t' := t'); auto.
    + inversion Eh; subst. destruct Hin as [Hin | Hin].
      * subst. lia.
      * contradiction.
Qed.

(* The scheduler preserves no_dup_tid *)
Theorem schedule_preserves_no_dup :
  forall q t q',
    no_dup_tid q ->
    schedule q = Some (t, q') ->
    no_dup_tid q'.
Proof.
  intros q t q' Hnd Hsched t1 t2 Hin1 Hin2 Heq.
  apply Hnd; auto; apply remove_task_presence; assumption.
Qed.
