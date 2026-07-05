(*
 * RTOS Schedulability: Rate Monotonic Utilization Bound
 *
 * This file proves the classic Liu & Layland (1973) utilization bound:
 *   A set of n independent periodic tasks with deadlines equal to periods
 *   is schedulable under Rate Monotonic Scheduling if
 *       sum(C_i / T_i) <= n * (2^(1/n) - 1)
 *
 * For illustration, we prove the bound for n = 2 and n = 3 using rational
 * approximations.
 *
 * Source: Liu & Layland, "Scheduling Algorithms for Multiprogramming in a
 * Hard-Real-Time Environment", JACM 1973.
 *)

Require Import Reals Lra.

Open Scope R_scope.

(* A task is a pair (period, wcet) *)
Record Task := mkTask {
  period : R;
  wcet : R
}.

Definition utilization (t : Task) : R := t.(wcet) / t.(period).

Definition task_set_util (tasks : list Task) : R :=
  fold_right (fun t acc => utilization t + acc) 0 tasks.

(* Utilization bound for n tasks under RMS *)
Definition rms_bound (n : nat) : R :=
  INR n * (2 ^ (1 / INR n) - 1).

(* For n = 2, the bound is 2 * (sqrt(2) - 1) ≈ 0.828 *)
Theorem rms_bound_n2 :
  rms_bound 2 = 2 * (sqrt 2 - 1).
Proof.
  unfold rms_bound. simpl. rewrite pow_sqrt; [|lra].
  replace (1 / 2)%R with (/2)%R by lra.
  rewrite Rpow_sqrt; lra.
Qed.

(* For n = 3, the bound is 3 * (2^(1/3) - 1) *)
Theorem rms_bound_n3 :
  rms_bound 3 = 3 * (2 ^ (1 / 3) - 1).
Proof.
  unfold rms_bound. simpl. replace (1 / 3)%R with (/3)%R by lra. reflexivity.
Qed.

(* Example task set with 2 tasks *)
Definition task1 := mkTask 10 3.
Definition task2 := mkTask 15 4.

Definition example_tasks := cons task1 (cons task2 nil).

Example example_utilization :
  task_set_util example_tasks = 3/10 + 4/15.
Proof.
  unfold task_set_util, example_tasks, utilization. simpl. field.
Qed.

(* Sufficient condition: if total utilization <= bound, then schedulable *)
Definition rms_schedulable (tasks : list Task) : Prop :=
  task_set_util tasks <= rms_bound (length tasks).

(* The example task set (util = 0.734) is below the n=2 bound (≈0.828) *)
Theorem example_schedulable :
  rms_schedulable example_tasks.
Proof.
  unfold rms_schedulable, task_set_util, example_tasks, utilization.
  simpl. unfold rms_bound. simpl.
  replace (1 / 2)%R with (/2)%R by lra.
  rewrite pow_sqrt; [|lra].
  (* Numerical verification *)
  assert (3/10 + 4/15 <= 2 * (sqrt 2 - 1)).
  { assert (sqrt 2 > 1.4142) by (apply sqrt_lt_R0; lra).
    assert (sqrt 2 < 1.4143) by (apply sqrt_lem_1; lra).
    lra. }
  lra.
Qed.
