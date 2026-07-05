theory OS_Scheduler
  imports Main
begin

(*
 * Operating System Scheduler Fairness in Isabelle/HOL
 *
 * Model: A ready queue containing tasks with priorities.
 * The scheduler always selects the task with the highest priority.
 * We prove that after scheduling, no ready task has higher priority
 * than the running task.
 *
 * Source: POSIX.1-2024 SCHED_FIFO, OSTEP Ch. 7~9
 *)

type_synonym tid = nat
type_synonym priority = nat

record task =
  tid :: tid
  priority :: priority

type_synonym ready_queue = "task list"

fun higher_priority :: "task \<Rightarrow> task \<Rightarrow> bool" where
"higher_priority t1 t2 = (priority t1 \<ge> priority t2)"

fun max_priority_task :: "ready_queue \<Rightarrow> task option" where
"max_priority_task [] = None" |
"max_priority_task [t] = Some t" |
"max_priority_task (t # ts) =
   (case max_priority_task ts of
      None \<Rightarrow> Some t
    | Some t' \<Rightarrow> if higher_priority t t' then Some t else Some t')"

fun remove_task :: "tid \<Rightarrow> ready_queue \<Rightarrow> ready_queue" where
"remove_task _ [] = []" |
"remove_task id (t # ts) =
   (if tid t = id then remove_task id ts else t # remove_task id ts)"

fun schedule :: "ready_queue \<Rightarrow> (task \<times> ready_queue) option" where
"schedule q =
   (case max_priority_task q of
      None \<Rightarrow> None
    | Some t \<Rightarrow> Some (t, remove_task (tid t) q))"

(* Invariant: scheduled task has priority \<ge> all remaining tasks *)
lemma max_priority_task_ge:
  "\<lbrakk> max_priority_task q = Some t; t' \<in> set q \<rbrakk> \<Longrightarrow> priority t \<ge> priority t'"
  apply (induction q arbitrary: t t')
   apply auto
  apply (case_tac "max_priority_task q")
   apply auto
  done

lemma remove_task_subset:
  "set (remove_task id q) \<subseteq> set q"
  by (induction q) auto

theorem schedule_highest_priority:
  assumes "schedule q = Some (t, q')"
      and "t' \<in> set q'"
    shows "priority t \<ge> priority t'"
proof -
  from assms have "max_priority_task q = Some t" by (auto split: option.splits)
  moreover from assms remove_task_subset have "t' \<in> set q" by auto
  ultimately show ?thesis using max_priority_task_ge by blast
qed

end
