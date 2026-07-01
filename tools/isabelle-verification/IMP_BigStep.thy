(*
  SystemOSIOT Isabelle/HOL 形式化示例
  目标：展示高阶逻辑证明助手在命令式语言语义中的应用。
  内容：IMP 语言（算术表达式、布尔表达式、命令）+ 大步操作语义 + 确定性证明。
  参考：Nipkow & Klein, "Concrete Semantics: With Isabelle/HOL".
*)

theory IMP_BigStep
  imports Main
begin

(* ---------- 算术表达式 ---------- *)

datatype aexp = N int | V string | Plus aexp aexp

fun aval :: "aexp => (string => int) => int" where
  "aval (N n) s = n"
| "aval (V x) s = s x"
| "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(* ---------- 布尔表达式 ---------- *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp => (string => int) => bool" where
  "bval (Bc v) s = v"
| "bval (Not b) s = (\<not> bval b s)"
| "bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"
| "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

(* ---------- 命令式语言 IMP ---------- *)

datatype com = SKIP
  | Assign string aexp
  | Seq com com
  | If bexp com com
  | While bexp com

(* 大步操作语义： (c, s) => s' *)
inductive big_step :: "com => (string => int) => (string => int) => bool"
  ("(_/ \<Rightarrow> _)" [60,0,60] 55) where
Skip:    "(SKIP, s) \<Rightarrow> s" |
Assign:  "(Assign x a, s) \<Rightarrow> s(x := aval a s)" |
Seq:     "\<lbrakk> (c1, s1) \<Rightarrow> s2; (c2, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (Seq c1 c2, s1) \<Rightarrow> s3" |
IfTrue:  "\<lbrakk> bval b s; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (If b c1 c2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not> bval b s; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (If b c1 c2, s) \<Rightarrow> t" |
WhileFalse: "\<not> bval b s \<Longrightarrow> (While b c, s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s1; (c, s1) \<Rightarrow> s2; (While b c, s2) \<Rightarrow> s3 \<rbrakk>
               \<Longrightarrow> (While b c, s1) \<Rightarrow> s3"

(* 语义确定性：若 (c, s) => t1 且 (c, s) => t2，则 t1 = t2 *)
theorem big_step_deterministic:
  "\<lbrakk> (c, s) \<Rightarrow> t; (c, s) \<Rightarrow> t' \<rbrakk> \<Longrightarrow> t = t'"
proof (induction arbitrary: t' rule: big_step.induct)
  case Skip
  then show ?case by auto
next
  case Assign
  then show ?case by auto
next
  case (Seq c1 s1 s2 c2 s3 t')
  then show ?case by auto
next
  case (IfTrue b s c1 t c2 t')
  then show ?case by auto
next
  case (IfFalse b s c2 t c1 t')
  then show ?case by auto
next
  case (WhileFalse b s c t')
  then show ?case by auto
next
  case (WhileTrue b s1 c s2 w s3 t')
  then show ?case by auto
qed

end
