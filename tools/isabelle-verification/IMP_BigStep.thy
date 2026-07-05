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
inductive big_step :: "com * (string => int) => (string => int) => bool"
  ("(_/ \<Rightarrow> _)" [60,60] 55) where
Skip:    "(SKIP, s) \<Rightarrow> s" |
Assign:  "(Assign x a, s) \<Rightarrow> s(x := aval a s)" |
Seq:     "\<lbrakk> (c1, s1) \<Rightarrow> s2; (c2, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (Seq c1 c2, s1) \<Rightarrow> s3" |
IfTrue:  "\<lbrakk> bval b s; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (If b c1 c2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not> bval b s; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (If b c1 c2, s) \<Rightarrow> t" |
WhileFalse: "\<not> bval b s \<Longrightarrow> (While b c, s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s1; (c, s1) \<Rightarrow> s2; (While b c, s2) \<Rightarrow> s3 \<rbrakk>
               \<Longrightarrow> (While b c, s1) \<Rightarrow> s3"

(* 大步语义的反演引理，用于确定性证明 *)
lemma Skip_inversion[dest]: "(SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
  by (cases rule: big_step.cases) auto

lemma Assign_inversion[dest]: "(Assign x a, s) \<Rightarrow> t \<Longrightarrow> t = s(x := aval a s)"
  by (cases rule: big_step.cases) auto

lemma Seq_inversion[dest]:
  "(Seq c1 c2, s) \<Rightarrow> t \<Longrightarrow> \<exists>s'. (c1, s) \<Rightarrow> s' \<and> (c2, s') \<Rightarrow> t"
  by (cases rule: big_step.cases) auto

lemma If_inversion[dest]:
  "(If b c1 c2, s) \<Rightarrow> t \<Longrightarrow> (bval b s \<longrightarrow> (c1, s) \<Rightarrow> t) \<and> (\<not> bval b s \<longrightarrow> (c2, s) \<Rightarrow> t)"
  by (cases rule: big_step.cases) auto

lemma WhileFalse_inversion[dest]:
  "\<not> bval b s \<Longrightarrow> (While b c, s) \<Rightarrow> t \<Longrightarrow> t = s"
  by (cases rule: big_step.cases) auto

lemma WhileTrue_inversion[dest]:
  "bval b s \<Longrightarrow> (While b c, s) \<Rightarrow> t \<Longrightarrow> \<exists>s'. (c, s) \<Rightarrow> s' \<and> (While b c, s') \<Rightarrow> t"
  by (cases rule: big_step.cases) auto

(* 语义确定性：若 (c, s) => t1 且 (c, s) => t2，则 t1 = t2 *)
theorem big_step_deterministic:
  "\<lbrakk> (c, s) \<Rightarrow> t; (c, s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
proof (induction arbitrary: u rule: big_step.induct)
  fix s u
  assume a2: "(SKIP, s) \<Rightarrow> u"
  from a2 show "u = s" by (rule Skip_inversion)
next
  fix x a s u
  assume a2: "(Assign x a, s) \<Rightarrow> u"
  from a2 show "u = s(x := aval a s)" by (rule Assign_inversion)
next
  fix c1 s1 s2 c2 s3 u
  assume ih1: "\<And>u. (c1, s1) \<Rightarrow> u \<Longrightarrow> u = s2"
    and ih2: "\<And>u. (c2, s2) \<Rightarrow> u \<Longrightarrow> u = s3"
    and a:  "(Seq c1 c2, s1) \<Rightarrow> u"
  from a obtain s2' where s1_s2': "(c1, s1) \<Rightarrow> s2'" and s2'_u: "(c2, s2') \<Rightarrow> u"
    by (auto dest: Seq_inversion)
  from ih1[OF s1_s2'] have "s2' = s2" by simp
  with s2'_u have "(c2, s2) \<Rightarrow> u" by simp
  from ih2[OF this] show "u = s3" by simp
next
  fix b s c1 t c2 u
  assume b_true: "bval b s"
    and ih: "\<And>u. (c1, s) \<Rightarrow> u \<Longrightarrow> u = t"
    and a: "(If b c1 c2, s) \<Rightarrow> u"
  from a b_true have "(c1, s) \<Rightarrow> u" by (auto dest: If_inversion)
  from ih[OF this] show "u = t" by simp
next
  fix b s c1 c2 t u
  assume b_false: "\<not> bval b s"
    and ih: "\<And>u. (c2, s) \<Rightarrow> u \<Longrightarrow> u = t"
    and a: "(If b c1 c2, s) \<Rightarrow> u"
  from a b_false have "(c2, s) \<Rightarrow> u" by (auto dest: If_inversion)
  from ih[OF this] show "u = t" by simp
next
  fix b s c u
  assume b_false: "\<not> bval b s"
    and a: "(While b c, s) \<Rightarrow> u"
  from b_false a show "u = s" by (auto dest: WhileFalse_inversion)
next
  fix b s1 c s2 s3 u
  assume b_true: "bval b s1"
    and ih1: "\<And>u. (c, s1) \<Rightarrow> u \<Longrightarrow> u = s2"
    and ih2: "\<And>u. (While b c, s2) \<Rightarrow> u \<Longrightarrow> u = s3"
    and a: "(While b c, s1) \<Rightarrow> u"
  from b_true a obtain s2' where c_s1_s2': "(c, s1) \<Rightarrow> s2'" and while_s2'_u: "(While b c, s2') \<Rightarrow> u"
    by (auto dest: WhileTrue_inversion)
  from ih1[OF c_s1_s2'] have "s2' = s2" by simp
  with while_s2'_u have "(While b c, s2) \<Rightarrow> u" by simp
  from ih2[OF this] show "u = s3" by simp
qed

end
