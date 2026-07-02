/-
SystemOSIOT Lean 4 形式化示例
目标：展示依赖类型与程序语义基础，作为项目形式化工件的起点。
内容：简单算术表达式语言 + 大步操作语义 + 类型系统 + Progress/Preservation。
参考：Pierce, "Types and Programming Languages"; Avigad et al., "Theorem Proving in Lean 4".
-/

-- 算术表达式：自然数、加法、条件判断（零/非零）
inductive Expr where
  | num : Nat → Expr
  | add : Expr → Expr → Expr
  | ifz : Expr → Expr → Expr → Expr  -- ifz e then e1 else e2
  deriving Repr

-- 值：自然数
inductive Value where
  | vnum : Nat → Value
  deriving Repr

-- 大步操作语义：e ⇓ v
inductive BigStep : Expr → Value → Prop where
  | bs_num : BigStep (.num n) (.vnum n)
  | bs_add : BigStep e1 (.vnum n1) → BigStep e2 (.vnum n2)
           → BigStep (.add e1 e2) (.vnum (n1 + n2))
  | bs_ifz_zero : BigStep e (.vnum 0) → BigStep e1 v → BigStep (.ifz e e1 e2) v
  | bs_ifz_succ : BigStep e (.vnum (n + 1)) → BigStep e2 v → BigStep (.ifz e e1 e2) v

-- 类型：自然数类型
inductive Ty where
  | nat : Ty
  deriving Repr, BEq

-- 类型判断：⊢ e : T
inductive HasType : Expr → Ty → Prop where
  | ht_num : HasType (.num n) .nat
  | ht_add : HasType e1 .nat → HasType e2 .nat → HasType (.add e1 e2) .nat
  | ht_ifz : HasType e .nat → HasType e1 T → HasType e2 T
           → HasType (.ifz e e1 e2) T

-- 值的类型
inductive ValueHasType : Value → Ty → Prop where
  | vht_num : ValueHasType (.vnum n) .nat

-- Progress 定理：若 ⊢ e : T，则 e 可求值为某个值 v
theorem progress : HasType e T → ∃ v, BigStep e v := by
  intro h
  induction h with
  | ht_num =>
      rename_i n
      exists Value.vnum n
      constructor
  | ht_add _ _ ih1 ih2 =>
      rcases ih1 with ⟨v1, h1'⟩
      rcases ih2 with ⟨v2, h2'⟩
      cases v1 <;> cases v2
      case vnum.vnum n1 n2 =>
        exists Value.vnum (n1 + n2)
        apply BigStep.bs_add h1' h2'
  | ht_ifz _ _ _ ih ih1 ih2 =>
      rcases ih with ⟨v, h'⟩
      cases v with
      | vnum n =>
          cases n with
          | zero =>
              rcases ih1 with ⟨v1, h1'⟩
              exists v1
              apply BigStep.bs_ifz_zero h' h1'
          | succ _ =>
              rcases ih2 with ⟨v2, h2'⟩
              exists v2
              apply BigStep.bs_ifz_succ h' h2'

-- Preservation 定理：若 ⊢ e : T 且 e ⇓ v，则 v 具有类型 T
theorem preservation : HasType e T → BigStep e v → ValueHasType v T := by
  intro ht hbs
  induction hbs generalizing T with
  | bs_num =>
      cases ht
      constructor
  | bs_add h1 h2 ih1 ih2 =>
      cases ht with
      | ht_add ht1 ht2 =>
          have hv1 := ih1 ht1
          have hv2 := ih2 ht2
          cases hv1; cases hv2
          constructor
  | bs_ifz_zero h h1 ih ih1 =>
      cases ht with
      | ht_ifz ht ht1 _ =>
          have _ := ih ht
          exact ih1 ht1
  | bs_ifz_succ h h2 ih ih2 =>
      cases ht with
      | ht_ifz ht _ ht2 =>
          have _ := ih ht
          exact ih2 ht2

-- 类型安全：良类型表达式求值结果类型正确
theorem type_safety : HasType e T → BigStep e v → ValueHasType v T :=
  preservation
