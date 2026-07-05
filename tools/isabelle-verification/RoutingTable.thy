(*
  SystemOSIOT Isabelle/HOL 网络协议形式化示例
  目标：验证简单距离向量路由表的单调性（metric 不恶化）。
  内容：路由表（目的地址 → metric）、更新操作、单调性定理。
  参考：RFC 1058 RIP 简化模型（metric 上限 16 视为不可达）。
*)

theory RoutingTable
  imports Main
begin

(* ---------- 基础定义 ---------- *)

type_synonym addr = string
type_synonym metric = nat

(* RIP 风格无穷大：metric 大于等于 16 视为不可达 *)
definition INF_RIP :: metric where
  "INF_RIP = 16"

(* 路由表：目的地址到 metric 的关联列表 *)
type_synonym routing_table = "(addr * metric) list"

(* 查询某目的地址的当前 metric；不存在则返回 INF_RIP *)
fun lookup :: "routing_table => addr => metric" where
  "lookup [] a = INF_RIP"
| "lookup ((d,m)#rest) a = (if d = a then m else lookup rest a)"

(* 单条路由更新：仅当新 metric 更小时才替换 *)
fun update_route :: "routing_table => addr => metric => routing_table" where
  "update_route [] a m = [(a, min m INF_RIP)]"
| "update_route ((d,md)#rest) a m =
     (if d = a then (d, min md m) # rest
      else (d,md) # update_route rest a m)"

(* 从邻居收到一组路由通告后批量更新 *)
fun update_table :: "routing_table => routing_table => routing_table" where
  "update_table t [] = t"
| "update_table t ((a,m)#rest) = update_table (update_route t a m) rest"

(* ---------- 单调性定义与定理 ---------- *)

(* 定义：路由表 t2 不比 t1 差，即对任意目的地址，t2 的 metric <= t1 的 metric *)
definition no_worse_than :: "routing_table => routing_table => bool" (infix "⊑" 60) where
  "t1 ⊑ t2 = (!a. lookup t2 a <= lookup t1 a)"

(* 引理 0：⊑ 关系具有传递性 *)
lemma monotonic_trans:
  assumes "t1 ⊑ t2" and "t2 ⊑ t3"
  shows "t1 ⊑ t3"
  using assms unfolding no_worse_than_def
  by (auto intro: order_trans)

(* 引理：单条路由更新后，被更新地址的 metric 不增大 *)
lemma update_route_no_worse_at:
  "lookup (update_route t a m) a <= lookup t a"
proof (induction t)
  case Nil
  then show ?case by (simp add: INF_RIP_def)
next
  case (Cons x t)
  then show ?case by (cases x) (auto simp add: min_def)
qed

(* 引理：单条路由更新后，其它地址的 metric 不变 *)
lemma update_route_unchanged:
  assumes "x ~= a"
  shows "lookup (update_route t a m) x = lookup t x"
  using assms by (induction t) auto

(* 定理 1：单条路由更新保持不恶化 *)
theorem update_route_monotonic:
  "t ⊑ update_route t a m"
proof (simp add: no_worse_than_def; intro allI)
  fix x
  show "lookup (update_route t a m) x <= lookup t x"
  proof (cases "x = a")
    case True
    then show ?thesis using update_route_no_worse_at by simp
  next
    case False
    then have "lookup (update_route t a m) x = lookup t x"
      using update_route_unchanged by blast
    then show ?thesis by simp
  qed
qed

(* 定理 2：批量更新保持不恶化 *)
theorem update_table_monotonic:
  "t ⊑ update_table t news"
proof (induction news arbitrary: t)
  case Nil
  then show ?case by (simp add: no_worse_than_def)
next
  case (Cons a_m news)
  obtain a m where am: "a_m = (a,m)" by fastforce
  have h1: "t ⊑ update_route t a m"
    by (rule update_route_monotonic)
  have h2: "update_route t a m ⊑ update_table (update_route t a m) news"
    using Cons by blast
  show ?case
    using am h1 h2 monotonic_trans by simp
qed

(* 定理 3：对任意目的地址，更新后的 metric 不大于原 metric *)
theorem lookup_update_nonincreasing:
  "lookup (update_table t news) a <= lookup t a"
  using update_table_monotonic unfolding no_worse_than_def by blast

end
