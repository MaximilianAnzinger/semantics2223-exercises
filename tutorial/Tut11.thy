theory Tut11
  imports "HOL-IMP.Complete_Lattice"
begin

instantiation list :: (order) order
begin

definition less_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "(xs:: 'a list) \<le> ys = (length xs = length ys \<and> (\<forall>i. i < length xs \<longrightarrow> xs ! i \<le> ys ! i))"

definition less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "(xs:: 'a list) < ys = (xs \<le> ys \<and> \<not> ys \<le> xs)"

instance
proof (standard, goal_cases)
  case (1 x y)
  then show ?case unfolding less_list_def ..
next
  case (2 x)
  then show ?case unfolding less_eq_list_def by simp
next
  case (3 x y z)
  then show ?case unfolding less_eq_list_def by fastforce
next
  case (4 x y)
  hence "\<forall>i < length x. x ! i = y ! i"
    using less_eq_list_def by fastforce
  with 4 show ?case unfolding less_eq_list_def by(auto intro: nth_equalityI)
qed

end

unbundle lattice_syntax

definition Inf_list :: "nat \<Rightarrow> ('a::complete_lattice) list set \<Rightarrow> 'a list"  where
  "Inf_list n S = map (\<lambda>i. \<Sqinter> ((\<lambda>xs. xs ! i) ` S)) [0..<n]"

interpretation
  Complete_Lattice "{xs. length xs = n}" "Inf_list n" for n
proof (standard, goal_cases)
  case (1 A a)
  then show ?case unfolding less_eq_list_def Inf_list_def by (auto intro: Inf_lower)
next
  case (2 b A)
  then show ?case unfolding less_eq_list_def Inf_list_def by (auto intro: Inf_greatest)
next
  case (3 A)
  then show ?case unfolding Inf_list_def by auto
qed

lemma 
    fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  assumes "x\<^sub>0 \<le> f x\<^sub>0"
  shows "\<Squnion> {(f^^i) x\<^sub>0 |i. i\<in>\<nat>} \<le> \<Squnion> {(f^^(i+1)) x\<^sub>0 | i. i\<in>\<nat>}"
proof (rule Sup_least)
  fix x assume "x \<in> {(f ^^ i) x\<^sub>0 |i. i \<in> \<nat>}"
  then obtain i where "x = (f ^^ i) x\<^sub>0" by blast
  show "x \<le> \<Squnion> {(f ^^ (i + 1)) x\<^sub>0 |i. i \<in> \<nat>}"
  proof (cases i)
    case 0
    have "x = x\<^sub>0" by (simp add: "0" \<open>x = (f ^^ i) x\<^sub>0\<close>)
    with assms have "x \<le> f x\<^sub>0" by simp
    also have "... \<le> \<Squnion> {(f ^^ (i + 1)) x\<^sub>0 |i. i \<in> \<nat>}"
    proof (rule Sup_upper)
      have "x\<^sub>0 = (f ^^ i) x\<^sub>0" using \<open>x = x\<^sub>0\<close> \<open>x = (f ^^ i) x\<^sub>0\<close> by simp
      then show "f x\<^sub>0 \<in> {(f ^^ (i + 1)) x\<^sub>0 |i. i \<in> \<nat>}" unfolding Nats_def apply auto by metis
    qed
    then show ?thesis using calculation by auto
  next
    case (Suc n)
    show ?thesis
    proof (intro Sup_upper)
      show "x \<in> {(f ^^ (i + 1)) x\<^sub>0 |i. i \<in> \<nat>}"
        unfolding Nats_def
        using Suc \<open>x = (f ^^ i) x\<^sub>0\<close> by fastforce
    qed
  qed
qed

end