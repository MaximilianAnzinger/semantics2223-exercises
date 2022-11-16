theory Submission
  imports Defs
begin

inductive path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" for E where
  empty: "path E []" |
  cont: "E a x \<Longrightarrow> path E (x#xs) \<Longrightarrow> path E (a#x#xs)"

lemma path_reverse: "path E (a#x#xs) \<Longrightarrow> (E a x \<and> path E (x#xs))"
  using Submission.path.cases by blast

lemma mono_path[simp]:
  assumes mono: "\<forall>a b. E a b \<longrightarrow> (f::'a \<Rightarrow> nat) a \<le> f b"
    and "path E (s # xs @ [t])"
  shows "f s \<le> f t"
  using assms proof(induction xs arbitrary: s t)
  case Nil
  then show ?case using path_reverse by fastforce
next
  case (Cons a xs)
  then have "E s a" using path_reverse
    by force
  then have "f s \<le> f a"
    using mono by blast
  moreover
  from Cons.prems Cons.IH have "f a \<le> f t" using path_reverse
    by force
  ultimately
  have "f s \<le> f t"
    using le_trans by blast
  thus ?case .
qed

theorem no_cycle:
  assumes mono: "\<forall>a b. E a b \<longrightarrow> (f::'a \<Rightarrow> nat) a \<le> f b"
      and fv_less: "\<forall>w. E v w \<longrightarrow> f v < f w"
  shows "\<not> (\<exists>xs. path E (v # xs @ [v]))"
proof
  assume path_ex:"\<exists>xs. path E (v # xs @ [v])"
  then obtain xs where p: "path E (v # xs @ [v])"
    by blast
  with fv_less have not_nil: "xs \<noteq> Nil" using path_reverse
    by fastforce
  then have "\<exists>x xs'. xs = x#xs'"
    using neq_Nil_conv by fastforce
  then obtain x xs' where split_xs: "xs = x#xs'"
    by blast
  from fv_less have "\<forall>x \<in> set xs. E v x \<longrightarrow> f v < f x" 
    by blast
  with split_xs have "f v < f x"
    using p path_reverse by fastforce
  moreover
  from p have "path E (x # xs' @ [v])" using path_reverse split_xs
    by fastforce
  with mono have "f x \<le> f v" using mono_path
    by simp
  ultimately
  show False
    by linarith
qed

value "lval (Let ''x'' (N 5) (Let ''y'' (V ''x'') (Plus (V ''x'') (Plus (V ''y'') (V ''x''))))) <> = 15"

paragraph \<open>Step 1\<close>

fun replace :: "lexp \<Rightarrow> vname \<Rightarrow> lexp \<Rightarrow> lexp" where
"replace e x (Let u a b) = Let u (replace e x a) (replace e x b)"
| "replace _ = undefined"
| "replace e x a = a"

paragraph \<open>Step 2\<close>

theorem lval_upd_state_same:
  "x \<notin> vars_of a \<Longrightarrow> lval a (s(x := v)) = lval a s"
  sorry

paragraph \<open>Step 3\<close>

theorem lval_replace:
  assumes "x \<notin> vars_of a"
      and "bounds_of a \<inter> vars_of e = {}"
  shows "lval (replace e x a) (s(x := lval e s)) = lval a s"
  sorry

paragraph \<open>Step 4\<close>

definition linearize :: "lexp \<Rightarrow> lexp" where
 "linearize e = (let
     exps = undefined;
     names = undefined;
     m = zip exps names
   in fold (\<lambda>(a, x) e. Let x a (replace a x e)) m e)"

value "linearize (Plus (Plus (Plus (V ''a'') (N 3)) (N 4)) (Plus (V ''a'') (N 3)))
= Let ''v'' (Plus (V ''a'') (N 3)) (Plus (Plus (V ''v'') (N 4)) (V ''v''))"

value "linearize (Plus (Plus (Plus (V ''a'') (N 3)) (N 4)) (Plus (Plus (V ''a'') (N 3)) (N 4)))
= Let ''v'' (Plus (V ''a'') (N 3)) (Let ''vv'' (Plus (V ''v'') (N 4)) (Plus (V ''vv'') (V ''vv'')))"

paragraph \<open>(Bonus) Step 5\<close>

lemma linearize_correct:
  assumes "\<forall>x. x \<in> vars_of e \<longrightarrow> CHR ''v'' \<notin> set x"
      and "bounds_of e = {}"
  shows "lval (linearize e) s = lval e s"
  sorry

end