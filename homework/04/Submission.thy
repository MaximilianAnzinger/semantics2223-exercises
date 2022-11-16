theory Submission
  imports Defs
begin

inductive path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" for E 

theorem no_cycle:
  assumes "\<forall>a b. E a b \<longrightarrow> (f::'a \<Rightarrow> nat) a \<le> f b"
      and "\<forall>w. E v w \<longrightarrow> f v < f w"
  shows "\<not> (\<exists>xs. path E (v # xs @ [v]))"
  sorry

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