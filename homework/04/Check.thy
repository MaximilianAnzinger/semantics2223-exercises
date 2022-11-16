theory Check
  imports Submission
begin

theorem no_cycle: "(\<forall>a b. E a b \<longrightarrow> (f::'a \<Rightarrow> nat) a \<le> f b) \<Longrightarrow> (\<forall>w. E v w \<longrightarrow> f v < f w) \<Longrightarrow> \<not> (\<exists>xs. path E (v # xs @ [v]))"
  by (rule Submission.no_cycle)

theorem lval_upd_state_same: "x \<notin> vars_of a \<Longrightarrow> lval a (s(x := v)) = lval a s"
  by (rule Submission.lval_upd_state_same)

theorem lval_replace: "(x \<notin> vars_of a) \<Longrightarrow> (bounds_of a \<inter> vars_of e = {}) \<Longrightarrow> lval (replace e x a) (s(x := lval e s)) = lval a s"
  by (rule Submission.lval_replace)

lemma linearize_correct: "(\<forall>x. x \<in> vars_of e \<longrightarrow> CHR ''v'' \<notin> set x) \<Longrightarrow> (bounds_of e = {}) \<Longrightarrow> lval (linearize e) s = lval e s"
  by (rule Submission.linearize_correct)

end