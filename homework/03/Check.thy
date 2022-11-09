theory Check
  imports Submission
begin

theorem G_is_replicate: "(w \<in> G) \<Longrightarrow> \<exists>n. w = replicate n a @ replicate n b"
  by (rule Submission.G_is_replicate)

theorem replicate_G: "(w = replicate n a @ replicate n b) \<Longrightarrow> w \<in> G"
  by (rule Submission.replicate_G)

theorem execs_append: "\<And>s. execs (xs @ ys) s = execs ys (execs xs s)"
  by (rule Submission.execs_append)

theorem val_maxvar_same: "\<forall>n \<le> maxvar e. s n = s' n \<Longrightarrow> val e s = val e s'"
  by (rule Submission.val_maxvar_same)

theorem compiler_correct: "execs (cmp e (maxvar e + 1)) s 0 = val e (s o Suc)"
  by (rule Submission.compiler_correct)

end