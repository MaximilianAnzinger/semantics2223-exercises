theory Check
  imports Submission
begin

lemma bound_decr: "while_free c \<Longrightarrow> (c, s) \<rightarrow> (c', s') \<Longrightarrow> bound c' < bound c"
  by (rule Submission.bound_decr)

end