theory Check
  imports Submission
begin

lemma ok_count_Zero: "ok bs \<Longrightarrow> count bs = 0"
  by (rule Submission.ok_count_Zero)

end