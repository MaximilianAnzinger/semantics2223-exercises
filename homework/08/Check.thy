theory Check
  imports Submission
begin

theorem denotational_is_big_step: "(s,t) \<in> D(c)  =  ((c,s) \<Rightarrow> t)"
  by (rule Submission.denotational_is_big_step)

end