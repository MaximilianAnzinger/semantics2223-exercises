theory Check
  imports Submission
begin

lemma ccomp_bigstep: "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
  by (rule Submission.ccomp_bigstep)

end