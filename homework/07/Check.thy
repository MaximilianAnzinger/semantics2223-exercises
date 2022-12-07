theory Check
  imports Submission
begin

theorem erase_correct: "\<lbrakk> (c,s) \<Rightarrow> s'; (erase l c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
   \<Longrightarrow> s' = t' (< l)"
  by (rule Submission.erase_correct)

theorem well_initialized_commands: "(D A c B) \<Longrightarrow> (s = s' on A) \<Longrightarrow> ((c,s) \<Rightarrow> t) \<Longrightarrow> ((c,s') \<Rightarrow> t') \<Longrightarrow> t=t' on B"
  by (rule Submission.well_initialized_commands)

end