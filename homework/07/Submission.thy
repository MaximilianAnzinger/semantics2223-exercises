theory Submission
  imports Defs
begin

fun erase :: "level \<Rightarrow> com \<Rightarrow> com"  where
  "erase _ = undefined"

theorem erase_correct:
  "\<lbrakk> (c,s) \<Rightarrow> s'; (erase l c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
   \<Longrightarrow> s' = t' (< l)"
  sorry

prop "\<lbrakk> (c,s) \<Rightarrow> s';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
  \<Longrightarrow> \<exists>t'. (erase l c,t) \<Rightarrow> t' \<and> s' = t' (< l)"
prop "\<lbrakk> (erase l c,s) \<Rightarrow> s';  0 \<turnstile> c;  s = t (< l) \<rbrakk> \<Longrightarrow> \<exists>t'. (c,t) \<Rightarrow> t'"
theorem well_initialized_commands:
  assumes "D A c B"
      and "s = s' on A"
      and "(c,s) \<Rightarrow> t"
      and "(c,s') \<Rightarrow> t'"
  shows "t=t' on B"
  sorry

end