theory Check
  imports Submission
begin

theorem big_ls: "(c,s) \<Rightarrow> t \<Longrightarrow> \<exists>sts. ls c s sts t"
  by (rule Submission.big_ls)

theorem ls_big: "ls c s ss t \<Longrightarrow> (c,s) \<Rightarrow> t"
  by (rule Submission.ls_big)

lemma ls_step: "\<lbrakk>ls c s ss t; c \<noteq> SKIP\<rbrakk> \<Longrightarrow> (case ss of 
  [] \<Rightarrow> (c,s) \<rightarrow> (SKIP,t) 
| (x#_) \<Rightarrow> \<exists>c'. (c,s) \<rightarrow> (c',x))"
  by (rule Submission.ls_step)

lemma ls_ls: "\<lbrakk>ls c s\<^sub>1 (s\<^sub>2#ss) s\<^sub>3; (c,s\<^sub>1) \<rightarrow> (c',s\<^sub>2)\<rbrakk> \<Longrightarrow> ls c' s\<^sub>2 ss s\<^sub>3"
  by (rule Submission.ls_ls)

theorem ls_steps: "ls c s\<^sub>1 (ss\<^sub>1@[s\<^sub>2]@ss\<^sub>2) t \<Longrightarrow> \<exists>c'. (c,s\<^sub>1) \<rightarrow>* (c',s\<^sub>2)"
  by (rule Submission.ls_steps)

end