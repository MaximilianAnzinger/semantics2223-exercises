theory Submission
  imports Defs
begin

fun erase :: "level \<Rightarrow> com \<Rightarrow> com"  where
  "erase l SKIP = SKIP" |
  "erase l (x ::= a) = (if sec (V x) \<ge> l then SKIP else (x ::= a))" |
  "erase l (c\<^sub>1;;c\<^sub>2) = (erase l c\<^sub>1) ;; (erase l c\<^sub>2)" |
  "erase l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (if sec b \<ge> l then SKIP else (IF b THEN (erase l c\<^sub>1) ELSE (erase l c\<^sub>2)))" |
  "erase l (WHILE b DO c) = (if sec b \<ge> l then SKIP else (WHILE b DO erase l c))"

lemma aval_eq: "\<lbrakk> s = t (< l); sec a < l \<rbrakk> \<Longrightarrow> aval a s = aval a t"
  by(induction rule: aexp.induct, auto)

theorem erase_correct:
  "\<lbrakk> (c,s) \<Rightarrow> s'; (erase l c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
   \<Longrightarrow> s' = t' (< l)"
proof(induction arbitrary: t t' rule: big_step_induct)
  case (Assign x a s)
  then have "sec x \<ge> sec a" using \<open>0 \<turnstile> x ::= a\<close> by auto
  then show ?case
    proof(cases "sec (V x) \<ge> l")
      case True
      then show ?thesis using Assign by fastforce
    next
      case False
      then have "erase l (x ::= a) = (x ::= a)" by simp
      moreover have "t' = t(x := aval a t)" using False Assign by auto
      moreover have "aval a s = aval a t" using Assign aval_eq False by auto
      ultimately show ?thesis
        by (simp add: Assign.prems(3))
    qed
  next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  then show ?case 
  proof(cases "sec b \<ge> l")
    case True
    then show ?thesis
      using IfTrue \<open>sec b \<turnstile> c\<^sub>1\<close> anti_mono confinement erase.simps(4) sec_type.Skip
      by fastforce
  next
    case False
    then show ?thesis  sorry
  qed
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case  sorry
next
  case (WhileFalse b s c)
  then show ?case sorry
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case  sorry
qed auto

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