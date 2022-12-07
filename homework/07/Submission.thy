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

lemma bval_eq: "\<lbrakk> s = t (< l); sec b < l \<rbrakk> \<Longrightarrow> bval b s = bval b t"
  by(induction rule: bexp.induct, auto simp: aval_eq)

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
    then have
      "erase l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =  IF b THEN (erase l c\<^sub>1) ELSE (erase l c\<^sub>2)"
      by simp
    then have "(erase l c\<^sub>1, t) \<Rightarrow> t'"
      using IfTrue bval_eq False by auto
    then show ?thesis
      using IfTrue.IH IfTrue.prems(3) \<open>sec b \<turnstile> c\<^sub>1\<close> anti_mono by blast
  qed
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  have "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" using \<open>0 \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2\<close> by auto
  then show ?case
  proof(cases "sec b \<ge> l")
    case True
    then show ?thesis
      using IfFalse \<open>sec b \<turnstile> c\<^sub>2\<close> anti_mono confinement erase.simps(4) sec_type.Skip
      by fastforce
  next
    case False
    then have
      "erase l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =  IF b THEN (erase l c\<^sub>1) ELSE (erase l c\<^sub>2)"
      by simp
    then have "(erase l c\<^sub>2, t) \<Rightarrow> t'"
      using IfFalse bval_eq False by auto
    then show ?thesis
      using IfFalse.IH IfFalse.prems(3) \<open>sec b \<turnstile> c\<^sub>2\<close> anti_mono by blast
  qed
next
  case (WhileFalse b s c)
  have "sec b \<turnstile> c" using WhileFalse.prems(2) by auto
  with WhileFalse show ?case
  proof cases
    assume "sec b \<ge> l"
    then show ?thesis
      using WhileFalse.prems(1) WhileFalse.prems(3) by auto
  next
    assume "\<not> sec b \<ge> l"
    then show ?thesis
      using WhileFalse.hyps WhileFalse.prems(1) WhileFalse.prems(3) \<open>\<not> l \<le> sec b\<close> bval_eq by auto
  qed
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3 t\<^sub>1 t\<^sub>3)
   have "sec b \<turnstile> c" using WhileTrue.prems(2) by auto
  with WhileTrue show ?case
  proof cases
    assume "sec b \<ge> l"
    then show ?thesis
      using \<open>sec b \<turnstile> c\<close> WhileTrue anti_mono confinement by metis
  next
    assume "\<not> sec b \<ge> l"
    hence "s\<^sub>1 = t\<^sub>1 (\<le> sec b)" using \<open>s\<^sub>1 = t\<^sub>1 (< l)\<close> by auto
    hence "bval b t\<^sub>1"
      using WhileTrue.hyps(1) bval_eq_if_eq_le by blast
    then obtain t\<^sub>2 where "(erase l c,t\<^sub>1) \<Rightarrow> t\<^sub>2" "(erase l (WHILE b DO c),t\<^sub>2) \<Rightarrow> t\<^sub>3"
      using \<open>(erase l (WHILE b DO c),t\<^sub>1) \<Rightarrow> t\<^sub>3\<close> \<open>\<not> l \<le> sec b\<close> by auto
    from WhileTrue.IH(2)[OF \<open>(erase l (WHILE b DO c),t\<^sub>2) \<Rightarrow> t\<^sub>3\<close> \<open>0 \<turnstile> WHILE b DO c\<close>
      WhileTrue.IH(1)[OF \<open>(erase l c,t\<^sub>1) \<Rightarrow> t\<^sub>2\<close> anti_mono[OF \<open>sec b \<turnstile> c\<close>]
        \<open>s\<^sub>1 = t\<^sub>1 (< l)\<close>]]
    show ?thesis by simp
  qed
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