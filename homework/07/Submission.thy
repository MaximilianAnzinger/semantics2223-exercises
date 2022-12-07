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
text \<open>
From big_step_determ we know big_step is deterministic. Hence we don't only know about the
existance of t' but even the exact outcome of (erase l c,t) \<Rightarrow> t'. Thus all the requirements
to apply erase_correct are given. Hence, also s' = t' (< l) must hold.
Therefore, this proposition holds.
\<close>

prop "\<lbrakk> (erase l c,s) \<Rightarrow> s';  0 \<turnstile> c;  s = t (< l) \<rbrakk> \<Longrightarrow> \<exists>t'. (c,t) \<Rightarrow> t'"
text \<open>
Counter example: An infinite loop that is erased by `erase l c`

l = 0; c = WHILE (Bc True) DO SKIP; s = 0; t = 0

Then:
erase l c s = SKIP
and
(erase l c,s) \<Rightarrow> s = s'
0 \<turnstile> c
and
s = t (< l)

but no terminal state (c,t) \<Rightarrow> t' exists since c is an infinite loop.
\<close>


theorem well_initialized_commands:
  assumes "D A c B"
      and "s = s' on A"
      and "(c,s) \<Rightarrow> t"
      and "(c,s') \<Rightarrow> t'"
    shows "t=t' on B"
using assms proof(induction arbitrary: s s' t t' rule: D.induct)
  case (Assign a A x)
  then have "vars a \<subseteq> A"
    by simp
  moreover have "D A (x ::= a) (insert x A)"
    by (simp add: D.Assign calculation)
  moreover have "aval a s = aval a s'"
    using aval_eq_if_eq_on_vars \<open>s = s' on A\<close> Assign.hyps by blast
  ultimately have "t = t' on (insert x A)" using Assign
    by auto
  then show ?case .
next
  case (If b A c\<^sub>1 A\<^sub>1 c\<^sub>2 A\<^sub>2)
  then have "vars b \<subseteq> A" "D A c\<^sub>1 A\<^sub>1" "D A c\<^sub>2 A\<^sub>2"
    by blast+
  moreover have "D A (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (A\<^sub>1 Int A\<^sub>2)"
    by (simp add: D.If calculation)
  moreover have "bval b s = bval b s'"
    using bval_eq_if_eq_on_vars \<open>s = s' on A\<close> If.hyps by blast
  ultimately have "t = t' on (A\<^sub>1 Int A\<^sub>2)"
    using Assign If.IH(1) If.IH(2) If.prems(1) If.prems(2) If.prems(3) IfE by blast
  then show ?case .
next
  case (While b A c A')
  from While(5) show ?case using While
  proof(induction "WHILE b DO c" s t arbitrary: s' t' rule: big_step_induct)
    case (WhileFalse s)
    have "bval b s = bval b s'"
      using bval_eq_if_eq_on_vars \<open>s = s' on A\<close> While.hyps by blast
    then show ?case
      using WhileFalse.hyps WhileFalse.prems(4) WhileFalse.prems(6) by auto
  next
    case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
    have "bval b s\<^sub>1 = bval b s'"
      using bval_eq_if_eq_on_vars \<open>s\<^sub>1 = s' on A\<close> While.hyps by blast
    then obtain s'\<^sub>2 where "(c,s') \<Rightarrow> s'\<^sub>2" "(WHILE b DO c, s'\<^sub>2) \<Rightarrow> t'"
      using WhileTrue.hyps(1) WhileTrue.prems(6) by auto
    then have "s\<^sub>2 = s'\<^sub>2 on A"
      using D_incr WhileTrue by blast
    then show ?case
      using WhileTrue \<open>(WHILE b DO c, s'\<^sub>2) \<Rightarrow> t'\<close> by blast
  qed
qed (blast)+

end