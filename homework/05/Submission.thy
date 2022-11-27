theory Submission
  imports Defs
begin

inductive ls :: "com \<Rightarrow> state \<Rightarrow> state list \<Rightarrow> state \<Rightarrow> bool" where
  Skip: "ls SKIP s [] s" |
  Assign: "ls (v ::= e) s [s(v := aval e s)] (s(v := aval e s))" |
  Seq: "\<lbrakk>ls c1 s xs t'; ls c2 t' ys t\<rbrakk> \<Longrightarrow> ls (c1 ;; c2) s (xs@t'#ys) t" |
  IfTrue: "\<lbrakk>bval b s; ls c1 s xs t\<rbrakk> \<Longrightarrow> ls (IF b THEN c1 ELSE c2) s (s#xs) t" |
  IfFalse: "\<lbrakk>\<not>bval b s; ls c2 s xs t\<rbrakk> \<Longrightarrow> ls (IF b THEN c1 ELSE c2) s (s#xs) t" |
  WhileTrue: "\<lbrakk>bval b s1; ls c s1 xs s2 ; ls (WHILE b DO c) s2 ys s3\<rbrakk> \<Longrightarrow> ls (WHILE b DO c) s1 (s1#s1#xs@s2#ys) s3" |
  WhileFalse: "\<not>bval b s \<Longrightarrow> ls (WHILE b DO c) s [s, s] s"

declare ls.intros[intro]
declare ls.cases[elim]
code_pred ls .

theorem big_ls: "(c,s) \<Rightarrow> t \<Longrightarrow> \<exists>sts. ls c s sts t"
proof(induction c s t rule: big_step_induct)
  case (Assign x a s)
  then show ?case by blast
qed auto

theorem ls_big: "ls c s ss t \<Longrightarrow> (c,s) \<Rightarrow> t"
  by(induction c s ss t rule: ls.induct, blast+)

abbreviation "ss_x c s \<equiv> {map (\<lambda>s. s ''x'') ss |ss t . ls c s ss t}"
values "ss_x (IF Bc True THEN ''x'' ::= N 3 ELSE ''x'' ::= N 1) <>" \<comment>\<open>[0, 3]\<close>
values "ss_x (WHILE Less (V ''x'') (N 1) DO ''x'' ::= Plus (V ''x'') (N 1)) <>" \<comment>\<open>[0, 0, 1, 1, 1, 1]\<close>

lemma ls_step: "\<lbrakk>ls c s ss t; c \<noteq> SKIP\<rbrakk> \<Longrightarrow> (case ss of 
  [] \<Rightarrow> (c,s) \<rightarrow> (SKIP,t) 
| (x#_) \<Rightarrow> \<exists>c'. (c,s) \<rightarrow> (c',x))"
proof(induction c s ss t rule: ls.induct)
  case (Seq c1 s xs t' c2 ys t)
  then show ?case
  proof(cases "xs = Nil")
    case True
    then show ?thesis
      using Seq.hyps(1) by auto
  next
    case False
    then have c1_not_SKIP: "c1 \<noteq> SKIP"
      using Seq.hyps(1) by auto
    from False obtain z zs where zzs_def: "xs = z#zs"
      using list.exhaust_sel by auto
    with c1_not_SKIP  have "\<exists>c'. (c1, s) \<rightarrow> (c', z)"
      using Seq.IH(1) by auto
    then show ?thesis
      using zzs_def by auto
  qed
next
qed auto

lemma ls_ls: "\<lbrakk>ls c s\<^sub>1 (s\<^sub>2#ss) s\<^sub>3; (c,s\<^sub>1) \<rightarrow> (c',s\<^sub>2)\<rbrakk> \<Longrightarrow> ls c' s\<^sub>2 ss s\<^sub>3"
proof(induction c s\<^sub>1 "(s\<^sub>2#ss)" s\<^sub>3 arbitrary: ss c' s\<^sub>2 rule: ls.induct)
  case (Seq c1 s xs t' c2 ys t)
  then show ?case
  proof(cases "xs = Nil")
    case True
    then have c1_is_SKIP: "c1 = SKIP"
      using Seq.hyps(1) by auto
    then have "(c1;;c2,s) \<rightarrow> (c2,s)"
      by simp
    then have "c' = c2"
      using Seq.prems deterministic by blast
    then show ?thesis
      using Seq.hyps(3) Seq.hyps(5) True by fastforce
  next
    case False
    then have c1_not_SKIP: "c1 \<noteq> SKIP"
      using Seq.hyps(1) by auto
    then obtain c1' where c1_step: "(c1, s) \<rightarrow> (c1', s\<^sub>2)"
      using Seq.prems by auto
    have step: "(c1;;c2 ,s) \<rightarrow> (c1';;c2 ,s\<^sub>2)"
      by (simp add: c1_step)
    from False obtain z zs where zzs_def: "xs = z#zs"
      using list.exhaust_sel by auto
    then have "ls c1' s\<^sub>2 zs t'"
      using c1_step Seq.hyps(2) Seq.hyps(5) by force
    then have "ls (c1';;c2) s\<^sub>2 (zs@t'#ys) t"
      by (simp add: Seq.hyps(3) ls.Seq)
    moreover
    have "c' = (c1';;c2)"
      using Seq.prems deterministic step by fastforce
    ultimately show ?thesis
      using Seq.hyps(5) zzs_def by fastforce
  qed
next
  case (WhileTrue b c xs s2 ys s3)
  then show ?case
    using ls.IfTrue ls.Seq by fastforce
qed auto

lemma interstate_not_SKIP: "ls c s (x#xs) t \<Longrightarrow> c \<noteq> SKIP"
  by(induction c s "(x#xs)" t rule: ls.induct, auto)

theorem ls_steps: "ls c s\<^sub>1 (ss\<^sub>1@[s\<^sub>2]@ss\<^sub>2) t \<Longrightarrow> \<exists>c'. (c,s\<^sub>1) \<rightarrow>* (c',s\<^sub>2)"
proof(induction ss\<^sub>1 arbitrary: s\<^sub>1 c)
  case Nil
  then have ls_simp: "ls c s\<^sub>1 ([s\<^sub>2]@ss\<^sub>2) t"
    by simp
  moreover
  from ls_simp have "c \<noteq> SKIP"
    by (simp add: interstate_not_SKIP)
  ultimately have "\<exists>c'. (c,s\<^sub>1) \<rightarrow> (c',s\<^sub>2)"
    using ls_step by fastforce
  then show ?case
    by blast
next
  case (Cons a ss\<^sub>1)
  then have "c \<noteq> SKIP"
    by (simp add: interstate_not_SKIP)
  have first_step_ex: "\<exists>c'. (c,s\<^sub>1) \<rightarrow> (c',a)"
    using Cons.prems ls_step by fastforce
  then obtain c' where first_step: "(c,s\<^sub>1) \<rightarrow> (c',a)"
    by blast
  then have "ls c' a (ss\<^sub>1 @ [s\<^sub>2] @ ss\<^sub>2) t"
    using Cons.prems ls_ls
    by simp
  then have "\<exists>c''. (c', a) \<rightarrow>* (c'', s\<^sub>2)"
    by (simp add: Cons.IH)
  then show ?case
    using first_step star.step by meson
qed

end