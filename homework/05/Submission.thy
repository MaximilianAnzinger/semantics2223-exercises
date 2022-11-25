theory Submission
  imports Defs
begin

inductive ls :: "com \<Rightarrow> state \<Rightarrow> state list \<Rightarrow> state \<Rightarrow> bool" where
  Skip: "ls SKIP s [] s" |
  Assign: "(v ::= e, s) \<Rightarrow> t \<Longrightarrow> ls (v ::= e) s [] t" |
  Seq: "\<lbrakk>(c1 ;; c2, s) \<Rightarrow> t; ls c1 s xs t'; ls c2 t' ys t\<rbrakk> \<Longrightarrow> ls (c1 ;; c2) s (xs@t'#ys) t" |
  IfTrue: "\<lbrakk>bval b s; (IF b THEN c1 ELSE c2, s) \<Rightarrow> t; ls c1 s xs t\<rbrakk> \<Longrightarrow> ls (IF b THEN c1 ELSE c2) s xs t" |
  IfFalse: "\<lbrakk>\<not>bval b s; (IF b THEN c1 ELSE c2, s) \<Rightarrow> t; ls c2 s xs t\<rbrakk> \<Longrightarrow> ls (IF b THEN c1 ELSE c2) s xs t" |
  WhileTrue: "\<lbrakk> bval b s1; (c, s1) \<Rightarrow> s2; ls (WHILE b DO c) s2 xs s3 \<rbrakk> \<Longrightarrow> ls (WHILE b DO c) s1 (s2#xs) s3" |
  WhileFalse: "\<not>bval b s  \<Longrightarrow> ls (WHILE b DO c) s [] s"

declare ls.intros[intro]
declare ls.cases[elim]
code_pred ls .

theorem big_ls: "(c,s) \<Rightarrow> t \<Longrightarrow> \<exists>sts. ls c s sts t"
proof(induction c s t rule: big_step_induct)
  case (Assign x a s)
  then show ?case by blast
qed auto

theorem ls_big: "ls c s ss t \<Longrightarrow> (c,s) \<Rightarrow> t"
  by(induction c s ss t rule: ls.induct, auto)


abbreviation "ss_x c s \<equiv> {map (\<lambda>s. s ''x'') ss |ss t . ls c s ss t}"
values "ss_x (IF Bc True THEN ''x'' ::= N 3 ELSE ''x'' ::= N 1) <>" \<comment>\<open>[0, 3]\<close>
values "ss_x (WHILE Less (V ''x'') (N 1) DO ''x'' ::= Plus (V ''x'') (N 1)) <>" \<comment>\<open>[0, 0, 1, 1, 1, 1]\<close>

lemma ls_step: "\<lbrakk>ls c s ss t; c \<noteq> SKIP\<rbrakk> \<Longrightarrow> (case ss of 
  [] \<Rightarrow> (c,s) \<rightarrow> (SKIP,t) 
| (x#_) \<Rightarrow> \<exists>c'. (c,s) \<rightarrow> (c',x))"
  sorry

lemma ls_ls: "\<lbrakk>ls c s\<^sub>1 (s\<^sub>2#ss) s\<^sub>3; (c,s\<^sub>1) \<rightarrow> (c',s\<^sub>2)\<rbrakk> \<Longrightarrow> ls c' s\<^sub>2 ss s\<^sub>3"
  sorry

theorem ls_steps: "ls c s\<^sub>1 (ss\<^sub>1@[s\<^sub>2]@ss\<^sub>2) t \<Longrightarrow> \<exists>c'. (c,s\<^sub>1) \<rightarrow>* (c',s\<^sub>2)"
  sorry

end