theory Defs
  imports "HOL-IMP.BExp"
begin

datatype
  com = SKIP
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | CONTINUE
  inductive
    big_step :: "com \<times> state \<Rightarrow> bool \<times> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
  where
  Skip: "(SKIP,s) \<Rightarrow> (False,s)" |
  Assign: "(x ::= a,s) \<Rightarrow> (False,s(x := aval a s))" |
  Seq1: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> (False,s\<^sub>2);  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
  Seq2: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> (True,s\<^sub>2) \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> (True,s\<^sub>2)" |
  IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
  IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
  WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> (False,s)" |
  WhileTrue:
  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> (_, s\<^sub>2);  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk>
  \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" | \<comment> \<open>We can simply reset the continue flag in a while loop\<close>
  Continue: "(CONTINUE,s) \<Rightarrow> (True,s)"

declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]
inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases ContinueE[elim!]: "(CONTINUE,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

type_synonym assn = "state \<Rightarrow> bool"

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s f t. P s \<and> (c,s) \<Rightarrow> (f, t)  \<longrightarrow>  Q t)"

definition
hoare_valid\<^sub>c :: "assn \<Rightarrow> assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>c{(1_)}/ {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>c{I} {P}c{Q} = (\<forall>s f t. P s \<and> (c,s) \<Rightarrow> (f, t)  \<longrightarrow> (if f then I t else Q t))"

consts hoare :: "assn \<Rightarrow> assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"

consts wp :: "com \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn"

end