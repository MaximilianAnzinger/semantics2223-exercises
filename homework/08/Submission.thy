theory Submission
  imports Defs
begin

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip:    "(SKIP,s) \<Rightarrow> s" |
Assign:  "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq:    "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2; (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue:  "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
OrLeft: "\<lbrakk> (c\<^sub>1,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2,s) \<Rightarrow> s'" |
OrRight: "\<lbrakk> (c\<^sub>2,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2,s) \<Rightarrow> s'" |
Assume: "bval b s \<Longrightarrow> (ASSUME b, s) \<Rightarrow> s" |
\<comment> \<open>Your cases here:\<close>
declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases skipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases OrE: "(c1 OR c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

type_synonym com_den = "(state \<times> state) set"

fun D :: "com \<Rightarrow> com_den" where
"D SKIP   = Id" |
"D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"D (c1;;c2)  = D(c1) O D(c2)" |
"D (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> D c1 else (s,t) \<in> D c2}" |
"D (WHILE b DO c) = lfp (W (bval b) (D c))"
\<comment> \<open>Your cases here:\<close>
| "D _ = undefined"

theorem denotational_is_big_step:
  "(s,t) \<in> D(c)  =  ((c,s) \<Rightarrow> t)"
  sorry

end