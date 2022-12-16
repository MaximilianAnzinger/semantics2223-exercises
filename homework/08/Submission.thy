theory Submission
  imports Defs
begin

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip:         "(SKIP,s) \<Rightarrow> s" |
Assign:       "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq:          "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2; (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue:       "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse:      "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse:   "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:    "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
OrLeft:       "\<lbrakk> (c\<^sub>1,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2,s) \<Rightarrow> s'" |
OrRight:      "\<lbrakk> (c\<^sub>2,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2,s) \<Rightarrow> s'" |
Assume:       "bval b s \<Longrightarrow> (ASSUME b, s) \<Rightarrow> s" |
LoopBreak:    "(LOOP c,s) \<Rightarrow> s" |
LoopContinue: "\<lbrakk> (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (LOOP c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (LOOP c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases skipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases OrE: "(c1 OR c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
inductive_cases LoopE: "(LOOP c, s) \<Rightarrow> t"

type_synonym com_den = "(state \<times> state) set"

definition W :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
  "W db dc = (\<lambda>dw. {(s,t). if db s then (s,t) \<in> dc O dw else s=t})"

definition L :: "com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
  "L dc = (\<lambda>dl. {(s,t). (s,t) \<in> dc O dl} \<union> Id)"

fun D :: "com \<Rightarrow> com_den" where
"D SKIP   = Id" |
"D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"D (c1;;c2)  = D(c1) O D(c2)" |
"D (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> D c1 else (s,t) \<in> D c2}" |
"D (WHILE b DO c) = lfp (W (bval b) (D c))" |
"D (c1 OR c2) = (D c1) \<union> (D c2)" |
"D (ASSUME b) = {(s,t). bval b s \<and> s = t}" |
"D (LOOP c) = lfp (L (D c))"

lemma W_mono: "mono (W b r)"
by (unfold W_def mono_def) auto

lemma D_While_If:
  "D(WHILE b DO c) = D(IF b THEN c;;WHILE b DO c ELSE SKIP)"
proof-
  let ?w = "WHILE b DO c" let ?f = "W (bval b) (D c)"
  have "D ?w = lfp ?f" by simp
  also have "\<dots> = ?f (lfp ?f)" by(rule lfp_unfold [OF W_mono])
  also have "\<dots> = D(IF b THEN c;;?w ELSE SKIP)" by (simp add: W_def)
  finally show ?thesis .
qed

thm lfp_unfold

lemma L_mono: "mono (L c)"
  by (unfold L_def mono_def) auto

lemma D_Loop_absorb: "D (Loop c) = D (c;;Loop c) \<union> Id"
proof-
  let ?l = "Loop c" let ?f = "L (D c)"
  have "D ?l = lfp ?f" by simp
  also have "... = ?f (lfp ?f)" by(rule lfp_unfold [OF L_mono])
  also have "... = D c O D ?l \<union> Id" by(simp add: L_def)
  also have "... = D (c;;?l) \<union> Id" by simp
  finally show ?thesis .
qed

lemma D_if_big_step:  "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> D(c)"
proof (induction rule: big_step_induct)
  case WhileFalse
  with D_While_If show ?case by auto
next
  case WhileTrue
  show ?case unfolding D_While_If using WhileTrue by auto
next
  case (LoopBreak c s)
  then have "D (LOOP c) = lfp (L (D c))" by simp
  then have "Id \<subseteq> lfp (L (D c))"
    using L_def Un_subset_iff lfp_greatest
    by (metis (no_types, lifting))
  then show ?case
    by (simp add: in_mono)
next
  case (LoopContinue c s\<^sub>1 s\<^sub>2 s\<^sub>3)
  show ?case unfolding D_Loop_absorb using LoopContinue by auto
qed auto

abbreviation Big_step :: "com \<Rightarrow> com_den" where
"Big_step c \<equiv> {(s,t). (c,s) \<Rightarrow> t}"

lemma Big_step_if_D:  "(s,t) \<in> D(c) \<Longrightarrow> (s,t) \<in> Big_step c"
proof (induction c arbitrary: s t)
  case Seq thus ?case by fastforce
next
  case (While b c)
  let ?B = "Big_step (WHILE b DO c)" let ?f = "W (bval b) (D c)"
  have "?f ?B \<subseteq> ?B" using While.IH by (auto simp: W_def)
  from lfp_lowerbound[where ?f = "?f", OF this] While.prems
  show ?case by auto
next
  case (ASSUME b)
  show ?case
    using ASSUME by auto
next
  case (Loop c)
  let ?B = "Big_step (LOOP c)" let ?f = "L (D c)"
  have "?f ?B \<subseteq> ?B" using Loop.IH by (auto simp: L_def)
  from lfp_lowerbound[where ?f = "?f", OF this] Loop.prems
  show ?case by auto
qed (auto split: if_splits)

theorem denotational_is_big_step:
  "(s,t) \<in> D(c)  =  ((c,s) \<Rightarrow> t)"
by (metis D_if_big_step Big_step_if_D[simplified])

end