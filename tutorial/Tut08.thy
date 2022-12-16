theory Tut08
  imports "HOL-IMP.BExp" "HOL-Library.While_Combinator"
begin

definition Inf_fixp :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "Inf_fixp f P = \<Union>{u. u \<subseteq> \<Inter>P \<inter> f u }"

lemma Inf_fixp_upperbound: "X \<subseteq> \<Inter>P \<Longrightarrow> X \<subseteq> f X \<Longrightarrow> X \<subseteq> Inf_fixp f P"
  by (auto simp: Inf_fixp_def)

lemma Inf_fixp_least: "(\<And>u. u \<subseteq> \<Inter>P \<Longrightarrow> u \<subseteq> f u \<Longrightarrow> u \<subseteq> X) \<Longrightarrow> Inf_fixp f P \<subseteq> X"
  by (auto simp: Inf_fixp_def)

lemma Inf_fixp:
  assumes mono: "mono f"
      and P: "\<And>p. p \<in> P \<Longrightarrow> f p = p"
    shows "Inf_fixp f P = f (Inf_fixp f P)"
proof
  show *: "Inf_fixp f P \<subseteq> f (Inf_fixp f P)"
  proof(rule Inf_fixp_least)
    fix u assume "u \<subseteq> \<Inter>P" and le: "u \<subseteq> f u"
    have "u \<subseteq> (Inf_fixp f P)"
      by(rule Inf_fixp_upperbound) fact+
    with mono have "f u \<subseteq> f (Inf_fixp f P)" unfolding mono_def by simp
    with le show "u \<subseteq> f (Inf_fixp f P)" by simp
  qed
  show "f (Inf_fixp f P) \<subseteq> Inf_fixp f P"
  proof(rule Inf_fixp_upperbound)
    show "f (Inf_fixp f P) \<subseteq> \<Inter> P"
    proof(rule Inter_greatest)
      fix p assume p_def: "p \<in> P"
      have "Inf_fixp f P \<subseteq> p"
      proof(rule Inf_fixp_least)
        fix u assume "u \<subseteq> \<Inter>P" "u \<subseteq> f u"
        with p_def show "u \<subseteq> p" by auto
      qed
      with P[OF p_def] mono show "f (Inf_fixp f P) \<subseteq> p"
        unfolding mono_def by auto
    qed
  next
    from * mono show "f (Inf_fixp f P) \<subseteq> f (f (Inf_fixp f P))"
      unfolding mono_def by simp
  qed
qed

lemma Inf_fixp_lower: "Inf_fixp f P \<subseteq> \<Inter>P"
  by(rule Inf_fixp_least)

lemma Inf_fixp_greatest:
  assumes "f q = q"
      and "q \<subseteq> \<Inter>P"
  shows "q \<subseteq> Inf_fixp f P"
proof(rule Inf_fixp_upperbound)
  show "q \<subseteq> f q" using assms by auto
qed fact

datatype com = SKIP
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Repeat com bexp         ("(REPEAT _/ UNTIL _)"  [0, 61] 61)

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
  "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk>
  \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
RepeatTrue:
  "\<lbrakk> bval b t;  (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t" |
RepeatFalse:
  "\<lbrakk> \<not>bval b s\<^sub>2;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2; (REPEAT c UNTIL b, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk>
  \<Longrightarrow> (REPEAT c UNTIL b, s\<^sub>1) \<Rightarrow> s\<^sub>3"

lemmas [intro] = big_step.intros
lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b, s) \<Rightarrow> t"
type_synonym com_den = "(state \<times> state) set"

definition W :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
"W db dc = (\<lambda>dw. {(s,t). if db s then (s,t) \<in> dc O dw else s=t})"

definition R :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
"R db dc = (\<lambda>dr. dc O {(s,t). if db s then s = t else (s,t) \<in> dr})"

fun D :: "com \<Rightarrow> com_den" where
"D SKIP   = Id" |
"D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"D (c1;;c2)  = D(c1) O D(c2)" |
"D (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> D c1 else (s,t) \<in> D c2}" |
"D (WHILE b DO c) = lfp (W (bval b) (D c))" |
"D (REPEAT c UNTIL b) = lfp (R (bval b) (D c))"

value "while (\<lambda>x::nat. x < 3) (\<lambda>x. x + 2) 0"

fun exec :: "com \<Rightarrow> state \<Rightarrow> state"  where
  "exec _ = undefined"

value "(exec (WHILE Less (V ''x'') (N 3) DO ''x'' ::= Plus (V ''x'') (N 2)) <>) ''x''"

lemma "(c,s) \<Rightarrow> t \<Longrightarrow> exec c s = t"
  sorry

end