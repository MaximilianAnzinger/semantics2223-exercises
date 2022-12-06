theory Tut07
  imports "HOL-IMP.Small_Step" "HOL-IMP.Def_Init" "HOL-IMP.Sec_Typing"
begin

inductive sec_type2' :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile>'' _ : _)" [0,0] 50) where
Skip2': "\<turnstile>' SKIP : l" |
Assign2': "sec x \<ge> sec a \<Longrightarrow> \<turnstile>' x ::= a : sec x" |
Seq2': "\<lbrakk> \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l \<rbrakk> \<Longrightarrow> \<turnstile>' c\<^sub>1 ;; c\<^sub>2 : l" |
If2': "\<lbrakk> sec b \<le> l;  \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l \<rbrakk> \<Longrightarrow> \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2 : l" |
While2': "\<lbrakk> sec b \<le> l;  \<turnstile>' c : l \<rbrakk> \<Longrightarrow> \<turnstile>' WHILE b DO c : l" |
Subsumption2': "\<lbrakk> \<turnstile>' c : l; l' \<le> l \<rbrakk> \<Longrightarrow> \<turnstile>' c : l'"

lemma "\<turnstile> c : l \<Longrightarrow> \<turnstile>' c : l"
proof(induction rule: sec_type2.induct)
  case (Seq2 c\<^sub>1 l\<^sub>1 c\<^sub>2 l\<^sub>2)
  then show ?case using Seq2' Subsumption2' by simp
next
  case (If2 b l\<^sub>1 l\<^sub>2 c\<^sub>1 c\<^sub>2)
  then show ?case by (auto intro: sec_type2'.intros simp: Subsumption2')
qed (auto intro: sec_type2'.intros)

lemma "\<turnstile>' c : l \<Longrightarrow> \<exists>l' \<ge> l. \<turnstile> c : l'"
proof(induction rule: sec_type2'.induct)
  case (Seq2' c\<^sub>1 l c\<^sub>2)
  then show ?case sorry
next
  case (If2' b l c\<^sub>1 c\<^sub>2)
  then show ?case sorry
next
  case (While2' b l c)
  then show ?case sorry
next
  case (Subsumption2' c l l')
  then show ?case sorry
qed (auto intro: sec_type2.intros)

fun AA :: "com \<Rightarrow> (vname \<times> aexp) set \<Rightarrow> (vname \<times> aexp) set" where
  "AA SKIP A = A"
| "AA (x ::= a) A = (if x \<notin> vars a then {(x, a)} else {})
    \<union> {(x', a'). (x', a') \<in> A \<and> x \<notin> {x'} \<union> vars a'}"
| "AA (c\<^sub>1;; c\<^sub>2) A = (AA c\<^sub>2 \<circ> AA c\<^sub>1) A"
| "AA (IF b THEN c\<^sub>1 ELSE c\<^sub>2) A = AA c\<^sub>1 A \<inter> AA c\<^sub>2 A"
| "AA (WHILE b DO c) A = A \<inter> AA c A"

theorem AA_sound:
  "(c, s) \<Rightarrow> s' \<Longrightarrow> \<forall>(x, a) \<in> AA c {}. s' x = aval a s'"
  sorry

lemma AA_idem: "AA c (AA c A) = AA c A"
  sorry

fun gen :: "com \<Rightarrow> (vname \<times> aexp) set" and kill :: "com \<Rightarrow> (vname \<times> aexp) set"  where
  "gen _ = undefined"

lemma "gen (''x''::=N 5;; ''x''::= N 6) = {(''x'',N 6)}"
  by simp

lemma "(''x'', N 6) \<notin> kill (''x''::=N 5;; ''x''::= N 6)"
  by simp

lemma AA_gen_kill: "AA c A = (A \<union> gen c) - kill c"
  sorry

end