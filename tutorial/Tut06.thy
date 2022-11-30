theory Tut06
  imports "HOL-IMP.Compiler" Complex_Main
begin

value "ccomp (IF Less (V ''x'') (N 5) THEN ''y'' ::= N 3 ELSE SKIP)"

fun ccomp2 :: "com \<Rightarrow> instr list" where
  "ccomp2 SKIP = []" |
  "ccomp2 (x ::= a) = acomp a @ [STORE x]" |
  "ccomp2 (c\<^sub>1;;c\<^sub>2) = ccomp2 c\<^sub>1 @ ccomp2 c\<^sub>2" |
  "ccomp2 (WHILE b DO c) =
    (let cc = ccomp2 c; cb = bcomp b False (size cc + 1)
    in cb @ cc @ [JMP (-(size cb + size cc + 1))])" |
  "ccomp2 (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (if c\<^sub>2 = SKIP then
    (let cc\<^sub>1 = ccomp2 c\<^sub>1; cb = bcomp b False (size cc\<^sub>1)
    in cb @ cc\<^sub>1)
  else
    (let cc\<^sub>1 = ccomp2 c\<^sub>1; cc\<^sub>2 = ccomp2 c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
     in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2))"

value "ccomp2 (IF Less (V ''x'') (N 5) THEN ''y'' ::= N 3 ELSE SKIP)"

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp2 c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp2 c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp2 c1"  let ?cc2 = "ccomp2 c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce 
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp2 c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp2 (WHILE b DO c)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb,s1,stk)"
    using \<open>bval b s1\<close> by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb,s1,stk) \<rightarrow>* (size ?cb + size ?cc,s2,stk)"
    using WhileTrue.IH(1) by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
qed fastforce+


end