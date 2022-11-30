theory Submission
  imports Defs
begin

fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (Loop c b) =
 (let cc = ccomp c; cb = bcomp b False 1
  in cc @ cb @ [JMP (-(size cc + size cb + 1))])"

value "ccomp (Loop (''u'' ::= Plus (V ''u'') (N 1)) (Less (N 0) (V ''u'')))"

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
  proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (LoopTrue c s1 s2 b s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False 1"
  let ?cl = "ccomp(Loop c b)"
  have "?cl \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc,s2,stk)"
    by (simp add: LoopTrue.IH(1) exec_appendR)
  moreover
  have "?cl \<turnstile> (size ?cc,s2,stk) \<rightarrow>* (size ?cc + size ?cb,s2,stk)"
    using \<open>bval b s2\<close> by fastforce
  moreover
  have "?cl \<turnstile> (size ?cc + size ?cb,s2,stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cl \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cl,s3,stk)" by(rule LoopTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
qed fastforce+

end