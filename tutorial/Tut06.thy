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
  "ccomp2 (IF b THEN c ELSE SKIP) = 
    (let cc = ccomp2 c; cb = bcomp b False (size cc + 1)
    in cb @ cc)" |
  "ccomp2 (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp2 c\<^sub>1; cc\<^sub>2 = ccomp2 c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)"

value "ccomp2 (IF Less (V ''x'') (N 5) THEN ''y'' ::= N 3 ELSE SKIP)"

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp2 c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp2 c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  then have "ccomp2 (x ::= a) = acomp a @ [STORE x]"
    by simp
  also have "... = ccomp (x ::= a)"
    by simp
  finally have "ccomp2 (x ::= a) = ccomp (x ::= a)"
    by simp
  then show ?case
    using assign_simp ccomp_bigstep by presburger
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case sorry
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case sorry
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case sorry
next
  case (WhileFalse b s c)
  then show ?case sorry
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case sorry
qed auto
  sorry


end