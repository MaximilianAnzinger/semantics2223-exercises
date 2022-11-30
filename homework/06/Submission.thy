theory Submission
  imports Defs
begin

fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)"
| "ccomp _ = undefined"

value "ccomp (Loop (''u'' ::= Plus (V ''u'') (N 1)) (Less (N 0) (V ''u'')))"

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
  sorry

end