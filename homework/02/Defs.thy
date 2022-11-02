theory Defs
  imports "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

declare [[names_short]]
lemmas [simp] = algebra_simps

datatype aexp = N int | V vname | Plus aexp aexp | Mult int aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
"aval (Mult i a) s = i * aval a s"


consts rlenc :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list"

consts rldec :: "('a \<times> nat) list \<Rightarrow> 'a list"

consts normal :: "aexp \<Rightarrow> bool"

consts normalize :: "aexp \<Rightarrow> aexp"


end