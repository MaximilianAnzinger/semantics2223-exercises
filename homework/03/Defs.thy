theory Defs
  imports Main
begin

abbreviation a where "a \<equiv> CHR ''a''"
abbreviation b where "b \<equiv> CHR ''b''"

definition
  "L = {w. \<exists>n. w = replicate n a @ replicate n b}"

datatype instr = LDI int | LD nat | ST nat | ADD nat

type_synonym rstate = "nat \<Rightarrow> int"


datatype expr = C int | V nat | A expr expr

fun val :: "expr \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int" where
"val(C i) s = i" |
"val(V n) s = s n" |
"val(A e1 e2) s = val e1 s + val e2 s"


consts G :: "string set"

consts exec :: "instr \<Rightarrow> rstate \<Rightarrow> rstate"

consts execs :: "instr list \<Rightarrow> rstate \<Rightarrow> rstate"

consts cmp :: "expr \<Rightarrow> nat \<Rightarrow> instr list"

consts maxvar :: "expr \<Rightarrow> nat"


end