theory Defs
  imports Main
begin

fun count :: "bool list \<Rightarrow> int" where
"count [] = 0" |
"count (True # bs) = count bs + 1" |
"count (False # bs) = count bs - 1"

inductive ok :: "bool list \<Rightarrow> bool" where
"ok []" |
"\<lbrakk> ok as;  ok bs \<rbrakk> \<Longrightarrow> ok (True # as @ False # bs)"

end
