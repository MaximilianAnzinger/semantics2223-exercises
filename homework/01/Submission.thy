theory Submission
  imports Defs
begin

fun find_pfx :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"  where
  "find_pfx [] v = []" |
  "find_pfx (x#xs) v = (if x = v then [x] else x#(find_pfx xs v))"

value "find_pfx [1::nat,2,3] 2 = [1,2]"
value "find_pfx [] (1::nat) = []"

lemma find_pfx_append:
  "(find_pfx (xs1 @ [x] @ xs2) x) = (find_pfx (xs1 @ [x]) x)"
  by(induction xs1, auto)

lemma find_pfx_not_empty: "x \<in> set xs \<Longrightarrow> length (find_pfx xs x) > 0"
  by(induction xs, auto)

lemma last_find_pfx_val:
  "last (find_pfx (xs @ [x]) x) = x"
  using find_pfx_not_empty by(induction xs, auto)

lemma find_pfx_suff[simp]: "x \<in> set xs \<Longrightarrow> find_pfx (xs @ ys) x = find_pfx xs x"
  by(induction xs, auto)

lemma pfx_append_same: "x \<in> set xs \<Longrightarrow> find_pfx (xs @ xs) x = find_pfx xs x"
  by simp

end