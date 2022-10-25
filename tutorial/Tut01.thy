theory Tut01
  imports Main
begin

value "2 + (2::nat)"
value "(2::nat) * (5 + 3)"
value "(3::nat) * 4 - 2 * (7 + 1)"

lemma comm: "(a::nat) + b = b + a"
  by simp

lemma assoc: "(a::nat) + (b + c) = (a + b) + c"
  by simp

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] v = 0" |
  "count (x#xs) v = (if x = v then 1 else 0) + count xs v"

lemma "x \<notin> set xs \<Longrightarrow> count xs x = 0"
  apply(induction xs) by auto

lemma "count (x#xs) x = 1 + count xs x"
  apply(induction xs) by auto

theorem "count xs x \<le> length xs"
  apply(induction xs) by auto

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] c = [c]" |
  "snoc (x#xs) c = x # (snoc xs c)"

lemma "snoc [] c = [c]"
  by simp

lemma snoc_is_append[simp]: "snoc xs x = xs @ [x]"
  apply(induction xs) by auto

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x#xs) = snoc (reverse xs) x"

lemma reverse_is_rev[simp]: "reverse xs = rev xs"
  apply(induction xs) by auto

theorem "reverse (reverse xs) = xs"
  apply(induction xs) by auto

end