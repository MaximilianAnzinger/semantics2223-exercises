theory Tut02
  imports "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

fun deduplicate :: "'a list \<Rightarrow> 'a list"  where
  "deduplicate [] = []" |
  "deduplicate [x] = [x]" |
  "deduplicate (x#y#xs) = (if x = y then deduplicate (x#xs) else x # deduplicate (y#xs))"

value "deduplicate [1,1,2,3,2,2,1::nat] = [1,2,3,2,1]"

lemma "length (deduplicate xs) \<le> length xs"
  apply(induction xs rule: deduplicate.induct) by auto

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
  "subst x a' (N n) = (N n)" |
  "subst x a' (V v) = (if x = v then a' else V v)" |
  "subst x a' (Plus i j) = Plus (subst x a' i) (subst x a' j)"

lemma subst_lemma: "aval (subst x a' a) s = aval a (s(x := aval a' s))"
  apply(induction a arbitrary: x a' s) by auto

lemma comp: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
  apply(induction a arbitrary: x a1 a2 s) using subst_lemma by auto


value "<>(x := 0)"
value "aval' (Plus' (PI' ''x'') (V' ''x'')) <>"
value "aval' (Plus' (Plus' (PI' ''x'') (PI' ''x'')) (PI' ''x'')) <>"

lemma aval'_inc:
  "aval' a <> = (v, s') \<Longrightarrow> 0 \<le> s' x"
  sorry

end