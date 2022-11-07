theory Tut02
  imports "HOL-IMP.AExp" "HOL-IMP.BExp"
begin

fun deduplicate :: "'a list \<Rightarrow> 'a list"  where
  "deduplicate [] = []" |
  "deduplicate [x] = [x]" |
  "deduplicate (x#y#xs) = (if x = y then deduplicate (x#xs) else x # deduplicate (y#xs))"

value "deduplicate [1,1,2,3,2,2,1::nat] = [1,2,3,2,1]"

lemma "length (deduplicate xs) \<le> length xs"
  by(induction xs rule: deduplicate.induct, auto)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
  "subst x a' (N n) = (N n)" |
  "subst x a' (V v) = (if x = v then a' else V v)" |
  "subst x a' (Plus i j) = Plus (subst x a' i) (subst x a' j)"

lemma subst_lemma[simp]: "aval (subst x a' a) s = aval a (s(x := aval a' s))"
  by(induction a arbitrary: x a' s, auto)

lemma comp: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
  by(induction a arbitrary: x a1 a2 s, auto)

datatype aexp' = N' int | V' vname | Plus' aexp' aexp' | PI' vname


fun aval' :: "aexp' \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
  "aval' (N' n) s = (n, s)" |
  "aval' (V' v) s = (s v, s)" |
  "aval' (Plus' i j) s = (
    let (i', s) = aval' i s;
    (j', s) = aval' j s
    in (i' + j', s))" |
  "aval' (PI' v) s = (s v, s(v := (s v) + 1))"

value "<>(x := 0)"
value "aval' (Plus' (PI' ''x'') (V' ''x'')) <>"
value "aval' (Plus' (Plus' (PI' ''x'') (PI' ''x'')) (PI' ''x'')) <>"

lemma aval'_PI'_inc:
  "aval' (PI' v) s = (r, s') \<Longrightarrow> s x \<le> s' x"
  by auto

lemma aval'_mono:
  "aval' a s = (r, s') \<Longrightarrow> s x \<le> s' x"
  by(induction a arbitrary: s r s', auto split: prod.splits, fastforce)

lemma aval'_inc:
  "aval' a <> = (v, s') \<Longrightarrow> 0 \<le> s' x"
  unfolding null_state_def using aval'_mono by fastforce

end