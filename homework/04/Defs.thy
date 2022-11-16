theory Defs
  imports "HOL-IMP.AExp"
begin

declare [[names_short]]
declare Let_def[simp]

datatype lexp = N int | V vname | Plus lexp lexp | Let vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
"lval (N n) s = n" |
"lval (V x) s = s x" |
"lval (Plus a\<^sub>1 a\<^sub>2) s = lval a\<^sub>1 s + lval a\<^sub>2 s" |
"lval (Let x a b) s = lval b (s(x := lval a s))"

fun vars_of :: "lexp \<Rightarrow> string set" where
  "vars_of (N _) = {}"
| "vars_of (V x) = {x}"
| "vars_of (Plus a b) = vars_of a \<union> vars_of b"
| "vars_of (Let x a b) = {x} \<union> vars_of a \<union> vars_of b"

fun bounds_of :: "lexp \<Rightarrow> string set" where
  "bounds_of (N _) = {}"
| "bounds_of (V x) = {}"
| "bounds_of (Plus a b) = bounds_of a \<union> bounds_of b"
| "bounds_of (Let x a b) = {x} \<union> bounds_of a \<union> bounds_of b"

fun collect :: "lexp \<Rightarrow> lexp list" where
  "collect (N n) = []"
| "collect (V _) = []"
| "collect (Plus a b) = collect a @ Plus a b # collect b"
| "collect (Let x a b) = collect a @ collect b"

fun invent_names :: "nat \<Rightarrow> string list" where
  "invent_names 0 = []"
| "invent_names (Suc n) = replicate (Suc n) (CHR ''v'') # invent_names n"

fun duplicates :: "'a list \<Rightarrow> 'a list" where
  "duplicates [] = []"
| "duplicates (x # xs) = (if x \<in> set xs then x # duplicates xs else duplicates xs)"


consts path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"

consts replace :: "lexp \<Rightarrow> vname \<Rightarrow> lexp \<Rightarrow> lexp"

consts linearize :: "lexp \<Rightarrow> lexp"


end