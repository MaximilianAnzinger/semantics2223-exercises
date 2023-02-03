theory Tut13
  imports "HOL-IMP.Small_Step" "HOL-IMP.Sem_Equiv" "HOL-IMP.Vars"
begin

datatype sign = None | Neg | Pos0 | Any

fun \<gamma> :: "sign \<Rightarrow> val set" where
"\<gamma> None = {}" |
"\<gamma> Neg = {i. i < 0}" |
"\<gamma> Pos0 = {i. i \<ge> 0}" |
"\<gamma> Any = UNIV"

(* _ = _ + _ then what can we say about _,_ *)
fun inv_plus' :: "sign \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign * sign"  where
  "inv_plus' None _ _ = (None, None)" |
  "inv_plus' _ None _ = (None, None)" |
  "inv_plus' _ _ None = (None, None)" |
  "inv_plus' Pos0 Neg Neg = (None, None)" |
  "inv_plus' Pos0 Neg _ = (Neg, Pos0)" |
  "inv_plus' Pos0 _ Neg = (Pos0, Neg)" |
  "inv_plus' Neg Pos0 Pos0 = (None, None)" |
  "inv_plus' Neg Pos0 _ = (Pos0, Neg)" |
  "inv_plus' Neg _ Pos0 = (Neg, Pos0)" |
  "inv_plus' _ x y = (x, y)"


lemma 
  "\<lbrakk> inv_plus' a a1 a2 = (a1',a2');  i1 \<in> \<gamma> a1;  i2 \<in> \<gamma> a2; i1+i2 \<in> \<gamma> a \<rbrakk>
  \<Longrightarrow> i1 \<in> \<gamma> a1' \<and> i2 \<in> \<gamma> a2' "
  by(induction a a1 a2 rule: inv_plus'.induct, auto)

fun inv_less' :: "bool \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign * sign"  where
  "inv_less' _ None _ = (None, None)" |
  "inv_less' _ _ None = (None, None)" |
  "inv_less' True Pos0 Neg = (None, None)" |
  "inv_less' True Pos0 Any = (Pos0, Pos0)" |
  "inv_less' True Any Neg = (Neg, Neg)" |
  "inv_less' False Neg Pos0 = (None, None)" |
  "inv_less' False Any Pos0 = (Pos0, Pos0)" |
  "inv_less' False Neg Any = (Neg, Neg)" |
  "inv_less' _ x y = (x, y)"

lemma 
  "\<lbrakk> inv_less' bv a1 a2 = (a1',a2');  i1 \<in> \<gamma> a1;  i2 \<in> \<gamma> a2; (i1<i2) = bv \<rbrakk>
  \<Longrightarrow> i1 \<in> \<gamma> a1' \<and> i2 \<in> \<gamma> a2'"
  by(cases a1; cases a2, auto)

end