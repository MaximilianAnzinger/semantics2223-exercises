theory Defs
  imports "HOL-Library.Extended_Real"
begin

type_synonym val = "ereal option"

datatype bound = NegInf ("\<infinity>\<^sup>-") | PosInf ("\<infinity>\<^sup>+") | NaN | Real

lemma UNIV_bound: "UNIV = {\<infinity>\<^sup>-,\<infinity>\<^sup>+,NaN,Real}"
  by (smt (verit, best) UNIV_eq_I bound.exhaust insert_iff)

instantiation bound :: enum
begin

definition "enum_bound = [\<infinity>\<^sup>-,\<infinity>\<^sup>+,NaN,Real]"
definition "enum_all_bound P \<equiv> P \<infinity>\<^sup>- \<and> P \<infinity>\<^sup>+ \<and> P NaN \<and> P Real"
definition "enum_ex_bound P \<equiv> P \<infinity>\<^sup>- \<or> P \<infinity>\<^sup>+ \<or> P NaN \<or> P Real"

instance
  by standard (auto simp: enum_bound_def enum_all_bound_def enum_ex_bound_def UNIV_bound)
  
end

datatype bounds = B "bound set"

fun \<gamma>_bound :: "bound \<Rightarrow> val set" where
"\<gamma>_bound \<infinity>\<^sup>- = {Some (- \<infinity>)}" |
"\<gamma>_bound \<infinity>\<^sup>+ = {Some \<infinity>}" |
"\<gamma>_bound NaN = {None}" |
"\<gamma>_bound Real = {Some r|r. r\<in>\<real>}"

fun \<gamma>_bounds :: "bounds \<Rightarrow> val set" where
"\<gamma>_bounds (B bnds) = \<Union> (\<gamma>_bound ` bnds)"

fun num_bound :: "ereal \<Rightarrow> bound" where
  "num_bound PInfty = \<infinity>\<^sup>+" |
  "num_bound MInfty = \<infinity>\<^sup>-" |
  "num_bound (ereal r) = Real"

definition num_bounds :: "ereal \<Rightarrow> bounds" where
"num_bounds v = B {num_bound v}"

fun plus_bound :: "bound \<Rightarrow> bound \<Rightarrow> bound" where
"plus_bound NaN _ = NaN" |
"plus_bound _ NaN = NaN" |
"plus_bound \<infinity>\<^sup>- \<infinity>\<^sup>+ = NaN" |
"plus_bound \<infinity>\<^sup>+ \<infinity>\<^sup>- = NaN" |
"plus_bound \<infinity>\<^sup>- _ = \<infinity>\<^sup>-" |
"plus_bound _ \<infinity>\<^sup>- = \<infinity>\<^sup>-" |
"plus_bound _ \<infinity>\<^sup>+ = \<infinity>\<^sup>+" |
"plus_bound \<infinity>\<^sup>+ _ = \<infinity>\<^sup>+" |
"plus_bound Real Real = Real"

fun plus_bounds :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds" where
  "plus_bounds (B X) (B Y) = B {plus_bound a b | a b. a \<in> X \<and> b \<in> Y}"

lemma minfty_bound[simp]: "Some (- \<infinity>) \<in> \<gamma>_bound bd \<longleftrightarrow> bd = \<infinity>\<^sup>-"
  by (cases bd; auto)

lemma pinfty_bound[simp]: "Some (\<infinity>) \<in> \<gamma>_bound bd \<longleftrightarrow> bd = \<infinity>\<^sup>+"
  by (cases bd; auto)

lemma NaN_bound[simp]: "None \<in> \<gamma>_bound bd \<longleftrightarrow> bd = NaN"
  by (cases bd; auto)

lemma Real_bound[simp]: "Some (ereal r) \<in> \<gamma>_bound bd \<longleftrightarrow> bd = Real"
  by (cases bd; auto simp: Reals_def)


consts inv_plus' :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds \<Rightarrow> (bounds * bounds)"

consts inv_less' :: "bool option \<Rightarrow> bounds \<Rightarrow> bounds \<Rightarrow> (bounds * bounds)"


end