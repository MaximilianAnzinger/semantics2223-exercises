theory Defs
  imports "HOL-IMP.Big_Step"
begin

datatype entry = Unchanged ("'_'_'_'_'_'_'_'_") | V "(int\<times>int) set"

unbundle lattice_syntax

definition chain :: "(nat \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool"
  where "chain C \<longleftrightarrow> (\<forall>n. C n \<le> C (Suc n))"

definition continuous :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> bool"
  where "continuous f \<longleftrightarrow> (\<forall>C. chain C \<longrightarrow> f (\<Squnion> (range C)) = \<Squnion> (f ` range C))"

lemma continuousD: "\<lbrakk>continuous f; chain C\<rbrakk> \<Longrightarrow> f (\<Squnion> (range C)) = \<Squnion> (f ` range C)"
  unfolding continuous_def by auto


consts A\<^sub>0 :: "entry list"

consts A\<^sub>1 :: "entry list"

consts A\<^sub>2 :: "entry list"

consts A\<^sub>3 :: "entry list"

consts A\<^sub>4 :: "entry list"

consts A\<^sub>5 :: "entry list"

consts A\<^sub>6 :: "entry list"


end