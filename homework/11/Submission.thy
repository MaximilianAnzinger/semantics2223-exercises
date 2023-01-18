theory Submission
  imports Defs
begin

definition A\<^sub>0 :: "entry list"  where
  "A\<^sub>0 _ = undefined"

definition A\<^sub>1 :: "entry list"  where
  "A\<^sub>1 _ = undefined"

definition A\<^sub>2 :: "entry list"  where
  "A\<^sub>2 _ = undefined"

definition A\<^sub>3 :: "entry list"  where
  "A\<^sub>3 _ = undefined"

definition A\<^sub>4 :: "entry list"  where
  "A\<^sub>4 _ = undefined"

definition A\<^sub>5 :: "entry list"  where
  "A\<^sub>5 _ = undefined"

definition A\<^sub>6 :: "entry list"  where
  "A\<^sub>6 _ = undefined"

lemma cont_imp_mono:
    fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes "continuous f"
  shows "mono f"
  sorry

thm mono_def monoI monoD

theorem kleene_lfp:
    fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes CONT: "continuous f"
  shows "lfp f = \<Squnion> (range (\<lambda>i. (f^^i) \<bottom>))"
proof -
  txt \<open> We propose a proof structure here, however, you may deviate from this
    and use your own proof structure: \<close>  
  let ?C = "\<lambda>i. (f^^i) \<bottom>"
  note MONO=cont_imp_mono[OF CONT]
  have CHAIN: "chain ?C"
  sorry
qed

show ?thesis
  proof (rule antisym)
    show "\<Squnion> (range ?C) \<le> lfp f"
   next
    show "lfp f \<le> Sup (range ?C)"
    qed
qed

thm lfp_unfold lfp_lowerbound Sup_subset_mono range_eqI

end