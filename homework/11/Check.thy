theory Check
  imports Submission
begin

lemma cont_imp_mono: "\<And> f :: 'a::complete_lattice \<Rightarrow> 'b::complete_lattice. (continuous f) \<Longrightarrow> mono f"
  by (rule Submission.cont_imp_mono)

theorem kleene_lfp: "\<And> f :: 'a::complete_lattice \<Rightarrow> 'a. (continuous f) \<Longrightarrow> lfp f = \<Squnion> (range (\<lambda>i. (f^^i) \<bottom>))"
  by (rule Submission.kleene_lfp)

end