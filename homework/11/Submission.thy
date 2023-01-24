theory Submission
  imports Defs
begin

definition A\<^sub>0 :: "entry list"  where
  "A\<^sub>0 = [(V {}), (V {(1, 0)}), Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>1 :: "entry list"  where
  "A\<^sub>1 = [(V {}), Unchanged, (V {(1, 1)}), Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>2 :: "entry list"  where
  "A\<^sub>2 = [(V {}), Unchanged, Unchanged, (V {(1, 1)}), Unchanged, Unchanged, Unchanged, (V {(1, 1), (0, -1)}), Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>3 :: "entry list"  where
  "A\<^sub>3 = [(V {}), Unchanged, Unchanged, Unchanged, (V {(1, -1)}), Unchanged, Unchanged, Unchanged, (V {(1, -1), (0, -3)}), Unchanged, Unchanged, Unchanged]"

definition A\<^sub>4 :: "entry list"  where
  "A\<^sub>4 = [(V {}), Unchanged, Unchanged, Unchanged, Unchanged, (V {(0, -1)}), Unchanged, Unchanged, Unchanged, (V {(0, -1), (-3, -3)}), Unchanged, Unchanged]"

definition A\<^sub>5 :: "entry list"  where
  "A\<^sub>5 = [(V {}), Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, (V {(0, -1)}), Unchanged, Unchanged, Unchanged, (V {(0, -1), (-3, -3)}), Unchanged]"

definition A\<^sub>6 :: "entry list"  where
  "A\<^sub>6 = [(V {}), Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, (V {(-3, -3)})]"

(*
| x := 1 {A0};
| y := 1 {A1};
| {A2} LOOP
| y := y - 2; {A3}
| x := x + y {A4}
| {A5}
| UNTIL x < 0
| {A6}
*)

lemma hint:
  "\<lbrakk>continuous f; chain C\<rbrakk> \<Longrightarrow> f (\<Squnion> range C) = \<Squnion> (f `range C)"
proof-
  assume contf: "continuous f"
  assume chainC: "chain C"
  have "(\<forall>C. chain C \<longrightarrow> f (\<Squnion> (range C)) = \<Squnion> (f ` range C))"
    by (simp add: contf continuousD)
  then show "f (\<Squnion> range C) = \<Squnion> (f ` range C)"
    using chainC by blast
qed

lemma lift_chain: "chain C \<Longrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> C x \<le> C y)"
  by (simp add: Defs.chain_def lift_Suc_mono_le)

lemma chain_exists: "x \<le> y \<Longrightarrow> \<exists>C i j. (x = C i \<longrightarrow> y = C j \<longrightarrow> chain C)"
proof(rule ccontr)
  assume assms: "x \<le> y" "\<nexists>C i j. x = C i \<longrightarrow> y = C j \<longrightarrow> chain C"
  then obtain C i j where "C 0 = x \<and> C 1 = y \<and> chain C"
    using Defs.chain_def by fastforce
  with assms show "False"
    by simp
qed

lemma cont_imp_mono:
    fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes "continuous f"
  shows "mono f"
proof
  fix x y :: "'a"
  assume "x \<le> y"
  let ?C = "(\<lambda>n::nat. if n = 0 then x else y)"
  have "\<forall>n. ?C n \<le> ?C (Suc n)"
    using \<open>x \<le> y\<close> by simp
  then have "chain ?C"
    by (simp add: Defs.chain_def)
  then have l: "f (\<Squnion> (range ?C)) = \<Squnion> (f ` range ?C)"
    using assms continuousD by blast
  have "x \<le> \<Squnion> (range ?C)"
    by simp
  then have "f x \<le> f (\<Squnion> (range ?C))"
    using l by auto
  moreover
  have "\<forall>v \<in> range ?C. v \<le> y"
    using \<open>x \<le> y\<close> by fastforce
  then have "y = \<Squnion> (range ?C)"
    using cSup_eq_maximum[of y "range ?C"] by force
  then have "f y = f (\<Squnion> (range ?C))"
    by presburger
  ultimately show "f x \<le> f y"
    by presburger
qed

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
  proof-
    have "(\<forall>n. ?C n \<le> ?C (Suc n))"
      using MONO funpow_decreasing le_SucI by blast
    then show "chain ?C"
      using Defs.chain_def by blast
  qed

  have "mono f"
    by (simp add: MONO)

  show ?thesis
  proof (rule antisym)
    show "\<Squnion> (range ?C) \<le> lfp f"
      by (simp add: Kleene_iter_lpfp MONO SUP_le_iff lfp_greatest)
  next
    have supout: "f (\<Squnion> range ?C) = \<Squnion> (f ` range ?C)"
      using CONT CHAIN continuous_def by blast
    have "\<forall> x \<in> f ` range (\<lambda>i. (f ^^ i) \<bottom>). x \<in> range (\<lambda>i. (f ^^ i) \<bottom>)"
    proof
      fix x
      assume xdef: "x \<in> f ` range (\<lambda>i. (f ^^ i) \<bottom>)"
      then obtain b where bdef: "x = f b" "b \<in> range (\<lambda>i. (f ^^ i) \<bottom>)" by blast
      then obtain i where idef: "b = (f ^^ i) \<bottom>" by blast
      with bdef(1) have "x = f ((f ^^ i) \<bottom>)"
        by simp
      also have "... = (f ^^ (Suc i)) \<bottom>"
        by simp
      finally have "x = (f ^^ (Suc i)) \<bottom>"
        by simp
      then show "x \<in> range (\<lambda>i. (f ^^ i) \<bottom>)"
        by blast
    qed
    then have subset: "f ` range (\<lambda>i. (f ^^ i) \<bottom>) \<subseteq> range (\<lambda>i. (f ^^ i) \<bottom>)"
      by blast
    show "lfp f \<le> Sup (range ?C)"
      apply(rule lfp_lowerbound)
      apply(subst supout)
      apply(rule Sup_subset_mono)
      using subset by simp
    qed
qed

thm lfp_unfold lfp_lowerbound Sup_subset_mono range_eqI

end