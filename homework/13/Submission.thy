theory Submission
  imports Defs
begin

fun inv_plus'_filter :: "bound \<Rightarrow> bound \<Rightarrow> bound \<Rightarrow> bool"  where
  "inv_plus'_filter NegInf NegInf NegInf = True" |
  "inv_plus'_filter NegInf NegInf Real = True" |
  "inv_plus'_filter NegInf Real NegInf = True" |
  "inv_plus'_filter PosInf PosInf PosInf = True" |
  "inv_plus'_filter PosInf PosInf Real = True" |
  "inv_plus'_filter PosInf Real PosInf = True" |
  "inv_plus'_filter NaN NegInf PosInf = True" |
  "inv_plus'_filter NaN PosInf NegInf = True" |
  "inv_plus'_filter NaN NaN _ = True" |
  "inv_plus'_filter NaN _ NaN = True" |
  "inv_plus'_filter Real Real Real = True" |
  "inv_plus'_filter _ _ _ = False"

fun inv_plus' :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds \<Rightarrow> (bounds * bounds)"  where
  "inv_plus' (B b) (B b1) (B b2) = 
  (B {bb1 \<in> b1. \<exists>bb \<in> b. \<exists>bb2 \<in> b2. inv_plus'_filter bb bb1 bb2},
  B {bb2 \<in> b2. \<exists>bb \<in> b. \<exists>bb1 \<in> b1. inv_plus'_filter bb bb1 bb2})"

fun inv_less'_helper :: "bool \<Rightarrow> bound \<Rightarrow> bound \<Rightarrow> (bound * bound) option" where
  "inv_less'_helper _ NaN _ = None" |
  "inv_less'_helper _ _ NaN = None" |
  "inv_less'_helper _ Real Real = Some (Real, Real)" |
  "inv_less'_helper True PosInf _ = None" |
  "inv_less'_helper True x PosInf = Some (x, PosInf)" |
  "inv_less'_helper True _ NegInf = None" |
  "inv_less'_helper True NegInf x = Some (NegInf, x)" |
  "inv_less'_helper False PosInf x = Some (PosInf, x)" |
  "inv_less'_helper False _ PosInf = None" |
  "inv_less'_helper False x NegInf = Some (x, NegInf)" |
  "inv_less'_helper False NegInf _ = None"

fun inv_less'_filter :: "bool option \<Rightarrow> bound \<Rightarrow> bound \<Rightarrow> bool" where
  "inv_less'_filter None NaN _ = True" |
  "inv_less'_filter None _ NaN = True" |
  "inv_less'_filter (Some _) NaN _ = False" |
  "inv_less'_filter (Some _) _ NaN = False" |
  "inv_less'_filter (Some _) Real Real = True" |
  "inv_less'_filter (Some True) PosInf _ = False" |
  "inv_less'_filter (Some True) _ PosInf = True" |
  "inv_less'_filter (Some True) _ NegInf = False" |
  "inv_less'_filter (Some True) NegInf _ = True" |
  "inv_less'_filter (Some False) PosInf _ = True" |
  "inv_less'_filter (Some False) _ NegInf = True" |
  "inv_less'_filter _ _ _ = False"

fun inv_less' :: "bool option \<Rightarrow> bounds \<Rightarrow> bounds \<Rightarrow> (bounds * bounds)"  where
  "inv_less' b (B b1) (B b2) = 
  (B {bb1 \<in> b1. \<exists>bb2 \<in> b2. inv_less'_filter b bb1 bb2},
  B {bb2 \<in> b2. \<exists>bb1 \<in> b1. inv_less'_filter b bb1 bb2})"

value "inv_plus' (B {NaN}) (B {\<infinity>\<^sup>+}) (B {\<infinity>\<^sup>-, Real}) = (B {\<infinity>\<^sup>+}, B {\<infinity>\<^sup>-})"
value "inv_plus' (B {\<infinity>\<^sup>+,\<infinity>\<^sup>-}) (B {\<infinity>\<^sup>+, NaN}) (B {\<infinity>\<^sup>-, Real, \<infinity>\<^sup>+}) = (B {\<infinity>\<^sup>+}, B {\<infinity>\<^sup>+, Real})"
value "inv_less' (Some True) (B {\<infinity>\<^sup>+, \<infinity>\<^sup>-}) (B {\<infinity>\<^sup>+}) = (B {\<infinity>\<^sup>-}, B {\<infinity>\<^sup>+})"

lemma inv_plus'_sub:
  assumes "inv_plus' (B A) (B A1) (B A2) = (B A1', B A2')"
  shows "A1' \<subseteq> A1" "A2' \<subseteq> A2" using assms by auto

lemma inv_plus'_sound:
    assumes "inv_plus' (B A) (B A1) (B A2) = (B A1', B A2')"
      and "i1 \<in> \<gamma>_bounds (B A1)"
      and "i2 \<in> \<gamma>_bounds (B A2)"
      and "(case (i1,i2) of
             (None, _) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (_, None) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (Some PInfty, Some MInfty) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (Some MInfty, Some PInfty) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (Some i1, Some i2) \<Rightarrow> Some (i1+i2) \<in> \<gamma>_bounds (B A))"
    shows "i1 \<in> \<gamma>_bounds (B A1') \<and> i2 \<in> \<gamma>_bounds (B A2')"
  apply(cases i1; cases i2)
proof(goal_cases)
  case 1
  with assms show ?case by fastforce
next
  case (2 a)
  with assms show ?case by fastforce
next
  case (3 a)
  with assms(4) have "None \<in> \<gamma>_bounds (B A)" by(cases a, auto)
  then have "NaN \<in> A" by auto
  with assms have "NaN \<in> A2'"
    apply (auto simp: 3(2))
    using \<gamma>_bound.cases inv_plus'_filter.simps by metis
  with 3(2) have "i2 \<in> \<gamma>_bounds (B A2')" by auto
  moreover
  have "\<forall>x. inv_plus'_filter NaN x NaN"
    using inv_plus'_filter.elims(3) by blast
  then have "\<forall>x. \<exists>bb \<in> A. \<exists>bb2 \<in> A2. inv_plus'_filter bb x bb2"
    using \<open>NaN \<in> A\<close> \<open>NaN \<in> A2'\<close>  inv_plus'_sub assms(1) by blast
  then obtain v where v_def: 
    "v = (case a of ereal r \<Rightarrow> Real | PInfty \<Rightarrow> PosInf | MInfty \<Rightarrow> NegInf)" by blast
  with assms 3 have "v \<in> A1" by(cases a, auto)
  then have "v \<in> A1'"
    using assms(1) \<open>\<forall>x. \<exists>bb \<in> A. \<exists>bb2 \<in> A2. inv_plus'_filter bb x bb2\<close> by auto
  then have "i1 \<in> \<gamma>_bounds (B A1')" by(cases a, auto simp: v_def 3(1))
  ultimately show ?case by simp
next
  case (4 a aa)
  with assms show ?case apply(cases a; cases aa, auto)
    using inv_plus'_filter.simps by blast+
qed

lemma inv_less'_sub:
  assumes "inv_less' bv (B A1) (B A2) = (B A1', B A2')"
  shows "A1' \<subseteq> A1" "A2' \<subseteq> A2" using assms by auto

lemma inv_less'_sound:
    assumes "inv_less' bv (B A1) (B A2) = (B A1',B A2')"
      and "i1 \<in> \<gamma>_bounds (B A1)"
      and "i2 \<in> \<gamma>_bounds (B A2)"
      and "(case (i1,i2) of 
             (None, _) \<Rightarrow> None = bv
           | (_, None) \<Rightarrow> None = bv
           | (Some i1, Some i2) \<Rightarrow> Some (i1<i2) = bv)"
  shows "i1 \<in> \<gamma>_bounds (B A1') \<and> i2 \<in> \<gamma>_bounds (B A2')" using assms
 apply(cases i1; cases i2)
proof(goal_cases)
  case 1
  with assms show ?case by fastforce
next
  case (2 a)
  with assms show ?case by fastforce
next
  case (3 a)
  with assms(4) have "None = bv" by(cases a, auto)
  with assms have "NaN \<in> A2'"
    apply (auto simp: 3(10))
    using \<gamma>_bound.cases inv_less'_filter.simps by metis
  with 3(10) have "i2 \<in> \<gamma>_bounds (B A2')" by auto
  moreover
  have "\<forall>x. inv_less'_filter None x NaN"
    using inv_less'_filter.elims(3) by blast
  then have "\<forall>x. \<exists>bb2 \<in> A2. inv_less'_filter bv x bb2"
    using \<open>None = bv\<close> \<open>NaN \<in> A2'\<close>  inv_less'_sub assms(1) by blast
  then obtain v where v_def: 
    "v = (case a of ereal r \<Rightarrow> Real | PInfty \<Rightarrow> PosInf | MInfty \<Rightarrow> NegInf)" by blast
  with assms 3 have "v \<in> A1" by(cases a, auto)
  then have "v \<in> A1'"
    using assms(1) \<open>\<forall>x. \<exists>bb2 \<in> A2. inv_less'_filter bv x bb2\<close> by auto
  then have "i1 \<in> \<gamma>_bounds (B A1')" by(cases a, auto simp: v_def 3(5))
  ultimately show ?case by simp
next
  case (4 a aa)
  with assms show ?case apply(cases a; cases aa, auto)
    using inv_less'_filter.simps by blast+
qed

end