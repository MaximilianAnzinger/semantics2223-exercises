theory Submission
  imports Defs
begin

fun inv_plus' :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds \<Rightarrow> (bounds * bounds)"  where
  "inv_plus' _ = undefined"

fun inv_less' :: "bool option \<Rightarrow> bounds \<Rightarrow> bounds \<Rightarrow> (bounds * bounds)"  where
  "inv_less' _ = undefined"

value "inv_plus' (B {NaN}) (B {\<infinity>\<^sup>+}) (B {\<infinity>\<^sup>-, Real}) = (B {\<infinity>\<^sup>+}, B {\<infinity>\<^sup>-})"
value "inv_plus' (B {\<infinity>\<^sup>+,\<infinity>\<^sup>-}) (B {\<infinity>\<^sup>+, NaN}) (B {\<infinity>\<^sup>-, Real, \<infinity>\<^sup>+}) = (B {\<infinity>\<^sup>+}, B {\<infinity>\<^sup>+, Real})"
value "inv_less' (Some True) (B {\<infinity>\<^sup>+, \<infinity>\<^sup>-}) (B {\<infinity>\<^sup>+}) = (B {\<infinity>\<^sup>-}, B {\<infinity>\<^sup>+})"

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
  sorry

lemma inv_less'_sound:
    assumes "inv_less' bv (B A1) (B A2) = (B A1',B A2')"
      and "i1 \<in> \<gamma>_bounds (B A1)"
      and "i2 \<in> \<gamma>_bounds (B A2)"
      and "(case (i1,i2) of 
             (None, _) \<Rightarrow> None = bv
           | (_, None) \<Rightarrow> None = bv
           | (Some i1, Some i2) \<Rightarrow> Some (i1<i2) = bv)"
  shows "i1 \<in> \<gamma>_bounds (B A1') \<and> i2 \<in> \<gamma>_bounds (B A2')"
  sorry

end