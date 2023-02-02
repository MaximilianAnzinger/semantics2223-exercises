theory Check
  imports Submission
begin

lemma inv_plus'_sound: "(inv_plus' (B A) (B A1) (B A2) = (B A1', B A2')) \<Longrightarrow> (i1 \<in> \<gamma>_bounds (B A1)) \<Longrightarrow> (i2 \<in> \<gamma>_bounds (B A2)) \<Longrightarrow> ((case (i1,i2) of
             (None, _) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (_, None) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (Some PInfty, Some MInfty) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (Some MInfty, Some PInfty) \<Rightarrow> None \<in> \<gamma>_bounds (B A)
           | (Some i1, Some i2) \<Rightarrow> Some (i1+i2) \<in> \<gamma>_bounds (B A))) \<Longrightarrow> i1 \<in> \<gamma>_bounds (B A1') \<and> i2 \<in> \<gamma>_bounds (B A2')"
  by (rule Submission.inv_plus'_sound)

lemma inv_less'_sound: "(inv_less' bv (B A1) (B A2) = (B A1',B A2')) \<Longrightarrow> (i1 \<in> \<gamma>_bounds (B A1)) \<Longrightarrow> (i2 \<in> \<gamma>_bounds (B A2)) \<Longrightarrow> ((case (i1,i2) of 
             (None, _) \<Rightarrow> None = bv
           | (_, None) \<Rightarrow> None = bv
           | (Some i1, Some i2) \<Rightarrow> Some (i1<i2) = bv)) \<Longrightarrow> i1 \<in> \<gamma>_bounds (B A1') \<and> i2 \<in> \<gamma>_bounds (B A2')"
  by (rule Submission.inv_less'_sound)

end