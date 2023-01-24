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

definition A\<^sub>7 :: "entry list"  where
  "A\<^sub>7 _ = undefined"

definition A\<^sub>8 :: "entry list"  where
  "A\<^sub>8 _ = undefined"

definition A\<^sub>9 :: "entry list"  where
  "A\<^sub>9 _ = undefined"

hide_const (open) None Some

instantiation bounds :: order
begin

definition less_eq_bounds where
"x \<le> y = (case (x, y) of (B x, B y) \<Rightarrow> x \<subseteq> y)"

definition less_bounds where
"x < y = (case (x, y) of (B x, B y) \<Rightarrow> x \<subset> y)"

instance
  sorry
end

instantiation bounds :: semilattice_sup_top
begin

definition sup_bounds where 
  "sup_bounds _ = undefined"

definition top_bounds where
  "top_bounds = undefined"
 
instance
  sorry
end


fun \<gamma>_bounds :: "bounds \<Rightarrow> val set"  where
  "\<gamma>_bounds _ = undefined"

definition num_bounds :: "ereal \<Rightarrow> bounds"  where
  "num_bounds _ = undefined"

fun plus_bounds :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds"  where
  "plus_bounds _ = undefined"

global_interpretation Val_semilattice
where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
  sorry

global_interpretation Abs_Int
where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
defines aval_bounds = aval' and step_bounds = step' and AI_bounds = AI
  sorry


global_interpretation Abs_Int_mono
  where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
  sorry

fun m_bounds :: "bounds \<Rightarrow> nat"  where
  "m_bounds _ = undefined"

abbreviation h_bounds :: nat where 
  "h_bounds = undefined"

global_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
and m = m_bounds and h = h_bounds
  sorry

end