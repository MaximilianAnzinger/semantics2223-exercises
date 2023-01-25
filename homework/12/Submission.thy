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



(* Abst_Int0 -------------------- START --------------------*)

(* Abst_Int0 --------------------- END ---------------------*)

(* Abst_Int1 -------------------- START --------------------*)
(* Abst_Int1 --------------------- END ---------------------*)

(* Abst_Int1_parity -------------------- START --------------------*)
(* Abst_Int1_parity --------------------- END ---------------------*)



hide_const (open) None Some

datatype bound = NegInf ("\<infinity>\<^sup>-") | PosInf ("\<infinity>\<^sup>+") | NaN | Real
datatype bounds = B "bound set"

instantiation bounds :: order
begin

definition less_eq_bounds where
"x \<le> y = (case (x, y) of (B x, B y) \<Rightarrow> x \<subseteq> y)"

definition less_bounds where
"x < y = (case (x, y) of (B x, B y) \<Rightarrow> x \<subset> y)"

instance
proof (standard, goal_cases)
  case (1 x y)
  then show ?case unfolding less_bounds_def less_eq_bounds_def by(fastforce split: bounds.splits)
next
  case (2 x)
  then show ?case unfolding less_eq_bounds_def by(simp split: bounds.splits)
next
  case (3 x y z)
  then show ?case unfolding less_eq_bounds_def by(fastforce split: bounds.splits)
next
  case (4 x y)
  then show ?case unfolding less_eq_bounds_def by(fastforce split: bounds.splits)
qed

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