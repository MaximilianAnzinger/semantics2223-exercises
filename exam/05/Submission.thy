theory Submission
  imports Defs
begin

fun less_eq_bits :: "bits \<Rightarrow> bits \<Rightarrow> bool" (infix "\<le>" 50) where
   "(B a::bits) \<le> (B b) = (a \<le> b)" |
   "_ \<le> Any = True" |
   "Any \<le> (B _) = False"

fun sup_bits :: "bits \<Rightarrow> bits \<Rightarrow> bits" (infix "\<squnion>" 50) where
  "_ \<squnion> Any = Any" |
  "Any \<squnion> _ = Any" |
  "B\<^sub>1 \<squnion> B\<^sub>2 = (if B\<^sub>1 \<le> B\<^sub>2 then B\<^sub>2 else B\<^sub>1)"

(* answer as boolean: *)
definition is_complete_lattice :: bool where
  "is_complete_lattice = True"

fun plus'_bits :: "nat \<Rightarrow> bits \<Rightarrow> bits \<Rightarrow> bits" where
  "plus'_bits _ = undefined"


definition A\<^sub>0 :: "entry list" where "A\<^sub>0=[None, Some (B 1), Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"
definition A\<^sub>1 :: "entry list" where "A\<^sub>1=[None, Unchanged, Some (B 1), Unchanged, Unchanged, Some Any, Unchanged, Unchanged]"
definition A\<^sub>2 :: "entry list" where "A\<^sub>2=[None, Unchanged, Unchanged, Some (B 1), Unchanged, Unchanged, Some Any, Unchanged]"
definition A\<^sub>3 :: "entry list" where "A\<^sub>3=[None, Unchanged, Unchanged, Unchanged, Some (B 2), Unchanged, Unchanged, Some Any]"
definition A\<^sub>4 :: "entry list" where "A\<^sub>4=[None, Unchanged, Unchanged, Some (B 1), Unchanged, Unchanged, Some Any, Unchanged]"


fun inv_plus'_bits :: "bits \<Rightarrow> bits \<Rightarrow> bits \<Rightarrow> (bits * bits)" where
  "inv_plus'_bits _ (B 0) _ = (B 0, B 0)" |
  "inv_plus'_bits _ _ (B 0) = (B 0, B 0)" |
  "inv_plus'_bits _ _ _ = undefined"

fun inv_less'_bits :: "bool \<Rightarrow> bits \<Rightarrow> bits \<Rightarrow> (bits * bits)" where
  "inv_less'_bits _ (B 0) _ = (B 0, B 0)" |
  "inv_less'_bits _ _ (B 0) = (B 0, B 0)" 

end
