theory Submission
  imports Defs
begin

inductive_set G :: "string set" where
empty: "[] \<in> G" |
pack: "w \<in> G \<Longrightarrow> (a#w@[b]) \<in> G"



theorem G_is_replicate:
  assumes "w \<in> G"
  shows "\<exists>n. w = replicate n a @ replicate n b"
  
  sorry

theorem replicate_G:
  assumes "w = replicate n a @ replicate n b"
  shows "w \<in> G"
   using assms apply(induction n)
   apply (simp add: G.empty)
 (*apply(induction w, auto intro: G.intros) sledgehammer *)
  sorry

corollary L_eq_G: "L = G"
  unfolding L_def using G_is_replicate replicate_G by auto


type_synonym rstate = "nat \<Rightarrow> int"

fun exec :: "instr \<Rightarrow> rstate \<Rightarrow> rstate"  where
  "exec (LDI i) s = s(0 := i)" |
  "exec (LD n) s = s(0 := s (n+1))" |
  "exec (ST n) s = s((n+1) := s 0)" |
  "exec (ADD n) s = s(0 := (s 0 + s (n+1)))"

fun execs :: "instr list \<Rightarrow> rstate \<Rightarrow> rstate"  where
  "execs [] s = s" |
  "execs (x#xs) s = execs xs (exec x s)"

theorem execs_append[simp]: "\<And>s. execs (xs @ ys) s = execs ys (execs xs s)"
  by(induction xs arbitrary: ys, auto)

fun cmp :: "expr \<Rightarrow> nat \<Rightarrow> instr list"  where
  "cmp (C i) _ = [LDI i]" |
  "cmp (V i) _ = [LD i]" |
  "cmp (A e1 e2) n = (cmp e1 n)@(ST n)#(cmp e2 (n+1))@[ADD (n)]"

value "cmp (A (V 1) (V 2)) 10"

fun maxvar :: "expr \<Rightarrow> nat"  where
  "maxvar (C c) = 0" |
  "maxvar (V i) = i" |
  "maxvar (A e1 e2) = max (maxvar e1) (maxvar e2)"

theorem val_maxvar_same[simp]:
  "\<forall>n \<le> maxvar e. s n = s' n \<Longrightarrow> val e s = val e s'"
  by(induction e, auto)

theorem compiler_correct: "execs (cmp e (maxvar e + 1)) s 0 = val e (s o Suc)"
  apply(induction e) apply(auto) sledgehammer
  sorry

end