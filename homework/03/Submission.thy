theory Submission
  imports Defs
begin

inductive_set G :: "string set" where
empty: "[] \<in> G" |
pack: "w \<in> G \<Longrightarrow> (a#w@[b]) \<in> G"

lemma G_inv: "w \<in> G \<Longrightarrow> w = (a#w'@[b]) \<Longrightarrow> w' \<in> G"
  using G.cases by blast

theorem G_is_replicate:
  assumes "w \<in> G"
  shows "\<exists>n. w = replicate n a @ replicate n b"
using assms proof(induction rule: G.induct)
  case empty
  then show ?case
    by simp
next
  case (pack w)
  obtain n' where "w = replicate n' a @ replicate n' b"
    using pack.IH by blast
  then have "a # w @ [b] = a # replicate n' a @ replicate n' b @ [b]"
    by force
  then have "a # w @ [b] = replicate (n' + 1) a @ replicate (n' + 1) b"
    by (simp add: replicate_append_same)
  then show ?case
    by blast
qed

lemma rep_suc: "replicate (Suc n) a @ replicate (Suc n) b = a # replicate n a @ replicate n b @ [b]"
  by (simp add: replicate_append_same)

theorem replicate_G:
  assumes "w = replicate n a @ replicate n b"
  shows "w \<in> G"
  using assms proof(induction n arbitrary: w)
  case 0
  then show ?case
    by (simp add: G.empty)
next
  case (Suc n)
  from Suc.IH have w': "(replicate n a @ replicate n b) \<in> G"
    by blast
  from Suc.IH w' have "a # replicate n a @ replicate n b @ [b] \<in> G" using G.pack
    by fastforce
  then have "w \<in> G"
    using rep_suc Suc.prems by presburger
  thus ?case.
qed

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
  "cmp (A e1 e2) n = (cmp e1 n)@(ST (n))#(cmp e2 (n+1))@[ADD (n)]"

value "cmp (A (V 1) (V 2)) 10"

fun maxvar :: "expr \<Rightarrow> nat"  where
  "maxvar (C c) = 0" |
  "maxvar (V i) = i" |
  "maxvar (A e1 e2) = max (maxvar e1) (maxvar e2)"

theorem val_maxvar_same[simp]:
  "\<forall>n \<le> maxvar e. s n = s' n \<Longrightarrow> val e s = val e s'"
  by(induction e, auto)

lemma cmp_n_same[simp]: "\<forall>i \<le> n. 0 < i \<longrightarrow> execs (cmp e n) s i = s i"
  by(induction e n arbitrary: s rule: cmp.induct, auto)

lemma cmp_maxvar_same[simp]:
  "\<forall>n > maxvar e. \<forall>i \<le> maxvar e. 0 < i \<longrightarrow> execs (cmp e n) s i = s i"
  by(induction e arbitrary: s, auto)

lemma compiler_correct_free_reg: "\<forall>n > maxvar e. execs (cmp e n) s 0 = val e (s o Suc)"
  by(induction e arbitrary: s, auto)

theorem compiler_correct: "execs (cmp e (maxvar e + 1)) s 0 = val e (s o Suc)"
  using compiler_correct_free_reg less_add_one by blast

end