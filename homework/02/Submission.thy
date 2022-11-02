theory Submission
  imports Defs
begin

fun rlenc :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) list"  where
  "rlenc v c [] = [(v, c)]" |
  "rlenc v c (x#xs) = (if v = x then rlenc v (c + 1) xs else (v, c) # rlenc x 1 xs)"

value "replicate (3::nat) (1::nat) = [1,1,1]"

value "rlenc 0 0 ([1,3,3,8] :: int list) = [(0,0),(1,1),(3,2),(8,1)]"
value "rlenc 1 0 ([3,4,5] :: int list) = [(1,0),(3,1),(4,1),(5,1)]"

fun rldec :: "('a \<times> nat) list \<Rightarrow> 'a list"  where
  "rldec [] = []" |
  "rldec ((v, c)#xs) = (replicate c v)@(rldec xs)"

lemma enc_dec_prep_same: " rldec (rlenc a (Suc c) l) = a # replicate c a @ l"
  apply(induction l arbitrary: a c) by(auto simp: replicate_append_same)

theorem enc_dec: "rldec (rlenc a 0 l) = l"
  apply(induction l arbitrary: a) by(auto simp: enc_dec_prep_same)

fun normal :: "aexp \<Rightarrow> bool"  where
  "normal (Plus a\<^sub>1 a\<^sub>2) = (normal a\<^sub>1 \<and> normal a\<^sub>2)"|
  "normal (Mult i a) = (case a of V x \<Rightarrow> True | _ \<Rightarrow> False)" |
  "normal _ = True"

fun normalize :: "aexp \<Rightarrow> aexp"  where
  "normalize (N n) = N n" |
  "normalize (V x) = V x" |
  "normalize (Plus a\<^sub>1 a\<^sub>2) = Plus (normalize a\<^sub>1) (normalize a\<^sub>2)" |
  "normalize (Mult i a) =
    (case a of
      V x \<Rightarrow> Mult i (V x) |
      N n \<Rightarrow> N (i * n) |
      Plus a\<^sub>1 a\<^sub>2 \<Rightarrow> Plus (normalize (Mult i a\<^sub>1)) (normalize (Mult i a\<^sub>2)) |
      Mult i' a' \<Rightarrow> normalize (Mult (i * i') a')
    )"

theorem semantics_unchanged: "aval (normalize a) s = aval a s"
  apply(induction a rule: normalize.induct) by(auto split: aexp.splits)

theorem normalize_normalizes: "normal (normalize a)"
  apply(induction a rule: normalize.induct) by(auto split: aexp.splits)

end