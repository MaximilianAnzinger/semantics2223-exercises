theory Tut05
  imports "HOL-IMP.Big_Step"
begin

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "Or b1 b2 = Not (And (Not b1) (Not b2))"

lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
proof(rule allI)+
  fix s t
  show "(IF And b1 b2 THEN c1 ELSE c2, s) \<Rightarrow> t = (IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2, s) \<Rightarrow> t"
  proof
    assume "(IF And b1 b2 THEN c1 ELSE c2, s) \<Rightarrow> t"
    then show "(IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2, s) \<Rightarrow> t"
      by(cases rule: big_step.cases, auto)
  next
    assume "(IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2, s) \<Rightarrow> t"
    then show "(IF And b1 b2 THEN c1 ELSE c2, s) \<Rightarrow> t"
      by(cases rule: big_step.cases, auto)
  qed
qed

lemma while_end: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not>bval b t"
  by(induction "WHILE b DO c" s t rule: big_step_induct, auto)

lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c"
  using while_end unfolding Or_def by force

fun deskseq :: "com \<Rightarrow> com \<Rightarrow> com" where
  "deskseq SKIP c = c" |
  "deskseq c SKIP = c" |
  "deskseq c1 c2 = c1;;c2"

fun deskif :: "bexp \<Rightarrow> com \<Rightarrow> com \<Rightarrow> com" where
  "deskif _ SKIP SKIP = SKIP" |
  "deskif b c1 c2 = IF b THEN c1 ELSE c2"

fun deskip :: "com \<Rightarrow> com"  where
  "deskip (c1;;c2) = deskseq (deskip c1) (deskip c2)" |
  "deskip (IF b THEN c1 ELSE c2) = deskif b (deskip c1) (deskip c2)" |
  "deskip (WHILE b DO c) = WHILE b DO (deskip c)" |
  "deskip c = c"

lemma deskseq_sim: "deskseq c1 c2 \<sim> c1;;c2"
  by(cases c1; cases c2, auto)

lemma deskif_sim: "deskif b c1 c2 \<sim> IF b THEN c1 ELSE c2"
  by(cases c1; cases c2, auto)

lemma "deskip c \<sim> c"
proof(induction c)
  case (Seq c1 c2)
  then show ?case using deskseq_sim by auto
next
  case (If x1 c1 c2)
  then show ?case using deskif_sim by auto
next
  case (While x1 c)
  then show ?case
    using sim_while_cong_aux by fastforce
qed auto


end