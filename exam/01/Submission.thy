theory Submission
  imports Defs
begin

lemma count_simp:  "count as = x \<Longrightarrow> count bs = y \<Longrightarrow> count (as@bs) = x + y"
by(induction as arbitrary: x bs y rule: count.induct, auto)

lemma ins_false: "count as = 0 \<Longrightarrow> count bs = 0 \<Longrightarrow> count (as @ False # bs) = -1"
  using count_simp by(induction as arbitrary: bs rule: count.induct, auto)

lemma ins_true: "count as = 0 \<Longrightarrow> count bs = 0 \<Longrightarrow> count (as @ True # bs) = 1"
  using count_simp by(induction as arbitrary: bs rule: count.induct, auto)

lemma ok_count_Zero: "ok bs \<Longrightarrow> count bs = 0"
apply(induction bs rule: ok.induct) using ins_false by auto

end
