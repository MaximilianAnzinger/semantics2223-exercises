theory Submission
  imports Defs
begin

fun bound :: "com \<Rightarrow> nat" where
"bound SKIP = 0" |
"bound (Assign x a) = 1" |
"bound (Seq c\<^sub>1 c\<^sub>2) = bound c\<^sub>1 + bound c\<^sub>2 + 1" |
"bound (If b c\<^sub>1 c\<^sub>2) = max (bound c\<^sub>1) (bound c\<^sub>2) + 1" |
"bound (While b c) = 0" (* assuming by the assignment this doesn't matter *)

lemma bound_decr: "while_free c \<Longrightarrow> (c, s) \<rightarrow> (c', s') \<Longrightarrow> bound c' < bound c"
by(induction c arbitrary: c' s s' rule: while_free.induct, auto)

end
