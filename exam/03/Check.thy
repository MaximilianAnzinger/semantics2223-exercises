theory Check
  imports Submission
begin

lemma sound: "\<Turnstile> {change_rule x b P} CHANGE x ST b {P}"
  by (rule Submission.sound)

lemma complete: "\<Turnstile> {P} (CHANGE x ST b) {Q} \<Longrightarrow> \<turnstile> {P} CHANGE x ST b {Q}"
  by (rule Submission.complete)  

lemma MINUS_correct:
  "\<turnstile> {\<lambda>s. s=s\<^sub>0} MINUS {\<lambda>s. s ''y'' = - s ''x'' \<and> (\<forall>v \<noteq> ''y''. s v = s\<^sub>0 v)}"
  by (rule Submission.MINUS_correct)

end