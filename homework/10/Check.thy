theory Check
  imports Submission
begin

theorem SQUARE_correct: "\<turnstile> {\<lambda>s. s ''n'' \<ge> 0 \<and> s=s\<^sub>0} SQUARE {\<lambda>s. s ''a'' = s\<^sub>0 ''n'' * s\<^sub>0 ''n''}"
  by (rule Submission.SQUARE_correct)

end