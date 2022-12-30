theory Check
  imports Submission
begin

theorem hoare_sound: "\<turnstile>{I} {P}c{Q} \<Longrightarrow> \<Turnstile>\<^sub>c{I} {P}c{Q}"
  by (rule Submission.hoare_sound)

lemma hoare_complete: "(\<Turnstile> {P}c{Q}) \<Longrightarrow> \<turnstile>{Q} {P}c{Q}"
  by (rule Submission.hoare_complete)

theorem hoare_sound_complete: "\<turnstile>{Q} {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
  by (rule Submission.hoare_sound_complete)

end