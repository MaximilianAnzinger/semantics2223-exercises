theory Submission
  imports Defs
begin

inductive
  hoare :: "assn \<Rightarrow> assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>{(1_)}/ ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip: "\<turnstile>{I} {P} SKIP {P}"  |
Assign:  "\<turnstile>{I} {\<lambda>s. P(s[a/x])} x::=a {P}"  |
Seq: "\<lbrakk> \<turnstile>{I} {P} c\<^sub>1 {Q};  \<turnstile>{I} {Q} c\<^sub>2 {R} \<rbrakk>
      \<Longrightarrow> \<turnstile>{I} {P} c\<^sub>1;;c\<^sub>2 {R}"  |
If: "\<lbrakk> \<turnstile>{I} {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q};  \<turnstile>{I} {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
     \<Longrightarrow> \<turnstile>{I} {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |
conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile>{I} {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile>{I} {P'} c {Q'}" |
While: "\<turnstile>{I} {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow>
        \<turnstile>{I} {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"  |
Continue: ""
\<comment> \<open>Add your cases here\<close>
theorem hoare_sound: "\<turnstile>{I} {P}c{Q} \<Longrightarrow> \<Turnstile>\<^sub>c{I} {P}c{Q}"
  sorry

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn"  where
  "wp _ = undefined"

lemma hoare_complete: assumes "\<Turnstile> {P}c{Q}"
  shows "\<turnstile>{Q} {P}c{Q}"
  sorry

theorem hoare_sound_complete: "\<turnstile>{Q} {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
  sorry

end