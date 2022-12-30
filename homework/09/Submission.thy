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
While: "\<turnstile>{P} {\<lambda>s. P s \<and> bval b s} c {\<lambda>s. P s} \<Longrightarrow>
        \<turnstile>{I} {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"  |
Continue: "\<turnstile>{I} {I} CONTINUE {P}"
\<comment> \<open>Add your cases here\<close>

lemmas [simp] = hoare.Skip hoare.Assign hoare.Seq If

lemmas [intro!] = hoare.Skip hoare.Assign hoare.Seq hoare.If

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile>{I} {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>{I} {P'} c {Q}"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile>{I} {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile>{I} {P} c {Q'}"
  by (blast intro: conseq)

theorem hoare_sound: "\<turnstile>{I} {P} c {Q} \<Longrightarrow> \<Turnstile>\<^sub>c{I} {P} c {Q}"
proof(induction rule: hoare.induct)
  case (While P b c I)
  have "(WHILE b DO c,s) \<Rightarrow> (f, t)  \<Longrightarrow>  P s  \<Longrightarrow>  P t \<and> \<not> bval b t" for s f t
  proof(induction "WHILE b DO c" s f t rule: big_step_induct)
    case WhileFalse thus ?case by blast
  next
    case WhileTrue thus ?case
      using While.IH unfolding hoare_valid_def
      by (simp add: hoare_valid\<^sub>c_def)
  qed
  moreover have "(WHILE b DO c,s) \<Rightarrow> (f, t) \<Longrightarrow> f = False" for s f t
   proof(induction "WHILE b DO c" s f t rule: big_step_induct)
    case WhileFalse thus ?case by blast
  next
    case WhileTrue thus ?case
      using While.IH unfolding hoare_valid_def
      by (simp add: hoare_valid\<^sub>c_def)
  qed
  ultimately show ?case unfolding hoare_valid\<^sub>c_def by fastforce
qed (fastforce simp: hoare_valid\<^sub>c_def)+

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile>{I} {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

lemma While':
assumes "\<turnstile>{P} {\<lambda>s. P s \<and> bval b s} c {P}" and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile>{I} {P} WHILE b DO c {Q}"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn \<Rightarrow> assn"  where
  "wp c I Q = (\<lambda>s. \<forall>f t. (c,s) \<Rightarrow> (f, t)  \<longrightarrow>  (if f then I t else Q t))"

lemma wp_SKIP[simp]: "wp SKIP I Q = Q"
by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) I Q = (\<lambda>s. Q(s[a/x]))"
by (rule ext) (auto simp: wp_def)

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) I Q = wp c\<^sub>1 I (wp c\<^sub>2 I Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) I Q =
 (\<lambda>s. if bval b s then wp c\<^sub>1 I Q s else wp c\<^sub>2 I Q s)"
by (rule ext) (auto simp: wp_def)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) I Q s = wp c (wp (WHILE b DO c) I Q) (wp (WHILE b DO c) I Q) s"
using WhileTrue wp_def by auto

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) I Q s = Q s"
  using WhileFalse wp_def by auto

lemma wp_Continue[simp]: "wp (CONTINUE) I Q = I"
  using wp_def by auto

lemma wp_is_pre: "\<turnstile>{I} {wp c I Q} c {Q}"
proof(induction c arbitrary: I Q)
  case If thus ?case
    by (smt (z3) conseq hoare.If wp_If)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  show "\<turnstile>{I} {wp ?w I Q} ?w {Q}"
  proof(rule While')
    show "\<turnstile>{wp ?w I Q} {\<lambda>s. wp ?w I Q s \<and> bval b s} c {wp ?w I Q}"
    proof(rule strengthen_pre[OF _ While.IH])
      show "\<forall>s. wp ?w I Q s \<and> bval b s \<longrightarrow> wp c (wp ?w I Q) (wp ?w I Q) s" by auto
    qed
    show "\<forall>s. wp ?w I Q s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
  qed
next case CONTINUE show ?case by (simp add: hoare.Continue)
qed auto

lemma hoare_complete: assumes "\<Turnstile> {P}c{Q}"
  shows "\<turnstile>{Q} {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "\<turnstile>{Q} {wp c Q Q} c {Q}" by(rule wp_is_pre)
qed

theorem hoare_sound_complete: "\<turnstile>{Q} {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
  by (metis hoare_complete hoare_sound hoare_valid\<^sub>c_def hoare_valid_def)

end