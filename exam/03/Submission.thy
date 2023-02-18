theory Submission
  imports Defs
begin

abbreviation (input) change_rule :: "vname \<Rightarrow> bexp \<Rightarrow> assn \<Rightarrow> assn" where
"change_rule x b P \<equiv> \<lambda>s. \<exists>x'. (bval b (s[x'/x]) \<and> P (s[x'/x]))"

inductive
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip: "\<turnstile> {P} SKIP {P}"  |

Assign:  "\<turnstile> {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile> {P} c\<^sub>1 {Q};  \<turnstile> {Q} c\<^sub>2 {R} \<rbrakk>
      \<Longrightarrow> \<turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"  |

If: "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
     \<Longrightarrow> \<turnstile> {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |

While: "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow>
        \<turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"  |

Swap: "\<turnstile> {\<lambda>s. P (s(x:=s y,y:=s x))} SWAP x y {P}" |

Change: "\<turnstile> {change_rule x b P} CHANGE x ST b {P}" |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> {P'} c {Q'}"

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P'} c {Q}"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> {P} c {Q'}"
by (blast intro: conseq)


lemma sound: "\<Turnstile> {change_rule x b P} CHANGE x ST b {P}" nitpick
  sorry

lemma complete: "\<Turnstile> {P} (CHANGE x ST b) {Q} \<Longrightarrow> \<turnstile> {P} CHANGE x ST b {Q}"
  sorry

value "(Not (Less (Plus (V ''y'') (V ''x'')) (N 0)))"
value "(Not (Less (N 0) (Plus (V ''y'') (V ''x''))))"
definition MINUS :: com where
 "MINUS = (
  CHANGE ''y'' ST (And
  (Not (Less (Plus (V ''y'') (V ''x'')) (N 0)))
  (Not (Less (N 0) (Plus (V ''y'') (V ''x''))))
)
)"

lemma MINUS_correct:
  "\<turnstile> {\<lambda>s. s=s\<^sub>0} MINUS {\<lambda>s. s ''y'' = - s ''x'' \<and> (\<forall>v \<noteq> ''y''. s v = s\<^sub>0 v)}"
  unfolding MINUS_def
  sorry

definition invar :: "vname \<Rightarrow> bexp \<Rightarrow> vname \<Rightarrow> state \<Rightarrow> assn" where
  "invar x b y s\<^sub>0 = undefined"

end