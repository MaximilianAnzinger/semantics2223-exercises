theory Chapter12_5a
imports "HOL-IMP.Hoare"
begin
definition hoare_tvalid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q}  \<longleftrightarrow>  (\<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q t))"
text\<open>
\exercise
An alternative version of the \<open>WHILE\<close> rule indexes the invariant
by a natural number that must goes down by one with every iteration:
\<close>
inductive
  hoaret :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>t {P} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>t {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1 {P\<^sub>2}; \<turnstile>\<^sub>t {P\<^sub>2} c\<^sub>2 {P\<^sub>3} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |

If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q}; \<turnstile>\<^sub>t {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>t {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |
While:
  "\<lbrakk> \<And>n::nat. \<turnstile>\<^sub>t {P (Suc n)} c {P n};
     \<forall>n s. P (Suc n) s \<longrightarrow> bval b s;  \<forall>s. P 0 s \<longrightarrow> \<not> bval b s \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>s. \<exists>n. P n s} WHILE b DO c {P 0}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"

text\<open>
Prove soundness and completeness of this alternative set of rules.
For the completeness proof it may be helpful to define a recursive function
\<open>wpw ::\<close> @{typ "bexp \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> assn \<Rightarrow> assn"} such that
@{term "wpw b c n Q"} is the weakest precondition such that @{term "WHILE b DO c"}
terminates after \<open>n\<close> iterations in a state satisfying \<open>Q\<close>.
\<close>
(* your definition/proof here *)
corollary hoaret_sound_complete: "\<turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> \<Turnstile>\<^sub>t {P}c{Q}"
by (metis hoaret_sound hoaret_complete)
end
