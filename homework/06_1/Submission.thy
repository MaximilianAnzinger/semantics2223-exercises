theory Submission
  imports Defs
begin

inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"taval (N i) s (Iv i)" |
"taval (V x) s (s x)" |
"taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2)
 \<Longrightarrow> taval (Plus a1 a2) s (Iv (i1 + i2))"

inductive_cases [elim!]:
  "taval (N i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"


inductive tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
"tbval (Bc v) s v" |
"tbval b s bv \<Longrightarrow> tbval (Not b) s (\<not> bv)" |
"tbval b1 s bv1 \<Longrightarrow> tbval b2 s bv2 \<Longrightarrow> tbval (And b1 b2) s (bv1 \<and> bv2)" |
"taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2) \<Longrightarrow> tbval (Less a1 a2) s (i1 < i2)"


inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55) 
where
Assign:  "taval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |
Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |
IfTrue:  "tbval b s True \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "tbval b s False \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |
While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50) where
Ic_ty: "\<Gamma> \<turnstile> N i : Ity" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x"


declare atyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> N i : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>"

inductive btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<turnstile>" 50) where
B_ty: "\<Gamma> \<turnstile> Bc v" |
Not_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> Not b" |
And_ty: "\<Gamma> \<turnstile> b1 \<Longrightarrow> \<Gamma> \<turnstile> b2 \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2" |
Less_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2"


declare btyping.intros [intro!]
inductive_cases [elim!]: "\<Gamma> \<turnstile> Not b" "\<Gamma> \<turnstile> And b1 b2" "\<Gamma> \<turnstile> Less a1 a2"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"


declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a" "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

theorem apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> taval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
  sorry

theorem aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. taval a s v"
  sorry

theorem bprogress: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tbval b s v"
  sorry

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
  sorry

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
  sorry

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
  sorry

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
  sorry

end