theory Submission
  imports Defs
begin

inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"taval (N i) s (Iv i)" |
"taval (V x) s (s x)" |
"taval a1 s (Iv i1) \<Longrightarrow> taval a2 s (Iv i2)
 \<Longrightarrow> taval (Plus a1 a2) s (Iv (i1 + i2))" |
"taval a1 s v1 \<Longrightarrow> taval a2 s v2 \<Longrightarrow> taval (Pair a1 a2) s (Pv v1 v2)" |
"taval p s (Pv v1 v2) \<Longrightarrow> taval (Fst p) s v1" |
"taval p s (Pv v1 v2) \<Longrightarrow> taval (Snd p) s v2"

inductive_cases [elim!]:
  "taval (N i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"
  "taval (Pair a1 a2) s v"
  "taval (Fst p) s v"
  "taval (Snd p) s v"


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
While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |
Swap:   "taval (V x) s (Pv v1 v2) \<Longrightarrow> (SWAP x, s) \<rightarrow> (x ::= Pair (Snd (V x)) (Fst (V x)), s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50) where
Ic_ty: "\<Gamma> \<turnstile> N i : Ity" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
P_ty: "\<Gamma> \<turnstile> a1 : \<tau>\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau>\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> Pair a1 a2 : Pty \<tau>\<^sub>1 \<tau>\<^sub>2" |
Fst_ty: " \<Gamma> \<turnstile> p : Pty \<tau>\<^sub>1 \<tau>\<^sub>2 \<Longrightarrow>  \<Gamma> \<turnstile> Fst p : \<tau>\<^sub>1" |
Snd_ty: " \<Gamma> \<turnstile> p : Pty \<tau>\<^sub>1 \<tau>\<^sub>2 \<Longrightarrow>  \<Gamma> \<turnstile> Snd p : \<tau>\<^sub>2"

declare atyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> N i : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>" "\<Gamma> \<turnstile> Pair a1 a2 : \<tau>" "\<Gamma> \<turnstile> Fst p : \<tau>" "\<Gamma> \<turnstile> Snd p : \<tau>"

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
While_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c" |
Swap_ty: "\<Gamma> \<turnstile> V x : Pty \<tau>\<^sub>1 \<tau>\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> SWAP x"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a" "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"
  "\<Gamma> \<turnstile> SWAP x"

theorem apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> taval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
apply(induction arbitrary: v rule: atyping.induct)
by (fastforce simp: styping_def)+

thm taval.simps
theorem aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. taval a s v"
proof(induction rule: atyping.induct)
  case (Fst_ty \<Gamma> p \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (metis apreservation taval.intros(5) ty.distinct(1) type.elims)
next
  case (Snd_ty \<Gamma> p \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (metis apreservation taval.intros(6) ty.distinct(1) type.elims)
qed(auto intro: taval.intros)

theorem bprogress: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tbval b s v"
proof(induction rule: btyping.induct)
  case (Less_ty \<Gamma> a1 a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2"
    by (metis aprogress)
  then show ?case
  proof (cases v1)
    case Iv
    with Less_ty v show ?thesis
      by (cases v2) (fastforce intro!: tbval.intros dest!:apreservation)+
  next
    case Pv
    then show ?thesis
      using Less_ty.hyps(1) Less_ty.prems apreservation v(1) by fastforce
  qed
qed(auto intro: tbval.intros)

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induction rule: ctyping.induct)
  case Skip_ty thus ?case by simp
next
  case Assign_ty 
  thus ?case by (metis Assign aprogress)
next
  case Seq_ty thus ?case by simp (metis Seq1 Seq2)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where "tbval b s bv" by (metis bprogress)
  show ?case
  proof(cases bv)
    assume "bv"
    with \<open>tbval b s bv\<close> show ?case by simp (metis IfTrue)
  next
    assume "\<not>bv"
    with \<open>tbval b s bv\<close> show ?case by simp (metis IfFalse)
  qed
next
  case While_ty show ?case by (metis While)
next
  case (Swap_ty \<Gamma> x \<tau>\<^sub>1 \<tau>\<^sub>2)
  then have "\<exists>v1 v2. taval (V x) s (Pv v1 v2)"
    by (metis apreservation aprogress ty.distinct(1) type.elims)
  then show ?case by(metis Swap)
qed

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induction rule: small_step_induct)
  case Assign thus ?case
    by (auto simp: styping_def) (metis Assign(1,3) apreservation)
qed auto

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
proof (induct rule: small_step_induct)
  case (Swap x s v1 v2)
  then have "\<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<Gamma> \<turnstile> V x : Pty \<tau>\<^sub>1 \<tau>\<^sub>2"
    by(auto simp: ctyping.intros) (metis V_ty)
  then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where vty: "\<Gamma> \<turnstile> V x : Pty \<tau>\<^sub>1 \<tau>\<^sub>2"
    by presburger
  then have "\<Gamma> \<turnstile> Fst (V x) : \<tau>\<^sub>1" "\<Gamma> \<turnstile> Snd (V x) : \<tau>\<^sub>2"
    using Fst_ty Snd_ty by auto
  then have "\<Gamma> \<turnstile> Pair (Snd (V x)) (Fst (V x)) : Pty \<tau>\<^sub>2 \<tau>\<^sub>1"
    by blast
  then show ?case apply(auto simp: ctyping.intros) sorry
qed(auto simp: ctyping.intros)

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
apply(induction rule:star_induct)
apply (metis progress)
by (metis styping_preservation ctyping_preservation)

end