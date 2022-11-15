theory Tut04
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma conv_evSS: "ev (Suc (Suc n)) \<Longrightarrow> ev n"
proof -
  assume "ev (Suc (Suc n))" then show "ev n"
  proof (cases)
    txt \<open>\qquad ...\<close> qed
qed

inductive_cases evSS_elim: "ev (Suc (Suc n))"

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))"
  then have "ev (Suc 0)" using conv_evSS
    by blast
  then show False
    using ev.cases by blast
qed

type_synonym ('q,'l) lts = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"

inductive word :: "('q,'l) lts \<Rightarrow> 'q \<Rightarrow> 'l list \<Rightarrow> 'q \<Rightarrow> bool" for \<delta> where
  empty: "word \<delta> p [] p" |
  app: "\<delta> p x q \<Longrightarrow> word \<delta> q xs r \<Longrightarrow> word \<delta> p (x#xs) r"

definition "det \<delta> \<equiv> \<forall>p l q1 q2. \<delta> p l q1 \<and> \<delta> p l q2 \<longrightarrow> q1 = q2"

lemma 
  assumes det: "det \<delta>"
  shows "word \<delta> p ls q \<Longrightarrow> word \<delta> p ls q' \<Longrightarrow> q = q'"
  using assms proof(induction ls arbitrary: p q q')
  case Nil
  from Nil.prems(1)  have "p = q"
    using word.cases by fastforce
  moreover
  from Nil.prems(2) have "p = q'"
    using word.cases by fastforce
  ultimately
  have "q = q'" by simp
  then show ?case .
next
  case (Cons a ls)
  from Cons.prems have "\<exists>r. (\<delta> p a r \<and> word \<delta> r ls q)"
    using word.cases by fastforce
  then obtain r where R: "\<delta> p a r " "word \<delta> r ls q"
    by force
  moreover
  from Cons.prems have "\<exists>r'. (\<delta> p a r' \<and> word \<delta> r' ls q')"
    using word.cases by force
  then obtain r' where R': "\<delta> p a r'" "word \<delta> r' ls q'"
    by force
  ultimately
  have "r = r'"
    using Cons.prems(3)
    by (simp add: det_def)
  then have "q = q'"
    using Cons.IH R'(2) R(2) det by blast
  then show ?case .
qed

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0"
| "count x (y # ys) = (if x=y then Suc (count x ys) else count x ys)"


lemma "count a xs = Suc n \<Longrightarrow> \<exists>ps ss. xs = ps @ a # ss \<and> count a ps = 0 \<and> count a ss = n"
proof(induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof(cases "a=x")
    case True
    then show ?thesis using Cons by force
  next
    case False
    then obtain ps' ss' where P: "xs = ps' @ a # ss'" "count a ps' = 0" "count a ss' = n"
      using Cons.IH Cons.prems by fastforce
    from Cons.prems have "count a (x # xs) = Suc n"
      by auto
    moreover
    have "count a (x#ps') = 0"
      by (simp add: False P(2))
    ultimately
    have "\<exists>ps ss. x # xs = ps @ a # ss \<and> count a ps = 0 \<and> count a ss = n" using P append_Cons
      by metis
    then show ?thesis .
  qed
qed

end