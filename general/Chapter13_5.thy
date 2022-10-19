theory Chapter13_5
imports Main
begin

unbundle lattice_syntax

text\<open>
\setcounter{exercise}{10}

\begin{exercise}
Take the Isabelle theories that define commands, big-step semantics,
annotated commands and the collecting semantics and extend them with a
nondeterministic choice construct. Start with Exercise~\ref{exe:IMP:OR}
and extend type @{text com}, then extend type @{text acom} with a
corresponding construct:
\begin{alltt}
  Or "'a acom" "'a acom" 'a     ("_ OR// _//{_}"  [60, 61, 0] 60)
\end{alltt}
Finally extend function @{text Step}. Update proofs as well.
Hint: think of @{text OR} as a nondeterministic conditional without a test.
\end{exercise}

\exercise
Prove the following lemmas in a detailed and readable style:
\<close>

lemma fixes x0 :: "'a :: order"
assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"  and  "f q \<le> q"  and  "x0 \<le> q"
shows "(f ^^ i) x0 \<le> q"
(* your definition/proof here *)


lemma fixes x0 :: "'a :: order"
assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y" and "x0 \<le> f x0"
shows "(f ^^ i) x0 \<le> (f ^^ (i+1)) x0"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise% needs lattice_syntax
Let @{typ 'a} be a complete lattice and
let @{text "f :: 'a \<Rightarrow> 'a"} be a monotone function.
Give a readable proof that if @{text P} is a set of pre-fixpoints of @{text f}
then @{term"\<Sqinter> P"} is also a pre-fixpoint of @{text f}:
\<close>

lemma fixes P :: "'a::complete_lattice set"
assumes "mono f" and "\<forall>p \<in> P. f p \<le> p"
shows "f(\<Sqinter> P) \<le> \<Sqinter> P"
(* your definition/proof here *)

text\<open>
Sledgehammer should give you a proof you can start from.
\endexercise
\<close>

end

