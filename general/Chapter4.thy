theory Chapter4
imports "HOL-IMP.ASM"
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text \<open>
\section*{Chapter 4}

\exercise
Start from the data type of binary trees defined earlier:
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text \<open>
An @{typ "int tree"} is ordered if for every @{term "Node l i r"} in the tree,
@{text l} and @{text r} are ordered
and all values in @{text l} are @{text "< i"}
and all values in @{text r} are @{text "> i"}.
Define a function that returns the elements in a tree and one
the tests if a tree is ordered:
\<close>

fun set :: "'a tree \<Rightarrow> 'a set"  where
"set Tip = {}" |
"set (Node l v r) = {v}\<union>(set l)\<union>(set r)"
(* your definition/proof here *)

fun ord :: "int tree \<Rightarrow> bool"  where
"ord Tip = True" |
"ord (Node l v r) = ((\<forall>x\<in>(set l). x < v) \<and> (\<forall>x\<in>(set r). v < x) \<and> (ord l) \<and> (ord r))"

(* your definition/proof here *)

text\<open>
 Hint: use quantifiers.

Define a function @{text ins} that inserts an element into an ordered @{typ "int tree"}
while maintaining the order of the tree. If the element is already in the tree, the
same tree should be returned.
\<close>

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree"  where
"ins i Tip = Node Tip i Tip " |
"ins i (Node l v r) = (if i = v then Node l v r else if i < v then Node (ins i l) v r else Node l v (ins i r))"
(* your definition/proof here *)

text\<open> Prove correctness of @{const ins}: \<close>

lemma set_ins: "set(ins x t) = {x} \<union> set t"
  by(induction x t rule: ins.induct, auto)
(* your definition/proof here *)

theorem ord_ins: "ord t \<Longrightarrow> ord(ins i t)"
  using set_ins by(induction t rule: ins.induct, auto)
(* your definition/proof here *)

  text\<open>
\endexercise

\exercise
Formalize the following definition of palindromes
\begin{itemize}
\item The empty list and a singleton list are palindromes.
\item If @{text xs} is a palindrome, so is @{term "a # xs @ [a]"}.
\end{itemize}
as an inductive predicate
\<close>

inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty: "palindrome []" |
  singleton: "palindrome [x]" |
  cont: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"
  

(* your definition/proof here *)

text \<open> and prove \<close>

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  by(induction xs rule: palindrome.induct, auto)
(* your definition/proof here *)

text \<open>
\endexercise

\exercise
We could also have defined @{const star} as follows:
\<close>

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

text \<open>
The single @{text r} step is performer after rather than before the @{text star'}
steps. Prove
\<close>

lemma "star' r x y \<Longrightarrow> star r x y"
  sorry
(* your definition/proof here *)



lemma "star r x y \<Longrightarrow> star' r x y"
  sorry
(* your definition/proof here *)

text \<open>
You may need lemmas. Note that rule induction fails
if the assumption about the inductive predicate
is not the first assumption.
\endexercise

\exercise\label{exe:iter}
Analogous to @{const star}, give an inductive definition of the @{text n}-fold iteration
of a relation @{text r}: @{term "iter r n x y"} should hold if there are @{text x\<^sub>0}, \dots, @{text x\<^sub>n}
such that @{prop"x = x\<^sub>0"}, @{prop"x\<^sub>n = y"} and @{text"r x\<^bsub>i\<^esub> x\<^bsub>i+1\<^esub>"} for
all @{prop"i < n"}:
\<close>

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
(* your definition/proof here *)

text\<open>
Correct and prove the following claim:
\<close>

lemma "star r x y \<Longrightarrow> iter r n x y"
(* your definition/proof here *)

text{*
\endexercise

\exercise\label{exe:cfg}
A context-free grammar can be seen as an inductive definition where each
nonterminal $A$ is an inductively defined predicate on lists of terminal
symbols: $A(w)$ mans that $w$ is in the language generated by $A$.
For example, the production $S \to aSb$ can be viewed as the implication
@{prop"S w \<Longrightarrow> S (a # w @ [b])"} where @{text a} and @{text b} are terminal symbols,
i.e., elements of some alphabet. The alphabet can be defined as a datatype:
*}

datatype alpha = a | b

text{*
If you think of @{const a} and @{const b} as ``@{text "("}'' and  ``@{text ")"}'',
the following two grammars both generate strings of balanced parentheses
(where $\varepsilon$ is the empty word):
\[
\begin{array}{r@ {\quad}c@ {\quad}l}
S &\to& \varepsilon \quad\mid\quad aSb \quad\mid\quad SS \\
T &\to& \varepsilon \quad\mid\quad TaTb
\end{array}
\]
Define them as inductive predicates and prove their equivalence:
*}

inductive S :: "alpha list \<Rightarrow> bool" where
(* your definition/proof here *)

inductive T :: "alpha list \<Rightarrow> bool" where
(* your definition/proof here *)

lemma TS: "T w \<Longrightarrow> S w"
(* your definition/proof here *)



lemma ST: "S w \<Longrightarrow> T w"
(* your definition/proof here *)

corollary SeqT: "S w \<longleftrightarrow> T w"
(* your definition/proof here *)

text{*
\endexercise
*}
(* your definition/proof here *)
text{*
\exercise
In Chapter 3 we defined a recursive evaluation function
@{text "aval ::"} @{typ "aexp \<Rightarrow> state \<Rightarrow> val"}.
Define an inductive evaluation predicate and prove that it agrees with
the recursive function:
*}

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
(* your definition/proof here *)

lemma aval_rel_aval: "aval_rel a s v \<Longrightarrow> aval a s = v"
(* your definition/proof here *)

lemma aval_aval_rel: "aval a s = v \<Longrightarrow> aval_rel a s v"
(* your definition/proof here *)

corollary "aval_rel a s v \<longleftrightarrow> aval a s = v"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Consider the stack machine from Chapter~3
and recall the concept of \concept{stack underflow}
from Exercise~\ref{exe:stack-underflow}.
Define an inductive predicate
*}

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
(* your definition/proof here *)

text{*
such that @{text "ok n is n'"} means that with any initial stack of length
@{text n} the instructions @{text "is"} can be executed
without stack underflow and that the final stack has length @{text n'}.

Using the introduction rules for @{const ok},
prove the following special cases: *}

lemma "ok 0 [LOAD x] (Suc 0)"
(* your definition/proof here *)

lemma "ok 0 [LOAD x, LOADI v, ADD] (Suc 0)"
(* your definition/proof here *)

lemma "ok (Suc (Suc 0)) [LOAD x, ADD, ADD, LOAD y] (Suc (Suc 0))"
(* your definition/proof here *)

text {* Prove that @{text ok} correctly computes the final stack size: *}

lemma "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"
(* your definition/proof here *)

text {*
Lemma @{thm [source] length_Suc_conv} may come in handy.

Prove that instruction sequences generated by @{text comp}
cannot cause stack underflow: \ @{text "ok n (comp a) ?"} \ for
some suitable value of @{text "?"}.
\endexercise
*}


end

