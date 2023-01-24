theory Defs
  imports "HOL-IMP.Complete_Lattice" "HOL-Library.Extended_Real" "HOL-Library.While_Combinator"
begin

section "AExp"

type_synonym vname = string
type_synonym val = "ereal option"
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = Some n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = (
   case (aval a\<^sub>1 s, aval a\<^sub>2 s) of
     (None, _) \<Rightarrow> None
   | (_, None) \<Rightarrow> None
   | (Some PInfty, Some MInfty) \<Rightarrow> None
   | (Some MInfty, Some PInfty) \<Rightarrow> None
   | (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 + v\<^sub>2)
  )"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"


section \<open>BExp\<close>

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool option" where
"bval (Bc v) s = Some v" |
"bval (Not b) s = map_option (HOL.Not) (bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (
   case (bval b\<^sub>1 s, bval b\<^sub>2 s) of
     (None, _) \<Rightarrow> None
   | (_, None) \<Rightarrow> None
   | (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 \<and> v\<^sub>2)
)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (
  case (aval a\<^sub>1 s, aval a\<^sub>2 s) of
    (None, _) \<Rightarrow> None |
    (_, None) \<Rightarrow> None |
    (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 < v\<^sub>2)
)"


section \<open>Com\<close>

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)


section \<open>Big_Step\<close>

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s = Some True;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> bval b s = Some False;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1 = Some True;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

code_pred big_step .

declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]
inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text \<open>An example combining rule inversion and derivations\<close>
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  \<comment> \<open>The other direction is analogous\<close>
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed


section "ACom"

datatype 'a acom =
  SKIP 'a                           ("SKIP {_}" 61) |
  Assign vname aexp 'a              ("(_ ::= _/ {_})" [1000, 61, 0] 61) |
  Seq "('a acom)" "('a acom)"       ("_;;//_"  [60, 61] 60) |
  If bexp 'a "('a acom)" 'a "('a acom)" 'a
    ("(IF _/ THEN ({_}/ _)/ ELSE ({_}/ _)//{_})"  [0, 0, 0, 61, 0, 0] 61) |
  While 'a bexp 'a "('a acom)" 'a
    ("({_}//WHILE _//DO ({_}//_)//{_})"  [0, 0, 0, 61, 0] 61)

notation com.SKIP ("SKIP")

fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {P}) = SKIP" |
"strip (x ::= e {P}) = x ::= e" |
"strip (C\<^sub>1;;C\<^sub>2) = strip C\<^sub>1;; strip C\<^sub>2" |
"strip (IF b THEN {P\<^sub>1} C\<^sub>1 ELSE {P\<^sub>2} C\<^sub>2 {P}) =
  IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2" |
"strip ({I} WHILE b DO {P} C {Q}) = WHILE b DO strip C"

fun asize :: "com \<Rightarrow> nat" where
"asize SKIP = 1" |
"asize (x ::= e) = 1" |
"asize (C\<^sub>1;;C\<^sub>2) = asize C\<^sub>1 + asize C\<^sub>2" |
"asize (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = asize C\<^sub>1 + asize C\<^sub>2 + 3" |
"asize (WHILE b DO C) = asize C + 3"

definition shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
"shift f n = (\<lambda>p. f(p+n))"

fun annotate :: "(nat \<Rightarrow> 'a) \<Rightarrow> com \<Rightarrow> 'a acom" where
"annotate f SKIP = SKIP {f 0}" |
"annotate f (x ::= e) = x ::= e {f 0}" |
"annotate f (c\<^sub>1;;c\<^sub>2) = annotate f c\<^sub>1;; annotate (shift f (asize c\<^sub>1)) c\<^sub>2" |
"annotate f (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  IF b THEN {f 0} annotate (shift f 1) c\<^sub>1
  ELSE {f(asize c\<^sub>1 + 1)} annotate (shift f (asize c\<^sub>1 + 2)) c\<^sub>2
  {f(asize c\<^sub>1 + asize c\<^sub>2 + 2)}" |
"annotate f (WHILE b DO c) =
  {f 0} WHILE b DO {f 1} annotate (shift f 2) c {f(asize c + 2)}"

fun annos :: "'a acom \<Rightarrow> 'a list" where
"annos (SKIP {P}) = [P]" |
"annos (x ::= e {P}) = [P]" |
"annos (C\<^sub>1;;C\<^sub>2) = annos C\<^sub>1 @ annos C\<^sub>2" |
"annos (IF b THEN {P\<^sub>1} C\<^sub>1 ELSE {P\<^sub>2} C\<^sub>2 {Q}) =
  P\<^sub>1 # annos C\<^sub>1 @  P\<^sub>2 # annos C\<^sub>2 @ [Q]" |
"annos ({I} WHILE b DO {P} C {Q}) = I # P # annos C @ [Q]"

definition anno :: "'a acom \<Rightarrow> nat \<Rightarrow> 'a" where
"anno C p = annos C ! p"

definition post :: "'a acom \<Rightarrow>'a" where
"post C = last(annos C)"

fun map_acom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a acom \<Rightarrow> 'b acom" where
"map_acom f (SKIP {P}) = SKIP {f P}" |
"map_acom f (x ::= e {P}) = x ::= e {f P}" |
"map_acom f (C\<^sub>1;;C\<^sub>2) = map_acom f C\<^sub>1;; map_acom f C\<^sub>2" |
"map_acom f (IF b THEN {P\<^sub>1} C\<^sub>1 ELSE {P\<^sub>2} C\<^sub>2 {Q}) =
  IF b THEN {f P\<^sub>1} map_acom f C\<^sub>1 ELSE {f P\<^sub>2} map_acom f C\<^sub>2
  {f Q}" |
"map_acom f ({I} WHILE b DO {P} C {Q}) =
  {f I} WHILE b DO {f P} map_acom f C {f Q}"

lemma annos_ne: "annos C \<noteq> []"
by(induction C) auto

lemma strip_annotate[simp]: "strip(annotate f c) = c"
by(induction c arbitrary: f) auto

lemma length_annos_annotate[simp]: "length (annos (annotate f c)) = asize c"
by(induction c arbitrary: f) auto

lemma size_annos: "size(annos C) = asize(strip C)"
by(induction C)(auto)

lemma size_annos_same: "strip C1 = strip C2 \<Longrightarrow> size(annos C1) = size(annos C2)"
apply(induct C2 arbitrary: C1)
apply(case_tac C1, simp_all)+
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]

lemma anno_annotate[simp]: "p < asize c \<Longrightarrow> anno (annotate f c) p = f p"
apply(induction c arbitrary: f p)
apply (auto simp: anno_def nth_append nth_Cons numeral_eq_Suc shift_def
            split: nat.split)
  apply (metis add_Suc_right add_diff_inverse add.commute)
 apply(rule_tac f=f in arg_cong)
 apply arith
apply (metis less_Suc_eq)
done

lemma eq_acom_iff_strip_annos:
  "C1 = C2 \<longleftrightarrow> strip C1 = strip C2 \<and> annos C1 = annos C2"
apply(induction C1 arbitrary: C2)
apply(case_tac C2, auto simp: size_annos_same2)+
done

lemma eq_acom_iff_strip_anno:
  "C1=C2 \<longleftrightarrow> strip C1 = strip C2 \<and> (\<forall>p<size(annos C1). anno C1 p = anno C2 p)"
by(auto simp add: eq_acom_iff_strip_annos anno_def
     list_eq_iff_nth_eq size_annos_same2)

lemma post_map_acom[simp]: "post(map_acom f C) = f(post C)"
by (induction C) (auto simp: post_def last_append annos_ne)

lemma strip_map_acom[simp]: "strip (map_acom f C) = strip C"
by (induction C) auto

lemma anno_map_acom: "p < size(annos C) \<Longrightarrow> anno (map_acom f C) p = f(anno C p)"
apply(induction C arbitrary: p)
apply(auto simp: anno_def nth_append nth_Cons' size_annos)
done

lemma strip_eq_SKIP:
  "strip C = SKIP \<longleftrightarrow> (\<exists>P. C = SKIP {P})"
by (cases C) simp_all

lemma strip_eq_Assign:
  "strip C = x::=e \<longleftrightarrow> (\<exists>P. C = x::=e {P})"
by (cases C) simp_all

lemma strip_eq_Seq:
  "strip C = c1;;c2 \<longleftrightarrow> (\<exists>C1 C2. C = C1;;C2 & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_If:
  "strip C = IF b THEN c1 ELSE c2 \<longleftrightarrow>
  (\<exists>P1 P2 C1 C2 Q. C = IF b THEN {P1} C1 ELSE {P2} C2 {Q} & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_While:
  "strip C = WHILE b DO c1 \<longleftrightarrow>
  (\<exists>I P C1 Q. C = {I} WHILE b DO {P} C1 {Q} & strip C1 = c1)"
by (cases C) simp_all

lemma [simp]: "shift (\<lambda>p. a) n = (\<lambda>p. a)"
by(simp add:shift_def)

lemma set_annos_anno[simp]: "set (annos (annotate (\<lambda>p. a) c)) = {a}"
by(induction c) simp_all

lemma post_in_annos: "post C \<in> set(annos C)"
by(auto simp: post_def annos_ne)

lemma post_anno_asize: "post C = anno C (size(annos C) - 1)"
by(simp add: post_def last_conv_nth[OF annos_ne] anno_def)

class vars =
fixes vars :: "'a \<Rightarrow> vname set"

instantiation aexp :: vars
begin

fun vars_aexp :: "aexp \<Rightarrow> vname set" where
"vars (N n) = {}" |
"vars (V x) = {x}" |
"vars (Plus a\<^sub>1 a\<^sub>2) = vars a\<^sub>1 \<union> vars a\<^sub>2"

instance ..

end

value "vars (Plus (V ''x'') (V ''y''))"

instantiation bexp :: vars
begin

fun vars_bexp :: "bexp \<Rightarrow> vname set" where
"vars (Bc v) = {}" |
"vars (Not b) = vars b" |
"vars (And b\<^sub>1 b\<^sub>2) = vars b\<^sub>1 \<union> vars b\<^sub>2" |
"vars (Less a\<^sub>1 a\<^sub>2) = vars a\<^sub>1 \<union> vars a\<^sub>2"

instance ..

end

value "vars (Less (Plus (V ''z'') (V ''y'')) (V ''x''))"

abbreviation
  eq_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
 ("(_ =/ _/ on _)" [50,0,50] 50) where
"f = g on X == \<forall> x \<in> X. f x = g x"

lemma aval_eq_if_eq_on_vars[simp]:
  "s\<^sub>1 = s\<^sub>2 on vars a \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
apply(induction a)
apply simp_all
done

lemma bval_eq_if_eq_on_vars:
  "s\<^sub>1 = s\<^sub>2 on vars b \<Longrightarrow> bval b s\<^sub>1 = bval b s\<^sub>2"
proof(induction b)
  case (Less a1 a2)
  hence "aval a1 s\<^sub>1 = aval a1 s\<^sub>2" and "aval a2 s\<^sub>1 = aval a2 s\<^sub>2" by simp_all
  thus ?case by simp
qed simp_all

fun lvars :: "com \<Rightarrow> vname set" where
"lvars SKIP = {}" |
"lvars (x::=e) = {x}" |
"lvars (c1;;c2) = lvars c1 \<union> lvars c2" |
"lvars (IF b THEN c1 ELSE c2) = lvars c1 \<union> lvars c2" |
"lvars (WHILE b DO c) = lvars c"

fun rvars :: "com \<Rightarrow> vname set" where
"rvars SKIP = {}" |
"rvars (x::=e) = vars e" |
"rvars (c1;;c2) = rvars c1 \<union> rvars c2" |
"rvars (IF b THEN c1 ELSE c2) = vars b \<union> rvars c1 \<union> rvars c2" |
"rvars (WHILE b DO c) = vars b \<union> rvars c"

instantiation com :: vars
begin

definition "vars_com c = lvars c \<union> rvars c"

instance ..

end

lemma vars_com_simps[simp]:
  "vars SKIP = {}"
  "vars (x::=e) = {x} \<union> vars e"
  "vars (c1;;c2) = vars c1 \<union> vars c2"
  "vars (IF b THEN c1 ELSE c2) = vars b \<union> vars c1 \<union> vars c2"
  "vars (WHILE b DO c) = vars b \<union> vars c"
by(auto simp: vars_com_def)

lemma finite_avars[simp]: "finite(vars(a::aexp))"
by(induction a) simp_all

lemma finite_bvars[simp]: "finite(vars(b::bexp))"
by(induction b) simp_all

lemma finite_lvars[simp]: "finite(lvars(c))"
by(induction c) simp_all

lemma finite_rvars[simp]: "finite(rvars(c))"
by(induction c) simp_all

lemma finite_cvars[simp]: "finite(vars(c::com))"
by(simp add: vars_com_def)


section \<open>Collecting\<close>
notation
  sup (infixl "\<squnion>" 65) and
  inf (infixl "\<sqinter>" 70) and
  bot ("\<bottom>") and
  top ("\<top>")

context
  fixes f :: "vname \<Rightarrow> aexp \<Rightarrow> 'a \<Rightarrow> 'a::sup"
  fixes g :: "bexp \<Rightarrow> 'a \<Rightarrow> 'a"
begin
fun Step :: "'a \<Rightarrow> 'a acom \<Rightarrow> 'a acom" where
"Step S (SKIP {Q}) = (SKIP {S})" |
"Step S (x ::= e {Q}) =
  x ::= e {f x e S}" |
"Step S (C1;; C2) = Step S C1;; Step (post C1) C2" |
"Step S (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) =
  IF b THEN {g b S} Step P1 C1 ELSE {g (Not b) S} Step P2 C2
  {post C1 \<squnion> post C2}" |
"Step S ({I} WHILE b DO {P} C {Q}) =
  {S \<squnion> post C} WHILE b DO {g b I} Step P C {g (Not b) I}"
end

lemma strip_Step[simp]: "strip(Step f g S C) = strip C"
by(induct C arbitrary: S) auto

instantiation acom :: (order) order
begin

definition less_eq_acom :: "('a::order)acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"C1 \<le> C2 \<longleftrightarrow> strip C1 = strip C2 \<and> (\<forall>p<size(annos C1). anno C1 p \<le> anno C2 p)"

definition less_acom :: "'a acom \<Rightarrow> 'a acom \<Rightarrow> bool" where
"less_acom x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof (standard, goal_cases)
  case 1 show ?case by(simp add: less_acom_def)
next
  case 2 thus ?case by(auto simp: less_eq_acom_def)
next
  case 3 thus ?case by(fastforce simp: less_eq_acom_def size_annos)
next
  case 4 thus ?case
    by(fastforce simp: le_antisym less_eq_acom_def size_annos
         eq_acom_iff_strip_anno)
qed

end

lemma less_eq_acom_annos:
  "C1 \<le> C2 \<longleftrightarrow> strip C1 = strip C2 \<and> list_all2 (\<le>) (annos C1) (annos C2)"
by(auto simp add: less_eq_acom_def anno_def list_all2_conv_all_nth size_annos_same2)

lemma SKIP_le[simp]: "SKIP {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = SKIP {S'} \<and> S \<le> S')"
by (cases c) (auto simp:less_eq_acom_def anno_def)

lemma Assign_le[simp]: "x ::= e {S} \<le> c \<longleftrightarrow> (\<exists>S'. c = x ::= e {S'} \<and> S \<le> S')"
by (cases c) (auto simp:less_eq_acom_def anno_def)

lemma Seq_le[simp]: "C1;;C2 \<le> C \<longleftrightarrow> (\<exists>C1' C2'. C = C1';;C2' \<and> C1 \<le> C1' \<and> C2 \<le> C2')"
apply (cases C)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

lemma If_le[simp]: "IF b THEN {p1} C1 ELSE {p2} C2 {S} \<le> C \<longleftrightarrow>
  (\<exists>p1' p2' C1' C2' S'. C = IF b THEN {p1'} C1' ELSE {p2'} C2' {S'} \<and>
     p1 \<le> p1' \<and> p2 \<le> p2' \<and> C1 \<le> C1' \<and> C2 \<le> C2' \<and> S \<le> S')"
apply (cases C)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

lemma While_le[simp]: "{I} WHILE b DO {p} C {P} \<le> W \<longleftrightarrow>
  (\<exists>I' p' C' P'. W = {I'} WHILE b DO {p'} C' {P'} \<and> C \<le> C' \<and> p \<le> p' \<and> I \<le> I' \<and> P \<le> P')"
apply (cases W)
apply(auto simp: less_eq_acom_annos list_all2_append size_annos_same2)
done

lemma mono_post: "C \<le> C' \<Longrightarrow> post C \<le> post C'"
using annos_ne[of C']
by(auto simp: post_def less_eq_acom_def last_conv_nth[OF annos_ne] anno_def
     dest: size_annos_same)

definition Inf_acom :: "com \<Rightarrow> 'a::complete_lattice acom set \<Rightarrow> 'a acom" where
"Inf_acom c M = annotate (\<lambda>p. INF C\<in>M. anno C p) c"

global_interpretation
  Complete_Lattice "{C. strip C = c}" "Inf_acom c" for c
proof (standard, goal_cases)
  case 1 thus ?case
    by(auto simp: Inf_acom_def less_eq_acom_def size_annos intro:INF_lower)
next
  case 2 thus ?case
    by(auto simp: Inf_acom_def less_eq_acom_def size_annos intro:INF_greatest)
next
  case 3 thus ?case by(auto simp: Inf_acom_def)
qed


definition "step = Step (\<lambda>x e S. {s(x := aval e s) |s. s \<in> S}) (\<lambda>b S. {s:S. bval b s = Some True})"

definition CS :: "com \<Rightarrow> state set acom" where
"CS c = lfp c (step UNIV)"

lemma mono2_Step: fixes C1 C2 :: "'a::semilattice_sup acom"
  assumes "!!x e S1 S2. S1 \<le> S2 \<Longrightarrow> f x e S1 \<le> f x e S2"
          "!!b S1 S2. S1 \<le> S2 \<Longrightarrow> g b S1 \<le> g b S2"
  shows "C1 \<le> C2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> Step f g S1 C1 \<le> Step f g S2 C2"
proof(induction S1 C1 arbitrary: C2 S2 rule: Step.induct)
  case 1 thus ?case by(auto)
next
  case 2 thus ?case by (auto simp: assms(1))
next
  case 3 thus ?case by(auto simp: mono_post)
next
  case 4 thus ?case
    by(auto simp: subset_iff assms(2))
      (metis mono_post le_supI1 le_supI2)+
next
  case 5 thus ?case
    by(auto simp: subset_iff assms(2))
      (metis mono_post le_supI1 le_supI2)+
qed

lemma mono2_step: "C1 \<le> C2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> step S1 C1 \<le> step S2 C2"
unfolding step_def by(rule mono2_Step) auto

lemma mono_step: "mono (step S)"
by(blast intro: monoI mono2_step)

lemma strip_step: "strip(step S C) = strip C"
by (induction C arbitrary: S) (auto simp: step_def)

lemma lfp_cs_unfold: "lfp c (step S) = step S (lfp c (step S))"
apply(rule lfp_unfold[OF _  mono_step])
apply(simp add: strip_step)
done

lemma CS_unfold: "CS c = step UNIV (CS c)"
by (metis CS_def lfp_cs_unfold)

lemma strip_CS[simp]: "strip(CS c) = c"
by(simp add: CS_def index_lfp[simplified])


lemma asize_nz: "asize(c::com) \<noteq> 0"
by (metis length_0_conv length_annos_annotate annos_ne)

lemma post_Inf_acom:
  "\<forall>C\<in>M. strip C = c \<Longrightarrow> post (Inf_acom c M) = \<Inter>(post ` M)"
apply(subgoal_tac "\<forall>C\<in>M. size(annos C) = asize c")
 apply(simp add: post_anno_asize Inf_acom_def asize_nz neq0_conv[symmetric])
apply(simp add: size_annos)
done

lemma post_lfp: "post(lfp c f) = (\<Inter>{post C|C. strip C = c \<and> f C \<le> C})"
by(auto simp add: lfp_def post_Inf_acom)

lemma big_step_post_step:
  "\<lbrakk> (c, s) \<Rightarrow> t;  strip C = c;  s \<in> S;  step S C \<le> C \<rbrakk> \<Longrightarrow> t \<in> post C"
proof(induction arbitrary: C S rule: big_step_induct)
  case Skip thus ?case by(auto simp: strip_eq_SKIP step_def post_def)
next
  case Assign thus ?case
    by(fastforce simp: strip_eq_Assign step_def post_def)
next
  case Seq thus ?case
    by(fastforce simp: strip_eq_Seq step_def post_def last_append annos_ne)
next
  case IfTrue thus ?case apply(auto simp: strip_eq_If step_def post_def)
    using subset_eq by blast
next
  case IfFalse thus ?case apply(auto simp: strip_eq_If step_def post_def)
    using subset_eq by blast
next
  case (WhileTrue b s1 c' s2 s3)
  from WhileTrue.prems(1) obtain I P C' Q where "C = {I} WHILE b DO {P} C' {Q}" "strip C' = c'"
    by(auto simp: strip_eq_While)
  from WhileTrue.prems(3) \<open>C = _\<close>
  have "step P C' \<le> C'"  "{s \<in> I. bval b s = Some True} \<le> P"  "S \<le> I"  "step (post C') C \<le> C"
    by (auto simp: step_def post_def)
  have "step {s \<in> I. bval b s = Some True} C' \<le> C'"
    by (rule order_trans[OF mono2_step[OF order_refl \<open>{s \<in> I. bval b s = Some True} \<le> P\<close>] \<open>step P C' \<le> C'\<close>])
  have "s1 \<in> {s\<in>I. bval b s = Some True}" using \<open>s1 \<in> S\<close> \<open>S \<subseteq> I\<close> \<open>bval b s1 = Some True\<close> by auto
  note s2_in_post_C' = WhileTrue.IH(1)[OF \<open>strip C' = c'\<close> this \<open>step {s \<in> I. bval b s = Some True} C' \<le> C'\<close>]
  from WhileTrue.IH(2)[OF WhileTrue.prems(1) s2_in_post_C' \<open>step (post C') C \<le> C\<close>]
  show ?case .
next
  case (WhileFalse b s1 c') thus ?case
    by (force simp: strip_eq_While step_def post_def)
qed

lemma big_step_lfp: "\<lbrakk> (c,s) \<Rightarrow> t;  s \<in> S \<rbrakk> \<Longrightarrow> t \<in> post(lfp c (step S))"
by(auto simp add: post_lfp intro: big_step_post_step)

lemma big_step_CS: "(c,s) \<Rightarrow> t \<Longrightarrow> t \<in> post(CS c)"
by(simp add: CS_def big_step_lfp)


datatype bound = NegInf ("\<infinity>\<^sup>-") | PosInf ("\<infinity>\<^sup>+") | NaN | Real
datatype bounds = B "bound set"


datatype parity = Even | Odd | Either
datatype entry = Unchanged ("'_'_'_'_'_'_'_'_") | None | Some parity


consts A\<^sub>0 :: "entry list"

consts A\<^sub>1 :: "entry list"

consts A\<^sub>2 :: "entry list"

consts A\<^sub>3 :: "entry list"

consts A\<^sub>4 :: "entry list"

consts A\<^sub>5 :: "entry list"

consts A\<^sub>6 :: "entry list"

consts A\<^sub>7 :: "entry list"

consts A\<^sub>8 :: "entry list"

consts A\<^sub>9 :: "entry list"

consts \<gamma>_bounds :: "bounds \<Rightarrow> val set"

consts num_bounds :: "ereal \<Rightarrow> bounds"

consts plus_bounds :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds"

consts m_bounds :: "bounds \<Rightarrow> nat"


end