theory Submission
  imports Defs
begin

definition A\<^sub>0 :: "entry list"  where
  "A\<^sub>0 = [Unchanged, Some Odd, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>1 :: "entry list"  where
  "A\<^sub>1 = [Unchanged, Unchanged, Some Odd, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>2 :: "entry list"  where
  "A\<^sub>2 = [Unchanged, Unchanged, Unchanged, Some Odd, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>3 :: "entry list"  where
  "A\<^sub>3 = [Unchanged, Unchanged, Unchanged, Unchanged, Some Even, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>4 :: "entry list"  where
  "A\<^sub>4 = [Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Some Even, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>5 :: "entry list"  where
  "A\<^sub>5 = [Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Some Odd, Unchanged, Unchanged]"

definition A\<^sub>6 :: "entry list"  where
  "A\<^sub>6 = [Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>7 :: "entry list"  where
  "A\<^sub>7 = [Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged]"

definition A\<^sub>8 :: "entry list"  where
  "A\<^sub>8 = [Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Some Odd, Unchanged]"

definition A\<^sub>9 :: "entry list"  where
  "A\<^sub>9 = [Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Unchanged, Some Odd]"

(*
r := 1; {A0}
{A1} WHILE b DO {A2} (
r := r * 2;{A3}
IF b THEN {A4}
r := r - 1{A5}
ELSE {A6}
r := r + 2{A7}
{A8}
){A9}
*)

hide_const (open) None Some

datatype bound = NegInf ("\<infinity>\<^sup>-") | PosInf ("\<infinity>\<^sup>+") | NaN | Real
datatype bounds = B "bound set"

instantiation bounds :: order
begin

definition less_eq_bounds where
"x \<le> y = (case (x, y) of (B x, B y) \<Rightarrow> x \<subseteq> y)"

definition less_bounds where
"x < y = (case (x, y) of (B x, B y) \<Rightarrow> x \<subset> y)"

instance
proof (standard, goal_cases)
  case (1 x y)
  then show ?case unfolding less_bounds_def less_eq_bounds_def by(fastforce split: bounds.splits)
next
  case (2 x)
  then show ?case unfolding less_eq_bounds_def by(simp split: bounds.splits)
next
  case (3 x y z)
  then show ?case unfolding less_eq_bounds_def by(fastforce split: bounds.splits)
next
  case (4 x y)
  then show ?case unfolding less_eq_bounds_def by(fastforce split: bounds.splits)
qed

end

(* Abst_Int0 -------------------- START --------------------*)
class semilattice_sup_top = semilattice_sup + order_top


instance "fun" :: (type, semilattice_sup_top) semilattice_sup_top ..

instantiation option :: (order)order
begin

fun less_eq_option where
"Some x \<le> Some y = (x \<le> y)" |
"None \<le> y = True" |
"Some _ \<le> None = False"

definition less_option where "x < (y::'a option) = (x \<le> y \<and> \<not> y \<le> x)"

lemma le_None[simp]: "(x \<le> None) = (x = None)"
by (cases x) simp_all

lemma Some_le[simp]: "(Some x \<le> u) = (\<exists>y. u = Some y \<and> x \<le> y)"
by (cases u) auto

instance
proof (standard, goal_cases)
  case 1 show ?case by(rule less_option_def)
next
  case (2 x) show ?case by(cases x, simp_all)
next
  case (3 x y z) thus ?case by(cases z, simp, cases y, simp, cases x, auto)
next
  case (4 x y) thus ?case by(cases y, simp, cases x, auto)
qed

end

instantiation option :: (sup)sup
begin

fun sup_option where
"Some x \<squnion> Some y = Some(x \<squnion> y)" |
"None \<squnion> y = y" |
"x \<squnion> None = x"

lemma sup_None2[simp]: "x \<squnion> None = x"
by (cases x) simp_all

instance ..

end

instantiation option :: (semilattice_sup_top)semilattice_sup_top
begin

definition top_option where "\<top> = Some \<top>"

instance
proof (standard, goal_cases)
  case (4 a) show ?case by(cases a, simp_all add: top_option_def)
next
  case (1 x y) thus ?case by(cases x, simp, cases y, simp_all)
next
  case (2 x y) thus ?case by(cases y, simp, cases x, simp_all)
next
  case (3 x y z) thus ?case by(cases z, simp, cases y, simp, cases x, simp_all)
qed

end

lemma [simp]: "(Some x < Some y) = (x < y)"
by(auto simp: less_le)

instantiation option :: (order)order_bot
begin

definition bot_option :: "'a option" where
"\<bottom> = None"

instance
proof (standard, goal_cases)
  case 1 thus ?case by(auto simp: bot_option_def)
qed

end


definition bot :: "com \<Rightarrow> 'a option acom" where
"bot c = annotate (\<lambda>p. None) c"

lemma bot_least: "strip C = c \<Longrightarrow> bot c \<le> C"
by(auto simp: bot_def less_eq_acom_def)

lemma strip_bot[simp]: "strip(bot c) = c"
by(simp add: bot_def)


subsubsection "Pre-fixpoint iteration"

definition pfp :: "(('a::order) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"pfp f = while_option (\<lambda>x. \<not> f x \<le> x) f"

lemma pfp_pfp: assumes "pfp f x0 = Some x" shows "f x \<le> x"
using while_option_stop[OF assms[simplified pfp_def]] by simp

lemma while_least:
fixes q :: "'a::order"
assumes "\<forall>x\<in>L.\<forall>y\<in>L. x \<le> y \<longrightarrow> f x \<le> f y" and "\<forall>x. x \<in> L \<longrightarrow> f x \<in> L"
and "\<forall>x \<in> L. b \<le> x" and "b \<in> L" and "f q \<le> q" and "q \<in> L"
and "while_option P f b = Some p"
shows "p \<le> q"
using while_option_rule[OF _  assms(7)[unfolded pfp_def],
                        where P = "%x. x \<in> L \<and> x \<le> q"]
by (metis assms(1-6) order_trans)

lemma pfp_bot_least:
assumes "\<forall>x\<in>{C. strip C = c}.\<forall>y\<in>{C. strip C = c}. x \<le> y \<longrightarrow> f x \<le> f y"
and "\<forall>C. C \<in> {C. strip C = c} \<longrightarrow> f C \<in> {C. strip C = c}"
and "f C' \<le> C'" "strip C' = c" "pfp f (bot c) = Some C"
shows "C \<le> C'"
by(rule while_least[OF assms(1,2) _ _ assms(3) _ assms(5)[unfolded pfp_def]])
  (simp_all add: assms(4) bot_least)

lemma pfp_inv:
  "pfp f x = Some y \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P(f x)) \<Longrightarrow> P x \<Longrightarrow> P y"
unfolding pfp_def by (blast intro: while_option_rule)

lemma strip_pfp:
assumes "\<And>x. g(f x) = g x" and "pfp f x0 = Some x" shows "g x = g x0"
using pfp_inv[OF assms(2), where P = "%x. g x = g x0"] assms(1) by simp


subsubsection "Abstract Interpretation"

definition \<gamma>_fun :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b)set" where
"\<gamma>_fun \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(F x)}"

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
"\<gamma>_option \<gamma> None = {}" |
"\<gamma>_option \<gamma> (Some a) = \<gamma> a"

text\<open>The interface for abstract values:\<close>

locale Val_semilattice =
fixes \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = UNIV"
fixes num' :: "ereal \<Rightarrow> 'av"
and plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av"
  assumes gamma_num': "Some i \<in> \<gamma>(num' i)"
  and gamma_plus': "i1 \<in> \<gamma> a1 \<Longrightarrow> i2 \<in> \<gamma> a2 \<Longrightarrow> j = (
   case (i1, i2) of
     (None, _) \<Rightarrow> None
   | (_, None) \<Rightarrow> None
   | (Some PInfty, Some MInfty) \<Rightarrow> None
   | (Some MInfty, Some PInfty) \<Rightarrow> None
   | (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 + v\<^sub>2)
  ) \<Longrightarrow> j \<in> \<gamma>(plus' a1 a2)"

instantiation acom :: (type) vars
begin

definition "vars_acom = vars o strip"

instance ..

end

lemma finite_Cvars: "finite(vars(C::'a acom))"
by(simp add: vars_acom_def)
(* Abst_Int0 --------------------- END ---------------------*)



(* Abst_Int1 -------------------- START --------------------*)

type_synonym 'a st_rep = "(vname * 'a) list"

fun fun_rep :: "('a::top) st_rep \<Rightarrow> vname \<Rightarrow> 'a" where
"fun_rep [] = (\<lambda>x. \<top>)" |
"fun_rep ((x,a)#ps) = (fun_rep ps) (x := a)"

lemma fun_rep_map_of[code]: \<comment> \<open>original def is too slow\<close>
  "fun_rep ps = (%x. case map_of ps x of None \<Rightarrow> \<top> | Some a \<Rightarrow> a)"
by(induction ps rule: fun_rep.induct) auto

definition eq_st :: "('a::top) st_rep \<Rightarrow> 'a st_rep \<Rightarrow> bool" where
"eq_st S1 S2 = (fun_rep S1 = fun_rep S2)"

declare [[typedef_overloaded]] \<comment> \<open>allow quotient types to depend on classes\<close>

quotient_type 'a st = "('a::top) st_rep" / eq_st
morphisms rep_st St
by (metis eq_st_def equivpI reflpI sympI transpI)

lift_definition update :: "('a::top) st \<Rightarrow> vname \<Rightarrow> 'a \<Rightarrow> 'a st"
  is "\<lambda>ps x a. (x,a)#ps"
by(auto simp: eq_st_def)

lift_definition "fun" :: "('a::top) st \<Rightarrow> vname \<Rightarrow> 'a" is fun_rep
by(simp add: eq_st_def)

definition show_st :: "vname set \<Rightarrow> ('a::top) st \<Rightarrow> (vname * 'a)set" where
"show_st X S = (\<lambda>x. (x, fun S x)) ` X"

definition "show_acom C = map_acom (map_option (show_st (vars(strip C)))) C"
definition "show_acom_opt = map_option show_acom"

lemma fun_update[simp]: "fun (update S x y) = (fun S)(x:=y)"
by transfer auto

definition \<gamma>_st :: "(('a::top) \<Rightarrow> 'b set) \<Rightarrow> 'a st \<Rightarrow> (vname \<Rightarrow> 'b) set" where
"\<gamma>_st \<gamma> F = {f. \<forall>x. f x \<in> \<gamma>(fun F x)}"

instantiation st :: (order_top) order
begin

definition less_eq_st_rep :: "'a st_rep \<Rightarrow> 'a st_rep \<Rightarrow> bool" where
"less_eq_st_rep ps1 ps2 =
  ((\<forall>x \<in> set(map fst ps1) \<union> set(map fst ps2). fun_rep ps1 x \<le> fun_rep ps2 x))"

lemma less_eq_st_rep_iff:
  "less_eq_st_rep r1 r2 = (\<forall>x. fun_rep r1 x \<le> fun_rep r2 x)"
apply(auto simp: less_eq_st_rep_def fun_rep_map_of split: option.split)
apply (metis Un_iff map_of_eq_None_iff option.distinct(1))
apply (metis Un_iff map_of_eq_None_iff option.distinct(1))
done

corollary less_eq_st_rep_iff_fun:
  "less_eq_st_rep r1 r2 = (fun_rep r1 \<le> fun_rep r2)"
by (metis less_eq_st_rep_iff le_fun_def)

lift_definition less_eq_st :: "'a st \<Rightarrow> 'a st \<Rightarrow> bool" is less_eq_st_rep
by(auto simp add: eq_st_def less_eq_st_rep_iff)

definition less_st where "F < (G::'a st) = (F \<le> G \<and> \<not> G \<le> F)"

instance
proof (standard, goal_cases)
  case 1 show ?case by(rule less_st_def)
next
  case 2 show ?case by transfer (auto simp: less_eq_st_rep_def)
next
  case 3 thus ?case by transfer (metis less_eq_st_rep_iff order_trans)
next
  case 4 thus ?case
    by transfer (metis less_eq_st_rep_iff eq_st_def fun_eq_iff antisym)
qed

end

lemma le_st_iff: "(F \<le> G) = (\<forall>x. fun F x \<le> fun G x)"
by transfer (rule less_eq_st_rep_iff)

fun map2_st_rep :: "('a::top \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep \<Rightarrow> 'a st_rep" where
"map2_st_rep f [] ps2 = map (%(x,y). (x, f \<top> y)) ps2" |
"map2_st_rep f ((x,y)#ps1) ps2 =
  (let y2 = fun_rep ps2 x
   in (x,f y y2) # map2_st_rep f ps1 ps2)"

lemma fun_rep_map2_rep[simp]: "f \<top> \<top> = \<top> \<Longrightarrow>
  fun_rep (map2_st_rep f ps1 ps2) = (\<lambda>x. f (fun_rep ps1 x) (fun_rep ps2 x))"
apply(induction f ps1 ps2 rule: map2_st_rep.induct)
apply(simp add: fun_rep_map_of map_of_map fun_eq_iff split: option.split)
apply(fastforce simp: fun_rep_map_of fun_eq_iff split:option.splits)
done

instantiation st :: (semilattice_sup_top) semilattice_sup_top
begin

lift_definition sup_st :: "'a st \<Rightarrow> 'a st \<Rightarrow> 'a st" is "map2_st_rep (\<squnion>)"
by (simp add: eq_st_def)

lift_definition top_st :: "'a st" is "[]" .

instance
proof (standard, goal_cases)
  case 1 show ?case by transfer (simp add:less_eq_st_rep_iff)
next
  case 2 show ?case by transfer (simp add:less_eq_st_rep_iff)
next
  case 3 thus ?case by transfer (simp add:less_eq_st_rep_iff)
next
  case 4 show ?case by transfer (simp add:less_eq_st_rep_iff fun_rep_map_of)
qed

end

lemma fun_top: "fun \<top> = (\<lambda>x. \<top>)"
by transfer simp

lemma mono_update[simp]:
  "a1 \<le> a2 \<Longrightarrow> S1 \<le> S2 \<Longrightarrow> update S1 x a1 \<le> update S2 x a2"
by transfer (auto simp add: less_eq_st_rep_def)

lemma mono_fun: "S1 \<le> S2 \<Longrightarrow> fun S1 x \<le> fun S2 x"
by transfer (simp add: less_eq_st_rep_iff)

locale Gamma_semilattice = Val_semilattice where \<gamma>=\<gamma>
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
begin

abbreviation \<gamma>\<^sub>s :: "'av st \<Rightarrow> state set"
where "\<gamma>\<^sub>s == \<gamma>_st \<gamma>"

abbreviation \<gamma>\<^sub>o :: "'av st option \<Rightarrow> state set"
where "\<gamma>\<^sub>o == \<gamma>_option \<gamma>\<^sub>s"

abbreviation \<gamma>\<^sub>c :: "'av st option acom \<Rightarrow> state set acom"
where "\<gamma>\<^sub>c == map_acom \<gamma>\<^sub>o"

lemma gamma_s_top[simp]: "\<gamma>\<^sub>s \<top> = UNIV"
by(auto simp: \<gamma>_st_def fun_top)

lemma gamma_o_Top[simp]: "\<gamma>\<^sub>o \<top> = UNIV"
by (simp add: top_option_def)

lemma mono_gamma_s: "f \<le> g \<Longrightarrow> \<gamma>\<^sub>s f \<subseteq> \<gamma>\<^sub>s g"
by(simp add:\<gamma>_st_def le_st_iff subset_iff) (metis mono_gamma subsetD)

lemma mono_gamma_o:
  "S1 \<le> S2 \<Longrightarrow> \<gamma>\<^sub>o S1 \<subseteq> \<gamma>\<^sub>o S2"
by(induction S1 S2 rule: less_eq_option.induct)(simp_all add: mono_gamma_s)

lemma mono_gamma_c: "C1 \<le> C2 \<Longrightarrow> \<gamma>\<^sub>c C1 \<le> \<gamma>\<^sub>c C2"
by (simp add: less_eq_acom_def mono_gamma_o size_annos anno_map_acom size_annos_same[of C1 C2])

lemma in_gamma_option_iff:
  "x \<in> \<gamma>_option r u \<longleftrightarrow> (\<exists>u'. u = Some u' \<and> x \<in> r u')"
by (cases u) auto

end



text\<open>Abstract interpretation over type \<open>st\<close> instead of functions.\<close>

context Gamma_semilattice
begin

fun aval' :: "aexp \<Rightarrow> 'av st \<Rightarrow> 'av" where
"aval' (N i) S = num' i" |
"aval' (V x) S = fun S x" |
"aval' (Plus a1 a2) S = plus' (aval' a1 S) (aval' a2 S)"

lemma aval'_correct: "s \<in> \<gamma>\<^sub>s S \<Longrightarrow> aval a s \<in> \<gamma>(aval' a S)"
by (induction a) (auto simp: gamma_num' gamma_plus' \<gamma>_st_def)

lemma gamma_Step_subcomm: fixes C1 C2 :: "'a::semilattice_sup acom"
  assumes "!!x e S. f1 x e (\<gamma>\<^sub>o S) \<subseteq> \<gamma>\<^sub>o (f2 x e S)"
          "!!b S. g1 b (\<gamma>\<^sub>o S) \<subseteq> \<gamma>\<^sub>o (g2 b S)"
  shows "Step f1 g1 (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (Step f2 g2 S C)"
proof(induction C arbitrary: S)
qed (auto simp: assms intro!: mono_gamma_o sup_ge1 sup_ge2)

lemma in_gamma_update: "\<lbrakk> s \<in> \<gamma>\<^sub>s S; i \<in> \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) \<in> \<gamma>\<^sub>s(update S x a)"
by(simp add: \<gamma>_st_def)

end


locale Abs_Int = Gamma_semilattice where \<gamma>=\<gamma>
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set"
begin

definition "step' = Step
  (\<lambda>x e S. case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S)))
  (\<lambda>b S. S)"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI c = pfp (step' \<top>) (bot c)"


lemma strip_step'[simp]: "strip(step' S C) = strip C"
by(simp add: step'_def)


text\<open>Correctness:\<close>

lemma step_step': "step (\<gamma>\<^sub>o S) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' S C)"
unfolding step_def step'_def
by(rule gamma_Step_subcomm)
  (auto simp: intro!: aval'_correct in_gamma_update split: option.splits)

lemma AI_correct: "AI c = Some C \<Longrightarrow> CS c \<le> \<gamma>\<^sub>c C"
proof(simp add: CS_def AI_def)
  assume 1: "pfp (step' \<top>) (bot c) = Some C"
  have pfp': "step' \<top> C \<le> C" by(rule pfp_pfp[OF 1])
  have 2: "step (\<gamma>\<^sub>o \<top>) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c C"  \<comment> \<open>transfer the pfp'\<close>
  proof(rule order_trans)
    show "step (\<gamma>\<^sub>o \<top>) (\<gamma>\<^sub>c C) \<le> \<gamma>\<^sub>c (step' \<top> C)" by(rule step_step')
    show "... \<le> \<gamma>\<^sub>c C" by (metis mono_gamma_c[OF pfp'])
  qed
  have 3: "strip (\<gamma>\<^sub>c C) = c" by(simp add: strip_pfp[OF _ 1] step'_def)
  have "lfp c (step (\<gamma>\<^sub>o \<top>)) \<le> \<gamma>\<^sub>c C"
    by(rule lfp_lowerbound[simplified,where f="step (\<gamma>\<^sub>o \<top>)", OF 3 2])
  thus "lfp c (step UNIV) \<le> \<gamma>\<^sub>c C" by simp
qed

end


subsubsection "Monotonicity"

locale Abs_Int_mono = Abs_Int +
assumes mono_plus': "a1 \<le> b1 \<Longrightarrow> a2 \<le> b2 \<Longrightarrow> plus' a1 a2 \<le> plus' b1 b2"
begin

lemma mono_aval': "S1 \<le> S2 \<Longrightarrow> aval' e S1 \<le> aval' e S2"
by(induction e) (auto simp: mono_plus' mono_fun)

theorem mono_step': "S1 \<le> S2 \<Longrightarrow> C1 \<le> C2 \<Longrightarrow> step' S1 C1 \<le> step' S2 C2"
unfolding step'_def
by(rule mono2_Step) (auto simp: mono_aval' split: option.split)

lemma mono_step'_top: "C \<le> C' \<Longrightarrow> step' \<top> C \<le> step' \<top> C'"
by (metis mono_step' order_refl)

lemma AI_least_pfp: assumes "AI c = Some C" "step' \<top> C' \<le> C'" "strip C' = c"
shows "C \<le> C'"
by(rule pfp_bot_least[OF _ _ assms(2,3) assms(1)[unfolded AI_def]])
  (simp_all add: mono_step'_top)

end


subsubsection "Termination"

locale Measure1 =
fixes m :: "'av::order_top \<Rightarrow> nat"
fixes h :: "nat"
assumes h: "m x \<le> h"
begin

definition m_s :: "'av st \<Rightarrow> vname set \<Rightarrow> nat" ("m\<^sub>s") where
"m_s S X = (\<Sum> x \<in> X. m(fun S x))"

lemma m_s_h: "finite X \<Longrightarrow> m_s S X \<le> h * card X"
by(simp add: m_s_def) (metis mult.commute of_nat_id sum_bounded_above[OF h])

definition m_o :: "'av st option \<Rightarrow> vname set \<Rightarrow> nat" ("m\<^sub>o") where
"m_o opt X = (case opt of None \<Rightarrow> h * card X + 1 | Some S \<Rightarrow> m_s S X)"

lemma m_o_h: "finite X \<Longrightarrow> m_o opt X \<le> (h*card X + 1)"
  by(auto simp add: m_o_def m_s_h le_SucI split: option.split dest:m_s_h)


definition m_c :: "'av st option acom \<Rightarrow> nat" ("m\<^sub>c") where
"m_c C = sum_list (map (\<lambda>a. m_o a (vars C)) (annos C))"
(*
text\<open>Upper complexity bound:\<close>

lemma m_c_h: "m_c C \<le> size(annos C) * (h * card(vars C) + 1)"
proof-
  let ?X = "vars C" let ?n = "card ?X" let ?a = "size(annos C)"
  have "m_c C = (\<Sum>i<?a. m_o (annos C ! i) ?X)"
    by(simp add: m_c_def sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> \<le> (\<Sum>i<?a. h * ?n + 1)"
    apply(rule sum_mono) using m_o_h[OF finite_Cvars] by simp
  also have "\<dots> = ?a * (h * ?n + 1)" by simp
  finally show ?thesis .
qed
*)

end

fun top_on_st :: "'a::order_top st \<Rightarrow> vname set \<Rightarrow> bool" ("top'_on\<^sub>s") where
"top_on_st S X = (\<forall>x\<in>X. fun S x = \<top>)"

fun top_on_opt :: "'a::order_top st option \<Rightarrow> vname set \<Rightarrow> bool" ("top'_on\<^sub>o") where
"top_on_opt (Some S)  X = top_on_st S X" |
"top_on_opt None X = True"

definition top_on_acom :: "'a::order_top st option acom \<Rightarrow> vname set \<Rightarrow> bool" ("top'_on\<^sub>c") where
"top_on_acom C X = (\<forall>a \<in> set(annos C). top_on_opt a X)"

lemma top_on_top: "top_on_opt (\<top>::_ st option) X"
by(auto simp: top_option_def fun_top)

lemma top_on_bot: "top_on_acom (bot c) X"
by(auto simp add: top_on_acom_def bot_def)

lemma top_on_post: "top_on_acom C X \<Longrightarrow> top_on_opt (post C) X"
by(simp add: top_on_acom_def post_in_annos)

lemma top_on_acom_simps:
  "top_on_acom (SKIP {Q}) X = top_on_opt Q X"
  "top_on_acom (x ::= e {Q}) X = top_on_opt Q X"
  "top_on_acom (C1;;C2) X = (top_on_acom C1 X \<and> top_on_acom C2 X)"
  "top_on_acom (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) X =
   (top_on_opt P1 X \<and> top_on_acom C1 X \<and> top_on_opt P2 X \<and> top_on_acom C2 X \<and> top_on_opt Q X)"
  "top_on_acom ({I} WHILE b DO {P} C {Q}) X =
   (top_on_opt I X \<and> top_on_acom C X \<and> top_on_opt P X \<and> top_on_opt Q X)"
by(auto simp add: top_on_acom_def)

lemma top_on_sup:
  "top_on_opt o1 X \<Longrightarrow> top_on_opt o2 X \<Longrightarrow> top_on_opt (o1 \<squnion> o2 :: _ st option) X"
apply(induction o1 o2 rule: sup_option.induct)
apply(auto)
by transfer simp

(*
lemma top_on_Step: fixes C :: "('a::semilattice_sup_top)st option acom"
assumes "!!x e S. \<lbrakk>top_on_opt S X; x \<notin> X; vars e \<subseteq> -X\<rbrakk> \<Longrightarrow> top_on_opt (f x e S) X"
        "!!b S. top_on_opt S X \<Longrightarrow> vars b \<subseteq> -X \<Longrightarrow> top_on_opt (g b S) X"
shows "\<lbrakk> vars C \<subseteq> -X; top_on_opt S X; top_on_acom C X \<rbrakk> \<Longrightarrow> top_on_acom (Step f g S C) X"
proof(induction C arbitrary: S)
qed (auto simp: top_on_acom_simps vars_acom_def top_on_post top_on_sup assms)
*)

locale Measure = Measure1 +
assumes m2: "x < y \<Longrightarrow> m x > m y"
begin

lemma m1: "x \<le> y \<Longrightarrow> m x \<ge> m y"
by(auto simp: le_less m2)

lemma m_s2_rep: assumes "finite(X)" and "S1 = S2 on -X" and "\<forall>x. S1 x \<le> S2 x" and "S1 \<noteq> S2"
shows "(\<Sum>x\<in>X. m (S2 x)) < (\<Sum>x\<in>X. m (S1 x))"
proof-
  from assms(3) have 1: "\<forall>x\<in>X. m(S1 x) \<ge> m(S2 x)" by (simp add: m1)
  from assms(2,3,4) have "\<exists>x\<in>X. S1 x < S2 x"
    by(simp add: fun_eq_iff) (metis Compl_iff le_neq_trans)
  hence 2: "\<exists>x\<in>X. m(S1 x) > m(S2 x)" by (metis m2)
  from sum_strict_mono_ex1[OF \<open>finite X\<close> 1 2]
  show "(\<Sum>x\<in>X. m (S2 x)) < (\<Sum>x\<in>X. m (S1 x))" .
qed

lemma m_s2: "finite(X) \<Longrightarrow> fun S1 = fun S2 on -X
  \<Longrightarrow> S1 < S2 \<Longrightarrow> m_s S1 X > m_s S2 X"
apply(auto simp add: less_st_def m_s_def)
apply (transfer fixing: m)
apply(simp add: less_eq_st_rep_iff eq_st_def m_s2_rep)
done

lemma m_o2: "finite X \<Longrightarrow> top_on_opt o1 (-X) \<Longrightarrow> top_on_opt o2 (-X) \<Longrightarrow>
  o1 < o2 \<Longrightarrow> m_o o1 X > m_o o2 X"
proof(induction o1 o2 rule: less_eq_option.induct)
  case 1 thus ?case by (auto simp: m_o_def m_s2 less_option_def)
next
  case 2 thus ?case by(auto simp: m_o_def less_option_def le_imp_less_Suc m_s_h)
next
  case 3 thus ?case by (auto simp: less_option_def)
qed

lemma m_o1: "finite X \<Longrightarrow> top_on_opt o1 (-X) \<Longrightarrow> top_on_opt o2 (-X) \<Longrightarrow>
  o1 \<le> o2 \<Longrightarrow> m_o o1 X \<ge> m_o o2 X"
by(auto simp: le_less m_o2)

(*
lemma m_c2: "top_on_acom C1 (-vars C1) \<Longrightarrow> top_on_acom C2 (-vars C2) \<Longrightarrow>
  C1 < C2 \<Longrightarrow> m_c C1 > m_c C2"
proof(auto simp add: le_iff_le_annos size_annos_same[of C1 C2] vars_acom_def less_acom_def)
  let ?X = "vars(strip C2)"
  assume top: "top_on_acom C1 (- vars(strip C2))"  "top_on_acom C2 (- vars(strip C2))"
  and strip_eq: "strip C1 = strip C2"
  and 0: "\<forall>i<size(annos C2). annos C1 ! i \<le> annos C2 ! i"
  hence 1: "\<forall>i<size(annos C2). m_o (annos C1 ! i) ?X \<ge> m_o (annos C2 ! i) ?X"
    apply (auto simp: all_set_conv_all_nth vars_acom_def top_on_acom_def)
    by (metis finite_cvars m_o1 size_annos_same2)
  fix i assume i: "i < size(annos C2)" "\<not> annos C2 ! i \<le> annos C1 ! i"
  have topo1: "top_on_opt (annos C1 ! i) (- ?X)"
    using i(1) top(1) by(simp add: top_on_acom_def size_annos_same[OF strip_eq])
  have topo2: "top_on_opt (annos C2 ! i) (- ?X)"
    using i(1) top(2) by(simp add: top_on_acom_def size_annos_same[OF strip_eq])
  from i have "m_o (annos C1 ! i) ?X > m_o (annos C2 ! i) ?X" (is "?P i")
    by (metis 0 less_option_def m_o2[OF finite_cvars topo1] topo2)
  hence 2: "\<exists>i < size(annos C2). ?P i" using \<open>i < size(annos C2)\<close> by blast
  have "(\<Sum>i<size(annos C2). m_o (annos C2 ! i) ?X)
         < (\<Sum>i<size(annos C2). m_o (annos C1 ! i) ?X)"
    apply(rule sum_strict_mono_ex1) using 1 2 by (auto)
  thus ?thesis
    by(simp add: m_c_def vars_acom_def strip_eq sum_list_sum_nth atLeast0LessThan size_annos_same[OF strip_eq])
qed
*)

end


locale Abs_Int_measure =
  Abs_Int_mono where \<gamma>=\<gamma> + Measure where m=m
  for \<gamma> :: "'av::semilattice_sup_top \<Rightarrow> val set" and m :: "'av \<Rightarrow> nat"
begin
(*
lemma top_on_step': "\<lbrakk> top_on_acom C (-vars C) \<rbrakk> \<Longrightarrow> top_on_acom (step' \<top> C) (-vars C)"
unfolding step'_def
by(rule top_on_Step)
  (auto simp add: top_option_def fun_top split: option.splits)

lemma AI_Some_measure: "\<exists>C. AI c = Some C"
unfolding AI_def
apply(rule pfp_termination[where I = "\<lambda>C. top_on_acom C (- vars C)" and m="m_c"])
apply(simp_all add: m_c2 mono_step'_top bot_least top_on_bot)
using top_on_step' apply(auto simp add: vars_acom_def)
done
*)
end
(* Abst_Int1 --------------------- END ---------------------*)



instantiation bounds :: semilattice_sup_top
begin

definition sup_bounds where 
  "sup_bounds x y = (case (x, y) of (B xs, B ys) \<Rightarrow> B (xs \<union> ys))"

definition top_bounds where
  "top_bounds = B {NegInf, PosInf, NaN, Real}"
 
instance
proof (standard, goal_cases)
  case (1 x y)
  then show ?case unfolding sup_bounds_def less_eq_bounds_def by(simp split: bounds.splits)
next
  case (2 y x)
  then show ?case unfolding sup_bounds_def less_eq_bounds_def by(simp split: bounds.splits)
next
  case (3 y x z)
  then show ?case unfolding sup_bounds_def less_eq_bounds_def by(simp split: bounds.splits)
next
  case (4 a)
  then show ?case
    unfolding top_bounds_def less_eq_bounds_def
    apply(simp split: bounds.splits)
    using Submission.bound.exhaust by blast
qed
end


fun \<gamma>_bounds :: "bounds \<Rightarrow> val set"  where
  "\<gamma>_bounds (B b) =
    (if PosInf \<in> b then {Some PInfty} else {})
    \<union> (if NegInf \<in> b then {Some MInfty} else {})
    \<union> (if Real \<in> b then {si. \<exists>i\<in>UNIV-{PInfty, MInfty}. si = Some i} else {})
    \<union> (if NaN \<in> b then {None} else {})"

lemma \<gamma>_bounds_excl:
  assumes "a = \<gamma>_bounds (B b)"
  shows "NaN \<notin> b \<Longrightarrow> None \<notin> a"
        "PosInf \<notin> b \<Longrightarrow> (Some PInfty) \<notin> a"
        "NegInf \<notin> b \<Longrightarrow> (Some MInfty) \<notin> a"
        "Real \<notin> b \<Longrightarrow> i \<noteq> PInfty \<Longrightarrow> i \<noteq> MInfty \<Longrightarrow> (Some i) \<notin> a"
  using assms by auto

lemma \<gamma>_bounds_incl:
  assumes "a = \<gamma>_bounds (B b)"
  shows "NaN \<in> b \<Longrightarrow> None \<in> a"
        "PosInf \<in> b \<Longrightarrow> (Some PInfty) \<in> a"
        "NegInf \<in> b \<Longrightarrow> (Some MInfty) \<in> a"
        "Real \<in> b \<Longrightarrow> i \<noteq> PInfty \<Longrightarrow> i \<noteq> MInfty \<Longrightarrow> (Some i) \<in> a"
  using assms by auto

lemma \<gamma>_bounds_backwards:
  assumes "a = \<gamma>_bounds (B b)"
  shows "None \<in> a \<Longrightarrow> NaN \<in> b"
        "(Some PInfty) \<in> a \<Longrightarrow> PosInf \<in> b"
        "(Some MInfty) \<in> a \<Longrightarrow> NegInf \<in> b"
        "(Some i) \<in> a \<Longrightarrow> i \<noteq> PInfty \<Longrightarrow> i \<noteq> MInfty \<Longrightarrow> Real \<in> b"
  using \<gamma>_bounds_excl(1) assms apply blast
  using \<gamma>_bounds_excl(2) assms apply blast
  using \<gamma>_bounds_excl(3) assms apply blast
  using \<gamma>_bounds_excl(4) assms by blast

  

definition num_bounds :: "ereal \<Rightarrow> bounds"  where
  "num_bounds er = B {(case er of
      PInfty \<Rightarrow> PosInf
    | MInfty => NegInf
    | _ \<Rightarrow> Real)}"

fun plus_bound_helper :: "bound \<Rightarrow> bound \<Rightarrow> bound" where
  "plus_bound_helper NaN _ = NaN" |
  "plus_bound_helper _ NaN = NaN" |
  "plus_bound_helper NegInf PosInf = NaN" |
  "plus_bound_helper PosInf NegInf = NaN" |
  "plus_bound_helper NegInf NegInf = NegInf" |
  "plus_bound_helper NegInf Real = NegInf" |
  "plus_bound_helper PosInf PosInf = PosInf" |
  "plus_bound_helper PosInf Real = PosInf" |
  "plus_bound_helper Real NegInf = NegInf" |
  "plus_bound_helper Real PosInf = PosInf" |
  "plus_bound_helper Real Real = Real"

fun plus_bounds :: "bounds \<Rightarrow> bounds \<Rightarrow> bounds"  where
  "plus_bounds (B b1) (B b2) = B {x. \<exists>bb1\<in>b1. \<exists>bb2\<in>b2. x = plus_bound_helper bb1 bb2}"

lemma plus_bounds_incl:
  assumes "plus_bounds (B b1) (B b2) = (B b3)"
      and "b1 \<noteq> {}"
      and "b2 \<noteq> {}"
    shows
      "NaN \<in> b1 \<Longrightarrow> NaN \<in> b3"
      "NaN \<in> b2 \<Longrightarrow> NaN \<in> b3"
      "NegInf \<in> b1 \<Longrightarrow> PosInf \<in> b2 \<Longrightarrow> NaN \<in> b3"
      "PosInf \<in> b1 \<Longrightarrow> NegInf \<in> b2 \<Longrightarrow> NaN \<in> b3"
      "NegInf \<in> b1 \<Longrightarrow> NegInf \<in> b2 \<Longrightarrow> NegInf \<in> b3"
      "NegInf \<in> b1 \<Longrightarrow> Real \<in> b2 \<Longrightarrow> NegInf \<in> b3"
      "PosInf \<in> b1 \<Longrightarrow> PosInf \<in> b2 \<Longrightarrow> PosInf \<in> b3"
      "PosInf \<in> b1 \<Longrightarrow> Real \<in> b2 \<Longrightarrow> PosInf \<in> b3"
      "Real \<in> b1 \<Longrightarrow> NegInf \<in> b2 \<Longrightarrow> NegInf \<in> b3"
      "Real \<in> b1 \<Longrightarrow> PosInf \<in> b2 \<Longrightarrow> PosInf \<in> b3"
      "Real \<in> b1 \<Longrightarrow> Real \<in> b2 \<Longrightarrow> Real \<in> b3"
  using assms proof-
    show "NaN \<in> b2 \<Longrightarrow> NaN \<in> b3"
    proof-
      assume "NaN \<in> b2"
      obtain e where "e\<in>b1" using assms(2) by auto
      then have "plus_bound_helper e NaN = NaN"
        using plus_bound_helper.elims by blast
      then show "NaN \<in> b3"
        using \<open>Submission.bound.NaN \<in> b2\<close> \<open>e \<in> b1\<close> assms(1) by fastforce
    qed
  qed(auto| fastforce)+

global_interpretation Val_semilattice
  where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
proof (standard, goal_cases)
  case (1 a b)
  then show ?case
    unfolding less_eq_bounds_def by(simp split: bounds.splits, blast)
next
  case 2
  then show ?case unfolding top_bounds_def by auto
next
  case (3 i)
  then show ?case unfolding num_bounds_def by(cases i, auto)
next
  case (4 i1 a1 i2 a2 j)
  obtain b\<^sub>1 where b1_def: "a1 = B b\<^sub>1"
    using \<gamma>_bounds.cases by auto
  then have "b\<^sub>1 \<noteq> {}" using 4(1) by auto
  obtain b\<^sub>2 where b2_def: "a2 = B b\<^sub>2"
    using \<gamma>_bounds.cases by auto
  then have "b\<^sub>2 \<noteq> {}" using 4(2) by auto
  obtain pb where pb_def: "B pb = plus_bounds a1 a2"
      using \<gamma>_bounds.cases by metis
  show ?case
  proof(cases i1)
    case None
    with 4 have "j = None" by simp
    with 4(1) have "NaN \<in> b\<^sub>1"
      using \<gamma>_bounds_backwards None b1_def by blast
    then have "NaN \<in> pb"
      using \<open>b\<^sub>1 \<noteq> {}\<close> \<open>b\<^sub>2 \<noteq> {}\<close> b1_def b2_def pb_def plus_bounds_incl(1) by auto
    then have "None \<in> \<gamma>_bounds (plus_bounds a1 a2)"
      using pb_def \<gamma>_bounds_incl by metis
    with \<open>j = None\<close> show ?thesis by simp
  next
    case (Some e1)
    then have i1_def: "i1 = Some e1" by simp
    then show ?thesis
    using 4 proof(cases i2)
      case None
      with 4 Some have "j = None" by(auto split: ereal.splits)
      with 4(2) have "NaN \<in> b\<^sub>2"
        using \<gamma>_bounds_backwards None b2_def by blast
      then have "NaN \<in> pb"
      using \<open>b\<^sub>1 \<noteq> {}\<close> \<open>b\<^sub>2 \<noteq> {}\<close> b1_def b2_def pb_def plus_bounds_incl(2) by auto
    then have "None \<in> \<gamma>_bounds (plus_bounds a1 a2)"
      using pb_def \<gamma>_bounds_incl by metis
      with \<open>j = None\<close> show ?thesis by simp
    next
      case (Some e2)
      then have i2_def: "i2 = Some e2" by simp
      then show ?thesis
      proof(cases e1)
        case (real r1)
        then have e1_def: "e1 = ereal r1" by simp
        with i1_def i2_def e1_def 4(3) have j_is_some: "j = Some (e1 + e2)" by simp
        have "Real \<in> b\<^sub>1"
            using 4(1) \<gamma>_bounds_excl(4) b1_def e1_def i1_def by blast
        show ?thesis
        proof(cases e2)
          case (real r2)
          then have "Real \<in> b\<^sub>2"
            using 4(2) \<gamma>_bounds_excl(4) b2_def i2_def by blast
          with \<open>Real \<in> b\<^sub>1\<close> have "Real \<in> pb"
            by (simp add: \<open>b\<^sub>1 \<noteq> {}\<close> \<open>b\<^sub>2 \<noteq> {}\<close> b1_def b2_def pb_def plus_bounds_incl(11))
          moreover have "e1 + e2 \<noteq> PInfty"
            by (simp add: e1_def real)
          moreover have "e1 + e2 \<noteq> MInfty"
            by (simp add: e1_def real)
          ultimately show ?thesis using j_is_some \<gamma>_bounds_incl(4) pb_def by metis
        next
          case PInf
          then have "PosInf \<in> b\<^sub>2"
            unfolding infinity_ereal_def using 4(2) \<gamma>_bounds_excl(2) b2_def i2_def by blast
          with \<open>Real \<in> b\<^sub>1\<close> have "PosInf \<in> pb"
            by (simp add: \<open>b\<^sub>1 \<noteq> {}\<close> \<open>b\<^sub>2 \<noteq> {}\<close> b1_def b2_def pb_def plus_bounds_incl(10))
          moreover from j_is_some PInf have "j = Some PInfty" by fastforce
          ultimately show ?thesis unfolding infinity_ereal_def using \<gamma>_bounds_incl(2) pb_def by metis
        next
          case MInf
          then have "NegInf \<in> b\<^sub>2"
            unfolding infinity_ereal_def using 4(2) \<gamma>_bounds_excl(3) b2_def i2_def
            by (metis uminus_ereal.simps(2))
          with \<open>Real \<in> b\<^sub>1\<close> have "NegInf \<in> pb"
            by (simp add: \<open>b\<^sub>1 \<noteq> {}\<close> \<open>b\<^sub>2 \<noteq> {}\<close> b1_def b2_def pb_def plus_bounds_incl(9))
          moreover from j_is_some MInf have "j = Some MInfty"
            by (simp add: real)
          ultimately show ?thesis unfolding infinity_ereal_def using \<gamma>_bounds_incl(3) pb_def by metis
        qed
      next
        case PInf
        then show ?thesis sorry
      next
        case MInf
        then show ?thesis sorry
      qed
    qed
  qed
qed

global_interpretation Abs_Int
where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
defines aval_bounds = aval' and step_bounds = step' and AI_bounds = AI
  ..


global_interpretation Abs_Int_mono
  where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
proof (standard, goal_cases)
  case (1 a1 b1 a2 b2)
  then show ?case unfolding less_eq_bounds_def by(cases a1;cases b1;cases a2;cases b2, auto)
qed

fun m_bounds :: "bounds \<Rightarrow> nat"  where
  "m_bounds _ = undefined"

abbreviation h_bounds :: nat where 
  "h_bounds = undefined"

global_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_bounds and num' = num_bounds and plus' = plus_bounds
and m = m_bounds and h = h_bounds
  sorry

end