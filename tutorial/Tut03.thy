theory Tut03
  imports "HOL-IMP.ASM"
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
app: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"

lemma star_prepend: "\<lbrakk>star r y z; r x y\<rbrakk> \<Longrightarrow> star r x z"
  by(induction rule:star.induct, auto intro: star.refl star.app)

lemma star_append: "\<lbrakk> star r x y; r y z \<rbrakk> \<Longrightarrow> star r x z"
  by(auto intro: app)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r  where
refl': "star' r x x" |
prep: "r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"

lemma star'_append: "\<lbrakk> star' r x y; r y z \<rbrakk> \<Longrightarrow> star' r x z"
  by(induction rule: star'.induct, auto intro: star'.intros)

lemma "star r x y = star' r x y"
proof
  assume "star r x y"
  thus "star' r x y" 
    by(induction rule: star.induct, auto intro: star'.intros star'_append)
next
  assume "star' r x y"
  thus  "star r x y"
    by(induction rule: star'.induct, auto intro: star.intros star_prepend)
qed

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option"  where
  "exec1 (LOADI n) _ stk  =  Some (n # stk)" |
  "exec1 (LOAD x) s stk  =  Some (s(x) # stk)" |
  "exec1  ADD _ (stk)  = (case stk of
    (i#j#stk) \<Rightarrow> Some ((i + j) # stk) |
    _ \<Rightarrow> None)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option"  where
  "exec [] _ stk = Some (stk)" |
  "exec (i#is) s stk = (case exec1 i s stk of
    Some stk \<Rightarrow> exec is s stk |
    _ \<Rightarrow> None)"

lemma exec_append: "exec (xs@ys) s stk = (case exec xs s stk of
  Some stk \<Rightarrow> exec ys s stk |
  None \<Rightarrow> None)"
  by(induction xs arbitrary: stk, auto split: option.splits)

theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
  by(induction a arbitrary: stk, auto simp: exec_append)

lemma 
  assumes total: "\<forall> x y. T x y \<or> T y x"
      and anti: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
      and subset: "\<forall> x y. T x y \<longrightarrow> A x y"
  shows "A x y \<longrightarrow> T x y"
proof
  fix x y
  assume "A x y"
  from total have "T x y \<or> T y x" by simp
  then show "T x y"
  proof (cases)
    assume "T x y"
    then show "T x y" .
  next
    assume "\<not>T x y"
    with \<open>T x y \<or> T y x\<close> have "T y x" by simp
    with subset have "A y x" by simp
    with \<open>A x y\<close> anti have "x = y" by simp
    with \<open>T y x\<close> show "T x y" by simp
  qed
qed

end