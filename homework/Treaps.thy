theory Treaps
  imports Main "HOL-IMP.Com" "HOL.Complex"
begin

datatype ('a::linorder) treap =
  Leaf ("\<langle>\<rangle>") |
  Node "'a treap" ("key": 'a) ("prio": real) "'a treap" ("(1\<langle>_,/ _,/ _,/ _\<rangle>)")

primrec key :: "('a::linorder) treap \<Rightarrow> 'a" where
  "key \<langle>l, k, p, r\<rangle> = k" |
  "key \<langle>\<rangle> = undefined"

primrec prio :: "('a::linorder) treap \<Rightarrow> real" where
  "prio \<langle>l, k, p, r\<rangle> = p" |
  "prio \<langle>\<rangle> = undefined"

primrec left :: "('a::linorder) treap \<Rightarrow> 'a treap" where
  "left \<langle>l, k, p, r\<rangle> = l" |
  "left \<langle>\<rangle> = \<langle>\<rangle>"

primrec right :: "('a::linorder) treap \<Rightarrow> 'a treap" where
  "right \<langle>l, k, p, r\<rangle> = r" |
  "right \<langle>\<rangle> = \<langle>\<rangle>"

fun height :: "('a::linorder) treap \<Rightarrow> nat" where
  "height \<langle>\<rangle> = 0" |
  "height \<langle>l, k, p, r\<rangle> = max (height l) (height r) + 1"

fun min_height :: "('a::linorder) treap \<Rightarrow> nat" where
  "min_height \<langle>\<rangle> = 0" |
  "min_height \<langle>l, k, p, r\<rangle> = min (height l) (height r) + 1"

fun size :: "('a::linorder) treap \<Rightarrow> nat" where
  "size \<langle>\<rangle> = 0" |
  "size \<langle>l, k, p, r\<rangle> = (size l) + (size r) + 1"

fun set :: "('a::linorder) treap \<Rightarrow> ('a \<times> real) set" where
  Leaf: "set \<langle>\<rangle> = {}" |
  Node: "set \<langle>l, k, p, r\<rangle> = {(k, p)} \<union> set l \<union> set r"

fun keys :: "('a::linorder) treap \<Rightarrow> 'a set" where
  "keys \<langle>\<rangle> = {}" |
  "keys \<langle>l, k, p, r\<rangle> = {k} \<union> keys l \<union> keys r"

fun prios :: "('a::linorder) treap \<Rightarrow> real set" where
  "prios \<langle>\<rangle> = {}" |
  "prios \<langle>l, k, p, r\<rangle> = {p} \<union> prios l \<union> prios r"

lemma set_finite: "finite (set t)" by(induction t, auto)
lemma keys_finite: "finite (keys t)" by(induction t, auto)
lemma prios_finite: "finite (prios t)" by(induction t, auto)

inductive child_of :: "('a::linorder) treap \<Rightarrow> ('a::linorder) treap \<Rightarrow> bool" where
  Left: "child_of l \<langle>l, k, p, r\<rangle>" |
  Right: "child_of r \<langle>l, k, p, r\<rangle>" |
  Cont: "\<lbrakk> child_of a b; child_of b c \<rbrakk> \<Longrightarrow> child_of a c"

definition parent_of :: "('a::linorder) treap \<Rightarrow> ('a::linorder) treap \<Rightarrow> bool" where
  "parent_of a b \<equiv> child_of b a"

inductive distinct_keys :: "('a::linorder) treap \<Rightarrow> bool" where
  Leaf: "distinct_keys \<langle>\<rangle> " |
  Node: "\<lbrakk> distinct_keys l; distinct_keys r;
        \<forall>(x\<^sub>k, x\<^sub>p) \<in> set l . x\<^sub>k \<noteq> k; \<forall>(x\<^sub>k, x\<^sub>p) \<in> set r . x\<^sub>k \<noteq> k;
        \<forall>(l\<^sub>k, l\<^sub>p) \<in> set l. \<forall>(r\<^sub>k, r\<^sub>p) \<in> set r. l\<^sub>k \<noteq> r\<^sub>k \<rbrakk>
        \<Longrightarrow> distinct_keys \<langle>l, k, p, r\<rangle>"

inductive distinct_prios :: "('a::linorder) treap \<Rightarrow> bool" where
  Leaf: "distinct_prios \<langle>\<rangle> " |
  Node: "\<lbrakk> distinct_prios l; distinct_prios r;
        \<forall>(x\<^sub>k, x\<^sub>p) \<in> set l. x\<^sub>p \<noteq> p; \<forall>(x\<^sub>k, x\<^sub>p) \<in> set r. x\<^sub>p \<noteq> p;
        \<forall>(l\<^sub>k, l\<^sub>p) \<in> set l. \<forall>(r\<^sub>k, r\<^sub>p) \<in> set r. l\<^sub>p \<noteq> r\<^sub>p \<rbrakk>
        \<Longrightarrow> distinct_prios \<langle>l, k, p, r\<rangle>"

definition is_distinct :: "('a::linorder) treap \<Rightarrow> bool" where
  "is_distinct t \<equiv> distinct_keys t \<and> distinct_prios t"

lemma distinct_rev: "is_distinct \<langle>l, k, p, r\<rangle> \<Longrightarrow> is_distinct l \<and> is_distinct r"
proof-
  assume t_dist: "is_distinct \<langle>l, k, p, r\<rangle>"
  let ?t = "\<langle>l, k, p, r\<rangle>"
  from t_dist have "distinct_keys ?t"
    using is_distinct_def by blast
  then have "distinct_keys l"
    using distinct_keys.simps by fast
  moreover
  from t_dist have "distinct_prios ?t"
    using is_distinct_def by blast
  then have "distinct_prios l"
    using distinct_prios.simps by fast
  moreover
  from t_dist have "distinct_keys ?t"
    using is_distinct_def by blast
  then have "distinct_keys r"
    using distinct_keys.simps by force
  moreover
  from t_dist have "distinct_prios ?t"
    using is_distinct_def by blast
  then have "distinct_prios r"
    using distinct_prios.simps by force
  ultimately show "is_distinct l  \<and> is_distinct r"
    by (simp add: is_distinct_def)
qed

lemma distinct_root_key: "distinct_keys \<langle>l, k, p, r\<rangle> \<Longrightarrow> (k, p) \<notin> set l \<union> set r"
  by(induction "\<langle>l, k, p, r\<rangle>" arbitrary: k p rule: distinct_keys.induct, auto)

lemma distinct_root: "is_distinct \<langle>l, k, p, r\<rangle> \<Longrightarrow> (k, p) \<notin> set l \<union> set r"
  using distinct_root_key is_distinct_def by blast

lemma child_dist_if_parent_dist:
  assumes "child_of c p"
      and "is_distinct p"
    shows "is_distinct c"
  using assms distinct_rev by(induction c p rule: child_of.induct, auto)

lemma lrchilds_disjoint_key: "distinct_keys \<langle>l, k, p, r\<rangle> \<Longrightarrow> set l \<inter> set r = {}"
  by(induction "\<langle>l, k, p, r\<rangle>" arbitrary: k p rule: distinct_keys.induct, auto)

lemma lrchilds_disjoint: "is_distinct \<langle>l, k, p, r\<rangle> \<Longrightarrow> set l \<inter> set r = {}"
  using lrchilds_disjoint_key is_distinct_def by blast

lemma size_correct: "is_distinct t \<Longrightarrow> size t = card (set t)"
proof(induction t)
  case (Node l k p r)
  then have "is_distinct l"
    using distinct_rev by auto
  then have "size l = card (set l)"
    by (simp add: Node.IH(1))
  moreover from Node.prems have "is_distinct r"
    using distinct_rev by auto
  then have "size r = card (set r)"
    by (simp add: Node.IH(2))
  ultimately have "size \<langle>l, k, p, r\<rangle> = card (set l) + card (set r) + 1"
    by simp
  also have "... = card (set l \<union> set r) + 1"
    using Node.prems lrchilds_disjoint set_finite card_Un_disjoint
    by metis
  also have "... = card (set \<langle>l, k, p, r\<rangle> - {(k, p)}) + 1"
    using Node.prems distinct_root by fastforce
  also have "... = card (set \<langle>l, k, p, r\<rangle> - {(k, p)}) + card ({(k, p)})"
    by simp
  also have "... = card (set \<langle>l, k, p, r\<rangle> - {(k, p)} \<union> {(k, p)})"
    by (metis Diff_disjoint add.commute card_Un_disjoint finite.emptyI finite.insertI finite_Diff2 set_finite sup_commute)
  also have "... = card (set \<langle>l, k, p, r\<rangle>)"
    by simp
  finally show ?case .
qed(simp)

lemma set_of_childs:
  assumes "is_distinct t"
  shows "set t - {(key t, prio t)} = set (left t) \<union> set (right t)"
using assms proof(induction t rule: set.induct)
  case (2 l k p r)
  let ?t = "\<langle>l, k, p, r\<rangle>"
  from "2.prems" have "(k, p) \<notin> set l \<union> set r"
    using is_distinct_def distinct_root by blast
  then show ?case by simp
qed(simp)

lemma pair_unique:
  assumes "is_distinct t" 
      and "(k\<^sub>1, p\<^sub>1)\<in> set t" "(k\<^sub>2, p\<^sub>2)\<in> set t"
    shows "k\<^sub>1 = k\<^sub>2 \<longleftrightarrow> p\<^sub>1 = p\<^sub>2"
proof
  show "k\<^sub>1 = k\<^sub>2 \<Longrightarrow> p\<^sub>1 = p\<^sub>2"
  using assms proof(induction t arbitrary: k\<^sub>1 p\<^sub>1 k\<^sub>2 p\<^sub>2)
    case (Node l k p r)
    then show ?case
    using assms proof(cases "p\<^sub>1 = p\<^sub>2")
      case False
      then show "k\<^sub>1 = k\<^sub>2 \<Longrightarrow> p\<^sub>1 = p\<^sub>2" using assms sorry
    qed(simp)
  qed(simp)
next
  show "p\<^sub>1 = p\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2" sorry
  oops

inductive is_bst :: "('a::linorder) treap \<Rightarrow> bool" where
  Leaf: "is_bst \<langle>\<rangle>" |
  Node: "\<lbrakk> is_bst l; is_bst r;
        \<forall>(x\<^sub>k, x\<^sub>p) \<in> set l. x\<^sub>k < k; \<forall>(x\<^sub>k, x\<^sub>p) \<in> set r. k < x\<^sub>k \<rbrakk>
        \<Longrightarrow> is_bst \<langle>l, k, p, r\<rangle>"

thm is_bst.induct
lemma bst_rev:
  "is_bst \<langle>l, k, p, r\<rangle> \<Longrightarrow> is_bst l \<and> is_bst r \<and> (\<forall>(x\<^sub>k, x\<^sub>p) \<in> set l . x\<^sub>k < k) \<and> (\<forall>(x\<^sub>k, x\<^sub>p) \<in> set r . k < x\<^sub>k)"
  by(induction "\<langle>l, k, p, r\<rangle>" rule: is_bst.induct, blast)

lemma smaller_key_is_left_child:
  assumes "is_bst t"
and "is_distinct t"
  and "(k, d) \<in> set t"
shows "k < key t \<Longrightarrow> (k, d) \<in> set (left t)"
  using assms by(induction t arbitrary: k d rule: is_bst.induct, auto)

lemma larger_key_is_right_child:
  assumes "is_bst t"
and "is_distinct t"
  and "(k, d) \<in> set t"
shows "key t < k \<Longrightarrow> (k, d) \<in> set (right t)"
  using assms by(induction t arbitrary: k d rule: is_bst.induct, auto)

inductive is_heap :: "('a::linorder) treap \<Rightarrow> bool" where
  Leaf: "is_heap \<langle>\<rangle>" |
  Node: "\<lbrakk>is_heap l; is_heap r; prio l > p; prio r > p \<rbrakk>
        \<Longrightarrow> is_heap \<langle>l, k, p, r\<rangle>"

lemma heap_root_has_smallest_prio:
  assumes "is_heap t"
      and "is_distinct t"
    shows "\<forall>(k', p') \<in> set (left t) \<union> set (right t). prio t < p'"
using assms proof(induction t arbitrary: p rule: is_heap.induct)
  case (Node l r p k)
  obtain p\<^sub>l p\<^sub>r where p_defs: "p\<^sub>l = prio l" "p\<^sub>r = prio r" by blast
  have p_less_pl: "p < p\<^sub>l"
    using Node.hyps(3) Node.prems p_defs(1) by auto
  moreover have "p < p\<^sub>r"
    using Node.hyps(4) Node.prems p_defs(2) by auto
  moreover have
    "\<forall>(k', p') \<in> set (left l) \<union> set (right l). p\<^sub>l < p'"
    "\<forall>(k', p') \<in> set (left r) \<union> set (right r). p\<^sub>r < p'"
    using Node.IH(1, 2) Node.prems Treaps.distinct_rev p_defs by blast+
  ultimately have
    "\<forall>(k', p') \<in> set (left l) \<union> set (right l). p < p'"
    "\<forall>(k', p') \<in> set (left r) \<union> set (right r). p < p'"
    by (smt (verit, ccfv_SIG) case_prodD case_prodI2)+
  then have
    "\<forall>(k', p') \<in> set l. p < p'"
    "\<forall>(k', p') \<in> set r. p < p'"
    using p_less_pl Node.hyps(3,4) Node.prems distinct_rev set_of_childs by blast+
  then show ?case
    by force
qed(simp)

definition is_treap :: "('a::linorder) treap \<Rightarrow> bool" where
  "is_treap t \<equiv> is_bst t \<and> is_heap t"

lemma empty_treap_is_leaf:
"set t = {} \<longleftrightarrow> t = \<langle>\<rangle>"
proof
  assume empty_set: "set t = {}"
  then show "t = \<langle>\<rangle>" by(cases t, auto)
qed(simp)

theorem treap_is_unique:
  assumes distinct:      "is_distinct t\<^sub>1" "is_distinct t\<^sub>2"
      and treaps:        "is_treap t\<^sub>1" "is_treap t\<^sub>2"
      and equal_entries[simp]: "set t\<^sub>1 = set t\<^sub>2"
    shows "t\<^sub>1 = t\<^sub>2"
using assms proof(induction t\<^sub>1 arbitrary: t\<^sub>2 rule:treap.induct)
  case Leaf
    then have "set t\<^sub>2 = {}"
      by simp
    then have "t\<^sub>2 = \<langle>\<rangle>"
      using empty_treap_is_leaf by auto
    then show ?case
      by simp
next
  case (Node l\<^sub>1 k\<^sub>1 p\<^sub>1 r\<^sub>1)
  let ?t\<^sub>1 = "\<langle>l\<^sub>1, k\<^sub>1, p\<^sub>1, r\<^sub>1\<rangle>"
  let ?entries = "set ?t\<^sub>1"
  have not_leaf: "t\<^sub>2 \<noteq> \<langle>\<rangle>"
    using Node.prems(5) by force
  then obtain l\<^sub>2 k\<^sub>2 p\<^sub>2 r\<^sub>2 where t2_def: "t\<^sub>2 = \<langle>l\<^sub>2, k\<^sub>2, p\<^sub>2, r\<^sub>2\<rangle>"
    using height.cases by blast
  let ?t\<^sub>2 = "\<langle>l\<^sub>2, k\<^sub>2, p\<^sub>2, r\<^sub>2\<rangle>"
  have "is_treap l\<^sub>2" "is_treap r\<^sub>2"
    using Node.prems(4) is_heap.cases is_bst.cases is_treap_def t2_def by fastforce+

  (* roots eq *)
  have "\<forall>(k', p') \<in> set (left ?t\<^sub>1) \<union> set (right ?t\<^sub>1). prio ?t\<^sub>1 < p'"
    using Node.prems(1, 3) heap_root_has_smallest_prio is_treap_def by blast
  then have "\<forall>(k', p') \<in> ?entries - {(k\<^sub>1, p\<^sub>1)}. prio ?t\<^sub>1 < p'"
    by simp
  then have "\<forall>(k', p') \<in> ?entries - {(k\<^sub>1, p\<^sub>1)}. prio ?t\<^sub>1 \<le> p'"
    using less_imp_le by blast
  then have "\<forall>(k', p') \<in> set ?t\<^sub>1. prio ?t\<^sub>1 \<le> p'" by auto
  moreover have "\<forall>(k', p') \<in> set (left ?t\<^sub>2) \<union> set (right ?t\<^sub>2). prio ?t\<^sub>2 < p'"
    using Node.prems(2, 4) heap_root_has_smallest_prio is_treap_def t2_def by blast
  then have root2_smallest_prio: "\<forall>(k', p') \<in> set ?t\<^sub>2 - {(k\<^sub>2, p\<^sub>2)}. prio ?t\<^sub>2 < p'"
    by simp
  then have "\<forall>(k', p') \<in> set ?t\<^sub>2 - {(k\<^sub>2, p\<^sub>2)}. prio ?t\<^sub>2 \<le> p'"
    using less_imp_le by blast
  then have "\<forall>(k', p') \<in> ?entries. prio ?t\<^sub>2 \<le> p'"
    using Node.prems(5) t2_def by auto
  moreover have root1_in_set: "(k\<^sub>1, p\<^sub>1) \<in> ?entries"
    by force
  moreover have root2_in_set: "(k\<^sub>2, p\<^sub>2) \<in> ?entries"
    using Node.prems(5) t2_def by auto
  ultimately have equal_prio:  "prio ?t\<^sub>1 = prio ?t\<^sub>2"
    by fastforce
  then have roots_eq_prios: "p\<^sub>1 = p\<^sub>2" by simp
  then have roots_eq_keys: "k\<^sub>1 = k\<^sub>2"
    using Node.prems(5) case_prodD root1_in_set root2_smallest_prio t2_def by fastforce

  (* left subtree eq *)
  have "\<forall>(k', p') \<in> ?entries. k' < key ?t\<^sub>1 \<longrightarrow> (k', p') \<in> set (left ?t\<^sub>1)"
    using Node.prems(1,3) is_treap_def smaller_key_is_left_child by fastforce
  moreover have "\<forall>(k', p') \<in> ?entries.  \<not>k' < key ?t\<^sub>1 \<longrightarrow> (k', p') \<notin> set (left ?t\<^sub>1)"
    using Node.prems(3) bst_rev is_treap_def by force
  moreover have "set (left ?t\<^sub>1) \<subseteq> ?entries"
    by auto
  ultimately have left1: "{(k', p') \<in> ?entries. k' < key ?t\<^sub>1} = set (left ?t\<^sub>1)"
    by blast

  have "\<forall>(k', p') \<in> ?entries. k' < key ?t\<^sub>2 \<longrightarrow> (k', p') \<in> set (left ?t\<^sub>2)"
    using Node.prems(2,4,5) is_treap_def smaller_key_is_left_child t2_def by fastforce
  moreover have "\<forall>(k', p') \<in> ?entries.  \<not>k' < key ?t\<^sub>2 \<longrightarrow> (k', p') \<notin> set (left ?t\<^sub>2)"
    using Node.prems(4) bst_rev is_treap_def t2_def
    by (metis (no_types, lifting) case_prodD case_prodI2 key.simps(1) left.simps(1))
  moreover have "set (left ?t\<^sub>2) \<subseteq> ?entries"
    using Node.prems(5) t2_def by auto
  ultimately have left2: "{(k', p') \<in> ?entries. k' < key ?t\<^sub>2} = set (left ?t\<^sub>2)"
    by blast

  from left1 left2 have "set (left ?t\<^sub>1) = set (left ?t\<^sub>2)"
    by (simp add: roots_eq_keys)
  then have left_subtrees_eq: "l\<^sub>1 = l\<^sub>2"
    using Node.IH(1) \<open>is_treap l\<^sub>2\<close> Node.prems distinct_rev bst_rev is_heap.cases is_treap_def t2_def
    by (metis left.simps(1) treap.distinct(1))

  (* right subtree eq *)
  have "\<forall>(k', p') \<in> ?entries. key ?t\<^sub>1 < k' \<longrightarrow> (k', p') \<in> set (right ?t\<^sub>1)"
    using Node.prems(1,3) is_treap_def larger_key_is_right_child by fastforce
  moreover have "\<forall>(k', p') \<in> ?entries.  \<not>key ?t\<^sub>1 < k' \<longrightarrow> (k', p') \<notin> set (right ?t\<^sub>1)"
    using Node.prems(3) bst_rev is_treap_def by force
  moreover have "set (right ?t\<^sub>1) \<subseteq> ?entries"
    by auto
  ultimately have right1: "{(k', p') \<in> ?entries. key ?t\<^sub>1 < k'} = set (right ?t\<^sub>1)"
    by blast

  have "\<forall>(k', p') \<in> ?entries.  key ?t\<^sub>2 < k' \<longrightarrow> (k', p') \<in> set (right ?t\<^sub>2)"
    using Node.prems(2,4,5) is_treap_def larger_key_is_right_child t2_def by fastforce
  moreover have "\<forall>(k', p') \<in> ?entries.  \<not>key ?t\<^sub>2 < k' \<longrightarrow> (k', p') \<notin> set (right ?t\<^sub>2)"
    using Node.prems(4) bst_rev is_treap_def t2_def
    by (metis (no_types, lifting) case_prodD case_prodI2 key.simps(1) right.simps(1))
  moreover have "set (right ?t\<^sub>2) \<subseteq> ?entries"
    using Node.prems(5) t2_def by auto
  ultimately have right2: "{(k', p') \<in> ?entries. key ?t\<^sub>2 < k'} = set (right ?t\<^sub>2)"
    by blast

  from right1 right2 have "set (right ?t\<^sub>1) = set (right ?t\<^sub>2)"
    by (simp add: roots_eq_keys)
  then have right_subtrees_eq: "r\<^sub>1 = r\<^sub>2"
    using Node.IH(2) \<open>is_treap r\<^sub>2\<close> Node.prems distinct_rev bst_rev is_heap.cases is_treap_def t2_def
    by (metis right.simps(1) treap.distinct(1))

  from left_subtrees_eq right_subtrees_eq show ?case
    by (simp add: roots_eq_keys roots_eq_prios t2_def)
qed

end