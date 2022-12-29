theory Treaps
  imports Main "HOL.Real"
begin

datatype ('a::linorder) treap =
  Leaf ("\<langle>\<rangle>") |
  Node "'a treap" ("key": 'a) ("prio": real) "'a treap" ("(1\<langle>_,/ _,/ _,/ _\<rangle>)")

primrec key :: "('a::linorder) treap \<Rightarrow> 'a" where
  "key \<langle>l, k, p, r\<rangle> = k" |
  "key \<langle>\<rangle> = undefined"

primrec prio :: "('a::linorder) treap \<Rightarrow> real" where
  "prio \<langle>l, k, p, r\<rangle> = p" |
  "prio \<langle>\<rangle> = 1"

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

lemma set_finite: "finite (set t)" by(induction t, auto)
lemma child_subset: "set (left t) \<subseteq> set t" "set (right t) \<subseteq> set t" by(induction t, auto)
lemma not_in_set_not_in_tree:
  assumes "t \<noteq> \<langle>\<rangle>"
      and "(k, p) \<notin> set t"
    shows "(k, p) \<noteq> (key t, prio t) \<and> (k, p) \<notin> set (left t) \<and> (k, p) \<notin> set (right t)"
  using assms by(induction t, auto)

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

inductive is_bst :: "('a::linorder) treap \<Rightarrow> bool" where
  Leaf: "is_bst \<langle>\<rangle>" |
  Node: "\<lbrakk> is_bst l; is_bst r;
        \<forall>(x\<^sub>k, x\<^sub>p) \<in> set l. x\<^sub>k < k; \<forall>(x\<^sub>k, x\<^sub>p) \<in> set r. k < x\<^sub>k \<rbrakk>
        \<Longrightarrow> is_bst \<langle>l, k, p, r\<rangle>"

lemma bst_rev:
  "is_bst \<langle>l, k, p, r\<rangle> \<Longrightarrow> is_bst l \<and> is_bst r \<and> (\<forall>(x\<^sub>k, x\<^sub>p) \<in> set l . x\<^sub>k < k) \<and> (\<forall>(x\<^sub>k, x\<^sub>p) \<in> set r . k < x\<^sub>k)"
  by(induction "\<langle>l, k, p, r\<rangle>" rule: is_bst.induct, blast)

lemma uni_bst[simp]: "is_bst \<langle>\<langle>\<rangle>, k, p, \<langle>\<rangle>\<rangle>"
proof-
  let ?l = "\<langle>\<rangle>" let ?r = "\<langle>\<rangle>"
  have "set \<langle>\<rangle> = {}" by simp
  have "is_bst ?l" by (simp add: is_bst.Leaf)
  moreover have "is_bst ?r" by (simp add: is_bst.Leaf)
  moreover have "\<forall>(x\<^sub>k, x\<^sub>p) \<in> set ?l. x\<^sub>k < k" by simp
  moreover have "\<forall>(x\<^sub>k, x\<^sub>p) \<in> set ?r. k < x\<^sub>k" by simp
  ultimately have "is_bst \<langle>?l, k, p, ?r\<rangle>"
    using is_bst.simps by fastforce
  then show "is_bst \<langle>\<langle>\<rangle>, k, p, \<langle>\<rangle>\<rangle>" by simp
qed

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

definition is_valid_prio :: "real \<Rightarrow> bool" where
  "is_valid_prio p \<equiv> 0 < p \<and> p < 1"

inductive is_heap :: "('a::linorder) treap \<Rightarrow> bool" where
  Leaf: "is_heap \<langle>\<rangle>" |
  Node: "\<lbrakk>is_heap l; is_heap r; prio l > p; prio r > p; is_valid_prio p \<rbrakk>
        \<Longrightarrow> is_heap \<langle>l, k, p, r\<rangle>"

lemma uni_heap[simp]: "is_valid_prio p \<Longrightarrow> is_heap \<langle>\<langle>\<rangle>, k, p, \<langle>\<rangle>\<rangle>"
proof-
  assume p_valid: "is_valid_prio p"
  let ?l = "\<langle>\<rangle>" let ?r = "\<langle>\<rangle>"
  have "set \<langle>\<rangle> = {}" by simp
  have "is_heap ?l" by (simp add: is_heap.Leaf)
  moreover have "is_heap ?r" by (simp add: is_heap.Leaf)
  moreover have "prio ?l = 1"
    by simp
  then have "prio ?l > p" using p_valid by (simp add: is_valid_prio_def)
  moreover have "prio ?r = 1"
    by simp
  then have "prio ?r > p" using p_valid by (simp add: is_valid_prio_def)
  ultimately have "is_heap \<langle>?l, k, p, ?r\<rangle>"
    using is_heap.Node p_valid by blast
  then show "is_heap \<langle>\<langle>\<rangle>, k, p, \<langle>\<rangle>\<rangle>" by simp
qed

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

fun bst_insert :: "('a::linorder) \<Rightarrow> real \<Rightarrow> 'a treap \<Rightarrow> 'a treap" where
  "bst_insert k p \<langle>\<rangle> = \<langle>\<langle>\<rangle>, k, p, \<langle>\<rangle>\<rangle>" |
  "bst_insert k p \<langle>l, k', p', r\<rangle> = (if k < k' then \<langle>bst_insert k p l, k', p', r\<rangle> else \<langle>l, k', p', bst_insert k p r\<rangle>)"

lemma bst_insert_correct: "is_bst t \<Longrightarrow> set (bst_insert k p t) = set t \<union> {(k, p)}"
  by(induction t arbitrary: k p rule: is_bst.induct, cases "k < k'", auto)

lemma "is_bst t \<Longrightarrow>\<forall>p. (k, p) \<notin> set t \<Longrightarrow> is_bst (bst_insert k p t)"
proof(induction t arbitrary: k p rule: is_bst.induct)
  case (Node l r k' p')
  then have "k \<noteq> k'" by auto
  then show ?case
  proof(cases "k < k'")
    case True
    then have "\<forall>p. (k, p) \<notin> set l" using Node.prems by auto
    then have lih: "is_bst (bst_insert k p l)" by (simp add: Node.IH(1))
    from True have "bst_insert k p \<langle>l, k', p', r\<rangle> = \<langle>bst_insert k p l, k', p', r\<rangle>" by simp
    moreover have "\<forall>(x\<^sub>k, x\<^sub>p) \<in> set l. x\<^sub>k < k'" by (simp add: Node.hyps(3))
    then have "\<forall>(x\<^sub>k, x\<^sub>p) \<in> set (bst_insert k p l). x\<^sub>k < k'"
      by (simp add: Node.hyps(1) True bst_insert_correct)
    ultimately show ?thesis
      by (simp add: Node.hyps(2) Node.hyps(4) is_bst.Node lih)
  next
    case False
    then have "k' < k" using \<open>k \<noteq> k'\<close> by auto
    then have "\<forall>p. (k, p) \<notin> set r" using Node.prems by auto
    then have rih: "is_bst (bst_insert k p r)" by (simp add: Node.IH(2))
    from False have "bst_insert k p \<langle>l, k', p', r\<rangle> = \<langle>l, k', p', bst_insert k p r\<rangle>" by simp
    moreover have "\<forall>(x\<^sub>k, x\<^sub>p) \<in> set r. k' < x\<^sub>k" by (simp add: Node.hyps(4))
    then have "\<forall>(x\<^sub>k, x\<^sub>p) \<in> set (bst_insert k p r). k' < x\<^sub>k"
      by (simp add: Node.hyps(2) \<open>k' < k\<close> bst_insert_correct)
    ultimately show ?thesis
      by (simp add: Node.hyps(1) Node.hyps(3) is_bst.Node rih)
  qed
qed(simp)

fun search :: "('a::linorder) \<Rightarrow> 'a treap \<Rightarrow> bool" where
  "search k \<langle>\<rangle> = False" |
  "search k \<langle>l, k', _, r\<rangle> = (if k = k' then True else if k < k' then search k l else search k r)"

lemma search_correct1: "is_bst t \<Longrightarrow> \<exists>p. (k, p) \<in> set t \<Longrightarrow> search k t"
  by(induction t arbitrary: k rule: is_bst.induct, auto)
lemma search_correct2: "is_bst t \<Longrightarrow> \<forall>p. (k, p) \<notin> set t \<Longrightarrow> \<not>search k t"
  by(induction t arbitrary: k rule: is_bst.induct, auto)
lemma search_correct: "is_bst t \<Longrightarrow> search k t \<longleftrightarrow> (\<exists>p. (k, p) \<in> set t)"
  using search_correct1 search_correct2 by blast


fun insert_prio :: "('a::linorder) \<Rightarrow> real \<Rightarrow> 'a treap \<Rightarrow> 'a treap" where
  "insert_prio k p \<langle>\<rangle> = \<langle>\<langle>\<rangle>, k, p, \<langle>\<rangle>\<rangle>" |
  "insert_prio k p \<langle>l\<^sub>r, k\<^sub>r, p\<^sub>r, r\<^sub>r\<rangle> =
    (if k < k\<^sub>r then
      (case insert_prio k p l\<^sub>r of
        \<langle>l\<^sub>c, k\<^sub>c, p\<^sub>c, r\<^sub>c\<rangle> \<Rightarrow>
          (if p\<^sub>r > p\<^sub>c then \<langle>l\<^sub>c, k\<^sub>c, p\<^sub>c, \<langle>r\<^sub>c, k\<^sub>r, p\<^sub>r, r\<^sub>r\<rangle>\<rangle>
          else \<langle>\<langle>l\<^sub>c, k\<^sub>c, p\<^sub>c, r\<^sub>c\<rangle>, k\<^sub>r, p\<^sub>r, r\<^sub>r\<rangle>) |
        _ \<Rightarrow> undefined)
    else
      (case insert_prio k p r\<^sub>r of
        \<langle>l\<^sub>c, k\<^sub>c, p\<^sub>c, r\<^sub>c\<rangle> \<Rightarrow>
          (if p\<^sub>r > p\<^sub>c then\<langle>\<langle>l\<^sub>r, k\<^sub>r, p\<^sub>r, l\<^sub>c\<rangle>, k\<^sub>c, p\<^sub>c, r\<^sub>c\<rangle>
          else \<langle>l\<^sub>r, k\<^sub>r, p\<^sub>r, \<langle>l\<^sub>c, k\<^sub>c, p\<^sub>c, r\<^sub>c\<rangle>\<rangle>) |
        _ \<Rightarrow> undefined)
    )"

lemma insert_prio_correct:
  "is_treap t \<Longrightarrow> is_valid_prio p \<Longrightarrow> \<forall>p. (k, p) \<notin> set t \<Longrightarrow> \<forall>k. (k, p) \<notin> set t \<Longrightarrow> is_treap (insert_prio k p t)"
proof(induction t arbitrary: k p)
  case Leaf
  then show ?case by (simp add: is_treap_def)
next
  case (Node l k' p' r)
  then have "k \<noteq> k'" by auto
  then show ?case
  proof(cases "k < k'")
    case True
    then show ?thesis sorry
  next
    case False
    then have "k' < k" using \<open>k \<noteq> k'\<close> by auto
    then show ?thesis sorry
  qed
qed

end