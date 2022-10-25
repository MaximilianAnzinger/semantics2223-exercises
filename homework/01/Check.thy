theory Check
  imports Submission
begin

lemma find_pfx_append: "(find_pfx (xs1 @ [x] @ xs2) x) = (find_pfx (xs1 @ [x]) x)"
  by (rule Submission.find_pfx_append)

lemma last_find_pfx_val: "last (find_pfx (xs @ [x]) x) = x"
  by (rule Submission.last_find_pfx_val)

lemma pfx_append_same: "x \<in> set xs \<Longrightarrow> find_pfx (xs @ xs) x = find_pfx xs x"
  by (rule Submission.pfx_append_same)

end