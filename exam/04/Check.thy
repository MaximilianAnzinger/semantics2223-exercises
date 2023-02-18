theory Check
  imports Submission
begin

lemma fixp: "\<And>f::nat \<Rightarrow> nat. \<forall>n. n \<le> f n \<Longrightarrow> A = {m. \<exists>n. m = f n} \<Longrightarrow> \<exists>m \<in> A. \<forall>n \<in> A. n \<le> m \<Longrightarrow> \<exists>k\<in>A. f k = k"
  by (rule Submission.fixp)

end