theory Submission
  imports Defs
begin

lemma fixp:
  fixes f :: "nat \<Rightarrow> nat"
  assumes incr: "\<forall>n. n \<le> f n"
  assumes A: "A = {m. \<exists>n. m = f n}"
  assumes max: "\<exists>m \<in> A. \<forall>n \<in> A. n \<le> m"
  shows "\<exists>k\<in>A. f k = k"
proof-
  from max obtain m where m_def: "\<forall>n \<in> A. n \<le> m" by auto
  then have "m \<le> f m" using incr by simp
  moreover from m_def A have "f m \<le> m" by blast
  ultimately have "m = f m" by auto
  then show "\<exists>k\<in>A. f k = k"
    using A by force
qed

end