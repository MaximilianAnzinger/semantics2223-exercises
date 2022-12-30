theory Tut09
  imports "HOL-IMP.Hoare_Sound_Complete"
begin

paragraph "Step 1"

definition Max :: "com"  where
  "Max = IF Less (V ''a'') (V ''b'') THEN ''c'' ::= V ''b'' ELSE ''c'' ::= V ''a''"

paragraph "Step 2"

lemma max_right[simp]: "(a::int)<b \<Longrightarrow> max a b = b"
  by simp

lemma max_left[simp]: "\<not>(a::int)<b \<Longrightarrow> max a b = a"
  by simp

lemma "\<turnstile> {\<lambda>s. True} Max {\<lambda>s. s ''c'' = max (s ''a'') (s ''b'')}"
  unfolding Max_def by(rule If Assign' | simp)+

paragraph "Step 3"

definition MUL :: "com"  where
  "MUL =
    ''z'' ::= N 0;;
  ''i'' ::= N 0;;
  WHILE Less (V ''i'') (V ''y'') DO
  (
    ''z'' ::= Plus (V ''z'') (V ''x'');;
    ''i'' ::= Plus (V ''i'') (N 1)
  )"

paragraph "Step 4"

lemmas Seq_bwd = Seq[rotated]

lemma "\<turnstile> {\<lambda>s. 0 \<le> s ''y''} MUL {\<lambda>s. s ''z'' = s ''x'' * s ''y''}"
  unfolding MUL_def
  by(rule Seq_bwd Assign Assign'
      While'[where P="\<lambda>s. s ''z'' = s ''i'' * s ''x'' \<and> s ''i'' \<le> s ''y''"]
      | auto simp: algebra_simps)+

lemmas hoare_rule[intro?] = Seq_bwd Assign Assign' If

paragraph "Step 5"

definition "MAX_wrong = (''a''::=N 0;;''b''::=N 0;;''c''::= N 0)"

lemma "\<turnstile> {\<lambda>s. True} MAX_wrong {\<lambda>s. s ''c'' = max (s ''a'') (s ''b'')}"
  unfolding MAX_wrong_def by(rule Seq_bwd Assign Assign' | simp)+

lemma "\<turnstile> {\<lambda>s. a=s ''a'' \<and> b=s ''b''} 
  Max {\<lambda>s. s ''c'' = max a b \<and> a = s ''a'' \<and> b = s ''b''}"
  unfolding Max_def by(rule If Assign' | simp)+

lemma "\<turnstile> {\<lambda>s. 0 \<le> s ''y'' \<and> x = s ''x'' \<and> y = s ''y''} MUL {\<lambda>s. s ''z'' = x * y \<and> s ''x'' = x \<and> s ''y'' = y}"
  unfolding MUL_def by(rule Seq_bwd Assign Assign'
      While'[where P="\<lambda>s. s ''z'' = s ''i'' * s ''x'' \<and> s ''i'' \<le> s ''y'' \<and> x = s ''x'' \<and> y = s ''y''"]
      | auto simp: algebra_simps)+

lemma fwd_Assign: "\<turnstile> {P} x::=a {\<lambda>s. \<exists>s'. P s' \<and> s'[a/x] = s}"
  apply(rule hoare_complete)
  unfolding hoare_valid_def by auto

lemmas fwd_Assign' = weaken_post[OF fwd_Assign]

lemma "\<turnstile> {\<lambda>s. True} Max {\<lambda>s. s ''c'' = max (s ''a'') (s ''b'')}"
  sorry

lemma "\<turnstile> {\<lambda>s. 0 \<le> s ''y''} MUL {\<lambda>s. s ''z'' = s ''x'' * s ''y''}"
  sorry

end