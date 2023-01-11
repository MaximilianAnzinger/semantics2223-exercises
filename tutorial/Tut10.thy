theory Tut10
  imports "HOL-IMP.VCG" "HOL-IMP.Hoare_Sound_Complete" "HOL-IMP.Hoare_Total"
begin

bundle ACOM begin
no_notation SKIP ("SKIP")
no_notation Assign ("_ ::= _" [1000, 61] 61)
no_notation Seq    ("_;;/ _"  [60, 61] 60)
no_notation If ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
notation Askip ("SKIP")
notation Aassign ("(_ ::= _)" [1000, 61] 61)
notation Aseq ("_;;/ _"  [60, 61] 60)
notation Aif ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
end

bundle COM begin
no_notation Askip ("SKIP")
no_notation Aassign ("(_ ::= _)" [1000, 61] 61)
no_notation Aseq ("_;;/ _"  [60, 61] 60)
no_notation Aif ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
notation SKIP ("SKIP")
notation Assign ("_ ::= _" [1000, 61] 61)
notation Seq    ("_;;/ _"  [60, 61] 60)
notation If ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
end

unbundle COM
definition MUL :: com where
"MUL =
  ''z''::=N 0;;
  ''c''::=N 0;;
  WHILE (Less (V ''c'') (V ''y'')) DO (
    ''z''::=Plus (V ''z'') (V ''x'');;
    ''c''::=Plus (V ''c'') (N 1))"

unbundle ACOM

abbreviation "MUL_invar sorig s \<equiv> s ''z'' = s ''c'' * s ''x'' \<and> s ''c'' \<le> s ''y'' \<and> (\<forall>v. v\<notin>{''z'',''c''} \<longrightarrow> s v = sorig v)"

definition MUL_annot :: "state \<Rightarrow> acom" where
"MUL_annot sorig =
  ''z''::=N 0;;
  ''c''::=N 0;;
  {MUL_invar sorig} WHILE (Less (V ''c'') (V ''y'')) DO (
    ''z''::=Plus (V ''z'') (V ''x'');;
    ''c''::=Plus (V ''c'') (N 1))"

lemma MUL_annot_same: "strip (MUL_annot sorig) = MUL"
  unfolding MUL_annot_def MUL_def by auto

theorem MUL_partially_correct:
"\<turnstile> {\<lambda>s. 0 \<le> s ''y'' \<and> s=sorig}
     MUL
   {\<lambda>s. s ''z'' = s ''x'' * s ''y'' \<and> (\<forall>v. v\<notin>{''z'',''c''} \<longrightarrow> s v = sorig v)}"
  unfolding MUL_annot_same[symmetric, of sorig]
  apply (rule vc_sound')
  unfolding MUL_annot_def
  by (simp add: algebra_simps | fastforce)+

unbundle COM

definition SQRT :: com where
"SQRT =
  ''r'' ::= N 0;;
  ''s'' ::= N 1;;
  WHILE (Not (Less (V ''x'') (V ''s''))) DO (
    ''r'' ::= Plus (V ''r'') (N 1);;
    ''s'' ::= Plus (V ''s'') (V ''r'');;
    ''s'' ::= Plus (V ''s'') (V ''r'');;
    ''s'' ::= Plus (V ''s'') (N 1)
  )"

unbundle ACOM

abbreviation "SQRT_invar sorig s \<equiv>
s ''r'' \<ge> 0
\<and> s ''s'' \<ge> 0
\<and> (s ''r'' + 1)^2 = s ''s''
\<and> (s ''r'')^2 \<le> s ''x''
\<and> (\<forall>v. v\<notin>{''s'',''r''} \<longrightarrow> s v = sorig v)"

definition SQRT_annot :: "state \<Rightarrow> acom" where
"SQRT_annot sorig =
  ''r'' ::= N 0;;
  ''s'' ::= N 1;;
  {SQRT_invar sorig} WHILE (Not (Less (V ''x'') (V ''s''))) DO (
    ''r'' ::= Plus (V ''r'') (N 1);;
    ''s'' ::= Plus (V ''s'') (V ''r'');;
    ''s'' ::= Plus (V ''s'') (V ''r'');;
    ''s'' ::= Plus (V ''s'') (N 1)
  )"

lemma SQRT_annot_strip: "strip (SQRT_annot sorig) = SQRT"
  unfolding SQRT_annot_def SQRT_def by auto

thm power2_eq_square

theorem SQRT_partially_correct:
"\<turnstile> {\<lambda>s. s=sorig \<and> s ''x'' \<ge> 0}
     SQRT
   {\<lambda>s. (s ''r'')^2 \<le> s ''x'' \<and> s ''x'' < (s ''r''+1)^2 \<and> (\<forall>v. v\<notin>{''s'',''r''} \<longrightarrow> s v = sorig v)}"
  unfolding SQRT_annot_strip[symmetric, of sorig]
  apply (rule vc_sound')
  unfolding SQRT_annot_def
  by (simp add: algebra_simps power2_eq_square | fastforce)+

lemmas Seq_bwd = Hoare_Total.Seq[rotated]

unbundle COM

lemma IfT:
  assumes "\<turnstile>\<^sub>t {P1} c\<^sub>1 {Q}"
      and "\<turnstile>\<^sub>t {P2} c\<^sub>2 {Q}"
    shows "\<turnstile>\<^sub>t {\<lambda>s. (bval b s \<longrightarrow> P1 s) \<and> (\<not> bval b s \<longrightarrow> P2 s)} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"
  by (auto intro: If conseq assms)
(*
  apply (rule If)
   apply (rule conseq)
     defer
     apply(rule assms(1))
    apply simp
   apply (rule conseq)
  defer
     apply (rule assms(2))
    apply simp+
  done
*)

lemmas hoareT_rule[intro?] = Seq_bwd Hoare_Total.Assign Hoare_Total.Assign' IfT


theorem MUL_totally_correct:
"\<turnstile>\<^sub>t {\<lambda>s. 0 \<le> s ''y'' \<and> s=sorig} 
      MUL 
    {\<lambda>s. s ''z'' = s ''x'' * s ''y'' \<and> (\<forall>v. v\<notin>{''z'',''c''} \<longrightarrow> s v = sorig v)}"
  unfolding MUL_def
  by(rule hoareT_rule While_fun'[where P="MUL_invar sorig" and f="\<lambda>s. nat (s ''y'' - s ''c'')"]
      | simp add: algebra_simps | fastforce)+

theorem SQRT_totally_correct:
"\<turnstile>\<^sub>t {\<lambda>s. s=sorig \<and> s ''x'' \<ge> 0} 
      SQRT 
    {\<lambda>s. (s ''r'')^2 \<le> s ''x'' \<and> s ''x'' < (s ''r''+1)^2 \<and> (\<forall>v. v\<notin>{''s'',''r''} \<longrightarrow> s v = sorig v)}"
  unfolding SQRT_def
  by(rule hoareT_rule While_fun'[where P="SQRT_invar sorig" and f="\<lambda>s. nat (s ''x'' - s ''r''^2)"]
      | simp add: algebra_simps power2_eq_square | fastforce)+

end