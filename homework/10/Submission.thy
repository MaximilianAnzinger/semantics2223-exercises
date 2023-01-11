theory Submission
  imports Defs
begin

unbundle ACOM

abbreviation "SQUARE_invar s\<^sub>0 s \<equiv>
s ''a'' = (s\<^sub>0 ''n'' - s ''n'')^2
\<and> s ''z'' = 2 * (s\<^sub>0 ''n'' - s ''n'') + 1
\<and> s ''n'' \<ge> 0"

definition SQUARE_annot :: "state \<Rightarrow> acom" where
"SQUARE_annot s\<^sub>0 = 
  ''z'' ::= N 1;;
  ''a'' ::= N 0;;
  {SQUARE_invar s\<^sub>0} WHILE Less (N 0) (V ''n'') DO (
     ''a'' ::= Plus (V ''a'') (V ''z'');;
     ''z'' ::= Plus (V ''z'') (N 2);; 
     ''n'' ::= Plus (V ''n'') (N (-1))
   )"

lemma SQUARE_annot_strip: "strip (SQUARE_annot s\<^sub>0) = SQUARE"
  unfolding SQUARE_annot_def SQUARE_def by auto

theorem SQUARE_correct:
  "\<turnstile> {\<lambda>s. s ''n'' \<ge> 0 \<and> s=s\<^sub>0} SQUARE {\<lambda>s. s ''a'' = s\<^sub>0 ''n'' * s\<^sub>0 ''n''}"
  unfolding SQUARE_annot_strip[symmetric, of s\<^sub>0]
  apply (rule vc_sound')
  unfolding SQUARE_annot_def
  by (simp add: algebra_simps power2_eq_square | fastforce)+

end