theory Defs
  imports "HOL-IMP.Small_Step"
begin

fun while_free :: "com \<Rightarrow> bool" where
"while_free (IF _ THEN c1 ELSE c2) \<longleftrightarrow> while_free c1 \<and> while_free c2" |
"while_free (c1 ;; c2) \<longleftrightarrow> while_free c1 \<and> while_free c2" |
"while_free (WHILE _ DO _) \<longleftrightarrow> False" |
"while_free _ \<longleftrightarrow> True"

consts bound :: "com \<Rightarrow> nat"

end
