theory Defs
  imports "HOL-IMP.Com"
begin

datatype
  com = SKIP
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq   com  com          ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Or com com              ("_ OR _" [57,58] 59)
      | ASSUME bexp
      | Loop com                ("(LOOP _)"  [61] 61)

type_synonym com_den = "(state \<times> state) set"


consts big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool"

consts D :: "com \<Rightarrow> com_den"

end