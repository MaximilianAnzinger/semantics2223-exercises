theory Defs
  imports "HOL-IMP.VCG"
begin

definition "SQUARE \<equiv> 
  ''z'' ::= N 1;;
  ''a'' ::= N 0;;
   WHILE Less (N 0) (V ''n'') DO (
     ''a'' ::= Plus (V ''a'') (V ''z'');;
     ''z'' ::= Plus (V ''z'') (N 2);; 
     ''n'' ::= Plus (V ''n'') (N (-1))
   )"

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



end