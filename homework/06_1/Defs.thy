theory Defs
  imports "HOL-IMP.Star"
begin

declare [[syntax_ambiguity_warning=false]]

datatype val = Iv int | Pv val val

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

datatype aexp =  N int | V vname | Plus aexp aexp | Pair aexp aexp | Fst aexp | Snd aexp

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)
      | SWAP   vname

datatype ty = Ity | Pty ty ty

type_synonym tyenv = "vname \<Rightarrow> ty"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Pv v1 v2) = Pty (type v1) (type v2)"

lemma type_eq_Ity[simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
  by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"


consts small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool"

consts taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"

consts tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool"

consts atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"

consts btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool"

consts ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool"

consts small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"


end