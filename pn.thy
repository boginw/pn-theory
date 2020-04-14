theory pn
  imports Main
begin
(* This is a comment *)

typedecl state

consts M :: "(state \<times> state) set"

typedecl "atom"

consts L :: "state \<Rightarrow> atom set"


end