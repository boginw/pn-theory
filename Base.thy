theory Base 
  imports Main
begin

declare[[typedef_overloaded]]

(* First, we have a finite number of players *)
consts num_players :: "nat"

(* Next, the domain for players is then defined as the
   numbers 0, 1, ..., num_players *)
typedef players = "{ i . i \<le> num_players}"
  apply(rule_tac x = 0 in exI)
  by simp

(* Similarily we have finite number of places *)
consts num_places :: "nat"

(* The domain of places is defined similarily to
   players, but with num_places instead *)
typedef places = "{ i . i \<le> num_places}"
  apply(rule_tac x = 0 in exI)
  by simp

end