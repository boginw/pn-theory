theory pn
  imports Main
begin

declare[[typedef_overloaded]]

(* First, we have a finite number of players, places, 
   and transitions 
*)
consts num_players :: "nat"
consts num_places :: "nat"
consts num_transitions :: "nat"

(* Next, the domain for players is then defined as the
   numbers 0, 1, ... num_players. Places and
   transitions are defined similarily, but with
   num_places and num_transitions respectively instead
*)
typedef players = "{ i . i \<le> num_players}"
  apply(rule_tac x = 0 in exI)
  by simp

typedef places = "{ i . i \<le> num_places}"
  apply(rule_tac x = 0 in exI)
  by simp

typedef transitions = "{ i . i \<le> num_transitions}"
  apply(rule_tac x = 0 in exI)
  by simp

(* Each transition is owned by exactly one player *)
type_synonym trans_owner = "transitions \<Rightarrow> players"

(* An arc is either going from a place to a transition
   or vice-versa 
*)
datatype arc = PT places transitions 
             | TP transitions places

(* Before we define our marking, we first define a 
   bound, which restricts the number of tokens that 
   may simultaneously appear on a place. This is in 
   place to enforce that there only exists finitely 
   many markings.
*)
consts bound :: "nat"

(* A marking is simply a function that assigns tokens
   to places*)
type_synonym marking = "places \<Rightarrow> nat"

(* Every arc has a weight. Either this is the token 
   cost going in to the transition, or the resulting
    tokens going into the output *)
type_synonym weights = "arc \<Rightarrow> nat"

(* Finally, a Petri-Net is a 4-tuple, consisting of
   1. a finite set of places,
   2. a finite set of transitions
   3. a function mapping each function to a player
   4. a function mapping all arcs to a weight
*)
type_synonym PN = "(places set) * (transitions set) * 
                   trans_owner * weights"

(* We instantiate an arbitrary Petri-Net*)
consts PetriNet :: "PN"

(* We define the components of our Petri-Net*)
definition P :: "places set" where "P \<equiv> (fst PetriNet)"
definition T :: "transitions set" where "T \<equiv> (fst (snd PetriNet))"
definition Q :: "trans_owner" where "Q \<equiv> (fst (snd (snd PetriNet)))"
definition W :: "weights" where "W \<equiv> (snd (snd (snd PetriNet)))"

(* All the enabled transitions in a given state *)
fun enabled :: "marking \<Rightarrow> (transitions set)"
  where
    "enabled m = 
      { t \<in> T . \<forall>p \<in> P . 
        ((m p) \<ge> (W (PT p t))) \<and>
        ((m p) \<le> bound)
      }"

fun enabled_p :: "marking \<Rightarrow> players \<Rightarrow> (transitions set)"
  where
    "enabled_p m p = { t . (t \<in> (enabled m)) \<and> ((Q t) = p) }"

(* Gives the marking resulting from firing a transition
   no matter if that transition is enabled or not
*)
fun resulting_marking :: "marking \<Rightarrow> transitions \<Rightarrow> marking"
  where "resulting_marking m t = (\<lambda>p. (m p) - (W (PT p t)) + (W (TP t p)))"

(* The firing of a marking produces another marking*)
fun fire :: "marking \<Rightarrow> transitions \<Rightarrow> (marking option)" where
  "fire m t = (if t \<in> (enabled m) 
      then Some (resulting_marking m t)
      else None)"

lemma cannot_fire[simp]: "t \<notin> (enabled m) \<Longrightarrow> fire m t = None"
  apply(simp)
  done

lemma can_fire[simp]: "t \<in> (enabled m) \<Longrightarrow> fire m t \<noteq> None"
  apply(simp)
  done

end