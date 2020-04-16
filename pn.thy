theory pn
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

(* We have a finite number of transitions *)
consts num_transitions :: "nat"

(* Transitions are defined similarily to players and 
   places, but with num_transitions instead *)
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

(* All the enabled transitions in a given marking *)
fun enabled :: "marking \<Rightarrow> (transitions set)"
  where
    "enabled m = 
      { t \<in> T . \<forall>p \<in> P . 
        ((m p) \<ge> (W (PT p t))) \<and>
        ((m p) \<le> bound)
      }"

(* All the enabled transitions for a given player at a given marking *)
fun enabled_p :: "marking \<Rightarrow> players \<Rightarrow> (transitions set)" where
  "enabled_p m p = { t . (t \<in> (enabled m)) \<and> ((Q t) = p) }"

(* Gives the marking resulting from firing a transition
   no matter if that transition is enabled or not
*)
fun resulting_marking :: "marking \<Rightarrow> transitions \<Rightarrow> marking" where
 "resulting_marking m t = (\<lambda>p. (m p) - (W (PT p t)) + (W (TP t p)))"

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

(*lemma enabled_trans[simp]: "\<forall>t. t \<in> (enabled m) \<longrightarrow> t \<in> T"
  apply(simp)
  done

lemma player_can_fire: "(t \<in> (enabled m) \<and> (Q t) = (Abs_players 1)) = (t \<in> (enabled_p m (Abs_players 1)))"
  apply(induct_tac t)
  oops*)

(* The operators allowed in expressions *)
datatype exprop = Plus | Minus | Mult

(* The syntax of our expressions *)
datatype Expr = Constant nat 
              | Place places 
              | Enabled players
              | Expr Expr exprop Expr

(* The operators allowed in our predicates *)
datatype predop = Le | Leq | Eq | Neq | Ge | Geq

(* The syntax of our predicates *)
datatype predicate = Boolean bool 
                   | Equation Expr predop Expr

(* Evaluation of an expression wrt. a marking *)
fun eval_e :: "marking \<Rightarrow> Expr \<Rightarrow> nat" where
  "eval_e _ (Constant c) = c" |
  "eval_e m (Place p) = (m p)" |
  "eval_e m (Enabled a) = (card (enabled_p m a))" |
  "eval_e m (Expr e1 Plus e2) = ((eval_e m e1) + (eval_e m e2))" |
  "eval_e m (Expr e1 Minus e2) = ((eval_e m e1) - (eval_e m e2))" |
  "eval_e m (Expr e1 Mult e2) = ((eval_e m e1) * (eval_e m e2))"

(* Evaluation of a predicate wrt. a marking *)
fun eval_p :: "marking \<Rightarrow> predicate \<Rightarrow> bool" where 
    "eval_p _ (Boolean a) = a"
  | "eval_p s (Equation a Le c) = ((eval_e s a) < (eval_e s c))"
  | "eval_p s (Equation a Leq c) = ((eval_e s a) \<le> (eval_e s c))"
  | "eval_p s (Equation a Eq c) = ((eval_e s a) = (eval_e s c))"
  | "eval_p s (Equation a Neq c) = ((eval_e s a) \<noteq> (eval_e s c))"
  | "eval_p s (Equation a Ge c) = ((eval_e s a) > (eval_e s c))"
  | "eval_p s (Equation a Geq c) = ((eval_e s a) \<ge> (eval_e s c))"

(* The syntax of our queries *)
datatype formula = Disjunction formula formula
                 | Predicate predicate
                 | Negation formula
                 | Next players formula
                 | Until players formula formula

(* Evaluation of formula *)
function eval_f :: "(marking set) \<Rightarrow> marking \<Rightarrow> formula \<Rightarrow> bool" ("(_,_ \<Turnstile> _)" [80,80,80] 80) where
  "eval_f r m (Disjunction f1 f2) = ((r,m \<Turnstile> f1) \<or> (r,m \<Turnstile> f2))" |
  "eval_f r m (Predicate p) = (eval_p m p)" |
  "eval_f r m (Negation f) = (\<not> (r,m \<Turnstile> f))" |
  "eval_f r m (Next p f) = 
    (\<exists>t \<in> T . 
      let m' = (fire m t) in 
        (case m' of None \<Rightarrow> False | Some m'' \<Rightarrow> (({m} \<union> r),m'' \<Turnstile> f)))" |
  "eval_f r m (Until p f1 f2) = 
    ((r,m \<Turnstile> f2) \<or> 
      ((r,m \<Turnstile> f1) \<and> 
        ((m \<notin> r) \<and> (r,m \<Turnstile> (Next p (Until p f1 f2))))))"
  by pat_completeness auto



end