theory PNEvaluation 
  imports pn ATL
begin

(* Evaluation of an expression wrt. a marking *)
fun eval_e :: "marking \<Rightarrow> Expr \<Rightarrow> nat" where
    "eval_e _ (Constant b) = b"
  | "eval_e m (Place b) = (m b)"
  | "eval_e m (Enabled a) = card (enabled_p m a)"
  | "eval_e m (Expr a Plus c) = ((eval_e m a) + (eval_e m c))"
  | "eval_e m (Expr a Minus c) = ((eval_e m a) - (eval_e m c))"
  | "eval_e m (Expr a Mult c) = ((eval_e m a) * (eval_e m c))"

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

function eval_f :: "(state set) \<Rightarrow> state \<Rightarrow> formula \<Rightarrow> bool"
  where
    "eval_f ss s (Disjunction f1 f2) = 
      ((isValidState s) \<and> ((eval_f ss s f1) \<or> (eval_f ss s f2)))"
  | "eval_f ss s (Predicate p) = 
      ((isValidState s) \<and> (eval_p s p))"
  | "eval_f ss s (Negation f) = 
      ((isValidState s) \<and> (\<not> (eval_f ss s f)))"
  | "eval_f ss s (Next p f) = 
      ((isValidState s) \<and> (\<exists>t \<in> (Ts s). (eval_f ({s} \<union> ss) (fire s t) f)))"
  | "eval_f ss s (Until p f1 f2) = False"

end