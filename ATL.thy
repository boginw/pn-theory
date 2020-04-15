theory ATL
  imports pn
begin

datatype predop = Le | Leq | Eq | Neq | Ge | Geq
datatype exprop = Plus | Minus | Mult

datatype Expr = Constant nat 
              | Place places 
              | Enabled players
              | Expr Expr exprop Expr

datatype predicate = Boolean bool 
                   | Equation Expr predop Expr

fun eval_e :: "marking \<Rightarrow> Expr \<Rightarrow> nat"
  where
    "eval_e _ (Constant b) = b"
  | "eval_e m (Place b) = (m b)"
  | "eval_e m (Enabled a) = card (enabled_p m a)"
  | "eval_e m (Expr a Plus c) = ((eval_e m a) + (eval_e m c))"
  | "eval_e m (Expr a Minus c) = ((eval_e m a) - (eval_e m c))"
  | "eval_e m (Expr a Mult c) = ((eval_e m a) * (eval_e m c))"

fun eval_p :: "marking \<Rightarrow> predicate \<Rightarrow> bool"
  where 
    "eval_p _ (Boolean a) = a"
  | "eval_p s (Equation a Le c) = ((eval_e s a) < (eval_e s c))"
  | "eval_p s (Equation a Leq c) = ((eval_e s a) \<le> (eval_e s c))"
  | "eval_p s (Equation a Eq c) = ((eval_e s a) = (eval_e s c))"
  | "eval_p s (Equation a Neq c) = ((eval_e s a) \<noteq> (eval_e s c))"
  | "eval_p s (Equation a Ge c) = ((eval_e s a) > (eval_e s c))"
  | "eval_p s (Equation a Geq c) = ((eval_e s a) \<ge> (eval_e s c))"


datatype formula = Disjunction formula formula
                 | Predicate predicate
                 | Negation formula
                 | Next players formula
                 | Until players formula formula