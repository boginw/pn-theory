theory ATL
  imports Base
begin

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

end