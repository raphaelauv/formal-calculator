
(* The supported operators should be at least:
   - With 0 argument: "pi" "e"
   - With 1 argument:
      "-" "sin" "cos" "tan" "asin" "acos" "atan"
      "sqrt" "exp" "log" (base-e logarithm)
   - With 2 arguments:
      "-" "/" "^" (power)
   - With arbitrary n arguments:
      "+" "*"
*)

type ('nums,'ops) generic_expr =
  | Num of 'nums
  | Var of string
  | Op of 'ops * ('nums,'ops) generic_expr list

type basic_expr = (int,string) generic_expr
