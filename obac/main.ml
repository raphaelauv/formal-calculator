
open Expr;;
open Mathexpr;;
open Simplify;;
open Derivative;;
open Plot;;

(* Only for debug *)
let something () =
  let example = "1/(cos(x)^2)" in
  (*  let e = Parsexpr.expr_of_string "5*sqrt(36+x^2)+4*(20-x)" in*)
  let e = Parsexpr.expr_of_string example in  
  let s = match e with
    | Op(o,_) -> "operator "^o
    | Var v -> "variable "^v
    | Num i -> "number "^(string_of_int i)
      
  and r = cons_math_expr e in
  print_string ("We have parsed "^example^" and its tree starts with "^s^"\n");

  print_string("\nmath_expr: "^(string_of_tree_of_math r));  
  print_string("\nFormula: "^(formula_of_math_expr r)^"\n\n");
  
  let simpl_e = simpl r in
(*  print_string("Simplifed math_expr: "^(string_of_tree_of_math simpl_e)^"\n");*)
  print_string("Simplified formula: "^(formula_of_math_expr simpl_e)^"\n");
(*  print_string("Derived math_expr: "^(string_of_tree_of_math (derive r "x"))^"\n");*)
  print_string("Derived formula: "^(formula_of_math_expr (derive r "x"))^"\n");
  print_string("Integral formula: "^(formula_of_math_expr (integ r "x" (Val(Num.Int(1))) (Val(Num.Int(10)))))^"\n");
(*  print_string("Solved math_expr: \n");(string_of_tree_of_math solved_e);*)
(*  print_string("Solved formula: \n");(print_solve (solved_e));*)
(*  print_string("The result of the evaluation is: "^string_of_float(eval simpl_e)^
		  "\n");*)
  
  (*
  let m="7" in
  let m2 = Parsexpr.expr_of_string m in
  let m3 = cons_math_expr m2 in
  let sub_e = Mathexpr.subst r "x" m3 in
  print_string("SUB x by 7 math_expr: "^(string_of_tree_of_math sub_e)^"\n\n");
  *)
(*  Plot.plotExt r "x" (-50) 50 (-50) 50*);;


type 'a option = None | Some of 'a

let main_parse str =
  try
    Some(cons_math_expr(Parsexpr.expr_of_string str))
  with
    | Parsing_error(s) -> print_string("Parsing: "^s^"\n\n"); None
    | Invalid_sqrt(s) -> print_string("Square root: "^s^"\n\n"); None
    | Invalid_log(s) -> print_string("Logarithm: "^s^"\n\n"); None
    | Invalid_trigo(s) -> print_string("trigo: "^s^"\n\n"); None
    | _ -> print_string("Unkown exception\n\n"); None
;;


let main_simpl expr =
  try
    begin
      let simplified_expr = (formula_of_math_expr (simpl expr)) in
      print_string("\nSimplified formula: "^simplified_expr^"\n");
    end
  with _ -> print_string("Cannot simplify the formula")
;;


let main_derive expr =
  try
    begin
      let derived_expr = formula_of_math_expr(derive expr "x") in
      print_string("\nDerived formula: "^derived_expr^"\n");
    end
  with 
    | Invalid_derivative(s) -> print_string(s)
    | _ -> print_string("derive : Unknown exception\n\n")
;;


let main_integral expr = 
  try
    begin
      let integ_expr = formula_of_math_expr(integ expr "x" 
					    (Val(Num.Int(42))) 
					    (Val(Num.Int(1)))) 
      in
      print_string("\nIntegral formula: "^integ_expr^"\n");
    end
  with 
    | Invalid_integration(s) -> print_string("integration: "^s)
    | _ -> print_string("integ : Unknown exception\n")
;;


let main_solve expr =
  try
    begin
      print_string("\nSolution(s) of the equation: \n");
      print_solve(solve expr "x");
      print_string("\n");
    end
  with 
    | Invalid_solve(s) -> print_string(s)
    | _ -> print_string("solve : Unknown exception\n")
;;


let main_eval expr =
  try
    let eval_expr = string_of_float(eval expr) in
      print_string("\nThe result of the evaluation is: "^eval_expr^"\n")
  with
    | Invalid_evaluation(s) -> print_string("eval: "^s)
    | _ -> print_string("eval : Unknown exception\n")
;;


let main_plot expr =
  try
  (*
    print_string("\nVoulez vous personaliser les bornes d'affichage ? 1 -> OUI | 0 -> NON: \n");
    in
    let read_mode = read_int() in
    let do()=
      if(mode=1){
        print_string("\n 1:\n");
        let x1 = read_int() in
        print_string("\n 2 ( superieur a 1):\n");
        let x2 = read_int() in
        print_string("\n 3:\n");
        let x3 = read_int() in
        print_string("\n 4( superieur a 3):\n");
        let x4 = read_int() in
        Plot.plotExt expr "x" x1 x2 x3 x4
      }
    else{
  *)
      Plot.plotExt expr "x" (-50) 50 (-50) 50
      
  with
    | Invalid_evaluation(s) -> print_string(s)
    | _ -> print_string("main_plot : Unknown exception\n\n")
;;


(* Interactive mode *)
let loop () =
  while(true) do
    begin
      print_string("\nPlease write the formula: \n");
      let read_str = read_line() in
      let parsed = main_parse read_str in
      match parsed with
	| Some(expr)->
	  print_string("\nSyntaxic representation: \n\n");
	  print_string((string_of_tree_of_math expr)^"\n");
	  main_simpl expr;
	  main_derive expr;
	  main_solve expr;
	  main_eval expr;
	  main_plot expr;
	| None -> print_string("There is nothing to do\n")
    end
  done
;;

let main =
  print_string "Welcome to Obac 1.0\n";
  if not !Sys.interactive then loop ()
