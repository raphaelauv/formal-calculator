open Expr;;
(*#use "expr.mli";*)

(* Generic mathematic expression *)
type ('n,'op) gen_math_expr =
  | Pi                                                      (* Pi : 3.14...   *)
  | Exp1                                                    (* e : exp(1)     *)
  | Val of 'n                                               (* Constant value *)
  | Var of string                                           (* Variable       *)
  | Unop of 'op * ('n,'op) gen_math_expr                    (* '+','-' unaire *)
  | Binop of 'op * 
      ('n,'op) gen_math_expr * 
      ('n,'op) gen_math_expr                                (* '+','-','*'    *)
  | Frac of ('n,'op) gen_math_expr * ('n,'op) gen_math_expr (* Fraction       *)
  | Pow of ('n,'op) gen_math_expr * ('n,'op) gen_math_expr  (* Power          *)
  | Sqrt of ('n,'op) gen_math_expr                          (* Square root    *)
  | Expo of ('n,'op) gen_math_expr                          (* Exponential    *)
  | Log of ('n,'op) gen_math_expr                           (* Logarithm      *)
  | Cos of ('n,'op) gen_math_expr                           (* Cosine         *)
  | Sin of ('n,'op) gen_math_expr                           (* Sine           *)
  | Tan of ('n,'op) gen_math_expr                           (* Tangent        *)
  | Acos of ('n,'op) gen_math_expr                          (* Secant         *)
  | Asin of ('n,'op) gen_math_expr                          (* Cosecant       *)
  | Atan of ('n,'op) gen_math_expr                          (* Cotangent      *)
;;


(* The Mathematical expression that will be used in the program *)
type math_expr = (Num.num,char) gen_math_expr;;

(* Exceptions *)
exception Reserved_keyword of string;;
exception Parsing_error of string;;
exception Invalid_binop of string;;
exception Invalid_fraction of string;;
exception Invalid_power of string;;
exception Invalid_sqrt of string;;
exception Invalid_log of string;;
exception Invalid_trigo of string;;
exception Invalid_math_expr of string;;
exception Invalid_derivative of string;;
exception Invalid_integration of string;;
exception Invalid_derive_n_Argument of string;;
exception Internal_mathexpr_error of string;;
exception Invalid_evaluation of string;;
exception Invalid_formula of string;;
exception Invalid_solve of string;;
exception Division_by_zero;;


let two_pi_div_three = Frac(Binop('*',Val(Num.Int(2)),Pi),Val(Num.Int(3))) 
let three_pi_div_three = Frac(Binop('*',Val(Num.Int(3)),Pi),Val(Num.Int(4)))
let five_pi_div_six = Frac(Binop('*',Val(Num.Int(5)),Pi),Val(Num.Int(6)))

let one_half = Frac(Val(Num.Int(1)),Val(Num.Int(2)))
let sqrt_three_div_two = Frac(Sqrt(Val(Num.Int(3))),Val(Num.Int(2)))
let sqrt_two_div_two = Frac(Sqrt(Val(Num.Int(2))),Val(Num.Int(2)))



(* A function that print the tree of the given expression *)
let rec string_of_tree_of_math : math_expr -> string = fun m ->
  match m with
    | Pi -> "Pi"
    | Exp1 -> "e"
    | Val(Num.Int(x)) -> "Val(Num.Int("^(string_of_int x)^"))"
    | Var s -> "Var("^s^")"
    | Unop(op,e) -> "Unop("^(Char.escaped op)^","^(string_of_tree_of_math e)^")"
    | Binop(op,e1,e2) -> "Binop("^(Char.escaped op)^","^(string_of_tree_of_math e1)^
      ","^(string_of_tree_of_math e2)^")"
    | Frac(e1,e2) -> "Frac("^(string_of_tree_of_math e1)^","^
      (string_of_tree_of_math e2)^")"
    | Pow(e1,e2) -> "Pow("^(string_of_tree_of_math e1)^","^
      (string_of_tree_of_math e2)^")"
    | Sqrt(n) -> "Sqrt("^(string_of_tree_of_math n)^")"
    | Expo(n) -> "Expo("^(string_of_tree_of_math n)^")"
    | Log(n) -> "Log("^(string_of_tree_of_math n)^")"
    | Cos(n) -> "Cos("^(string_of_tree_of_math n)^")"
    | Sin(n) -> "Sin("^(string_of_tree_of_math n)^")"
    | Tan(n) -> "Tan("^(string_of_tree_of_math n)^")"
    | Acos(n) -> "Acos("^(string_of_tree_of_math n)^")"
    | Asin(n) -> "Asin("^(string_of_tree_of_math n)^")"
    | Atan(n) -> "Atan("^(string_of_tree_of_math n)^")"
    | _ -> raise (Invalid_math_expr "Invalid mathematic expression to print")
;;


(* Print the formula of mathematic expression *)
let rec formula_of_math_expr : math_expr -> string = 
  fun e -> 
    match e with
      | Pi -> "pi"
      | Exp1 -> "e"
      | Var(x) -> x
      | Val(Num.Int(v)) -> (string_of_int v)
      | Unop(op,e) -> unop_formula_of_math_expr op e
      | Binop(op,e1,e2) -> binop_formula_of_math_expr op e1 e2
      | Frac(e1,e2) -> frac_formula_of_math_expr e1 e2
      | Pow(x,e) -> pow_formula_of_math_expr x e
      | Sqrt(x) -> "sqrt("^(formula_of_math_expr x)^")"
      | Expo(x) -> "exp("^(formula_of_math_expr x)^")"
      | Log(x) -> "ln("^(formula_of_math_expr x)^")"
      | Cos(x) -> "cos("^(formula_of_math_expr x)^")"
      | Sin(x) -> "sin("^(formula_of_math_expr x)^")"
      | Tan(x) -> "tan("^(formula_of_math_expr x)^")"
      | Acos(x) -> "acos("^(formula_of_math_expr x)^")"
      | Asin(x) -> "asin("^(formula_of_math_expr x)^")"
      | Atan(x) -> "atan("^(formula_of_math_expr x)^")"
      | _ -> raise (Invalid_formula("Cannot get the formula"))


and unop_formula_of_math_expr : char -> math_expr -> string = 
  fun op e -> match op with
    | '-' -> 
      (match e with
	| Binop(_,_,_) -> "-("^(formula_of_math_expr e)^")"
	| _ -> "-"^(formula_of_math_expr e)
      )
    | '+' -> formula_of_math_expr e
    | _ -> raise (Invalid_binop "formula_of_unnop_formula: Internal error")
      

(* Print a binop formula *)
and binop_formula_of_math_expr : char -> math_expr -> math_expr -> string =
  fun op e1 e2 -> match op with
    | '+' | '-' -> let f1 = formula_of_math_expr e1 in
		   f1^" "^(Char.escaped op)^" "^(formula_of_math_expr e2)
    | '*' -> let f1 = formula_of_math_expr e1 in
	     let f2 = formula_of_math_expr e2 in
	     formula_of_binop_aux op e1 e2 f1 f2
    | _ -> raise (Invalid_binop "binop_formula_of_math_expr: Internal error")
      
      
and formula_of_binop_aux op e1 e2 f1 f2 =
  let normal_string = (f1^(Char.escaped op)^f2) in
  let formatted_string = ("("^f1^")"^(Char.escaped op)^"("^f2^")") in
  let left_formatted_string = ("("^f1^")"^(Char.escaped op)^f2) in
  let right_formatted_string = (f1^(Char.escaped op)^"("^f2^")") in
  match e1,e2 with
    | Binop(o1,_,_),Binop(o2,_,_) 
      when (o1 = '+' || o1 = '-') 
	&& (o2 = '+' || o2 = '-') -> formatted_string
    
    | Frac(_,_), Frac(_,_) -> formatted_string
    | Pow(_,_), Pow(_,_) -> formatted_string
    | Unop('-',_), Unop('-',_) -> formatted_string
      
    | Binop(op,_,_),_ when (op = '+' || op = '-') -> left_formatted_string
    | Frac(_,_),_ | Pow(_,_),_ | Unop('-',_),_ -> left_formatted_string
    
    | _,Binop(op,_,_) when (op = '+' || op = '-') -> right_formatted_string
    | _,Frac(_,_) | _,Pow(_,_) | _,Unop('-',_) -> right_formatted_string
    
    | _ -> normal_string


and frac_formula_of_math_expr : math_expr -> math_expr -> string =
  fun e1 e2 -> 
    let f1 = formula_of_math_expr e1 in
    let f2 = formula_of_math_expr e2 in
    let normal_string = (f1^"/"^f2) in
    let formatted_string = ("("^f1^")"^"/"^"("^f2^")") in
    let left_formatted_string = ("("^f1^")"^"/"^f2) in
    let right_formatted_string = (f1^"/"^"("^f2^")") in
    match e1,e2 with
      | Binop(_,_,_),Binop(_,_,_) | Frac(_,_), Frac(_,_) 
      | Pow(_,_), Pow(_,_) -> formatted_string
      | Binop(_,_,_),_ | Frac(_,_),_ | Pow(_,_),_ -> left_formatted_string
      | _,Binop(_,_,_) | _,Frac(_,_) | _,Pow(_,_) -> right_formatted_string
      | _ -> normal_string


and pow_formula_of_math_expr : math_expr -> math_expr -> string = 
  fun x e -> let x_formula = formula_of_math_expr x in
	     let exponent_formula = formula_of_math_expr e in
	     "("^(x_formula^")^("^exponent_formula^")")

;;


(* Check if the string is a reserved keyword *)
let is_not_reserved_keyword = function
  | "pow" | "sqrt" | "exp" | "log" -> false 
  | "cos" | "sin" | "tan" | "acos" | "asin" | "atan" -> false
  | _ -> true
;;


(* A shorcut to apply map *)
let map_list f l = List.map f l;;


let consVar: string -> math_expr = 
  fun s ->
    if is_not_reserved_keyword(s)
    then 
      (Var s)
    else 
      raise (Reserved_keyword (s^" is a keyword, not usable as a variable"))
;;

(* Build a recursive Binop expression with the same operator *)
let rec cons_binop (op: char) (l : math_expr list) : math_expr = 
  match l with
    | [] -> raise (Invalid_binop "Binop cannot be applied on an empty list")
    | [x] -> x
    | t::q -> Binop(op,t,(cons_binop op q))
;;


(* Create the Fraction expression *)
let cons_frac:  math_expr list -> math_expr = 
  fun l -> 
    match l with
      | [x;y] -> Frac(x,y)
      | _ -> raise (Invalid_fraction "Invalid fraction expression")
;;

(* Create the Power expression *)
let cons_pow: math_expr list -> math_expr = 
  fun l -> 
    match l with
      | [x;y] -> Pow(x,y)
      | _ -> raise (Invalid_power "Invalid power expression")
;;


(* Auxilliary function for binary operations *)
let parse_binop_aux op l f = 
      let ll = map_list f l in
      match op with
	| "+" -> cons_binop '+' ll
	| "-" -> cons_binop '-' ll
	| "*" -> cons_binop '*' ll
	| "/" -> cons_frac ll
	| _  as s -> raise (Invalid_math_expr (s^"is not a valid operator"))
;;



(* Build a mathematical expression from a basic expression *)
let rec cons_math_expr (b : basic_expr) : math_expr = 
match b with
  | Num n -> Val (Num.Int n)
  | Var s -> consVar s
  | Op(s,l) -> parse_op (s,l)


(* Parse any kind of operation *)
and parse_op = function
  | ("pi",[]) -> Pi
  | ("e",[]) -> Exp1
  (* Basic operations *)
  | ("+",_) as p -> parse_basic_op p
  | ("-",_) as m -> parse_basic_op m
  | ("*",_) as f -> parse_basic_op f
  | ("/",_) as d -> parse_basic_op d
  (* Mathematical functions *)
  | _ as o -> parse_math_function o


(* Mathematical functions to parse *)
and parse_math_function = function
  | ("^",l) when (List.length l = 2) -> 
    let ll = map_list (cons_math_expr) l in cons_pow ll
  | ("sqrt",[x]) -> parse_sqrt (cons_math_expr x)
  | ("exp",[x]) -> Expo(cons_math_expr x)
  | ("log",[x]) -> parse_log (cons_math_expr x)
  | ("cos",[x]) -> Cos(cons_math_expr x)
  | ("sin",[x]) -> Sin(cons_math_expr x)
  | ("tan",[x]) -> Tan(cons_math_expr x)
  | ("acos",[x]) -> Acos(parse_trigo (cons_math_expr x))
  | ("asin",[x]) -> Asin(parse_trigo (cons_math_expr x))
  | ("atan",[x]) -> Atan(parse_trigo (cons_math_expr x))
  | _ -> raise (Parsing_error "Unrecognized mathematic operator to parse")

(* Parse any kind of basic operation: '+', '-', '*', '/' *)
and parse_basic_op = function
  | ("+",[t]) -> let m1 = cons_math_expr t in
		 Unop ('+',m1)
  | ("-",[t]) -> let m1 = cons_math_expr t in
		  Unop ('-',m1)
  | ("+",l) -> parse_binop_aux "+" l (cons_math_expr)
  | ("-",l) when (List.length l = 2) -> parse_binop_aux "-" l (cons_math_expr)
  | ("*",l) when (List.length l > 1) -> parse_binop_aux "*" l (cons_math_expr)
  | ("/",l) when (List.length l = 2) -> parse_binop_aux "/" l (cons_math_expr)
  | _ -> raise (Parsing_error "Unrecognized basic operator to parse")


(* Check if the argument of sqrt is valid *)
and parse_sqrt = function
  (* If the argument is a positive or null value -> OK; otherwise -> KO *)
  | Val(Num.Int(x)) as v when x >= 0 -> Sqrt(v)
  | Val(Num.Int(x)) -> raise (Invalid_sqrt ("Invalid square root of "
					    ^(string_of_int x)^""))
  (* If the argument is -y -> KO*)
  | (Unop('-',Var(y))) -> raise (Invalid_sqrt ("Invalid square root of -"^y^""))

  (* Warning : some expressions can be invalid,
     so it will be necessary to check them during evaluation *)
  | _ as r -> Sqrt(r)

(* Check if the argument of log is valid *)
and parse_log = function
  (* If the argument is a non-zero but positive value -> OK; otherwise -> KO *)
  | Val(Num.Int(x)) as v when x > 0 -> Log(v)
  | Val(Num.Int(x)) -> raise (Invalid_log ("Invalid logarithm of "
					    ^(string_of_int x)^""))

  (* If the argument is -y -> KO*)
  | (Unop('-',Var(y))) -> raise (Invalid_log ("Invalid logarithm of -"^y^""))

  | _ as r -> Log(r)


and parse_trigo = function
  (* If -1 <= x =< 1 -> OK; otherwise -> KO *)
  | Val(Num.Int(x)) as v when x <= 1 && x >= -1 -> v
  | Val(Num.Int(x)) -> raise (Invalid_trigo ("Invalid trigonometric function"
					     ^" applied on "
					     ^(string_of_int x)^""))
  | _ as r -> r
;;


(* Solve a first degree equation *)
let solve_binop : (char * math_expr) -> math_expr =
fun binop -> let (op,n) = binop in
	       match op with 
		 | '+' -> Unop('-',n)
		 | '-' -> n
		 | '*' -> Frac(Val(Num.Int(1)),n)
		 | _ -> raise (Invalid_binop "Unrecognized operation")
;;


let solve_2nd_aux :  int -> int -> int -> math_expr list = 
  fun a b delta -> 
    let aa = Val(Num.Int(a)) in
    let bb = Val(Num.Int(-b)) in
    let sqrt_d = (Sqrt(Val(Num.Int(delta)))) in
    [Frac(Binop('+',bb,sqrt_d),Binop('*',Val(Num.Int(2)),aa));
     Frac(Binop('+',bb,sqrt_d),Binop('*',Val(Num.Int(2)),aa))]
;;

(* Solve a first degree equation *)
let solve_2nd_degree_equation : int -> int -> int -> math_expr list =
fun a b c -> let delta = (b*b) - 4*a*c in
	     match delta with
	       | 0 -> [Unop('-',Frac(Val(Num.Int(b)),
				     Binop('*',Val(Num.Int(2)),
					   Val(Num.Int(a)))))]
	       | _ -> 
		 (
		   if delta > 0 
		   then solve_2nd_aux a b delta
		   else []
		 )
;;


(* Solve an equation finding a value that 
   puts the expression to zero *)
let rec solve : math_expr -> string -> math_expr list = 
  fun x s -> match x with
    (* x = 0, -x = 0 *)
    | Unop(_,Var(v)) | Var(v) when v = s -> [Val(Num.Int(0))]

    (*ax + b*)
    | Binop('+',Binop('*',Val(Num.Int(a)),Var(v)),Val(Num.Int(b)))
	when v = s -> [Frac(Val(Num.Int(-b)),Val(Num.Int(a)))]

    (* ax² + bx + c = 0*)
    | Binop('+',
	    Binop('*',Val(Num.Int(a)),Pow(Var(x),Val(Num.Int(2)))),
	    Binop('+',Binop('*',Val(Num.Int(b)),Var(y)),Val(Num.Int(c))))
	 when x = y -> (solve_2nd_degree_equation a b c)
  
    (* x + n = 0, n + x = 0, x - n = 0, n - x = 0, n is a value *)
    | Binop(op,(Val(_) as n),Var(v)) | Binop(op,Var(v),(Val(_) as n))
	 when v = s -> [solve_binop (op,n)]

    | Expo(Var(v)) | Cos(Var(v)) | Sin(Var(v)) when v = s -> []
    | Log(Var(v)) when v = s -> [Val(Num.Int(0))]
    | Sqrt(Var(v)) when v = s -> [Val(Num.Int(1))]
    | _ -> raise (Invalid_solve("Cannot solve the equation\n"))
;;



(* Subtitution *)
let rec subst : math_expr -> string -> math_expr -> math_expr = 
  fun x s m -> match x with
    | Var(str) when str = s -> m
    | Unop(op,e) -> Unop(op,(subst e s m))
    | Binop(op,e1,e2) -> Binop(op,(subst e1 s m),(subst e2 s m))
    | Frac(e1,e2) -> Frac((subst e1 s m),(subst e2 s m))
    | Pow(e1,e2) -> Pow((subst e1 s m),(subst e2 s m))
    | Sqrt(n) -> Sqrt(subst n s m)
    | Expo(n) -> Expo(subst n s m)
    | Log(n) -> Log(subst n s m)
    | Cos(n) -> Cos(subst n s m)
    | Sin(n) -> Sin(subst n s m)
    | Tan(n) -> Tan (subst n s m)
    | Acos(n) -> Acos(subst n s m)
    | Asin(n) -> Asin(subst n s m)
    | Atan(n) -> Atan(subst n s m)
    | _ as r-> r 


(* Test if there at maximum 1 VAR s, this is for PLOT*)
let rec plotTest : math_expr -> string -> bool = 
  fun x s -> match x with
    | Var str when str<>s -> false
    | Unop(op,e) ->  plotTest e s 
    | Binop(op,e1,e2) -> (plotTest e1 s ) && (plotTest e2 s )
    | Frac(e1,e2) ->  (plotTest e1 s ) && (plotTest e2 s )
    | Pow(e1,e2) -> (plotTest e1 s ) && (plotTest e2 s)
    | Sqrt(n) -> plotTest n s 
    | Expo(n) ->plotTest n s 
    | Log(n) ->plotTest n s 
    | Cos(n) ->plotTest n s 
    | Sin(n) -> plotTest n s 
    | Tan(n) ->plotTest n s 
    | Acos(n) -> plotTest n s 
    | Asin(n) -> plotTest n s 
    | Atan(n) -> plotTest n s 
    | _ -> true
;;


(* Leibniz formula *)
let rec sum_leibniz (n: float) : float =
  let rec sum_aux v acc =
    match v with
      | 0. -> 1. +. acc
      | k -> sum_aux (k -. 1.) ((((-1.) ** k)/.(2. *. k +. 1.)) +. acc)
  in
  sum_aux n 0.
;;

(* Optimized Leibniz formula *)
let rec sum_leibniz_opt i j = match i with
  | 0. -> sum_leibniz j
  | _ -> ((sum_leibniz_opt (i -. 1.) j) +. 
	     (sum_leibniz_opt (i -. 1.) (j +. 1.))) /. 2.
;;

(* Evaluate Pi *)
let eval_pi = 4. *. (sum_leibniz_opt 16. 16.);;



let eval_frac (num: float) (denom: float) = 
  if(denom = 0.) then raise Division_by_zero
  else (num /. denom)
;;


(* Evaluate an expression to get a floating point value *)
let rec eval : math_expr -> float = 
  fun m -> match m with
	| Var str -> raise (Invalid_evaluation("An expression cannot"^
			      " have a variable\n"))
	| Pi -> eval_pi
	| Exp1 -> exp(1.)
	| Unop('-',x) -> 0. -. (eval x)
	| Binop('+',e1,e2) -> (eval e1) +. (eval e2)
	| Binop('-',e1,e2) -> (eval e1) -. (eval e2)
	| Binop('*',e1,e2) -> (eval e1) *. (eval e2)	
	| Val(Num.Int(x)) -> float_of_int x
	| Frac(e1,e2) -> eval_frac (eval e1) (eval e2)
	| Pow(e1,e2) -> (eval e1) ** (eval e2)
	| Sqrt(n) -> sqrt (eval n)
	| Expo(n) -> exp (eval n)
	| Log(n) -> log (eval n)
	| Cos(n) -> cos (eval n)
	| Sin(n) -> sin (eval n) 
	| Tan(n) -> tan (eval n) 
	| Acos(n) -> acos (eval n) 
	| Asin(n) -> asin (eval n) 
	| Atan(n) -> atan (eval n)
	| _ -> raise (Invalid_math_expr "Unrecognized mathematic expression")
;;

(* Display the results of solve() as formulas *)
let rec print_solve : math_expr list -> unit = 
fun l -> match l with
  | [] -> print_string("No solution found\n")
  | [s] -> print_string(formula_of_math_expr(s)^"\n"); ()
  | h::q -> print_string(formula_of_math_expr(h)^"\n"); print_solve q;
;;
