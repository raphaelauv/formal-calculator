

(** Derivative and integration *)

open Mathexpr;;
open Simplify;;


(*let rec is_derivable : math_expr -> string -> bool = 
fun m s -> match m with
  | Pi | Exp1 | Val(_) -> true
  | Var(v) when v = s -> true
  | Var(_) as var -> false
  | Unop(_,x) -> is_derivable x
  | Binop(_,x,y) -> (if (is_derivable x) then)*)


(* Derive an expression *)
let rec derive : math_expr -> string -> math_expr = 
  fun ex s -> match ex with
    | Pi | Exp1 | Val(_) -> Val(Num.Int(0))
    | Var(v) when v = s -> Val(Num.Int(1))
    | Var(_) as var -> var

    (* (+/- u)' = +/- u' *)
    | Unop('+',u) -> simpl((derive u s))
    | Unop('-',u) -> simpl(Unop('-',(derive u s)))

    (* (u + v)' = u' + v' et (u - v)' = u' - v' *)
    | Binop(op,u,v) 
	when op = '+' || op = '-' -> simpl(Binop(op,(derive u s),(derive v s)))

    (* (nx)' = n, n is a value *)
    | Binop(op,(Val(Num.Int(_)) as n),Var(v))
    | Binop(op,(Var(_) as n),Var(v)) when v = s -> n

    (* (u*v)' = u'v + uv' *)
    | Binop(op,u,v) -> simpl(Binop('+',Binop(op,(derive u s),v),
			     Binop(op,u,(derive v s))))

    (* (x/y) does not change if x and y are values*)
    | Frac(Pi,Pi) | Frac(Pi,Exp1) | Frac(Exp1,Pi) | Frac(Exp1,Exp1)
    | Frac(Pi,Val(_)) | Frac(Val(_),Pi) | Frac(Val(_),Exp1) | Frac(Exp1,Val(_))
    | Frac(Val(_),Val(_))as f -> f

    (* (y/u)' = -y*(u'/u²) y is a variable*)
    | Frac((Var(_) as y),u) -> Unop('-',
				    Binop('*',y,Frac((derive u s),
						     Pow(u,Val(Num.Int(2))))))


    (* (1/u)' = -(u'/u²)*)
    | Frac(Val(Num.Int(1)),u) -> Unop('-',Frac((derive u s),
					       Pow(u,Val(Num.Int(2)))))

    (* (u/v)' = (u'v + uv')/v² *)
    | Frac(u,v) -> simpl(Frac((Binop('-',Binop('*',(derive u s),v),
			       Binop('*',u,(derive v s)))),
			Pow(v,Val(Num.Int(2)))))
    
    (* (u^n)' = nu'*u^(n-1) *)
    | Pow(u,(Val(Num.Int(n)) as nn)) -> simpl(Binop('*',Binop('*',nn,(derive u s)),
				      Pow(u,Val(Num.Int(n-1)))))

    (* (sqrt(u))' = u'/(2*sqrt(v)) *)
    | Sqrt(u) as sq -> simpl(Frac((derive u s),(Binop('*',Val(Num.Int(2)),sq))))

    (* (Log(u))' = u'/u *)
    | Log(u) -> simpl(Frac((derive u s),u))

    (* e^y = u'*e^u *)
    | Expo(u) as e -> simpl(Binop('*',(derive u s),e))

    (* cos(u)' = u'*(-sin(u)) *)
    | Cos(u) -> (Binop('*',(derive u s),Unop('-',Sin(u))))
    | Sin(u) -> simpl(Binop('*',(derive u s),Cos(u)))
    | Tan(u) -> simpl(Frac(Val(Num.Int(1)),Pow(Cos(u),Val(Num.Int(2)))))

    | _ -> raise(Invalid_derivative("Unsupported derivation of "^
					(string_of_tree_of_math ex)^""))
;;


(* OPTIONAL :  give the n derivation of an math_expr *)
(*let  rec derive_n : math_expr -> int -> math_expr = 
  fun x y -> match y with
    | 0 -> x
    (*    | y when y<0 -> raise Invalid_derive_n_Argument ("argument de derivation_n inferieur a 0 ") *)
    | y -> derive_n  (derive x) (y-1)
;;  *)

      
(* Integration of an expression *)
let rec integ : math_expr -> string -> math_expr -> math_expr -> math_expr = 
  fun x s a b -> match x with
    | Val(Num.Int(0)) -> Val(Num.Int(1))
    | Val(Num.Int(1)) -> Binop('-',b,a)
    | Val(Num.Int(x)) as c -> Binop('-',Binop('*',c,b),Binop('*',c,a))
    | Pi -> Binop('-',Binop('*',Pi,b),Binop('*',Pi,a))
    | Exp1 -> Binop('-',Binop('*',Exp1,b),Binop('*',Exp1,a))

    (* nu'*u^(n-1) ->  (u^n)' *)
    | Binop('*',Binop('*',n,u), Pow(v,Val(_)))
	when u = v -> Binop('-',Pow(b,n),Pow(a,n))
    | Binop('*',n,u) -> Binop('-',Pow(b,n),Pow(a,n))

    (* u'/u^n *)
    | Frac(Val(Num.Int(-1)),
		    Pow(Var(v),Val(Num.Int(2))))
	when v = s -> Binop('-',Frac(Val(Num.Int(1)),b),Frac(Val(Num.Int(1)),a))

    | Frac(Val(Num.Int(n)),
		    Pow(Var(v),Val(Num.Int(m))))
	when v = s && m = (n+1) 
	       -> Binop('-',Frac(Val(Num.Int(n)),b),Frac(Val(Num.Int(n)),a))

    | Frac(Val(Num.Int(1)),(Binop('*',Val(Num.Int(2)),Sqrt(Var(v)))))
	when v = s -> Binop('-',Sqrt(b),Sqrt(a))

    (* 1/x -> log(x)*)
    | Frac(Val(Num.Int(1)),Var(v)) 
	when v = s -> Binop('-', Log(b),Log(a))

    | Expo(Var(v)) when v = s -> Binop('-', Expo(b),Expo(a))

    (*Cosine, Sine and Tangent*)
    | Cos(Var(v)) when v = s -> Binop('-', Sin(b),Sin(a))
    | Unop('-',Sin(Var(v))) when v = s -> Binop('-', Cos(b),Cos(a))
    | Frac(Val(Num.Int(1)),Pow(Cos(Var(v)),Val(Num.Int(2))))
	when v = s -> Binop('-', Tan(b),Tan(a))

    | _  -> raise (Invalid_integration("Cannot integrate the expression"))
;;
