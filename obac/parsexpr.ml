
open Expr
open Genlex

let flat_op o e = match e with
  | Op (o',l) when o=o' -> l
  | _ -> [e]

(* We direclty build n-ary nodes for "+" and "*" *)
let mkop o e1 e2 =
  match o with
  | "+" | "*" -> Op (o, flat_op o e1 @ flat_op o e2)
  | _ -> Op (o, [e1;e2])

let left_operation lire_base operateurs =
  let rec lire_reste e1 = parser
  | [< 'Kwd op when List.mem op operateurs;
       e2 = lire_base;
       e = lire_reste (mkop op e1 e2) >] -> e
  | [< 'Int n when n < 0 && List.mem "-" operateurs;
       e = lire_reste (Op ("-", [e1;Num (-n)])) >] -> e
  | [< >] -> e1 in
  parser
  | [< e1 = lire_base; e = lire_reste e1 >] -> e
  | [< 'Kwd "-" when List.mem "-" operateurs;
       e1 = lire_base; e = lire_reste (Op ("-",[e1])) >] -> e

let right_operation lire_base operateurs =
  let rec lire_reste e1 = parser
  | [< 'Kwd op when List.mem op operateurs;
       e2 = lire_base;
       e = lire_reste e2 >] -> Op (op, [e1;e])
  | [< >] -> e1 in
  parser [< e1 = lire_base; e = lire_reste e1 >] -> e

let rec expr_simple = parser
  | [< 'Int i >] -> Num i
  | [< 'Ident "pi" >] -> Op ("pi",[])
  | [< 'Ident "e" >] -> Op ("e",[])
  | [< 'Ident id; e = post_ident id >] -> e
  | [< 'Kwd "("; e = expression; 'Kwd ")" >] -> e

and post_ident id = parser
  | [< 'Kwd "("; l = expressions; 'Kwd ")" >] -> Op(id,l)
  | [< >] -> Var id

and expr0 flux =
  right_operation expr_simple ["^"] flux

and expr1 flux =
  left_operation expr0 ["*"; "/"] flux

and expression flux =
  left_operation expr1 ["+"; "-"] flux

and expressions = parser
  | [< e1 = expression; l = lire_suite >] -> e1::l

and lire_suite = parser
  | [< 'Kwd ","; l = expressions >] -> l
  | [< >] -> []

let analyseur_lexical =
  Genlex.make_lexer [ "("; ")";","; "*"; "/"; "-"; "+"; "^" ]

let expr_of_stream flux =
  try
    let tokens = analyseur_lexical flux in
    let e = expression tokens in
    let () = Stream.empty tokens in
    e
  with err ->
    Printf.printf "Parse error at char %d\n%!" (Stream.count flux);
    raise err

let expr_of_string s = expr_of_stream (Stream.of_string s)
