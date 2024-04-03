open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = Tml.var -> Tml.tp

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = (fun t -> raise TypeError)

(* val typing : context -> Tml.exp -> Tml.tp *)
let rec typing (cxt: context) (e: Tml.exp): Tml.tp =
  match e with
  | Tml.Var var -> cxt var
  | Tml.Lam (var, typ, exp) -> Tml.Fun (typ, typing (fun x -> if x = var then typ else cxt x) exp)
  | Tml.App (exp1, exp2) -> 
    (
    match (typing cxt exp1) with
    | Tml.Fun (typ1, typ2) ->
      if (typing cxt exp2) = typ1 then typ2
      else raise TypeError
    | _ -> raise TypeError
    )
  | Tml.Pair (exp1, exp2) -> Tml.Prod(typing cxt exp1, typing cxt exp2)
  | Tml.Fst (exp) -> 
    (
    match exp with
    | Tml.Pair (exp1, exp2) -> typing cxt exp1
    | _ -> raise TypeError
    )
  | Tml.Snd (exp) -> 
    (
    match exp with
    | Tml.Pair (exp1, exp2) -> typing cxt exp2
    | _ -> raise TypeError
    )
  | Tml.Eunit -> Tml.Unit
  | Tml.Inl (exp, typ) -> Tml.Sum(typing cxt exp, typ)
  | Tml.Inr (exp, typ) -> Tml.Sum(typ, typing cxt exp)
  | Tml.Case (exp, var1, exp1, var2, exp2) ->
    (
    match (typing cxt exp) with
    | Tml.Sum (typ1, typ2) ->
      if (typing (fun t -> if t = var1 then typ1 else cxt t) exp1) = (typing (fun t -> if t = var2 then typ2 else cxt t) exp2) then
        (typing (fun t -> if t = var1 then typ1 else cxt t) exp1)
      else raise TypeError
    | _ -> raise TypeError
    )
  | Tml.Fix (var, typ, exp) -> typing (fun x -> if x = var then typ else cxt x) exp
  | Tml.True | Tml.False -> Tml.Bool
  | Tml.Ifthenelse (expcond, exptrue, expfalse) -> 
    (
    match (typing cxt expcond) with
    | Bool ->
      if (typing cxt exptrue) = (typing cxt expfalse) then (typing cxt exptrue)
      else raise TypeError
    | _ -> raise TypeError
    )
  | Num (n) -> Int
  | Plus -> Fun(Prod(Int, Int), Int)
  | Minus -> Fun(Prod(Int, Int), Int)
  | Eq -> Fun(Prod(Int, Int), Bool)

let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None