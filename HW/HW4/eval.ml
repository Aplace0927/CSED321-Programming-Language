(*
 * Call-by-value reduction   
 *)

exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1
  in
  s ^ "__" ^ (string_of_int (!freshVarCounter))
               
(*
 * implement a single step with reduction using the call-by-value strategy.
 *)
 let rec stepv (e: Uml.exp): Uml.exp =
  let rec substitute (vbef: Uml.exp) (vaft: Uml.exp) (expr: Uml.exp): Uml.exp = 
    match expr with
    | Var (x: Uml.var) -> if x = (Inout.exp2string vbef) then vaft else expr (* Only when should be replaced: NOT in free var *)
    | App (e1, e2: Uml.exp * Uml.exp) -> App (substitute vbef vaft e1, substitute vbef vaft e2) 
    | Lam (x, e: Uml.var * Uml.exp) -> 
      if x = (Inout.exp2string vbef) then
        Lam(x, e)
      else
        let rec freevar (expr: Uml.exp): Uml.var list =
          match expr with
          | Var (x: Uml.var) -> [x] (* Single free variable *)
          | App (e1, e2: Uml.exp * Uml.exp) -> freevar e1 @ freevar e2 (* Union of free variables of both expression *)
          | Lam (x, e: Uml.var * Uml.exp) -> List.filter (fun v -> x <> v) (freevar e) (* Free variable except x*)
        in
      if List.mem x (freevar vaft) then  (* x in free-var space of expression, need to be 'a-subst *)
        let fv = getFreshVariable x in
        Lam (fv, substitute vbef vaft (substitute (Uml.Var x) (Uml.Var fv) e))  (* Subst. with fresh variable*)
      else
        Lam (x, substitute vbef vaft e)
    in
  match e with
  | App(Lam(v, exp), Lam(v', exp')) -> substitute (Var v) (Lam(v', exp')) exp (* Apply CBV directly *)
  | App(Lam(v, exp), following) -> App(Lam(v, exp), stepv following)  (* Apply CBV on following side *)
  | App(heading, following) -> App(stepv heading, following)  (* Apply CBV on heading side *)
  | _ -> raise Stuck

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

