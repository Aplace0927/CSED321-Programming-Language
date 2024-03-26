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
      if List.mem x (freevar e) then  (* x in free-var space of expression, need to be 'a-subst *)
        let fv = getFreshVariable x in
        let modify_e = substitute (Uml.Var x) (Uml.Var fv) e in
        Lam (fv, substitute vbef vaft modify_e)  (* Subst. with fresh variable*)
      else  (* No need to be 'a-subst-ed*)
        Lam (x, substitute vbef vaft e)
    in
  match e with
  | App (Lam(bef, expr), aft) -> substitute (Uml.Var bef) aft expr (* Directly apply 'b-reduction *)
  | App (e1, e2) -> let reduced_e1 = (stepv e1) in if e1 = reduced_e1 then App (e1, stepv e2) else App (stepv e1, e2) (* Apply 'b-reduction as CBV policy *)
  | Lam (x, e) -> Lam (x, stepv e) (* Try step on expression part *)
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

