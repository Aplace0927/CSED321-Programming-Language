open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = Heap.loc list
 and value = 
  | VClosure of env * exp
  | VEunit
  | VInl of env * exp
  | VInr of env * exp
  | VTrue | VFalse
  | VNum of int
  | VPlus | VMinus | VEq

 and frame = 
  | FApp of env * exp
  | FCase of env * exp * exp
  | FIfthenelse of env * exp * exp
  | FFst | FSnd
  | FPlus | FPlus_Env_Exp of env * exp | FPlus_Num of int
  | FMinus | FMinus_Env_Exp of env * exp | FMinus_Num of int
  | FEq | FEq_Env_Exp of env * exp | FEq_Num of int
  | FLoc of int

(* Define your own empty environment *)
let emptyEnv = []

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp (v: value): exp = 
  match v with
  | VTrue -> True
  | VFalse -> False
  | VEunit -> Eunit
  | VNum (i) -> Num (i)
  | _ -> raise NotConvertible

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)

module NamingCtxKey = 
struct
  type t = var
  let compare = Stdlib.compare
end

module Gamma = Map.Make(NamingCtxKey)

module ControlFlow =
struct
  let return (st: state) (vl: value): state = 
    match st with
    | Return_ST(_, _, _) -> raise Stuck
    | Anal_ST(heap, stck, expr, envr) -> Return_ST(heap, stck, vl)
  let call (st: state) (fr: frame) (ex: exp): state = 
    match st with
    | Return_ST(_, _, _) -> raise Stuck
    | Anal_ST(heap, stck, expr, envr) -> Anal_ST(heap, Frame_SK(stck, fr), ex, envr)
  let jump (st: state) (fr: frame) (ex: exp) (nv: env): state = 
    match st with
    | Return_ST(_, _, _) -> raise Stuck
    | Anal_ST(heap, stck, expr, envr) -> Anal_ST(heap, Frame_SK(stck, fr), ex, nv)
  let branch (st: state) (ex: exp) (nv: env): state = 
    match st with
    | Return_ST(_, _, _) -> raise Stuck
    | Anal_ST(heap, stck, expr, envr) -> Anal_ST(heap, stck, ex, nv)
  let allocate (st: state) (ex: exp) (nv: env) (he, loc: (int * stoval) list * index): state = 
    match st with
    | Return_ST(_, _, _) -> raise Stuck
    | Anal_ST(heap, stck, expr, envr) -> Anal_ST(he, stck, ex, [loc] @ nv)
end

let context (txp: texp): int Gamma.t =
  let rec context_rec (txp: texp) (bndd_val: var list) (free_val: int Gamma.t) (lv: int): (int Gamma.t * int) = 
    let context_among (x_list: texp list) (v_list: var list list): (int Gamma.t * int) = 
      let ffrec_double (x: texp) (v: var list) (f, lv: int Gamma.t * int) = context_rec (x) (v @ bndd_val) (f) (lv) in
      List.fold_right2 (ffrec_double) (x_list) (v_list) (free_val, lv)
    in
    match txp with
    | Tvar(v) -> if ((List.mem (v) (bndd_val)) || (Gamma.mem (v) (free_val))) then (free_val, lv) else ((Gamma.add v lv free_val), lv + 1)
    | Tlam(v, _, x) -> context_rec (x) ([v] @ bndd_val) (free_val) (lv)
    | Tapp(xfun, xarg) -> context_among ([xfun; xarg]) ([[];[]])
    | Tpair(xfst, xsnd) -> context_among  ([xfst; xsnd]) ([[];[]])
    | Tfst(x) | Tsnd(x) | Tinl(x, _) | Tinr(x, _) -> context_rec (x) (bndd_val) (free_val) (lv)
    | Tcase(xcase, vl, xl, vr, xr) -> context_among ([xcase; xl; xr]) ([[]; [vl]; [vr]])
    | Tifthenelse(xif, xtrue, xfalse) -> context_among ([xif; xtrue; xfalse]) ([[];[];[]])
    | Tfix(v, _, e) -> context_rec (e) ([v] @ bndd_val) (free_val) (lv)
    | _ -> (free_val, lv)
    in
  let (ctx, _) = context_rec (txp) ([]) (Gamma.empty) (0) in ctx


let texp2exp (txp: texp): exp =
  let rec texp2exp_ctx (txp': texp) (ctx: int Gamma.t) (lv: int): exp =
    match txp' with
    | Teunit -> Eunit
    | Tvar(v) -> if (Gamma.mem (v) (ctx)) then Ind(lv - (Gamma.find (v) (ctx)) - 1) else Ind((Gamma.find (v) (context txp)) + lv)
    | Tlam(v, _, x) -> Lam(texp2exp_ctx x (Gamma.add (v) (lv) (ctx)) (lv + 1))
    | Tapp(xfun, xarg) -> App(texp2exp_ctx xfun ctx lv, texp2exp_ctx xarg ctx lv)
    | Tpair(xfst, xsnd) -> Pair(texp2exp_ctx xfst ctx lv, texp2exp_ctx xsnd ctx lv)
    | Tfst(x) -> Fst(texp2exp_ctx x ctx lv)
    | Tsnd(x) -> Snd(texp2exp_ctx x ctx lv)
    | Tcase(xcase, vl, xl, vr, xr) -> Case(texp2exp_ctx xcase ctx lv, texp2exp_ctx (xl) (Gamma.add (vl) (lv) (ctx)) (lv + 1), texp2exp_ctx (xr) (Gamma.add (vr) (lv) (ctx)) (lv + 1))
    | Tinl(x, _) -> Inl(texp2exp_ctx x ctx lv)
    | Tinr(x, _) -> Inr(texp2exp_ctx x ctx lv)
    | Tfix(v, _, x) -> Fix(texp2exp_ctx (x) (Gamma.add (v) (lv) (ctx)) (lv + 1))
    | Ttrue -> True
    | Tfalse -> False
    | Tifthenelse(xif, xtrue, xfalse) -> Ifthenelse(texp2exp_ctx xif ctx lv, texp2exp_ctx xtrue ctx lv, texp2exp_ctx xfalse ctx lv)
    | Tnum(n) -> Num (n)
    | Tplus -> Plus
    | Tminus -> Minus
    | Teq -> Eq
  in texp2exp_ctx (txp) (Gamma.empty) (0)
  

(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   
 let rec tau (e: exp) (n: int) (i: int): exp =
  match e with
  | Eunit -> Eunit
  | Ind(m) -> if (m >= i) then Ind(m + n) else Ind(m)
  | Lam(elam) -> Lam(tau elam n (i+1))
  | App(efun, earg) -> App(tau efun n i, tau earg n i)
  | Pair(efst, esnd) -> Pair(tau efst n i, tau esnd n i)
  | Fst(epair) -> Fst(tau epair n i)
  | Snd(epair) -> Snd(tau epair n i)
  | Case(ecase, el, er) -> Case(tau ecase n i, tau el n (i+1), tau er n (i+1))
  | Inl(ecase) -> Inl(tau ecase n i)
  | Inr(ecase) -> Inr(tau ecase n i)
  | Fix(efix) -> Fix(tau efix n (i+1))
  | True -> True
  | False -> False
  | Ifthenelse(eif, etrue, efalse) -> Ifthenelse(tau eif n i, tau etrue n i, tau efalse n i)
  | Num(n) -> Num(n)
  | Plus -> Plus
  | Minus -> Minus
  | Eq -> Eq

let rec sigma (n: int) (ebef: exp) (eaft: exp): exp =
  match ebef with
  | Eunit -> Eunit
  | Ind m -> if (m = n) then (tau eaft n 0) else if (m > n) then Ind(m - 1) else Ind(m)
  | Lam(x) -> Lam(sigma (n+1) x eaft)
  | App(efun, earg) -> App(sigma n efun eaft, sigma n earg eaft)
  | Pair(efst, esnd) -> Pair(sigma n efst eaft, sigma n esnd eaft)
  | Fst(epair) -> Fst(sigma n epair eaft)
  | Snd(epair) -> Snd(sigma n epair eaft)
  | Case(ecase, el, er) -> Case(sigma n ecase eaft, sigma (n+1) el eaft, sigma (n+1) er eaft)
  | Inl(ecase) -> Inl(sigma n ecase eaft)
  | Inr(ecase) -> Inr(sigma n ecase eaft)
  | Fix(ecase) -> Fix(sigma (n+1) ecase eaft)
  | True -> True
  | False -> False
  | Ifthenelse(eif, etrue, efalse) -> Ifthenelse(sigma n eif eaft, sigma n etrue eaft, sigma n efalse eaft)
  | Num(n) -> Num(n)
  | Plus -> Plus
  | Minus -> Minus
  | Eq -> Eq

let rec step1 (e: exp): exp =
  let rec redex (e: exp): bool = 
    match e with
    | Eunit | True | False | Num _ | Lam _ -> false
    | Pair(xfst, xsnd) -> (redex xfst) || (redex xsnd)
    | Inl(x) | Inr(x) -> redex x
    | _ -> true
  in 
  match e with
  | App(Lam(efun), earg) -> if redex earg then App(Lam(efun), step1 earg) else sigma 0 efun earg
  | App(Plus, expr) -> 
    (
      match expr with
      | Pair(Num(i), Num(j)) -> Num(i + j)
      | other -> App(Plus, step1 other)
    )
  | App(Minus, expr) -> 
    (
      match expr with
      | Pair(Num(i), Num(j)) -> Num(i - j)
      | other -> App(Minus, step1 other)
    )
  | App(Eq, expr) -> 
    (
      match expr with
      | Pair(Num(i), Num(j)) -> if (i = j) then True else False
      | other -> App(Eq, step1 other)
    )
  | App(efun, earg) -> App(step1 efun, earg)
  | Pair(efst, esnd) -> if redex efst then Pair(step1 efst, esnd) else Pair(efst, step1 esnd)
  | Fst(epair) ->
    if redex epair then Fst(step1 epair)
    else (
      match epair with
      | Pair(efst, esnd) -> efst
      | _ -> raise Stuck
    )
  | Snd(epair) ->
    if redex epair then Snd(step1 epair)
    else (
      match epair with
      | Pair(efst, esnd) -> esnd
      | _ -> raise Stuck
    )
  | Case(ecase, el, er) -> 
    if redex ecase then Case(step1 ecase, el, er)
    else (
      match ecase with 
      | Inl(expr) -> sigma 0 el expr 
      | Inr(expr) -> sigma 0 er expr 
      | _ -> raise Stuck
    )
  | Inl(ecase) -> Inl(step1 ecase)
  | Inr(ecase) -> Inr(step1 ecase)
  | Ifthenelse(expr, etrue, efalse) -> 
    (
      match expr with
      | True -> etrue
      | False -> efalse
      | other -> Ifthenelse(step1 other, etrue, efalse)
    )
  | Fix(expr) -> sigma 0 expr (Fix(expr))
  | _ -> raise Stuck

(* Problem 3. 
 * step2 : state -> state *)
let step2 (st: state): state =
  match st with
  | Anal_ST (heap, stck, expr, envr: stoval Heap.heap * stack * exp * env) -> (
      match expr with
      | Eunit -> ControlFlow.return (st) (VEunit)
      | Ind(x) -> (
        if ((List.length (envr)) <= x) then raise Stuck
        else (
          let fram = Heap.deref (heap) (List.nth (envr) (x)) in
          match fram with
          | Computed(valu) -> ControlFlow.return (st) (valu)
          | Delayed(expr, envr) -> ControlFlow.call (st) (FLoc(List.nth (envr) (x))) (expr)
        )
      )
      | Lam(elam) -> ControlFlow.return (st) (VClosure(envr, Lam(elam)))
      | App(efun, earg) -> ControlFlow.call (st) (FApp(envr, earg)) (efun)
      | Pair(efst, esnd) -> ControlFlow.return (st) (VClosure(envr, Pair(efst, esnd)))
      | Fst(epair) -> ControlFlow.call (st) (FFst) (epair)
      | Snd(epair) -> ControlFlow.call (st) (FSnd) (epair)
      | Case(ecase, el, er) -> ControlFlow.call (st) (FCase(envr, el, er)) (ecase)
      | Inl(ecase) -> ControlFlow.return (st) (VInl(envr, ecase))
      | Inr(ecase) -> ControlFlow.return (st) (VInr(envr, ecase))
      | Fix(expr) -> ControlFlow.return (st) (VClosure(envr, Fix(expr)))
      | True -> ControlFlow.return (st) (VTrue)
      | False -> ControlFlow.return (st) (VFalse)
      | Ifthenelse(eif, etrue, efalse) -> ControlFlow.call (st) (FIfthenelse(envr, etrue, efalse)) (eif)
      | Num(n) -> ControlFlow.return (st) (VNum(n))
      | Plus -> ControlFlow.return (st) (VPlus)
      | Minus -> ControlFlow.return (st) (VMinus)
      | Eq -> ControlFlow.return (st) (VEq)
    )
  | Return_ST (heap, stck, envr: stoval Heap.heap * stack * value) -> (
    match stck with
      | Hole_SK -> raise Stuck
      | Frame_SK (stck, fr) ->
        (match fr, envr with
        | _, VEunit -> raise Stuck
        | _, VClosure(nlam, Fix(exp)) -> ControlFlow.allocate (st) (exp) (nlam) (Heap.allocate (heap) (Delayed(Fix(exp), nlam)))
        | (FLoc (idx), env) -> Return_ST(Heap.update (heap) (idx) (Computed env), stck, env) 
        | (FApp (napp, eapp), VClosure (nfun, Lam (efun))) -> ControlFlow.allocate (st) (efun) (nfun) (Heap.allocate (heap) (Delayed(eapp, napp)))
        | (FFst, VClosure(npair, Pair(efst, esnd))) -> ControlFlow.branch (st) (efst) (npair)
        | (FSnd, VClosure(npair, Pair(efst, esnd))) -> ControlFlow.branch (st) (esnd) (npair)
        | (FCase(ncase, el, er), VInl(ninl, ecase)) -> ControlFlow.allocate (st) (el) (ncase) (Heap.allocate (heap) (Delayed(ecase, ninl)))
        | (FCase(ncase, el, er), VInr(ninr, ecase)) -> ControlFlow.allocate (st) (er) (ncase) (Heap.allocate (heap) (Delayed(ecase, ninr)))
        | (FIfthenelse(nif, etrue, efalse), VTrue) -> ControlFlow.branch (st) (etrue) (nif)
        | (FIfthenelse(nif, etrue, efalse), VFalse) -> ControlFlow.branch (st) (efalse) (nif)
        | (FApp(napp, eapp), VPlus) ->  ControlFlow.jump (st) (FPlus) (eapp) (napp)
        | (FApp(napp, eapp), VMinus) ->  ControlFlow.jump (st) (FMinus) (eapp) (napp)
        | (FApp(napp, eapp), VEq) -> ControlFlow.jump (st) (FEq) (eapp) (napp)
        | (FPlus, VClosure(nfun, Pair(efst, esnd))) -> ControlFlow.jump (st) (FPlus_Env_Exp(nfun, esnd)) (efst) (nfun)
        | (FMinus, VClosure(nfun, Pair(efst, esnd))) -> ControlFlow.jump (st) (FMinus_Env_Exp(nfun, esnd)) (efst) (nfun)
        | (FEq, VClosure(nfun, Pair(efst, esnd))) -> ControlFlow.jump (st) (FEq_Env_Exp(nfun, esnd)) (efst) (nfun)
        | (FPlus_Env_Exp(nplus, eplus), VNum(i)) -> ControlFlow.jump (st) (FPlus_Num(i)) (eplus) (nplus)
        | (FMinus_Env_Exp(nminus, eminus), VNum(i)) -> ControlFlow.jump (st) (FMinus_Num(i)) (eminus) (nminus)
        | (FEq_Env_Exp(neq, eeq), VNum(i)) -> ControlFlow.jump (st) (FEq_Num(i)) (eeq) (neq)
        | (FPlus_Num(i), VNum(j)) -> ControlFlow.return (st) (VNum(i + j))
        | (FMinus_Num(i), VNum(j)) -> ControlFlow.return (st) (VNum(i - j))
        | (FEq_Num(i), VNum(j)) -> ControlFlow.return (st) (if i = j then VTrue else VFalse)
        | _ -> raise Stuck
        )
  )
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "(fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
let state2string st = match st with
    Anal_ST(_,_,exp,_) -> "Analysis : ???"
  | Return_ST(_,_,_) -> "Return : ??? "

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
