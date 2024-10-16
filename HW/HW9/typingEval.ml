open Fjava

exception NotImplemented
exception TypeError
exception Stuck

(* Helper module of Constructor definition *)
module Constructor = 
struct
  let name (ctor: constructorDecl): typ = let (nam, prm, sup, ass) = ctor in nam
  let param (ctor: constructorDecl): (typ * string) list = let (nam, prm, sup, ass) = ctor in prm
  let super_init (ctor: constructorDecl): typ list = let (nam, prm, sup, ass) = ctor in sup
  let self_init (ctor: constructorDecl): (typ * typ) list = let (nam, prm, sup, ass) = ctor in ass
end

(* Helper module for Class definition *)
module Class =
struct
  let find_decl (ctx: classDecl list) (cname: typ): classDecl = 
    match List.find_opt (fun (cdecl) -> let (n, _, _, _, _) = cdecl in n = cname) (ctx) with
    | Some cdecl -> cdecl
    | None -> raise TypeError
  let name (ctx: classDecl list) (cname: typ): typ = let (nam, sup, fld, cto, mtd) = find_decl (ctx) (cname) in nam
  let super (ctx: classDecl list) (cname: typ): typ = let (nam, sup, fld, cto, mtd) = find_decl (ctx) (cname) in sup
  let rec fields (ctx: classDecl list) (cname: typ): (typ * string) list = if cname = "Object" then ([]) else let (nam, sup, fld, cto, mtd) = find_decl (ctx) (cname) in fld @ (fields (ctx) (super (ctx) (cname)))
  let ctor (ctx: classDecl list) (cname: typ): constructorDecl = let (nam, sup, fld, cto, mtd) = find_decl (ctx) (cname) in cto
  let rec methods (ctx: classDecl list) (cname: typ): methodDecl list = if cname = "Object" then ([]) else let (nam, sup, fld, cto, mtd) = find_decl (ctx) (cname) in mtd @ (methods (ctx) (super (ctx) (cname)))
  let rec inheritance (ctx: classDecl list) (cname: typ): typ list = if cname = "Object" then ["Object"] else let (nam, sup, fld, cto, mtd) = find_decl (ctx) (cname) in [nam] @ (inheritance (ctx) (super (ctx) (cname)))
end

(* Helper module for Method definition *)
module Meth = 
struct
  let name (mtd: methodDecl): typ = let (typ, nam, prm, bdy) = mtd in nam
  let return_type (mtd: methodDecl): typ = let (typ, nam, prm, bdy) = mtd in typ
  let args (mtd: methodDecl): (string * typ) list = let (typ, nam, prm, bdy) = mtd in prm
  let args_type (mtd: methodDecl): typ list = let (typ, nam, prm, bdy) = mtd in List.map (fun (atype, aname) -> atype) (prm)
  let args_name (mtd: methodDecl): typ list = let (typ, nam, prm, bdy) = mtd in List.map (fun (atype, aname) -> aname) (prm)
  let body (mtd: methodDecl): exp = let (typ, nam, prm, bdy) = mtd in bdy
end

(* Helper module for deducting specific types *)
module TypeOf = 
struct
  let field (ctx_val: (string * typ) list) (fld: string): typ =
    match List.find_opt (fun (ftype, fname) -> fname = fld) (ctx_val) with
    | Some (ftype, fname) -> ftype
    | None -> raise TypeError
    
  let methd (ctx_cls: classDecl list) (cls: string) (mtd: string): typ list * typ = 
    match List.find_opt (fun (mret, mname, margs, mbody) -> mname = mtd) (Class.methods (ctx_cls) (cls)) with
    | Some (mret, mname, margs, mbody) -> (List.map (fun (ftype, fname) -> ftype) (margs), mret)
    | None -> raise TypeError
end

(* Typing expression with specific class context and variable context *)
let rec type_in_ctx (ctx_cls: classDecl list) (ctx_val: (typ * string) list) (expr: exp) =
  match expr with
  | Var (var) -> TypeOf.field (ctx_val) (var) (* T-Var *)
  | Field (exp, fld) -> TypeOf.field (Class.fields (ctx_cls) (type_in_ctx (ctx_cls) (ctx_val) (exp))) (fld) (*T-Field *)
  | Method (exp, mtd, args) ->
      let (margs, mret) = TypeOf.methd (ctx_cls) (type_in_ctx (ctx_cls) (ctx_val) (exp)) (mtd) in
      if List.length (args) <> List.length (margs) then raise TypeError (* mtype(m, C_0) != _D -> _C *)
      else if List.exists2 (fun (arg) (marg) -> List.mem (marg) (Class.inheritance (ctx_cls) (type_in_ctx (ctx_cls) (ctx_val) (arg))) = false) (args) (margs) then raise TypeError (* C </: D*)
      else mret (* T-Invk *)
  | New (tp, args) ->
      if List.length (args) <> List.length (Class.fields (ctx_cls) (tp)) then raise TypeError (* fields(C) != _D _f *)
      else if List.exists2 (fun (arg) (ftype, fname) -> List.mem (ftype) (Class.inheritance (ctx_cls) (type_in_ctx (ctx_cls) (ctx_val) (arg))) = false) (args) (Class.fields (ctx_cls) (tp)) then raise TypeError (* C </: D *)
      else tp (* T-New *)
  | Cast (cast_to, exp) ->
      let cast_from = type_in_ctx (ctx_cls) (ctx_val) (exp) in
      if (List.mem (cast_from) (Class.inheritance (ctx_cls) (cast_to))) || (List.mem (cast_to) (Class.inheritance (ctx_cls) (cast_from))) then cast_to  (* T-Ucast & T-Dcast *)
      else let _ = Printf.printf "Stupid Cast\n" in cast_to (* T-Scast *)

(* Compilation: Check element's validness of specific class from class context *)
module Valid =
struct
  (* Is Constructor well-defined? *)
  let ctor (ctx: classDecl list) (cls: classDecl): bool = 
    let (nam, sup, fld, cto, mtd) = cls in
    if nam <> Constructor.name (cto) then false
    else if List.length (Class.fields (ctx) (sup)) <> List.length (Constructor.super_init (cto)) then false
    else if List.length (fld) <> List.length (Constructor.self_init (cto)) then false
    else if not (List.for_all2 (Stdlib.(=)) (Constructor.param (cto)) (Class.fields (ctx) (sup) @ fld)) then false
    else if not (List.for_all (fun (x, y) -> x = y) (Constructor.self_init (cto))) then false
    else if not (List.for_all (fun (x, y) -> x = y) (Constructor.self_init (cto)) && List.for_all2 (Stdlib.(=)) (List.map (fun (ftype, fname) -> fname) (Constructor.param (cto))) (Constructor.super_init (cto) @ List.map (fun (ftype, fname) -> fname) (Constructor.self_init(cto)))) then false
    else true

  (* Are some method can overriden properly from parent class method to child class method? *)
  let overrd (ctx: classDecl list) (met: methodDecl) (cls: classDecl): bool = 
    let (nam, sup, fld, cto, mtd) = cls in
    let (marg, mret) = try TypeOf.methd (ctx) (Meth.name(met)) (sup) with TypeError -> (Meth.args_type(met), Meth.return_type(met)) in
    if List.length (marg) <> List.length (Meth.args_type(met)) then false
    else if List.exists2 (Stdlib.(!=)) (marg) (Meth.args_type(met)) then false
    else if mret <> Meth.return_type(met) then false
    else true

  (* All of method in specific class from class context are defined well? *)
  (* Checking Method typing *)
  let methd (ctx: classDecl list) (cls: classDecl): bool =
    let methd_of (ctx) (cls) (met: methodDecl): bool = 
      let (nam, sup, fld, cto, mtd) = cls in
      let tbody = type_in_ctx (ctx) ([(nam, "this")] @ Meth.args (met)) (Meth.body (met)) in
      if not (List.mem (Meth.return_type(met)) (Class.inheritance (ctx) (tbody))) then false
      else if not (overrd (ctx) (met) (cls)) then false
      else true
    in
    let (nam, sup, fld, cto, mtd) = cls in List.for_all (methd_of (ctx) (cls)) (mtd)
end
  
(* Typing expression, with validating every class from class context *)
let typeOf (prog: program) =
  let (ctx, exp) = prog in
  if not (List.for_all (Valid.ctor (ctx)) (ctx)) then raise TypeError (* Checking Class typing *)
  else if not (List.for_all (Valid.methd (ctx)) (ctx)) then raise TypeError (* Checking Class typing *)
  else type_in_ctx (ctx) ([]) (exp)

let rec substitute (ctx_val: (typ * exp) list) (expr: exp): exp = (* RC-Invk-Arg *)
  match expr with
  | Var(var) -> (
    match List.find_opt (fun (vname, vexp) -> vname = var) (ctx_val) with
    | Some (vname, vexp) -> vexp
    | None -> raise Stuck
  )
  | Field(fexp, fname) -> Field(substitute (ctx_val) (fexp), fname)
  | Method(mexp, mret, margs) -> Method(substitute (ctx_val) (mexp), (mret), List.map (fun arg -> substitute (ctx_val) (arg)) (margs))
  | New(ntyp, nargs) -> New(ntyp, List.map (fun arg -> substitute (ctx_val) (arg)) (nargs))
  | Cast(ctyp, cexp) -> Cast (ctyp, substitute (ctx_val) (cexp))


let rec idx_of (x: 'a) (l: 'a list): int =
  match l with
  | [] -> raise Stuck
  | hd::tl -> if x = hd then 0 else (idx_of (x) (tl)) + 1
let rec redex (expr: exp): bool =
  match expr with
  | Var(_) -> false
  | New(ntype, nargs) -> List.exists (fun arg -> redex (arg)) (nargs)
  | _ -> true

let rec redex_depth (expl: exp list): int =
  match expl with
  | [] -> raise Stuck
  | hd::tl -> if redex (hd) then 0 else (redex_depth tl) + 1

let step (prog: program): program =
  let (pctx, pexp) = prog in
  let rec step_exp (sexp: exp): exp =
    match sexp with
    | Var _ -> raise Stuck
    | Field(New(ntype, nargs), fname) -> ( (* R-Field *)
      if redex (New(ntype, nargs)) then Field(step_exp (New(ntype, nargs)), fname) 
      else List.nth (nargs) (idx_of (fname) (List.map (fun (ftype, fname) -> fname) (Class.fields (pctx) (ntype))))
    )
    | Field (fexp, fname) -> Field(step_exp (fexp), fname) (* RC-Field *)
    | Method(New(ntype, nargs), mtype, margs) -> (
      if redex (New(ntype, nargs)) then Method(step_exp (New(ntype, nargs)), mtype, margs) (* RC-Invk-Recv *)
      else (
        try ( (* RC-Invk-Arg *)
          let i = redex_depth (margs) in
          Method(New(ntype, nargs), mtype, List.mapi (fun i' e' -> if i' = i then step_exp e' else e') (margs))
        )
        with Stuck -> ( (* R-Invk *)
          let mtd = (
            match List.find_opt (fun meth -> Meth.name(meth) = mtype) (Class.methods (pctx) (ntype)) with
            | Some mtd -> mtd
            | None -> raise Stuck
          ) in
          if List.length (Meth.args_name(mtd)) <> List.length (margs) then raise Stuck
          else substitute ([("this", New(ntype, nargs))] @ (List.combine (Meth.args_name(mtd)) (margs))) (Meth.body (mtd))
        )
      )
    )
    | Method(mexp, mret, margs) -> Method(step_exp mexp, mret, margs)
    | New(ntype, nargs) -> (
        let i = redex_depth nargs
        in New(ntype, List.mapi (fun i' e' -> if i' = i then step_exp e' else e') nargs)
    )
    | Cast(ctype, New(ntype, nargs)) -> ( (* R-Cast *)
      if redex (Cast(ctype, step_exp (New(ntype, nargs)))) then (Cast(ctype, step_exp (New(ntype, nargs)))) (* RC-Cast *)
      else if List.mem (ctype) (Class.inheritance (pctx) (ntype)) then New(ntype, nargs)
      else raise Stuck
    )
    | Cast(ctype, cexp) -> Cast(ctype, step_exp (cexp)) (* RC-Cast *)
  in (pctx, step_exp (pexp))
  
let typeOpt p = try Some (typeOf p) with TypeError -> None
let stepOpt p = try Some (step p) with Stuck -> None
let rec multiStep p = try multiStep (step p) with Stuck -> p

let rec stepStream e =
  let rec steps e =
    match stepOpt e with
        None -> Stream.from (fun _ -> None)
      | Some e' -> Stream.icons e' (steps e')
  in Stream.icons e (steps e)
