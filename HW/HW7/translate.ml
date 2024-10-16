open Mach
open Mono 

exception NotImplemented

(* location *)
type loc =
    L_INT of int          (* integer constant *)
  | L_BOOL of bool        (* boolean constant *)
  | L_UNIT                (* unit constant *)
  | L_STR of string       (* string constant *)
  | L_ADDR of Mach.addr   (* at the specified address *)
  | L_REG of Mach.reg     (* at the specified register *)
  | L_DREF of loc * int   (* at the specified location with the specified offset *)

type venv = (Mono.avid, loc) Dict.dict  (* variable environment *)
let venv0 : venv = Dict.empty           (* empty variable environment *)

type env = venv * int
let env0 : env = (venv0, 0)

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec loc2rvalue l = match l with
    L_INT i -> (Mach.code0, Mach.INT i)
  | L_BOOL b -> (Mach.code0, Mach.BOOL b)
  | L_UNIT -> (Mach.code0, Mach.UNIT)
  | L_STR s -> (Mach.code0, Mach.STR s)
  | L_ADDR a -> (Mach.code0, Mach.ADDR a)
  | L_REG r -> (Mach.code0, Mach.REG r)
  | L_DREF (L_ADDR a, i) -> (Mach.code0, Mach.REFADDR (a, i))
  | L_DREF (L_REG r, i) -> (Mach.code0, Mach.REFREG (r, i))
  | L_DREF (l, i) ->
     let (code, rvalue) = loc2rvalue l in
     (Mach.cpost code [Mach.MOVE (Mach.LREG Mach.tr, rvalue)], Mach.REFREG (Mach.tr, i))

(*
 * helper functions for debugging
 *)
(* val loc2str : loc -> string *)
let rec loc2str l = match l with 
    L_INT i -> "INT " ^ (string_of_int i)
  | L_BOOL b -> "BOOL " ^ (string_of_bool b)
  | L_UNIT -> "UNIT"
  | L_STR s -> "STR " ^ s
  | L_ADDR (Mach.CADDR a) -> "ADDR " ^ ("&" ^ a)
  | L_ADDR (Mach.HADDR a) -> "ADDR " ^ ("&Heap_" ^ (string_of_int a))
  | L_ADDR (Mach.SADDR a) -> "ADDR " ^ ("&Stack_" ^ (string_of_int a))
  | L_REG r -> 
     if r = Mach.sp then "REG SP"
     else if r = Mach.bp then "REG BP"
     else if r = Mach.cp then "REG CP"
     else if r = Mach.ax then "REG AX"
     else if r = Mach.bx then "REG BX"
     else if r = Mach.tr then "REG TR"
     else if r = Mach.zr then "REG ZR"
     else "R[" ^ (string_of_int r) ^ "]"
  | L_DREF (l, i) -> "DREF(" ^ (loc2str l) ^ ", " ^ (string_of_int i) ^ ")"

(* val loc2rvalue : loc -> Mach.code * rvalue *)
let rec rvalue2loc r =
  match r with
  | INT i -> L_INT i
  | BOOL b -> L_BOOL b
  | UNIT -> L_UNIT
  | STR s -> L_STR s
  | ADDR a -> L_ADDR a
  | REG r -> L_REG r
  | REFADDR (a, i) -> L_DREF (L_ADDR a, i)
  | REFREG (r, i) -> L_DREF (L_REG r, i)

(*
 * Generate code for Abstract Machine MACH 
 *)
(* pat2code : Mach.label -> Mach.label -> loc -> Mono.pat -> Mach.code * venv *)

let fail_label = labelNewStr ""

let find_free_vars expty =
  let rec find_bound_vars_in_patty patty bound_vars = (
    match patty with
      PATTY (P_VID (avid, VAR), _) -> avid :: bound_vars
    | PATTY (P_VIDP ((_, CONF), patty'), _) -> find_bound_vars_in_patty patty' bound_vars
    | PATTY (P_PAIR (patty1, patty2), _) -> find_bound_vars_in_patty patty1 (find_bound_vars_in_patty patty2 bound_vars)
    | _ -> bound_vars
  ) in
  let rec find_free_vars_in_expty expty bound_vars free_vars = (
    let exists x vars = List.exists (fun elem -> elem = x) vars
    in
      match expty with
        EXPTY (E_VID (avid, VAR), _) -> if (exists avid bound_vars) || (exists avid free_vars) then free_vars else avid :: free_vars
      | EXPTY (E_FUN mlist, _) -> List.fold_left (fun acc (M_RULE (patty, expty)) ->
          let bound_vars' = find_bound_vars_in_patty patty bound_vars
          in
            find_free_vars_in_expty expty bound_vars' acc
        ) free_vars mlist
      | EXPTY (E_APP (expty1, expty2), _) -> find_free_vars_in_expty expty2 bound_vars (find_free_vars_in_expty expty1 bound_vars free_vars)
      | EXPTY (E_PAIR (expty1, expty2), _) -> find_free_vars_in_expty expty2 bound_vars (find_free_vars_in_expty expty1 bound_vars free_vars)
      | EXPTY (E_LET (D_VAL (patty, expty1), expty2), _) -> (
          let bound_vars' = find_bound_vars_in_patty patty bound_vars in
          let free_vars' = find_free_vars_in_expty expty1 bound_vars' free_vars
          in
            find_free_vars_in_expty expty2 bound_vars' free_vars'
        )
      | EXPTY (E_LET (D_REC (patty, expty1), expty2), _) -> (
          let bound_vars' = find_bound_vars_in_patty patty bound_vars in
          let free_vars' = find_free_vars_in_expty expty1 bound_vars' free_vars
          in
            find_free_vars_in_expty expty2 bound_vars' free_vars'
        )
      | _ -> free_vars
  )
  in
    find_free_vars_in_expty expty [] []

let find_constructors (dlist, et) =
  let rec find_constructors_in_expty constructors (EXPTY (exp, _)) = (
    let (cons, confs) = constructors
    in
      match exp with
        E_VID (avid, CON) -> (
          if (List.exists (fun elem -> elem = avid) cons)
          then (cons, confs)
          else (avid :: cons, confs)
        )
      | E_VID (avid, CONF) -> (
          if (List.exists (fun elem -> elem = avid) confs)
          then (cons, confs)
          else (cons, avid :: confs)
        )
      | E_FUN mlist -> (
          List.fold_left (fun constructors_acc (M_RULE (_, expty)) -> find_constructors_in_expty constructors_acc expty) constructors mlist
        )
      | E_APP (expty1, expty2) -> find_constructors_in_expty (find_constructors_in_expty constructors expty1) expty2
      | E_PAIR (expty1, expty2) -> find_constructors_in_expty (find_constructors_in_expty constructors expty1) expty2
      | E_LET (dec, expty) -> find_constructors_in_expty (find_constructors_in_dec constructors dec) expty
      | _ -> constructors
  )
  and find_constructors_in_dec constructors dec = (
    match dec with
      D_VAL (_, expty) -> find_constructors_in_expty constructors expty
    | D_REC (_, expty) -> find_constructors_in_expty constructors expty
    | _ -> constructors
  )
  in
    List.fold_left (fun constructors_acc dec -> find_constructors_in_dec constructors_acc dec) (find_constructors_in_expty ([], []) et) dlist

(*  -> code * env *)
let create_datatype_closures (dlist, et) =
  let create_con_closure (code, (venv, count)) con = (
    let code' = clist [
      MALLOC (LREG cx, INT 1);
      MOVE (LREFREG (cx, 0), STR con);
      PUSH (REG cx);
    ]
    in
      (code @@ code', (Dict.insert (con, L_DREF (L_REG bx, count)) venv, count + 1))
  ) in
  let create_conf_closure (code, (venv, count)) conf = (
    let label_start = labelNewStr ("_DT_" ^ conf ^ "_START") in
    let label_end = labelNewStr ("_DT_" ^ conf ^ "_END") in
    let code' = clist [
      DEBUG conf;
      JUMP (ADDR (CADDR label_end));
      LABEL label_start;
      MALLOC (LREG cx, INT 2);
      MOVE (LREFREG (cx, 0), STR conf);
      MOVE (LREFREG (cx, 1), REFREG (bp, -3));
      MOVE (LREG ax, REG cx);
      RETURN;
      LABEL label_end;
      MALLOC (LREG cx, INT 1);
      MOVE (LREFREG (cx, 0), ADDR (CADDR label_start));
      PUSH (REG cx);
    ]
    in
      (code @@ code', (Dict.insert (conf, L_DREF (L_REG bx, count)) venv, count + 1))
  ) in
  let (cons, confs) = find_constructors (dlist, et) in
  let (code1, env1) = List.fold_left create_con_closure (code0, (venv0, 0)) cons
  in
    List.fold_left create_conf_closure (code1, env1) confs

let count_closures (dlist, et) =
  let rec count_global_closures count dec = (
    match dec with
      D_VAL (PATTY (P_PAIR (patty1, patty2), _), EXPTY (E_PAIR (expty1, expty2), _)) ->
        count_global_closures (count_global_closures count (D_VAL (patty1, expty1))) (D_VAL (patty2, expty2))
    | D_VAL (_, EXPTY (E_FUN _, _)) -> count + 1
    | D_VAL (_, EXPTY (E_APP (EXPTY (E_VID (avid, CONF), _), _), _)) -> count + 1
    | D_VAL (_, EXPTY (E_PAIR _, _)) -> count + 1
    | D_REC (_, EXPTY (E_FUN _, _)) -> count + 1
    | _ -> count
  ) in
  let rec count_local_closures_in_expty count (EXPTY (exp, _)) = (
    match exp with
    | E_FUN mlist -> (
        List.fold_left (fun count_acc (M_RULE (_, expty)) ->
          let count_mrule = count_local_closures_in_expty count expty
          in
            if count_mrule > count_acc then count_mrule else count_acc
          ) count mlist
      )
    | E_APP (expty1, expty2) -> (
        let count1 = count_local_closures_in_expty count expty1 in
        let count2 = count_local_closures_in_expty count expty2
        in
          if count1 > count2 then count1 else count2
      )
    | E_PAIR (expty1, expty2) -> (
        let count1 = count_local_closures_in_expty count expty1 in
        let count2 = count_local_closures_in_expty count expty2
        in
          if count1 > count2 then count1 else count2
      )
    | E_LET (dec, expty) -> (
        let count1 = count_global_closures count dec
        in
          count_local_closures_in_expty count1 expty
      )
    | _ -> count
  ) in
  let count_local_closures_in_dec count dec = (
    match dec with
      D_VAL (PATTY (P_PAIR (patty1, patty2), _), EXPTY (E_PAIR (expty1, expty2), _)) -> (
        let count1 = count_local_closures_in_expty count expty1 in
        let count2 = count_local_closures_in_expty count expty2
        in
          count1 + count2
      )
    | D_VAL (_, expty) -> count_local_closures_in_expty count expty
    | D_REC (_, expty) -> count_local_closures_in_expty count expty
    | _ -> count
  ) in
  (* let (cons, confs) = find_constructors (dlist, et) in *)
  let count_global = List.fold_left count_global_closures 0 dlist in
  let count_local = List.fold_left (fun count_acc dec -> 
      let count_dec = count_local_closures_in_dec 0 dec
      in
        if count_dec > count_acc then count_dec else count_acc
    ) (count_local_closures_in_expty 0 et) dlist
  in
    count_global + count_local

let rec create_closure_space code n =
  if n = 0 then code
  else create_closure_space (cpost code [PUSH (INT 0)]) (n - 1)

(* pat2code : Mach.label -> Mach.label - > loc -> Mono.pat -> Mach.code * env *)
let rec pat2code saddr faddr l pat count = match pat with
    P_WILD -> (cpre [LABEL saddr] code0, (venv0, 0))
  | P_INT n -> (
      let (code, rvalue) = loc2rvalue l in
      let code' = cpost code [JMPNEQ (ADDR (CADDR faddr), rvalue, INT n)]
      in
        (cpre [LABEL saddr] code', (venv0, 0))
    )
  | P_BOOL true -> (
      let (code, rvalue) = loc2rvalue l in
      let label_true = labelNewLabel saddr "_TRUE" in
      let code' = cpost code [
        JMPTRUE (ADDR (CADDR label_true), rvalue);
        JUMP (ADDR (CADDR faddr));
        LABEL label_true;
      ]
      in
        (cpre [LABEL saddr] (code @@ code'), (venv0, 0))
    )
  | P_BOOL false -> (
      let (code, rvalue) = loc2rvalue l in
      let code' = cpost code [JMPTRUE (ADDR (CADDR faddr), rvalue)]
      in
        (cpre [LABEL saddr] (code @@ code'), (venv0, 0))
    )
  | P_VID (avid, VAR) -> (
      let (code, rvalue) = loc2rvalue l
      in
        match l with
          L_REG cx -> (  (* when variable is pointing a closure *)
            let code' = [MOVE (LREFREG (bx, count), REG cx)] in
            let venv' = Dict.insert (avid, L_DREF (L_REG bx, count)) venv0
            in
              (cpre [LABEL saddr] (code @@ code'), (venv', 1))
          )
        | _ -> (
            let venv' = Dict.insert (avid, l) venv0
            in
              (cpre [LABEL saddr] code, (venv', 0))
          )
    )
  | P_VID (avid, CON) -> (
      let (code, rvalue) = loc2rvalue l in
      let code_post = clist [MOVE (LREG ax, rvalue); JMPNEQSTR (ADDR (CADDR faddr), REFREG (ax, 0), STR avid)]
      in
        (cpre [LABEL saddr] (code @@ code_post), (venv0, 0))
    )
  | P_VIDP ((avid, CONF), patty) -> (
      let (code, rvalue) = loc2rvalue l in
      let code_mid = clist [MOVE (LREG ax, rvalue); JMPNEQSTR (ADDR (CADDR faddr), REFREG (ax, 0), STR avid)] in
      let (code2, (venv2, count2)) = patty2code (labelNewLabel saddr "_DATA") faddr (L_DREF (l, 1)) patty count
      in
        (cpre [LABEL saddr] (code @@ code_mid @@ code2), (venv2, count + count2)) 
    )
  | P_PAIR (patty1, patty2) -> (
      let (code, rvalue) = loc2rvalue l in
      let (code1, (venv1, count1)) = patty2code (labelNewLabel saddr "_FST") faddr (L_DREF (l, 0)) patty1 count in
      let (code2, (venv2, count2)) = patty2code (labelNewLabel saddr "_SND") faddr (L_DREF (l, 1)) patty2 (count + count1)
      in
        (cpre [LABEL saddr; DEBUG ("pair - " ^ loc2str l)] (code @@ code1 @@ code2), (Dict.merge venv1 venv2, count + count1 + count2))
    )
  | _ -> (cpre [LABEL saddr] code0, (venv0, 0))

(* patty2code : Mach.label -> Mach.label -> loc -> Mono.patty -> Mach.code * venv *)
and patty2code saddr faddr l patty count =
  let PATTY (pat, _) = patty
  in
    pat2code saddr faddr l pat count

(* exp2code : env -> Mach.label -> Mono.exp -> Mach.code * Mach.rvalue *)
and exp2code environ saddr exp =
  let (venviron, count) = environ in
  match exp with
      E_INT n -> (code0, INT n)
    | E_BOOL b -> (code0, BOOL b)
    | E_UNIT -> (code0, UNIT)
    | E_VID (avid, VAR) -> (
        match Dict.lookup avid venviron with
          None -> (clist [DEBUG (avid ^ " missing"); EXCEPTION], INT (-1))
        | Some l ->
            let (code, rvalue) = loc2rvalue l
            in
              (code, rvalue)
      )
    | E_VID (avid, CON) -> (
        match Dict.lookup avid venviron with
          None -> (clist [DEBUG (avid ^ " missing(conf)"); EXCEPTION], INT (-1))
        | Some l ->
            let (code, rvalue) = loc2rvalue l
            in
              (code, rvalue)
        (* let code = clist [
          MALLOC (LREG cx, INT 1);
          MOVE (LREFREG (cx, 0), STR avid);
        ]
        in
          (code, REG cx) *)
      )
    | E_VID (avid, CONF) -> (
        match Dict.lookup avid venviron with
          None -> (clist [DEBUG (avid ^ " missing(conf)"); EXCEPTION], INT (-1))
        | Some l ->
            let (code, rvalue) = loc2rvalue l
            in
              (code, rvalue)
      )
    | E_PAIR (expty1, expty2) -> (
        let label_start1 = labelNewLabel saddr "_1" in
        let label_start2 = labelNewLabel saddr "_2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2 in
        let code_mid = clist [PUSH rvalue1] in
        let code_post = clist [
          PUSH rvalue2;
          MALLOC (LREG cx, INT 2);
          MOVE (LREFREG (cx, 0), REFREG (sp, -2));
          MOVE (LREFREG (cx, 1), REFREG (sp, -1));
          POP (LREG tr);
          POP (LREG tr);]
        in
          (code1 @@ code_mid @@ code2 @@ code_post, REG cx)
      )
    | E_LET (dec, expty) -> (
        let label_start1 = labelNewLabel saddr "_LETDEC" in
        let label_start2 = labelNewLabel saddr "_LETEXPTY" in
        let (code1, environ1) = dec2code environ label_start1 dec in
        let (code2, rvalue) = expty2code environ1 label_start2 expty
        in
          (code1 @@ code2, rvalue)
      )
    | _ -> (code0, INT (-1))

(* expty2code : env -> Mach.label -> Mono.expty -> Mach.code * Mach.rvalue *)
and expty2code environ saddr expty =
  let (venviron, count) = environ
  in
    match expty with
      EXPTY (E_FUN mlist, _) -> (
        (* create labels *)
        let label_start = labelNewLabel saddr "_START" in
        let label_end = labelNewLabel saddr "_END" in
        (* get free variables *)
        let free_vars = find_free_vars expty in
        let (code_free_vars, venv_free_vars, count_free_vars) = (List.fold_left (fun (code_acc, venv_acc, index) free_var ->
          let (code_free_var, venv_free_var) =
            match Dict.lookup free_var venv_acc with
              None -> ([DEBUG (free_var ^ " missing"); EXCEPTION], venv_acc)
            | Some l ->
                let (code, rvalue) = loc2rvalue l
                in ([MOVE (LREFREG(cx, index + 1), rvalue)], Dict.insert (free_var, L_DREF (L_REG cp, index + 1)) venv_acc)
          in (cpost code_acc code_free_var, venv_free_var, index + 1)
        ) (code0, venviron, 0) free_vars) in
        (* create codes *)
        let (code_mlist, faddr_mlist) = List.fold_left (fun (code_acc, saddr_acc) mrule ->
          let faddr = labelNewLabel saddr "_CASE" in
          let code_mrule = mrule2code (venv_free_vars, count) saddr_acc faddr mrule
          in
            (code_acc @@ code_mrule, faddr)
        ) (code0, labelNewLabel saddr "_CASE") mlist in
        let code_pre = clist [
          JUMP (ADDR (CADDR label_end));
          LABEL label_start;
          DEBUG ("free vars - " ^ List.fold_left (fun acc elem -> acc ^", "^ elem) "" free_vars)
        ] in
        let code_post = cpre [
          LABEL faddr_mlist; EXCEPTION;
          LABEL label_end;
          MALLOC (LREG cx, INT ((List.length free_vars) + 1));
          MOVE (LREFREG (cx, 0), ADDR (CADDR label_start));
        ] code_free_vars
        in (code_pre @@ code_mlist @@ code_post, REG cx)
      )
    | EXPTY(E_APP (EXPTY (E_PLUS, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let label_start1 = labelNewLabel saddr "_1" in
        let label_start2 = labelNewLabel saddr "_2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2
        in
          match (rvalue1, rvalue2) with
            (INT n, INT m) -> (code1 @@ code2, INT (n + m))
          | (INT n, _) -> (cpost (code1 @@ code2) [ADD (LREG ax, INT n, rvalue2)], REG ax)
          | (_, INT m) -> (cpost (code1 @@ code2) [ADD (LREG ax, rvalue1, INT m)], REG ax)
          | _ -> (cpost (code1 @@ (clist [PUSH rvalue1]) @@ code2) [ADD (LREG ax, REFREG (sp, -1), rvalue2); POP (LREG tr)], REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_MINUS, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let label_start1 = labelNewLabel saddr "_1" in
        let label_start2 = labelNewLabel saddr "_2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2
        in
          match (rvalue1, rvalue2) with
            (INT n, INT m) -> (code1 @@ code2, INT (n - m))
          | (INT n, _) -> (cpost (code1 @@ code2) [SUB (LREG ax, INT n, rvalue2)], REG ax)
          | (_, INT m) -> (cpost (code1 @@ code2) [SUB (LREG ax, rvalue1, INT m)], REG ax)
          | _ -> (cpost (code1 @@ (clist [PUSH rvalue1]) @@ code2) [SUB (LREG ax, REFREG (sp, -1), rvalue2); POP (LREG tr)], REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_MULT, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let label_start1 = labelNewLabel saddr "_1" in
        let label_start2 = labelNewLabel saddr "_2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2
        in
          match (rvalue1, rvalue2) with
            (INT n, INT m) -> (code1 @@ code2, INT (n * m))
          | (INT n, _) -> (cpost (code1 @@ code2) [MUL (LREG ax, INT n, rvalue2)], REG ax)
          | (_, INT m) -> (cpost (code1 @@ code2) [MUL (LREG ax, rvalue1, INT m)], REG ax)
          | _ -> (cpost (code1 @@ (clist [PUSH rvalue1]) @@ code2) [MUL (LREG ax, REFREG (sp, -1), rvalue2); POP (LREG tr)], REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_EQ, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let label_start1 = labelNewLabel saddr "_1" in
        let label_start2 = labelNewLabel saddr "_2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2 in
        let label_neq = labelNewLabel saddr "_NEQ" in
        let label_final = labelNewLabel saddr "_FINAL"
        in
          match (rvalue1, rvalue2) with
            (INT n, INT m) -> (code1 @@ code2, if n = m then BOOL true else BOOL false)
          | (INT n, _) -> (cpost (code1 @@ code2) [
              JMPNEQ (ADDR (CADDR label_neq), INT n, rvalue2);
              MOVE (LREG ax, BOOL true);
              JUMP (ADDR (CADDR label_final));
              LABEL label_neq;
              MOVE (LREG ax, BOOL false);
              LABEL label_final;
            ], REG ax)
          | (_, INT m) -> (cpost (code1 @@ code2) [
              JMPNEQ (ADDR (CADDR label_neq), rvalue1, INT m);
              MOVE (LREG ax, BOOL true);
              JUMP (ADDR (CADDR label_final));
              LABEL label_neq;
              MOVE (LREG ax, BOOL false);
              LABEL label_final;
            ], REG ax)
          | _ -> (cpost (code1 @@ (clist [PUSH rvalue1]) @@ code2) [
              JMPNEQ (ADDR (CADDR label_neq), REFREG (sp, -1), rvalue2);
              MOVE (LREG ax, BOOL true);
              JUMP (ADDR (CADDR label_final));
              LABEL label_neq;
              MOVE (LREG ax, BOOL false);
              LABEL label_final;
              POP (LREG tr);
            ], REG ax)
      )
    | EXPTY(E_APP (EXPTY (E_NEQ, _), EXPTY (E_PAIR (expty1, expty2), _)), _) -> (
        let label_start1 = labelNewLabel saddr "_1" in
        let label_start2 = labelNewLabel saddr "_2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2 in
        let label_neq = labelNewLabel saddr "_NEQ" in
        let label_final = labelNewLabel saddr "_FINAL"
        in
          match (rvalue1, rvalue2) with
            (INT n, INT m) -> (code1 @@ code2, if n = m then BOOL false else BOOL true)
          | (INT n, _) -> (cpost (code1 @@ code2) [
              JMPNEQ (ADDR (CADDR label_neq), INT n, rvalue2);
              MOVE (LREG ax, BOOL false);
              JUMP (ADDR (CADDR label_final));
              LABEL label_neq;
              MOVE (LREG ax, BOOL true);
              LABEL label_final;
            ], REG ax)
          | (_, INT m) -> (cpost (code1 @@ code2) [
              JMPNEQ (ADDR (CADDR label_neq), rvalue1, INT m);
              MOVE (LREG ax, BOOL false);
              JUMP (ADDR (CADDR label_final));
              LABEL label_neq;
              MOVE (LREG ax, BOOL true);
              LABEL label_final;
            ], REG ax)
          | _ -> (cpost (code1 @@ (clist [PUSH rvalue1]) @@ code2) [
              JMPNEQ (ADDR (CADDR label_neq), REFREG (sp, -1), rvalue2);
              MOVE (LREG ax, BOOL false);
              JUMP (ADDR (CADDR label_final));
              LABEL label_neq;
              MOVE (LREG ax, BOOL true);
              LABEL label_final;
              POP (LREG tr);
            ], REG ax)
      )
    | EXPTY (E_APP (expty1, expty2), _) -> (
        let label_start1 = labelNewLabel saddr "_START1" in
        let label_start2 = labelNewLabel saddr "_START2" in
        let (code1, rvalue1) = expty2code environ label_start1 expty1 in
        let (code2, rvalue2) = expty2code environ label_start2 expty2 in
        let code_post = 
          (* match rvalue1 with
            REFREG (bx, 1) -> clist [
          PUSH (REG cp);
          PUSH rvalue2;
          MOVE (LREG cp, REFREG (sp, -3));
          HALT (REG cp);
          POP (LREG tr);
          POP (LREG cp);
          POP (LREG tr);
        ]
          | _ -> *)
          clist [
          PUSH (REG cp);
          PUSH rvalue2;
          MOVE (LREG cp, REFREG (sp, -3));
          CALL (REFREG (cp, 0));
          POP (LREG tr);
          POP (LREG cp);
          POP (LREG tr);
        ]
        in
          (code1 @@ (clist [PUSH rvalue1]) @@ code2 @@ code_post, REG ax)
      )
    | _ -> (
        let EXPTY (exp, ty) = expty
        in
          exp2code environ saddr exp
      )

(* dec2code : env -> Mach.label -> Mono.dec -> Mach.code * env *)
and dec2code environ saddr dec =
  let (venv, count) = environ
  in
    match dec with
      D_VAL (PATTY (P_PAIR (patty1, patty2), _), EXPTY (E_PAIR (expty1, expty2), _)) ->
        let (code1, env1) = dec2code environ (labelNewLabel saddr "DECVALPAIR1_") (D_VAL (patty1, expty1)) in
        let (code2, env2) = dec2code env1 (labelNewLabel saddr "DECVALPAIR2_") (D_VAL (patty2, expty2))
        in
          (code1 @@ code2, env2)
    | D_VAL (patty, expty) ->
        let (code1, rvalue) = expty2code environ (labelNewLabel saddr "DECVALPAT_") expty in
        let (code2, (venv2, count2)) = patty2code (labelNewLabel saddr "DECVALEXP_") fail_label (rvalue2loc rvalue) patty count
        in
          (code1 @@ code2, (Dict.merge venv venv2, count + count2))
    | D_REC (PATTY (P_VID (avid, VAR), ty), expty) ->
        let (code2, (venv2, count2)) = patty2code (labelNewLabel saddr "DECRECPAT_") fail_label (L_REG cx) (PATTY (P_VID (avid, VAR), ty)) count in
        let environ' = Dict.merge venv venv2, count + count2 in
        let (code1, rvalue) = expty2code environ' (labelNewLabel saddr "DECRECEXP_") expty in
        let free_vars = List.mapi (fun i free_var -> (i, free_var)) (find_free_vars expty) in
        let (index, _) = List.find (fun (i, free_var) -> avid = free_var) free_vars in
        let code_post = [MOVE (LREFREG (cx, index + 1), REG cx)]
        in
          (code1 @@ code2 @@ code_post, environ')
    | _ -> (code0, environ)

(* mrule2code : env -> Mach.label -> Mach.label -> Mono.mrule -> Mach.code *)
and mrule2code environ saddr faddr (M_RULE (patty, expty)) =
  let (venv, count) = environ in
  let saddr' = labelNewLabel saddr "_EXPTY" in
  let (code1, (venv1, count1)) = patty2code saddr faddr (L_DREF (L_REG bp, -3)) patty count in
  let environ' = (Dict.merge venv venv1, count + count1) in
  let (code2, rvalue) = expty2code environ' saddr' expty in
  let code_post = clist [MOVE (LREG ax, rvalue); RETURN;]
  in
    code1 @@ code2 @@ code_post


(* program2code : Mono.program -> Mach.code *)
let program2code (dlist, et) =
  let (code1, environ1) = create_datatype_closures (dlist, et) in
  let closure_count = count_closures (dlist, et) in
  let code2 = create_closure_space code0 closure_count in
  let (code3, environ3) = List.fold_left (
    fun (code_acc, environ_acc) dec ->
      let (code_dec, environ_dec) = dec2code environ_acc (labelNewStr "PRDEC_") dec
      in
        (code_acc @@ code_dec, environ_dec)
  ) (code0, environ1) dlist in
  let (code4, rvalue) = expty2code environ3 (labelNewStr "PREXP_") et
  in 
  let (venv1, count1) = environ1 in
    [LABEL start_label; MOVE (LREG bx, REG sp)] @@ code1 @@ code2 @@ code3 @@ code4 @@ [HALT rvalue; LABEL fail_label; EXCEPTION]