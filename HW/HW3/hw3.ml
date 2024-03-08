open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y = x || y
  let ( ** ) x y = x && y
  let (==) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create (l: elem list): t = l
  let to_list (v: t): elem list = v
  let dim (v: t) = List.length v
  let nth (v: t) (n: int): elem = 
    if n >= (dim v) then raise VectorIllegal 
    else List.nth v n

  let (++) (v1: t) (v2: t): t = 
    if dim v1 <> dim v2 then raise VectorIllegal
    else List.map2 (fun x y -> Scal.(++) x y) v1 v2

  let (==) (v1: t) (v2: t): bool =
    if dim v1 <> dim v2 then raise VectorIllegal
    else List.fold_left (fun x y -> x && y) true (List.map2 (fun x y -> Scal.(==) x y) v1 v2) 
  
  let innerp (v1: t) (v2: t): elem =
    if dim v1 <> dim v2 then raise VectorIllegal
    else List.fold_left (fun x y -> Scal.(++) x y) Scal.zero (List.map2 (fun x y -> Scal.( ** ) x y) v1 v2)
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list list

  exception MatrixIllegal

  let create (l: elem list list): t = 
    match l with
    | [[]] -> raise MatrixIllegal
    | _ -> 
      if List.for_all (fun x -> x = List.length l) (List.map List.length l) then l
      else raise MatrixIllegal

  let identity (n: int): t = 
    if n <= 0 then raise MatrixIllegal
    else
      let rec row_eye (n: int) (c: int) (length: int) (acc: elem list): elem list = 
        if length = c then acc
        else row_eye (n) (c + 1) (length) (acc @ [if c = n then Scal.one else Scal.zero])
      in
      let rec mat_construct (n: int) (length: int) (acc: elem list list): elem list list = 
        if length = n then acc
        else mat_construct (n + 1) (length) (acc @ [row_eye (n) (0) (length) ([])])
      in mat_construct (0) (n) ([])

  let dim (m: t): int = List.length m
  let rec transpose (m: t): t = 
    match m with
    | []::_ -> []
    | r -> [List.map (List.hd) (r)] @ transpose (List.map (List.tl) (r))


  let to_list (m: t): elem list list = m
  let get (m: t) (r: int) (c: int) = 
    if List.length m <= r || List.length (List.hd m) <= c then raise MatrixIllegal
    else List.nth (List.nth m r) c

  let (++) (m1: t) (m2: t): t = 
    if dim (m1) <> dim (m2) then raise MatrixIllegal
    else List.map2 (fun v1 v2 -> List.map2 Scal.(++) v1 v2) (m1) (m2)

  let ( ** ) (m1: t) (m2: t): t = 
    if dim (m1) <> dim (m2) then raise MatrixIllegal
    else
      let multiply_row_col (r) (c) =
        List.fold_left (Scal.(++)) (Scal.zero) (List.map2 (Scal.( ** )) (r) (c))
      in
      List.map (fun r -> List.map (fun c -> multiply_row_col r c) (transpose m2)) (m1)

  let (==) (m1: t) (m2: t): bool =
    if dim (m1) <> dim (m2) then raise MatrixIllegal
    else List.fold_left (fun x y -> x && y) true (List.map2 (fun v1 v2 -> List.fold_left (fun x y -> x && y) true (List.map2 Scal.(==) v1 v2)) (m1) (m2)) 
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure (mat: Mat.t): Mat.t =
    let ident =
      Mat.identity (Mat.dim mat)
    in
    let rec rec_closure (cur_closure: Mat.t): Mat.t = 
      if Mat.(cur_closure == (ident ++ (cur_closure ** mat))) then cur_closure
      else rec_closure Mat.(ident ++ (cur_closure ** mat))
    in
    rec_closure ident
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach (l: bool list list): bool list list = 
  let module ReachMat = MatrixFn(Boolean) in
  let module ReachCls = ClosureFn(ReachMat) in
  let mat_dist = ReachMat.create l in
  ReachMat.to_list (ReachCls.closure mat_dist) 

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = -1             (* Dummy value : Rewrite it! *)
  let one = 0               (* Dummy value : Rewrite it! *)

  let (++) (x: t) (y: t): t =
    if x = zero then y
    else if y = zero then x
    else if x < y then x else y

  let ( ** ) (x: t) (y: t): t =
    if x = zero || y = zero then zero
    else x + y

  let (==) (x: t) (y: t) = x = y
end

(* .. Write some code here .. *)

let distance (l: int list list): int list list = 
  let module DistMat = MatrixFn(Distance) in
  let module DistCls = ClosureFn(DistMat) in
  let mat_dist = DistMat.create l in
  DistMat.to_list (DistCls.closure mat_dist)

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0             (* Dummy value : Rewrite it! *)
  let one = -1              (* Dummy value : Rewrite it! *)
 
  let (++) (x: t) (y: t): t =
    if x = one || y = one then one
    else if x > y then x else y

  let ( ** ) (x: t) (y: t): t =
    if x = one then y
    else if y = one then x
    else if x < y then x else y

  let (==) (x: t) (y: t) = x = y
end

(* .. Write some code here .. *)

let weight (l: int list list): int list list =  
  let module WeightMat = MatrixFn(Weight) in
  let module WeightCls = ClosureFn(WeightMat) in
  let mat_dist = WeightMat.create l in
  WeightMat.to_list (WeightCls.closure mat_dist)

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

