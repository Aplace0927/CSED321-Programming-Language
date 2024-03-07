exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum x = if x <> 0 then x + sum (x-1) else 0;;
let rec power x n = if n <> 0 then x * power x (n-1) else 1;;
let rec gcd m n = if n <> 0 then gcd n (m mod n) else m;;
let rec combi n k = if n < k then 0 else if n = k || k = 0 then 1 else (combi (n-1) (k-1)) + (combi (n-1) (k));;

let rec sum_tree (t: int tree): int =
  match t with
    | Leaf v -> v
    | Node (l, v, r) -> (sum_tree l) + v + (sum_tree r)
;;

let rec depth (t: 'a tree): int = 
  match t with
    | Leaf _ -> 0
    | Node (l, v, r) -> if (depth l) >= (depth r) then (depth l) + 1 else (depth r) + 1
;;

let rec bin_search (t: 'a tree) (x: 'a): bool = 
  match t with
    | Leaf v -> (v = x)
    | Node (l, v, r) -> (bin_search l x) || (v = x) || (bin_search r x)
;;


let rec postorder (t: 'a tree): 'a list = 
  match t with
    | Leaf v -> [v]
    | Node (l, v, r) -> (postorder l) @ (postorder r) @ [v]
;;

let rec max (l: int list): int = 
  match l with
    | [] -> 0
    | [t] -> t
    | f::b -> if f > (max b) then f else (max b)
;;

let rec list_add (l1: int list) (l2: int list): int list = 
  match l1, l2 with
    | [], [] -> []
    | [], f2::b2 -> [f2] @ (list_add [] b2)
    | f1::b1, [] -> [f1] @ (list_add b1 [])
    | f1::b1, f2::b2 -> [f1 + f2] @ (list_add b1 b2)
;;

let rec insert (m: int) (l: int list): int list = 
  match l with
    | [] -> [m]
    | f::b -> if m < f then [m] @ l else f::(insert m b)
;;

let rec insort (l: int list): int list = 
  match l with
    | [] -> []
    | f::b -> (insert f (insort b))
;;

let rec compose f g = fun x -> g(f(x));;
let rec curry f a b = f (a, b);;
let rec uncurry f (a, b) = f a b;;
let rec multifun f n = fun x -> if n = 1 then f x else (multifun f (n-1)) (f x);;

let rec ltake (l: 'a list) (n: int): 'a list = 
  match l with
    | [] -> []
    | f::b -> if n > 0 then [f] @ ltake b (n-1) else []
;;

let rec lall (f: 'a -> bool) (l: 'a list): bool = 
  match l with
    | [] -> true
    | [x] -> f x
    | a::b -> (f a) && lall f b
;;

let rec lmap (f: 'a -> 'b) (l: 'a list): 'b list = 
  match l with
    | [] -> []
    | a::b -> [f a] @ lmap f b
;;

let rec lrev (l: 'a list): 'a list = 
  match l with
    | [] ->  []
    | f::b -> lrev b @ [f]

let rec lflat (l: 'a list list): 'a list =
  match l with
    | [] -> []
    | f::b -> f @ lflat b
;;

let rec lzip (x: 'a list) (y: 'b list): ('a * 'b) list = 
  match x, y with
  | fx::bx, fy::by -> [(fx, fy)] @ lzip bx by
  | _ -> []
;;

let rec split (x: 'a list): ('a list * 'a list) = 
  match x with
  | [] -> [], []
  | [a] -> [a], []
  | a::b::l -> let (a_l, b_l) = split l in (a::a_l , b::b_l)
;;

let rec cartprod (l1: 'a list) (l2: 'b list): ('a * 'b) list =
  match l1 with
  | [] -> []
  | f1::b1 -> 
    let rec combine (x: 'a) (l: 'b list) =
      match l with
      | [] -> []
      | f2::b2 -> [(f1, f2)] @ combine x b2
    in combine f1 l2 @ cartprod b1 l2
;;

let rec powerset (l: 'a list): ('a list list) = 
  match l with
  | [] -> []
  | [x] -> [[]; [x]]
  | f::b -> 
    let rec join (x: 'a list) (sub: 'a list list): 'a list list = 
      match sub with
      | [] -> [[]]
      | fr::br -> [fr @ x] @ join x br  
    in join [] (powerset b) @ join [f] (powerset b)
;;
