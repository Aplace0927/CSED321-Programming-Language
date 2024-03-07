exception NotImplemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lrevrev (l: 'a list list): 'a list list = 
  match l with
  | [] -> []
  | fd::bk -> 
    let rec lrev (ll: 'a list): 'a list = 
      match ll with
      | [] -> []
      | f::b -> lrev b @ [f]
    in lrevrev bk @ [lrev fd]
;;

let rec lfoldl (f: 'a * 'b -> 'b) (e: 'b) (l: 'a list): 'b =
  match l with
  | [] -> e
  | fd::bk -> lfoldl f (f (fd, e)) bk
;;
			 
(** Tail recursive functions  **)

let fact (n: int): int = 
  let rec fact_tail (acc: int) (n: int): int =
    if n = 0
      then acc
    else
      fact_tail (acc * n) (n-1)
  in fact_tail 1 n
;;

let fib (n: int): int = 
  if n <= 1 then 1
  else
    let rec fib_tail (acc_prevprev: int) (acc_prev: int) (remain: int): int =
      if remain == 0 then acc_prevprev + acc_prev
      else
        fib_tail (acc_prev) (acc_prevprev + acc_prev) (remain - 1)
    in fib_tail 1 1 (n-2)
  ;;

let alterSum (l: int list): int =
  let rec alter_tail (acc: int) (remain: int list) (add: bool): int = 
    match remain with
    | [] -> acc
    | f::b -> alter_tail (if add then acc + f else acc - f) (b) (not add)
  in alter_tail 0 l true
;;

let ltabulate (n: int) (f: int -> 'a): 'a list = 
  let rec ltabulate_tail (k: int) (f: int -> 'a) (acc: 'a list): 'a list = 
    if k = n then acc
    else ltabulate_tail (k+1) (f) (acc @ [f k])
  in ltabulate_tail 0 f []
;;

let lfilter (f: 'a -> bool) (l: 'a list): 'a list = 
  let rec lfilter_tail (f: 'a -> bool) (rem: 'a list) (acc: 'a list): 'a list = 
    match rem with
    | [] -> acc
    | fd::bk -> lfilter_tail f bk (if (f fd) then acc @ [fd] else acc)
  in lfilter_tail f l []
;;


let rec union (s: 'a list) (t: 'a list): 'a list = 
  match s with
  | [] -> t
  | fd::bk -> 
    let rec has_elem (elem: 'a) (l: 'list) (has: bool): bool = 
      match l with
      | [] -> has
      | f::b -> has_elem elem b (has || (f = elem))
    in union (bk) (if has_elem fd t false = true then t else [fd] @ t)
;;

let inorder (t: 'a tree): 'a list = 
  let rec inorder_save_traverse (tl: 'a tree list) (trav: 'a list): 'a list = 
    match tl with
    | [] -> trav
    | fd::bk ->
      match fd with
      | Leaf x -> inorder_save_traverse (bk) (trav @ [x])
      | Node (l, v, r) -> inorder_save_traverse ([l] @ [Leaf v] @ [r] @ bk) (trav)
  in inorder_save_traverse [t] []
;;

let postorder (t: 'a tree): 'a list =
  let rec postorder_save_traverse (tl: 'a tree list) (trav: 'a list): 'a list = 
    match tl with
    | [] -> trav
    | fd::bk ->
      match fd with
      | Leaf x -> postorder_save_traverse (bk) (trav @ [x])
      | Node (l, v, r) -> postorder_save_traverse ([l] @ [r] @ [Leaf v] @ bk) (trav)
  in postorder_save_traverse [t] []
;;

let preorder (t: 'a tree): 'a list =
  let rec preorder_save_traverse (tl: 'a tree list) (trav: 'a list): 'a list = 
    match tl with
    | [] -> trav
    | fd::bk ->
      match fd with
      | Leaf x -> preorder_save_traverse (bk) (trav @ [x])
      | Node (l, v, r) -> preorder_save_traverse ([Leaf v] @ [l] @ [r] @ bk) (trav)
  in preorder_save_traverse [t] []
;;


(** Sorting in the ascending order **)

let rec quicksort (l: 'a list): 'a list = 
  match l with
  | [] -> []
  | piv::other -> (quicksort (lfilter (fun x -> x <= piv) other)) @ [piv] @ (quicksort (lfilter (fun x -> x > piv) other))
;;

let rec mergesort (l: 'a list): 'a list =
  match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let rec concat_ordered (l: 'a list) (r: 'a list) (con: 'a list): 'a list = 
      match (l, r) with
      | ([], _) -> con @ r
      | (_, []) -> con @ l 
      | (fl::bl, fr::br) -> if fl < fr then concat_ordered (bl) (r) (con @ [fl]) else concat_ordered (l) (br) (con @ [fr])
    in
    let (fd, bk) = 
      let rec split_list (l: 'a list) (acc_1: 'a list) (acc_2: 'a list): ('a list * 'a list) = 
        match l with
        | [] -> (acc_1, acc_2)
        | [x] -> (acc_1 @ [x], acc_2)
        | f::b::other -> split_list (other) (acc_1 @ [f]) (acc_2 @ [b])
      in split_list l [] []
    in concat_ordered (mergesort fd) (mergesort bk) []
  ;;
    
			
(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = int      (* dummy type, to be chosen by students *) 
    type 'a heap = 'a list    (* dummy type, to be chosen by students *)

    let empty () : 'a heap = []
    let allocate (h: 'a heap) (v: 'a): ('a heap * loc) =
      let updated_heap = List.append h [v] in 
        (updated_heap, (List.length updated_heap) - 1)
    
    let dereference (h: 'a heap) (l: loc): 'a = 
      if (0 <= l && l < List.length (h)) then
        List.nth h l
      else
        raise InvalidLocation
    
    let update (h: 'a heap) (l: loc) (v: 'a): 'a heap =
      if (0 <= l && l < List.length (h)) then
        List.mapi (fun idx value -> if idx = l then v else value) h
      else
        raise InvalidLocation
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list

    let empty () : 'a dict = [] 
    let lookup (d: 'a dict) (k: key): 'a option = 
      match List.find_opt (fun (ke, va) -> k = ke) d with
      | Some (ke, va) -> Some (va)
      | None -> None

    let delete (d: 'a dict) (k: key): 'a dict =
      List.filter (fun (ke, va: key * 'a) -> ke <> k) d
      
    let insert (d: 'a dict) (k, v: key * 'a): 'a dict =
      match List.find_opt (fun (ke, va) -> k = ke) d with
      | Some (ke) -> List.map (fun (ke, va) -> if ke = k then (k, v) else (k, va)) d
      | None -> List.append d [(k, v)]
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty (): 'a dict = (fun (k: key) -> None)
    let lookup (d: 'a dict) (k: key): 'a option = d k

    let delete (d: 'a dict) (k: key): 'a dict = fun (del_k: key) -> if del_k = k then None else (d k)
    let insert (d: 'a dict) (k, v: key * 'a): 'a dict = fun (new_k: key) -> if new_k = k then Some v else (d k)
  end
