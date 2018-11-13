(* Assumptions variables and constants have height 0, and size 1 *)

module SS = Set.Make(String);;
type table = Table of (string, int) Hashtbl.t;;
(* add key value to a table t like add tab "a" 1 *)
let add (Table tab) key value = Hashtbl.add tab key value;;
(* find key value to a table t like find_key tab "a" *)
let find_key (Table t) key = Hashtbl.find t key;;
let has_key (Table t) key = Hashtbl.mem t key;;

(*let arity s = match s with
                "Const" ->  1
            |   "Plus"  ->  2
            |   "Sub"   ->  2
            |     _     -> -1;;
*)(*let arity s = match s with
     "X" -> 0
    |"Y" -> 0
    |"f" -> 1
    |"g" -> 2
    |"h" -> 3
    | _ -> 2;;*)
    
let sig_list = ["Const"; "Plus"; "Sub"];;

let rec check_arity s = match s with 
                        [] -> true
                    |  x::xs -> if (arity x) < 0 then false else check_arity xs;;
    
(* gives true if there is no repetiton*)
let rec check_no_repetition s table = match s with 
                        [] -> true
                    |  x::xs -> if (has_key table x) 
                                then false
                                else begin
                                    add table x (arity x);
                                    check_no_repetition xs table 
                                end ;;

(* Returns true if signature is valid else returns false - uses two helper functions *)
let check_sig s = if check_arity s then check_no_repetition s (Table (Hashtbl.create 1000)) else false;;

type variable = Var of string;;
type symbol = Sym of string;; 
type term = V of variable | Node of symbol*(term list);;

(* Returns true if a wfterm else false*)
let rec wfterm term = match term with 
                V x -> true
            |   Node ((Sym x), y) -> if List.length y != (arity x)  then false else List.fold_left (&&) true (List.map wfterm y);;


let rec max_in_list l m = match l with
                    [] -> m
                |  x::xs -> let z = max x m in max z (max_in_list xs z);;


(* Assuming variables and constants have height equal to 0 *)
let rec ht term = match term with 
                V x -> 0
            | Node (Sym ("X"), l) -> 0
            |  Node( x, y ) -> 1 + List.fold_left max 0 (List.map ht y);;

(* Assuming variables and constants have size equal to 1 *)
let rec size term = match term with 
                V x -> 1
            | Node (Sym ("Const"), y) -> 1
            | Node (x, y) -> 1 + List.fold_left (+) 0 (List.map size y);;

let rec _vars set term = match term with 
        V (Var x) -> SS.add x set
    |  Node(s, l) -> List.fold_left (fun s sym -> _vars s sym) set l;;

(* Makes a list out of a set *)
let vars term = let v = _vars (SS.empty) term in SS.fold (fun a b -> Var(a)::b) v [];;

let idn_subst x = V(x);;

let rec subst func term = match term with
                  V (x) -> func x
                | Node(x, y) -> Node(x, (List.map (subst func)) y);;

let compose g f x = subst g (f x);;

exception NOT_UNIFIABLE;;

let rec mgu t1 t2 = match (t1, t2) with 
                V(x), V(y)  -> (fun v -> if v = x 
                                         then V(y) 
                                         else V(v)) 
                                        (* if x is in vars of l1 then not unifiable *)
            | Node(s, l1), V(Var x) ->  if SS.mem x (_vars (SS.empty) (Node(s, l1))) 
                                        then raise NOT_UNIFIABLE 
                                        else (fun var -> if var = (Var x) 
                                                         then Node(s, l1) 
                                                         else V var)
            | V(x), Node(s, l1) -> mgu (Node(s, l1)) (V(x))
            | Node(s1, l1), Node(s2, l2) -> if (s1 <> s2 || List.length l1 != List.length l2) 
                                            then raise NOT_UNIFIABLE 
                                            (* List.fold_left2 f a [b1; ...; bn] [c1; ...; cn] is f (... (f (f a b1 c1) b2 c2) ...) bn cn.  *)
                                            else List.fold_left2 (fun sub x1 x2 -> compose (mgu(subst sub x1) (subst sub x2)) sub ) idn_subst l1 l2;;