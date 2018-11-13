type prop = ATOM of string      |
            NOT of prop         |
            AND of prop*prop    |
            OR of prop*prop     |
            COND of prop*prop   |
            BIC of prop*prop
;;

(* storing prop which caused the split as sigleton in the last list *)
type tree = Node of (prop list * bool * prop list) * ( tree list )
;; 

type value_prop = Value of prop*int;;

type value_tree= ValueNode of (value_prop list * bool * prop list) * (value_tree list);;

(* check if a prop is a literal *)
let isLiteral lit = match lit with
            ATOM( s )       -> true
        |   NOT(ATOM( s ))  -> true
        |   _               -> false
;;

let rec bigAnd l = match l with 
        [] -> true
    |   x::xs -> x && bigAnd xs
;;    

(* check if a list consists of all literals *)
let isAllLiterals l = bigAnd (List.map isLiteral l) 
;;

let complement exp = match exp with 
            NOT( x )    -> x
        |   x           -> NOT( x )
;;

(*check if a list has complement literals *)
let rec hasComplements l = match l with
                [] -> false
            |   [x] -> false
            |   x::xs -> if (List.mem (complement x) xs) then true else (hasComplements xs)
;;

(* check if a list of expression is closed *)
type check = NOT_LITERAL | LITERALS of bool ;;

let closed l = if (isAllLiterals l) then LITERALS( (hasComplements l) ) else NOT_LITERAL
;;

let isClosed pr = match pr with
    Node( (_, b, _), _ ) -> b
;;

let rec getNonLiteral l = match l with
        [] -> []
    | x::xs -> if (isLiteral x) then  (getNonLiteral xs) else x :: (getNonLiteral xs)
;;

let rec getLiterals l = match l with
        [] -> []
    | x::xs -> if (isLiteral x) then  x::(getNonLiteral xs) else (getLiterals xs)
;;

let rec delete elmt w = match w with
            []      ->      []
        |   x::xs   ->   ( if x=elmt then (delete elmt xs) else x :: (delete elmt xs) )
;;


let rec setFromList l = match l with    
            [] -> []
        | x :: xs -> if (List.mem x xs) then xs else x :: setFromList xs
;;

let alpha xs = [(setFromList xs)]
;;

let make_list a = [a];;

let beta = List.map make_list;;

exception NOT_BRANCHABLE;;


let isAlpha exp = match exp with 
            NOT ( NOT p )      ->    true
        |   AND ( p, q )       ->    true
        |   NOT( OR( p, q ))   ->    true
        |   NOT( COND(p, q) )  ->    true
        |   BIC(p, q)          ->    true
        |   _                  ->    false
;;

let branch exp = match exp with
            NOT ( NOT p )      ->    alpha [p]
        |   AND ( p, q )       ->    alpha [p; q]
        |   NOT( OR( p, q ))   ->    alpha [NOT p; NOT q]
        |   NOT( COND(p, q) )  ->    alpha [p; NOT q]
        |   BIC(p, q)          ->    alpha [COND(p, q); COND(q, p)]
        |   NOT(AND(p, q))     ->    beta  [NOT p; NOT q]
        |   OR(p, q)           ->    beta  [p; q]
        |   COND(p, q)         ->    beta  [NOT p; q]
        |   NOT(BIC(p, q))     ->    beta  [NOT(COND(p, q)); NOT(COND(q, p))] 
        |   _                  ->    raise NOT_BRANCHABLE 
;; 

let rec listUnion l1 l2 = match l1 with 
                [] -> l2
            |   x::xs -> if (List.mem x l2) then (listUnion xs l2) else x :: (listUnion xs l2)
;; 

(* take and of all the propositions and show its negation's tableaux is closed *)
(* Node boolean shows whether closed has been found below *)
let rec build prop_list = match (closed prop_list) with
                LITERALS(s)  -> (Node( ( prop_list, s, []), [] ))
            |   NOT_LITERAL  -> 
            ( 
                let w = ( getNonLiteral prop_list )
                in
                (
                    (*(print_int (List.length w))*)
                    let x = (List.hd w) in 
                    (
                        let u = (delete x prop_list)
                        in
                        (   
                            let ts = List.map build (List.map (listUnion u) (branch x)) 
                            in
                            (
                                let b = (bigAnd ( List.map isClosed ts ))
                                in
                                   ( Node( (prop_list, b, [x]), ts ))
                            )
                        )
                    )
                )
            )
;;

let rec cleanup_list seen l = match l with
            [] -> []
        | x :: xs -> if List.mem x seen then cleanup_list seen xs  else x :: (cleanup_list seen xs)
;;


let rec cleanup_tableau seen tabl =  match tabl with 
            Node((prop_list, b, s), ts) -> let cleaned_list = (cleanup_list seen prop_list) in
                                        Node( (cleaned_list, b, s), (List.map (cleanup_tableau (seen@cleaned_list)) ts) )
;;

let cleanup_tabl tabl = cleanup_tableau [] tabl;;

let rec addUpList l = match l with 
            [] -> 0 
        |   x :: xs -> x + addUpList xs
;;


let rec size_tabl tabl = match tabl with
                Node((prop_list, b, s), []) -> List.length prop_list
            |   Node((prop_list, b, s), l)  -> (List.length prop_list) + addUpList(List.map size_tabl l) 
;;


type table = Table of (int, prop) Hashtbl.t;;
(*type table2 = InvTable of (int, prop) Hashtbl.t;;*)
(* add key value to a table t like add tab "a" 1 *)
let add (Table tab) key value = Hashtbl.add tab key value;;
(*let add_prop (InvTable tab) key value = Hashtbl.add tab key value;;*)
(* find key value to a table t like find_key tab "a" *)
let find_key (Table t) key = Hashtbl.find t key;;
(*let find_prop (InvTable t) key = Hashtbl.find t key;;*)
(*let has_prop (InvTable t) key = Hashtbl.mem t key;;*)
let has_key (Table t) key = Hashtbl.mem t key;;

(*Table (Hashtbl.create 1000))*)
let make_unit l = ();;

type counter = { mutable value : int };;

let a = {value=1};;
let b = {value=1};;
let map = (Table (Hashtbl.create 1000));;
(*let invmap = (InvTable (Hashtbl.create 1000));;*)
(*
let rec addToTabl l = match l with 
                [] -> ()
            |   x::xs -> ((add map x (a.value)); (add_prop invmap (a.value) x); a.value <- a.value+1; )
;;
*)
let v = {value=1};;

let add_value n =  let () =  (a.value <- (a.value+1))  in
                   ( let () = (add map (a.value-1) n) in
                                       Value(n, (a.value-1)) )
;;

let rec give_value tabl = match tabl with
            Node((prop_list, b, []), _) -> ValueNode( ((List.map add_value prop_list), b, []), [] )
        |   Node((prop_list, b, [sp]), ts) ->   (

                                                ValueNode( ((List.map add_value prop_list), b, [sp]), (List.map give_value ts) )
                                                )  
        | _ -> raise NOT_BRANCHABLE
;;

let getValue n = match n with
        Value(_, i) -> i
;;

let rec getAdjacent l = match l with
                []      -> []
            |    [x]    -> []
            |  x::y::xs -> (x, y) ::getAdjacent (y::xs)
;;

let val_to_prop v = match v with
    Value(p, i) -> p
;;

let rec getSplitterValue sp l = match l with
               [] -> -1
            |  x :: xs -> if (val_to_prop x)=sp then (getValue x) else getSplitterValue sp xs
;;

let rec getValues v = match v with
            []  -> []
        |   ValueNode((val_list, _, _), _) :: xs -> (List.map getValue val_list) @ getValues xs
;;

let rec addParent p vs = match vs with
            []  -> []
        |   x::xs -> (p, x) :: (addParent p xs)
;;


let rec getValues2 v = match v with
            []  -> []
        |   ValueNode((val_list, _, _), _) :: xs -> (val_list) @ getValues2 xs
;;

let rec addParent2 p ts = match ts with
            []  -> []
        |   [Value(prop, v)] -> [(p,v)]
        |   Value(prop, v) :: ys -> if isAlpha prop then [(p, v)] else addParent2 p ys
;;


let rec getList l = match l with 
        [] -> []
    | x::xs -> x@ (getList xs)
;;

(*let List.nth l ((List.length l)-1)*)
let rec getLast l = match l with 
        | [x] -> x
        | x::xs -> getLast xs
        | _  -> raise NOT_BRANCHABLE;;

let rec connected_edges t = match t with 
            ValueNode( (val_list, b, []), _ ) -> []
        |   ValueNode((val_list, b, [sp]), ts) -> if List.mem sp (List.map val_to_prop val_list) 
                                                  then
                                                      (* children have edge with parent *)
                                                  (
                                                    if isAlpha sp 
                                                    then
                                                    (
                                                    let v = getSplitterValue sp val_list in
                                                    (let c = getValues2 ts in
                                                     let s = addParent2 v c in 
                                                     (
                                                        (getAdjacent ( (delete v (List.map getValue val_list))@[v] ) )  @ s @ (getList(List.map connected_edges ts))
                                                     )
                                                    )
                                                   )
                                                    else
                                                    (    let v = getSplitterValue sp val_list in
                                                    (let c = getValues ts in
                                                     let s = addParent v c in 
                                                     (
                                                        (getAdjacent ( (delete v (List.map getValue val_list))@[v] ) )  @ s @ (getList(List.map connected_edges ts))
                                                     )
                                                    )
                                                    )
                                                  ) 
                                                  else 
                                                  (
                                                    if isAlpha sp 
                                                    then
                                                    (
                                                        let l = (List.map getValue val_list) in 
                                                    let v = getLast l in
                                                    (let c = getValues2 ts in
                                                     let s = addParent2 v c in 
                                                     (
                                                        (getAdjacent ( (delete v (List.map getValue val_list))@[v] ) )  @ s @ (getList(List.map connected_edges ts))
                                                     )
                                                    )
                                                   )
                                                    
                                                    else
                                                    ( 
                                                    let l = (List.map getValue val_list) in 
                                                    (let v = getLast l in
                                                    let c = getValues ts in
                                                     let s = addParent v c in 
                                                     (
                                                        (getAdjacent ( (delete v (List.map getValue val_list))@[v] ) )  @ s @ (getList(List.map connected_edges ts))
                                                     )
                                                    )
                                                    )
                                                )

                                           | _ -> raise NOT_BRANCHABLE       

;;
(* write a file with these *)
let s = "digraph{
ranksep = 0.35;
node [shape=plaintext];\n"

let default_start = " [texlbl=\"\\underline{ {\\LARGE \\color{green} $";;
let default_end   = "$}}\"];"

let rec disp prop = match prop with 
            ATOM x       ->  x
        |   NOT x        -> "\\neg (" ^ (disp x) ^ ")"
        |   AND(x, y)    -> "(" ^ (disp x) ^ " \\wedge " ^ (disp y) ^ ")"
        |   OR(x, y)     -> "(" ^ (disp x) ^ " \\vee " ^ (disp y) ^ ")"
        |   COND(x, y)   -> "(" ^ (disp x) ^ " \\rightarrow " ^ (disp y) ^ ")"
        |   BIC(x, y)    -> "(" ^ (disp x) ^ " \\xleftrightarrow " ^ (disp y) ^ ")"
;;

type message = { mutable msg : string };;
let x = {msg = s};; 

let rec digraph num = if num > 0 
                            then 
                                (
                                    (x.msg <- (x.msg ^ (string_of_int b.value) ^ default_start ^ (disp (find_key map b.value)) ^ default_end ^ "\n"));
                                    (b.value <- b.value +1);
                                    (digraph (num-1) ); 

                                ) 
                        else (x.msg <- x.msg ^"\n")
;;



(*x.msg <- (x.msg ^ sub_start);;*)
let rec subgraph l = match l with
               [] -> ()
        |   y::xs -> let ()  = (( x.msg <- (x.msg ^ (string_of_int (fst y)) ^ " -> " ^ (string_of_int (snd y))  ^ ";\n") )) in
                        subgraph xs
;;



  
let file = "a2.dot";;


let p = ATOM "p";;
let q = ATOM "q";;
let r = ATOM "r";;


let rec takeAnd l = match l with
            [x] -> x
        | x::xs -> AND(x, (takeAnd xs))
        | _ -> raise NOT_BRANCHABLE;;

let  z = OR(AND (OR (ATOM "p", ATOM "q"), AND (NOT (ATOM "p"), NOT (ATOM "q"))) , (OR (NOT(ATOM "p"), NOT(ATOM "q"))) );;

(*let () = a.value <- 1;;
let tabl = cleanup_tabl (build [z]);;
let t = give_value tabl;;

*)

let tableau prop_list = ( 
    let z = takeAnd prop_list in
        let () = a.value <- 1 in
            let tabl = cleanup_tabl (build [z]) in 
                let t = give_value tabl in 
                    let () = digraph (a.value-1) in
                        let sub_start  = "subgraph dir\n{\n" in 
                            let () = x.msg <- x.msg ^ sub_start in 
                                let g = connected_edges t in
                                    let () = subgraph g in 
                                        let () = x.msg <- (x.msg ^ "}\n}\n"  ) in 
                                            let oc = open_out file in    
                                                Printf.fprintf oc "%s\n" x.msg;  
                                                close_out oc;
) 
;;

tableau [z];;
