type prop = ATOM of string      |
            NOT of prop         |
            AND of prop*prop    |
            OR of prop*prop     |
            COND of prop*prop   |
            BIC of prop*prop
;;

type tree = Node of (prop list * bool) * ( tree list )
;; 

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
    Node( (_, b), _ ) -> b
;;

let rec getNonLiteral l = match l with
        [] -> []
    | x::xs -> if (isLiteral x) then  (getNonLiteral xs) else x :: (getNonLiteral xs)
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

let branch exp = match exp with
            NOT ( NOT p )      ->    alpha [p]
        |   AND ( p, q )       ->    alpha [p; q]
        |   NOT( OR( p, q ))   ->    alpha [NOT p; NOT q]
        |   NOT( COND(p, q) )  ->    alpha [p; NOT q]
        |   BIC(p, q)          ->    alpha [ COND(p, q); COND(q, p) ]
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
let rec build prop_list = match (closed prop_list) with
                LITERALS(s)  ->  Node( ( prop_list, s ), [] )
            |   NOT_LITERAL  -> 
            ( 
                let w = ( getNonLiteral prop_list )
                in
                (
                    (*(print_int (List.length w))*)
                    let x = (List.hd w) in 
                    (
                        let u = (delete x w)
                        in
                        (   
                            let ts = List.map build (List.map (listUnion u) (branch x)) 
                            in
                            (
                                let b = (bigAnd ( List.map isClosed ts ))
                                in
                                   ( Node( (prop_list, b), ts ))
                            )
                        )
                    )
                )
            )
;;