open Signature
module A3 : Assignment3 = struct
(* Your code goes here *)

type term = C of string | V of string | F of string * (term list)
;;

type form = PRED of string * (term list)
            | NOT of form
            | AND of form * form
            | OR of form * form
            | FORALL of term * form (* This term should be a variable only*)
            | EXISTS of term * form (* This term should be a variable only*)
;;

exception Not_wff of (term list * form list);;
exception Not_closed of term list;;
exception DPLL_unsat of int;;

type wf = FR of string * (term list) | PR of (string*term list)
;;


let f1 = FORALL (V "x", FORALL (V "y", FORALL (V "x", PRED ("p", [C "a"]))))
  ;;
let f11 = FORALL (V "x", FORALL (V "y", EXISTS (V "x", PRED ("p", [C "a"]))))
  ;;
let f2 = FORALL (V "x", FORALL (V "y", PRED ("p", [C "a"])))
  ;;
let f3 = FORALL (V "x", EXISTS (V "x", PRED ("p", [C "a"])))
  ;;


let rec check_quantifier v f = match f with     
            FORALL ( a, b ) -> (if (List.mem a v) then (raise (Not_wff([a], []))) else (check_quantifier (a::v) b) )
        |   EXISTS ( a, b ) -> (check_quantifier v (FORALL(a, b)))
        |   PRED (x, y)     -> true
        |   NOT f           -> (check_quantifier v f)
        |   AND (a, b)      -> (check_quantifier v a) && (check_quantifier v b)
        |   OR (a, b)       -> (check_quantifier v a) && (check_quantifier v b)
;;

let fst (x, y, z) = x;;
let snd (x, y, z) = y;;
let thd (x, y, z) = z;;

let rec get_arities l tl = match tl with 
                    (F (s, tl)) :: xs  ->  (get_arities (((s, (List.length tl), (FR (s, tl))))::((get_arities l tl))) xs)
                |    (C s ) :: xs      ->  (get_arities l xs) 
                |    (V s) :: xs       ->  (get_arities l xs)
                |    []                ->  l
;;

let rec check_arity x l = match x with 
            FORALL ( a, b ) -> (check_arity b l)
        |   EXISTS ( a, b ) -> (check_arity b l)
        |   PRED (x, y)     -> (x, (List.length y), PR((x, y)))::(get_arities l y)
        |   NOT f           -> (check_arity f l)
        |   AND (a, b)      -> (check_arity a []) @ (check_arity b l)
        |   OR (a, b)       -> (check_arity a []) @ (check_arity b l)
;;

let rec search k ar p l = match l with 
                x :: xs ->  if (fst x) = k then 
                                (if (snd x) = ar then (search k ar p xs) else (match ((thd x), p) with 
                                    (FR(a,b), FR(c,d)) -> raise (Not_wff ([(F(a,b)); F(c, d)], []) )  
                                    |  (PR(a,b), PR(c, d)) -> raise (Not_wff ([], [(PRED(a, b)); PRED(c, d)])) ))  
                            else (search k ar p xs)
            |   []      ->  true
;;

let rec is_clean l = match l with
            x :: xs ->  if (search (fst x) (snd x) (thd x) xs) then is_clean xs else false 
        |   []      ->  true
;;

let f = FORALL( V"x", PRED ("p", [C "a"]) );;
let f = FORALL ( V"x", f);;

let f2 = AND( (PRED ("p", [C "a"; C "b"])), (PRED ("p", [C "a"])) );;
let f2 = AND( (PRED ("p", [ (F ("x", [V "x"; V "y"])) ])), (PRED ("p", [(F ("x", [V "x"]) )])) );;

(*RECHECK QUANTIFIER CHECK*)
let rec wff x = is_clean (check_arity x []) 
;;

let rec union l1 l2 = match l1 with 
            x :: xs -> if List.mem x l2 then l2 else x::l2
        |   [] -> l2
;;

let rec remove key l = match l with 
            x :: xs -> if (x = key) then (remove key xs) else (x :: (remove key xs))
            | [] -> []
;;

let rec get_vars t l = match t with 
          (V x) :: xs -> (V x) :: (get_vars xs l)
        | (C x) :: xs -> (get_vars xs l) 
        | (F (a, b)) :: xs -> (get_vars b []) @ (get_vars xs l)
        | [] -> l
;;

let rec get_constants t l = match t with 
          (C x) :: xs -> (C x) :: (get_constants xs l)
        | (V x) :: xs -> (get_constants xs l) 
        | (F (a, b)) :: xs -> (get_constants b []) @ (get_constants xs l)
        | [] -> l
;;

let rec fv x = match x with 
            PRED (x, y)     -> get_vars y []
        |   NOT f           -> (fv f)
        |   AND (a, b)      -> (union (fv a) (fv b)) 
        |   OR (a, b)       -> (union (fv a) (fv b)) 
        |   FORALL ( a, b ) -> remove (List.nth (get_vars [a] []) 0) (fv b)
        |   EXISTS ( a, b ) -> remove (List.nth (get_vars [a] []) 0) (fv b)
;;

let rec fc x = match x with 
            PRED (x, y)     -> get_constants y []
        |   NOT f           -> (fc f)
        |   AND (a, b)      -> (union (fc a) (fc b)) 
        |   OR (a, b)       -> (union (fc a) (fc b)) 
        |   FORALL ( a, b ) -> remove (List.nth (get_constants [a] []) 0) (fc b)
        |   EXISTS ( a, b ) -> remove (List.nth (get_constants [a] []) 0) (fc b)
;;

let closed x = if ((List.length (fv x))==0) then true else raise (Not_closed (fv x))
;;

(* replace a by b *)
let rec replace_term (V a) t2 t = match t with 
        l :: ls -> (
                    match l with 
                        (V x)       -> (if x = a then t2 :: (replace_term (V a) t2 ls) else (V x) :: (replace_term (V a) t2 ls) )
                    |   (C s)       -> (C s)::(replace_term (V a) t2 ls)
                    |   (F (c, d))  -> (F(c, (replace_term (V a) t2 d)))::(replace_term (V a) t2 ls)
                   )
    |   [] -> []
;;
(* replace v2 by v2 *)
let rec replace v1 v2 f = match f with 
            PRED (s, t) ->  PRED(s, (replace_term v1 v2 t))
        |   NOT a       ->  NOT (replace v1 v2 a)
        |   AND (a, b)  ->  AND ((replace v1 v2 a), (replace v1 v2 b))
        |   OR (a, b)   ->  OR ((replace v1 v2 a), (replace v1 v2 b))
        |   FORALL(a, b)-> FORALL(a, (replace v1 v2 b))
        |   EXISTS(a, b)-> EXISTS(a, (replace v1 v2 b))
;;

let rec replace_vars f str i = match f with 
            PRED (x, y)     -> PRED (x, y)
        |   NOT f           -> NOT (replace_vars f (str^"x") i)
        |   AND (a, b)      -> AND ((replace_vars a ("x"^str) i), (replace_vars b ("y"^str) (i+1)))
        |   OR (a, b)       -> OR ((replace_vars a ("x"^str) i), (replace_vars b ("y"^str) (i+1))) 
        |   FORALL ( a, b ) -> ( let x = str^string_of_int i in
                                    FORALL ( V x, (replace a (V x) (replace_vars b str (i+1)) ))
                               )

        |   EXISTS ( a, b ) -> ( let x = str^string_of_int i in
                                    EXISTS ( V x, (replace a (V x) (replace_vars b str (i+1)) ))
                               )
;;

let z =  AND (FORALL (V "x", FORALL (V "y", AND(PRED ("p", [V "x"]), PRED("p", [V "y"])))), FORALL (V "x", PRED ("q", [V "x"]))) 
    ;;
(*replace_vars z "" 0;;*)

let z2 = FORALL (V "x", FORALL (V "y", AND(PRED ("p", [V "x"]), PRED("p", [V "y"]))));;

(* resolve negation *)
let s = OR(NOT(FORALL(V"y",(PRED("p",[V "y"])))),FORALL(V"z",PRED("q",[V"z"])))
;;

let r = OR(NOT(FORALL(V"x",(OR((NOT(PRED("p",[V"x"]))),(PRED("q",[V "x"])))))),s) 
;;

let rec resolve_negation f = match f with 
                NOT (FORALL(a, b))  -> EXISTS (a, resolve_negation(NOT(b)))
            |   NOT (EXISTS(a, b))  -> FORALL (a, resolve_negation(NOT(b)))
            |   NOT (NOT a)         -> a
            |   NOT(OR(a, b))       -> resolve_negation (AND(NOT(a),NOT(b)))
            |   NOT(AND(a, b))      -> resolve_negation (OR(NOT a,NOT b))
            |   AND(a, b)           -> AND( (resolve_negation a), (resolve_negation b) )
            |   OR(a, b)            -> OR( (resolve_negation a), (resolve_negation b) )
            |   FORALL(a, b)        -> FORALL( a, (resolve_negation b) )
            |   EXISTS(a, b)        -> EXISTS( a, (resolve_negation b) )
            |   a                   -> a
;;


let f2  = FORALL (V "y", PRED ("p", [C "a"]));;
let f = NOT( f2 );;
(* works for r check page 174 *)

let rec extract_quantifiers f = match f with 
            |   AND(a, FORALL(b, c))   ->  (FORALL(b, (extract_quantifiers (AND((extract_quantifiers a), (extract_quantifiers c))))))
            |   OR(a,  FORALL(b, c))   ->  (FORALL(b, (extract_quantifiers (OR((extract_quantifiers a), (extract_quantifiers c))))))
            |   OR(a,  EXISTS(b, c))   ->  (EXISTS(b, (extract_quantifiers (OR((extract_quantifiers a), (extract_quantifiers c))))))
            |   AND(a,  EXISTS(b, c))  ->  (EXISTS(b, (extract_quantifiers (AND((extract_quantifiers a), (extract_quantifiers c))))))
            |   AND(FORALL(b, c), a)   ->  (FORALL(b, (extract_quantifiers (AND((extract_quantifiers a), (extract_quantifiers c))))))
            |   OR(FORALL(b, c), a)    ->  (FORALL(b, (extract_quantifiers (OR((extract_quantifiers a), (extract_quantifiers c))))))
            |   OR(EXISTS(b, c), a)    ->  (EXISTS(b, (extract_quantifiers (OR((extract_quantifiers a), (extract_quantifiers c))))))
            |   AND(EXISTS(b, c), a)   ->  (EXISTS(b, (extract_quantifiers (AND((extract_quantifiers a), (extract_quantifiers c))))))
            |   a                      -> a
;;

let rec distribute f = match f with 
                EXISTS(a, b)     -> EXISTS(a, (distribute b))
            |   FORALL(a, b)     -> FORALL(a, (distribute b))
            |   OR(AND(a, b), c) -> AND((distribute (OR( distribute(a), distribute(c)))), (distribute (OR(distribute(b), distribute(c)))))
            |   OR(c, AND(a, b)) -> AND((distribute (OR( distribute(a), distribute(c)))), (distribute (OR(distribute(b), distribute(c)))))
            |   AND(a, b)        -> AND(a, b)
            |   OR(a, b)         -> OR(a, b)
            |   a                -> a
;;

(*let make_function f l = F( f, l );;*)

let rec remove_existence f str i l = match f with 
                EXISTS(a, b)     -> (if (List.length l) = 0 
                                        then 
                                            (let c = (C ("a"^str^(string_of_int i))) in 
                                                (replace a c (remove_existence b ("a"^str) (i+1) l))
                                            ) 
                                        else (let f1 = (F(("f"^str), l )) in  
                                                (replace a f1 (remove_existence b ("f"^str) (i+1) l))
                                             ) 
                                    )
            |   FORALL(a, b)     -> (remove_existence b str i (a::l))
            |   a                -> a
;;

let f1 = OR( EXISTS(V "y" , NOT(PRED("p", [V "y"]))), FORALL(V "z", PRED("q", [V "z"])) );;

let f2 = OR((EXISTS( (V"x"), AND( (PRED("p", [V"x"])), (NOT( (PRED ("q", [V"x"])))) ))), f1);;

let scnf f = 
    (let a = (replace_vars f "" 0) in 
        let b = (resolve_negation a) in 
            let c = (extract_quantifiers b) in 
                let d = (distribute c) in 
                    let e = (remove_existence d "" 0 []) in 
                        e
    )
;;

let constants = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
                 "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"];;


(* gets list of all the clauses *)
let rec get_clauses_helper f l = match f with 
            AND( a, b) ->  (get_clauses_helper a [])  @ (get_clauses_helper b l)
        |   OR( a, b ) ->  (a::(get_clauses_helper b []))
        |   a          ->  [a]
;;

(* gets list of (list of clauses) *)
let rec get_clauses f = match f with 
             AND( a, b) -> (get_clauses_helper a []) :: [(get_clauses_helper b [])]
            | b -> [(get_clauses_helper b [])]
            ;;

(*OR (PRED ("q", [V "yy2"]), NOT (PRED ("p", [F ("fa", [V "yy2"])])));;*)
(* converts list of list to list *)
let rec make_list l = match l with 
        x :: xs -> x @ make_list xs
        | [] -> []
;;

(* remove duplicates from list *)
let rec cleanup_list f l = match f with 
            x :: xs -> if (List.mem x l) then cleanup_list xs l else (cleanup_list xs (x::l))
        |    [] -> l
;;

(* given a scnf form gives out variables in the formula *)
let vars f =  (let z = make_list (List.map fv (get_clauses_helper f []))  in (cleanup_list z []));;
let consts f =  (let z = make_list (List.map fc (get_clauses_helper f []))  in (cleanup_list z []));;

let append s1 s2 = s1^s2;;

let rec sublist b e l = 
  match l with
    [] -> failwith "sublist"
  | h :: t -> 
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail
;;


let rec get_const_list num consts init l2 = 
        (
            if num>25 then
            (
                let a = (List.map (append (List.nth constants init)) l2 ) in 
                    if init = 26 then (get_const_list num consts 0 a) 
                    else 
                        (
                            (*if init=0 then consts@(get_const_list (num-26) a (init+1) a) *)
                            (*else *)
                                consts@(get_const_list (num-26) a  (init+1) l2 ) 
                        )
                 
            )
            else (sublist 0 (num-1) consts)
        )
;;

let get_consts num = get_const_list num constants 0 constants;;


(* replace V a by t2 *)
let rec _replace_var (V a) t2 t = match t with 
        l :: ls -> (
                    match l with 
                        (V x)       -> (
                                            if x = a 
                                            then t2 :: (_replace_var (V a) t2 ls) 
                                            else (V x) :: (_replace_var (V a) t2 ls) 
                                       )
                    |   (C s)       -> (C s)::(_replace_var (V a) t2 ls)
                    |   (F (c, d))  -> (F(c, (_replace_var (V a) t2 d)))::(_replace_var (V a) t2 ls)
                   )
    |   [] -> []
;;

let rec _replace_const (C a) t2 t = match t with 
        l :: ls -> (
                    match l with 
                        (C x)       -> (
                                            if x = a 
                                            then t2 :: (_replace_const (C a) t2 ls) 
                                            else (C x) :: (_replace_const (C a) t2 ls) 
                                       )
                    |   (V s)       -> (V s)::(_replace_const (C a) t2 ls)
                    |   (F (c, d))  -> (F(c, (_replace_const (C a) t2 d)))::(_replace_const (C a) t2 ls)
                   )
    |   [] -> []
;;


(* replace v2 by v2 *)
let rec _replace v1 v2 f = match f with 
            PRED (s, t) ->  (match v1 with V x -> PRED(s, (_replace_var v1 v2 t)) | (C x) ->  PRED(s, (_replace_const v1 v2 t)))
        |   NOT a       ->  NOT (_replace v1 v2 a)
        |   AND (a, b)  ->  AND ((_replace v1 v2 a), (_replace v1 v2 b))
        |   OR (a, b)   ->  OR ((_replace v1 v2 a), (_replace v1 v2 b))
        |   FORALL(a, b)-> FORALL(a, (_replace v1 v2 b))
        |   EXISTS(a, b)-> EXISTS(a, (_replace v1 v2 b))
;;

let rec get_var_list vars consts = match vars with 
                x::xs -> (x, consts) :: get_var_list xs consts
            |   []    -> []
;;


let ins_all_positions x l =  
  let rec aux prev acc = function
    | [] -> (prev @ [x]) :: acc |> List.rev
    | hd::tl as l -> aux (prev @ [hd]) ((prev @ [x] @ l) :: acc) tl
  in
  aux [] [] l
;;

let rec permutations = function  
  | [] -> []
  | x::[] -> [[x]]
  | x::xs -> List.fold_left (fun acc p -> acc @ ins_all_positions x p ) [] (permutations xs)
(*| _ -> []*)
;;


let combs_with_rep m xs =
  let arr = Array.make (m+1) [] in
  arr.(0) <- [[]];
  List.iter (fun x ->
    for i = 1 to m do
      arr.(i) <- arr.(i) @ List.map (fun xs -> x::xs) arr.(i-1)
    done
  ) xs;
  arr.(m)
;;

let rec uniq x =
  let rec uniq_help l n = 
    match l with
    | [] -> []
    | h :: t -> if n = h then uniq_help t n else h::(uniq_help t n) in
  match x with
     | [] -> []
     | h::t -> h::(uniq_help (uniq t) h)
;;

let num_uniq l = List.length (uniq l);;


let rec clean_list l i = match l with
        x ::xs -> (if (num_uniq x) = i then x :: (clean_list xs i) else (clean_list xs i))
    |   []  -> []
;;


let rec eq v1 v2 = match v1, v2 with
| [], []       -> true
| [], _
| _, []        -> false
| x::xs, y::ys -> x = y && eq xs ys
;;

let rec comp l1 l2 = match l2 with 
        x :: xs -> (if eq l1 x then true else comp l1 xs)
    |   []      -> false
;;

let rec rem_dup l = match l with 
        x::xs -> if comp x xs then rem_dup xs else x:: (rem_dup xs)
    |   []    -> []
;;

(* i is the number of variables, whereas l is the list of constants *)
let combs i l =
    ( 
        let n = List.length l in 
        rem_dup (make_list (List.map permutations (clean_list (combs_with_rep i l) n)))
    )
;;


let rec replace_constants l1 l2 f = match l1, l2 with
            x::xs, y::ys -> let g = _replace x (C y) f in replace_constants xs ys g
        |   [], []   -> f
;;


let rec replace_variables l1 l2 f = match l1, l2 with
            x::xs, y::ys -> let g = _replace x (C y) f in replace_variables xs ys g
        |   [],[]    -> f
;;


let rec empty_clause l = match l with 
        x :: xs -> if (List.length x) = 0 then true else empty_clause xs
    |   []      -> false
;;

let rec unit_clause l ul = match l with
        x::xs   -> if (List.length x) = 1 then unit_clause xs (x@ul) else unit_clause xs ul
    |   []      -> ul
;;

let negate_literal l = match l with
    NOT x -> x
    | x -> NOT x
;;

let rec clean_clause clause l b = match clause with 
            x :: xs ->  if List.mem x l then (true, [] , true)                    
                        else
                            (
                                if List.mem (negate_literal x) l then  
                                    let f = (clean_clause xs l false) in 
                                        ((fst f), (snd f), true) 
                                else 
                                    let f = (clean_clause xs l false) in 
                                        ((fst f), (x::(snd f)), true) 
                            )
        |   []      -> (b, [], b)
;;

let rec remove_clauses g l = match g with
        x:: xs -> ( let t = (clean_clause x l false) in if (fst t) then remove_clauses xs l else (snd t)::remove_clauses xs l)
        | [] -> []
;;

(* remove empty lists *)
let rec cleanup l = match l with
        x :: xs-> (if List.length x = 0 then cleanup xs else x::(cleanup xs))
        | []->[]
;;

let rec check_contra cl = match cl with 
        x :: xs -> if List.mem (negate_literal x) cl then true else check_contra xs
        |[]  -> false
;;

let rec remove_tautology g = match g with
            x :: xs -> if (check_contra x) then remove_tautology xs else x :: remove_tautology xs
        |   []      -> []
;;

let rec apply_dppll g l1 l2 = match g with
        x :: xs -> ( 
         let g = remove_tautology g in
            if empty_clause g then (false, [], []) 
                    else 
                        (
                            let ul = unit_clause g [] in
                                let t = remove_clauses g ul in 
                            if empty_clause t then (false, [], []) 
                            else
                            let t2 = make_list t in
                            (
                                if List.length t2 = 0 then (true, l1, (ul@l2))
                                else 
                                    (
                                        let l = List.nth t2 0 in 
                                            let t3 = (apply_dppll ([l]::g) l1 (l2)) in 
                                                if (fst t3) then t3
                                                else 
                                                    let t4 = (apply_dppll ([NOT(l)]::g) l1 (l2)) in
                                                        t4
                                    )
                            )
                        )
                    )


    |   []      -> (true, l1, l2)
;;

let rec dppll_helper vars vars_asgnmt f = match vars_asgnmt with 
    x :: xs -> (let g = get_clauses (replace_variables vars x f) in 
                    let t = apply_dppll g [] [] in (* should give predicates and list of terms *)
                        (
                            if fst t then t else dppll_helper vars xs f
                        )
                ) 
    | [] -> false, [], []
;;

let dpll x y = 
    (
        let f = scnf x in
            let cts = consts f in
                let vrs = vars f in 
                    (if (List.length cts) > y then 
                        (raise (DPLL_unsat y)) 
                    else 
                        (
                            let l = (List.length cts) in 
                                let domain = get_consts y in
                                if l > 0 then 
                                    let c1 = sublist 0 (l-1) domain in 
                                        let c2 = sublist l (y-1) domain in 
                                            let f = replace_constants cts c1 f in 
                                            
                                                let vars_assignment = (combs (List.length vrs) c2) in
                                                    let k = dppll_helper vrs vars_assignment f in 
                                                        if fst k then (snd(k), thd(k)) else (raise (DPLL_unsat y)) 
                                                        
                                else 
                                    let vars_assignment = (combs (List.length vrs) domain) in
                                                    let k = dppll_helper vrs vars_assignment f in 
                                                        if fst k then (snd(k), thd(k)) else (raise (DPLL_unsat y)) 
                        )
                    )
    )
;;

let dpll_h x y = 
    (
        let f = scnf x in
            let cts = consts f in
                let vrs = vars f in 
                    (if (List.length cts) > y then 
                        (false, [], []) 
                    else 
                        (
                            let l = (List.length cts) in 
                                let domain = get_consts y in
                                if l > 0 then 
                                    let c1 = sublist 0 (l-1) domain in 
                                        let c2 = sublist l (y-1) domain in 
                                            let f = replace_constants cts c1 f in 
                                            
                                                let vars_assignment = (combs (List.length vrs) c2) in
                                                    let k = dppll_helper vrs vars_assignment f in 
                                                        if fst k then (true, snd(k), thd(k)) else (false , [], []) 
                                                        
                                else 
                                    let vars_assignment = (combs (List.length vrs) domain) in
                                                    let k = dppll_helper vrs vars_assignment f in 
                                                        if fst k then (true, snd(k), thd(k)) else (false, [], []) 
                        )
                    )
    )
;;
            
(*let p = FORALL(V"x", FORALL(V"y", OR(PRED("q", [V"x"]), AND(PRED("p", [V"x"]), PRED("p", [V"y"])))));;*)
(*let p2 = FORALL(V"x", FORALL(V"y", AND(PRED("q", [V"x"]), AND(PRED("p", [V"x"]), PRED("p", [V"y"])))));;*)

let rec sat_helper f i k= 
    if i <= k then 
        let b = dpll_h f i in 
            if (fst b) then (snd(b), thd(b)) else sat_helper f (i+1) k
    else 
        raise (DPLL_unsat(k))
;;

let sat x y = 
    let b = (wff x) in 
        let b = (closed x) in 
            sat_helper x 1 y
    ;; 
