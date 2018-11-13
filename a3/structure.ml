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

let wff x = match x with 
            PRED (x, y) -> true;;

let fv x = match x with 
            PRED (x, y) -> [C "x"]
;;

let closed x = match x with 
            PRED (x, y) -> false
;;

let scnf x = match x with 
            PRED (x, y) -> PRED (x, y)
;;

let dpll x y = match x with 
            PRED (a, b) -> [C "x"], [PRED (a, b)]
;;

let sat x y = match x with 
            PRED (a, b) -> true, [C "x"], [PRED (a, b)]
;;

end