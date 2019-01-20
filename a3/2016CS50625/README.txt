scnf gives term in a way that all variables in the term are quantified by a FORALL quantifier

Some testcases that demonstrate working.


let f1 = AND( (PRED ("p", [C "a"; C "b"])), (PRED ("p", [C "a"])) );;
(* wff f1 gives exception *)
wff f1;;


let f2 = AND( (PRED ("p", [ (F ("x", [V "x"; V "y"])) ])), (PRED ("p", [(F ("x", [V "x"]) )])) );;
(* wff f2 gives exception *)
wff f2;;

(* Free Variables *)
let t = EXISTS (V "x", PRED ("p", [V "x"; C "x"; F ("f", [V "y"])]));;
fv t;;

let p = FORALL(V"x", FORALL(V"y", OR(PRED("q", [V"x"]), AND(PRED("p", [V"x"]), PRED("p", [V"y"])))));;
(* sat p 1 gives p(a) *)
sat p 1;;


let p2 = FORALL(V"x", FORALL(V"y", AND(PRED("q", [V"x"]), AND(PRED("p", [V"x"]), PRED("p", [V"y"])))));;
(* sat p2 1 gives q(a) , p(a) *)
sat p2 1;;

let f1 = OR( EXISTS(V "y" , NOT(PRED("p", [V "y"]))), FORALL(V "z", PRED("q", [V "z"])) );;
let f2 = OR((EXISTS( (V"x"), AND( (PRED("p", [V"x"])), (NOT( (PRED ("q", [V"x"])))) ))), f1);;
(* FOR f2 : sat f2 1 gives 
    => ([], [PRED ("p", [C "a"]); NOT (PRED ("q", [C "a"]))]) 
    => p(a) and q(a) need to be true in order to satisfy the statement
*)
sat f2 1;;


let a = AND( 
      NOT (PRED ("p", [F ("f", [V "y"])])),
     AND
     (OR (PRED ("p", [C "a"]),
       OR (PRED ("q", [V "y"]), NOT (PRED ("p", [F ("f", [V "y"])])))),
     OR (NOT (PRED ("q", [C "a"])),
      OR (PRED ("q", [V "y"]), NOT (PRED ("p", [F ("f", [V "y"])]))))));;
(* dpll a 1  gives p(f(a)) as true predicate in order to satisy a *)
dpll a 1;;