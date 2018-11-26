(* Well formed formulas *)
let f1 = AND( (PRED ("p", [C "a"; C "b"])), (PRED ("p", [C "a"])) );;
(* wff f1 gives exception *)

let f2 = AND( (PRED ("p", [ (F ("x", [V "x"; V "y"])) ])), (PRED ("p", [(F ("x", [V "x"]) )])) );;
(* wff f2 gives exception *)

let f1 = FORALL (V "x", FORALL (V "y", FORALL (V "x", PRED ("p", [C "a"]))))
  ;;

(* Free Variables *)
let t = EXISTS (V "x", PRED ("p", [V "x"; C "x"; F ("f", [V "y"])]));;
