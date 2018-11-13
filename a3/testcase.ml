open structure.Assignment3;;
(* The test cases go here.
Below is a sample call to wff function *)
(* FOL formula e.g: loves(romeo, juliet) *)
let t1 = C "romeo";;
let t2 = C "juliet";;
let fml = PRED("loves", [t1; t2]);;
wff fml;;