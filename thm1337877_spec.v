Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337877 : forall (x1 : prod hreal hreal) (y1 : prod hreal hreal), ((real_mul (mk_real (treal_eq x1)) (mk_real (treal_eq y1))) = (mk_real (treal_eq (treal_mul x1 y1)))) = ((mk_real (treal_eq (treal_mul x1 y1))) = (real_mul (mk_real (treal_eq x1)) (mk_real (treal_eq y1)))).
