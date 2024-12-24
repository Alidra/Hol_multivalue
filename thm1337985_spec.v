Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337985 : forall (x1 : prod hreal hreal) (y1 : prod hreal hreal), (real_le (mk_real (treal_eq x1)) (mk_real (treal_eq y1))) = (treal_le x1 y1).
