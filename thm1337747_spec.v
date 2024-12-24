Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337747 : forall (x1 : prod hreal hreal) (y1 : prod hreal hreal), (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq y1))) = (mk_real (treal_eq (treal_add x1 y1))).
