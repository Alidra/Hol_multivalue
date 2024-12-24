Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1338076 : forall (x : prod hreal hreal), (real_inv (mk_real (treal_eq x))) = (mk_real (treal_eq (treal_inv x))).
