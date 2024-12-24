Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337622 : forall (x1 : prod hreal hreal), (real_neg (mk_real (treal_eq x1))) = (mk_real (treal_eq (treal_neg x1))).
