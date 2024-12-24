Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1338113 : forall (x : prod hreal hreal) (y : prod hreal hreal), ((fun y' : prod hreal hreal => (treal_eq x y') = ((mk_real (treal_eq x)) = (mk_real (treal_eq y')))) y) = ((treal_eq x y) = ((mk_real (treal_eq x)) = (mk_real (treal_eq y)))).
