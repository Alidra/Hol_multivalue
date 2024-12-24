Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1337493 : forall (r : (prod hreal hreal) -> Prop), (exists x : prod hreal hreal, r = (treal_eq x)) = ((dest_real (mk_real r)) = r).
