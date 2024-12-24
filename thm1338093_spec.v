Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1338093 : (forall x : prod hreal hreal, forall y : prod hreal hreal, (treal_eq x y) = ((mk_real (treal_eq x)) = (mk_real (treal_eq y)))) /\ ((forall P : real -> Prop, (forall x : prod hreal hreal, P (mk_real (treal_eq x))) = (forall x : real, P x)) /\ ((forall P : real -> Prop, (exists x : prod hreal hreal, P (mk_real (treal_eq x))) = (exists x : real, P x)) /\ (forall x : real, (mk_real (treal_eq (@ε (prod hreal hreal) (dest_real x)))) = x))).
