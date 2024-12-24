Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7603491 : forall {A : Type'}, (forall a : finite_image A, (@finite_index A (@dest_finite_image A a)) = a) /\ (forall r : nat, (@IN nat r (dotdot (NUMERAL (BIT1 0)) (@dimindex A (@UNIV A)))) = ((@dest_finite_image A (@finite_index A r)) = r)).
