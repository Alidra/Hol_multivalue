Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7662540 : forall {_140454 _140455 _140456 : Type'} (P : (cart _140454 (finite_sum _140455 _140456)) -> Prop), (forall p : cart _140454 (finite_sum _140455 _140456), P p) = (forall x : cart _140454 _140455, forall y : cart _140454 _140456, P (@pastecart _140454 _140455 _140456 x y)).
