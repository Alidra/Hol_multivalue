Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2749910 : forall {A : Type'}, forall P : A -> Prop, forall m : A -> int, ((forall x : A, int_le (int_of_num (NUMERAL 0)) (m x)) /\ (forall x : A, (forall y : A, (int_lt (m y) (m x)) -> P y) -> P x)) -> forall x : A, P x.
