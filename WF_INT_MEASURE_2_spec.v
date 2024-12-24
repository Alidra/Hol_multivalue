Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2750525 : forall {A B : Type'}, forall P : A -> B -> Prop, forall m : A -> B -> int, ((forall x : A, forall y : B, int_le (int_of_num (NUMERAL 0)) (m x y)) /\ (forall x : A, forall y : B, (forall x' : A, forall y' : B, (int_lt (m x' y') (m x y)) -> P x' y') -> P x y)) -> forall x : A, forall y : B, P x y.
