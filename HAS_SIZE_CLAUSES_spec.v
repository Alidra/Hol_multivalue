Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3887954 : forall {_100499 : Type'} (n : nat) (s : _100499 -> Prop), ((@HAS_SIZE _100499 s (NUMERAL 0)) = (s = (@EMPTY _100499))) /\ ((@HAS_SIZE _100499 s (S n)) = (exists a : _100499, exists t : _100499 -> Prop, (@HAS_SIZE _100499 t n) /\ ((~ (@IN _100499 a t)) /\ (s = (@INSERT _100499 a t))))).
