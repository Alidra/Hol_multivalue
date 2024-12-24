Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3863773 : forall {_100044 : Type'}, forall s : _100044 -> Prop, forall n : nat, (@HAS_SIZE _100044 s n) = ((@FINITE _100044 s) /\ ((@CARD _100044 s) = n)).
