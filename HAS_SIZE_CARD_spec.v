Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3863852 : forall {_100063 : Type'}, forall s : _100063 -> Prop, forall n : nat, (@HAS_SIZE _100063 s n) -> (@CARD _100063 s) = n.
