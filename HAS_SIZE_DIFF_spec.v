Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3868414 : forall {_100233 : Type'}, forall s : _100233 -> Prop, forall t : _100233 -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE _100233 s m) /\ ((@HAS_SIZE _100233 t n) /\ (@SUBSET _100233 t s))) -> @HAS_SIZE _100233 (@DIFF _100233 s t) (Nat.sub m n).
