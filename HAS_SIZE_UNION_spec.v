Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3868180 : forall {_100197 : Type'}, forall s : _100197 -> Prop, forall t : _100197 -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE _100197 s m) /\ ((@HAS_SIZE _100197 t n) /\ (@DISJOINT _100197 s t))) -> @HAS_SIZE _100197 (@UNION _100197 s t) (Nat.add m n).
