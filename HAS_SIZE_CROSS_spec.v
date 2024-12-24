Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4325462 : forall {_103746 _103749 : Type'}, forall s : _103746 -> Prop, forall t : _103749 -> Prop, forall m : nat, forall n : nat, ((@HAS_SIZE _103746 s m) /\ (@HAS_SIZE _103749 t n)) -> @HAS_SIZE (prod _103746 _103749) (@CROSS _103749 _103746 s t) (Nat.mul m n).
