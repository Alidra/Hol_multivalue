Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3867912 : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s (S n)) = ((~ (s = (@EMPTY A))) /\ (forall a : A, (@IN A a s) -> @HAS_SIZE A (@DELETE A s a) n)).
