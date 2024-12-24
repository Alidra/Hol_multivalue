Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7209759 : forall {A : Type'}, forall R : real -> real -> Prop, forall f : A -> real, forall g : A -> real, forall s : A -> Prop, ((forall m : real, forall n : real, forall m' : real, forall n' : real, ((R m n) /\ (R m' n')) -> R (real_add m m') (real_add n n')) /\ ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ (forall x : A, (@IN A x s) -> R (f x) (g x))))) -> R (@sum A s f) (@sum A s g).
