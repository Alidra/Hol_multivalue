Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7203538 : forall {A : Type'}, forall R : real -> real -> Prop, forall f : A -> real, forall g : A -> real, forall s : A -> Prop, ((R (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ ((forall m : real, forall n : real, forall m' : real, forall n' : real, ((R m n) /\ (R m' n')) -> R (real_add m m') (real_add n n')) /\ ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> R (f x) (g x))))) -> R (@sum A s f) (@sum A s g).
