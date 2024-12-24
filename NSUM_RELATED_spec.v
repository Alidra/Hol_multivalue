Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7034542 : forall {A : Type'}, forall R : nat -> nat -> Prop, forall f : A -> nat, forall g : A -> nat, forall s : A -> Prop, ((R (NUMERAL 0) (NUMERAL 0)) /\ ((forall m : nat, forall n : nat, forall m' : nat, forall n' : nat, ((R m n) /\ (R m' n')) -> R (Nat.add m m') (Nat.add n n')) /\ ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> R (f x) (g x))))) -> R (@nsum A s f) (@nsum A s g).
