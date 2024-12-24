Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6975627 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> Peano.le (f x) b) /\ (exists x : A, (@IN A x s) /\ (Peano.lt (f x) b)))) -> Peano.lt (@nsum A s f) (Nat.mul (@CARD A s) b).
