Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6982957 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, forall b : nat, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ (forall x : A, (@IN A x s) -> Peano.lt (f x) (Nat.div b (@CARD A s))))) -> Peano.lt (@nsum A s f) b.
