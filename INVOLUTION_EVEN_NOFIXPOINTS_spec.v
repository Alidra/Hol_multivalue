Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4289223 : forall {A : Type'}, forall f : A -> A, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> (@IN A (f x) s) /\ ((~ ((f x) = x)) /\ ((f (f x)) = x)))) -> Coq.Arith.PeanoNat.Nat.Even (@CARD A s).
