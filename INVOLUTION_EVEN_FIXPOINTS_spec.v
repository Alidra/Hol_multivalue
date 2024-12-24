Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4292765 : forall {A : Type'}, forall f : A -> A, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> (@IN A (f x) s) /\ ((f (f x)) = x))) -> (Coq.Arith.PeanoNat.Nat.Even (@CARD A (@GSPEC A (fun GEN_PVAR_118 : A => exists x : A, @SETSPEC A GEN_PVAR_118 ((@IN A x s) /\ ((f x) = x)) x)))) = (Coq.Arith.PeanoNat.Nat.Even (@CARD A s)).
