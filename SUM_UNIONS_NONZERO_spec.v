Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7188776 : forall {A : Type'}, forall f : A -> real, forall s : (A -> Prop) -> Prop, ((@FINITE (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @FINITE A t) /\ (forall t1 : A -> Prop, forall t2 : A -> Prop, forall x : A, ((@IN (A -> Prop) t1 s) /\ ((@IN (A -> Prop) t2 s) /\ ((~ (t1 = t2)) /\ ((@IN A x t1) /\ (@IN A x t2))))) -> (f x) = (real_of_num (NUMERAL 0))))) -> (@sum A (@UNIONS A s) f) = (@sum (A -> Prop) s (fun t : A -> Prop => @sum A t f)).
