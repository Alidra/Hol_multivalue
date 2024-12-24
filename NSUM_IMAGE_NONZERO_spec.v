Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7017843 : forall {A B : Type'}, forall d : B -> nat, forall i : A -> B, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((i x) = (i y))))) -> (d (i x)) = (NUMERAL 0))) -> (@nsum B (@IMAGE A B i s) d) = (@nsum A s (@o A B nat d i)).
