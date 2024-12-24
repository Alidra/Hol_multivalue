Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7178038 : forall {A B : Type'}, forall d : B -> real, forall i : A -> B, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((i x) = (i y))))) -> (d (i x)) = (real_of_num (NUMERAL 0)))) -> (@sum B (@IMAGE A B i s) d) = (@sum A s (@o A B real d i)).
