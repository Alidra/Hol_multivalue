Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3807377 : forall {A B : Type'}, forall f : A -> B -> B, forall b : B, (forall x : A, forall y : A, forall s : B, (~ (x = y)) -> (f x (f y s)) = (f y (f x s))) -> forall n1 : nat, forall n2 : nat, forall s : A -> Prop, forall a1 : B, forall a2 : B, ((@FINREC A B f b s a1 n1) /\ (@FINREC A B f b s a2 n2)) -> (a1 = a2) /\ (n1 = n2).
