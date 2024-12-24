Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3811194 : forall {A B C : Type'}, forall P : A -> Prop, forall R : A -> B -> C -> Prop, ((forall s : A, (P s) -> exists a : B, exists n : C, R s a n) /\ (forall n1 : C, forall n2 : C, forall s : A, forall a1 : B, forall a2 : B, ((R s a1 n1) /\ (R s a2 n2)) -> (a1 = a2) /\ (n1 = n2))) -> exists f : A -> B, forall s : A, forall a : B, (P s) -> (exists n : C, R s a n) = ((f s) = a).
