Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem120109 : forall P : nat -> nat -> Prop, ((forall m : nat, P m m) /\ (forall m : nat, forall n : nat, ((Peano.le m n) /\ (P m n)) -> P m (S n))) -> forall m : nat, forall n : nat, (Peano.le m n) -> P m n.
