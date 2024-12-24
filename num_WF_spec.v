Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem115780 : forall P : nat -> Prop, (forall n : nat, (forall m : nat, (Peano.lt m n) -> P m) -> P n) -> forall n : nat, P n.
