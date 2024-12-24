Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4626359 : forall s : nat -> Prop, (@FINITE nat s) -> exists a : nat, ~ (@IN nat a s).
