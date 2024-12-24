Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem241861 : forall P : nat -> Prop, forall n : nat, (forall a : nat, (Peano.lt a n) -> P a) = ((n = (NUMERAL 0)) \/ (forall a : nat, P (Nat.modulo a n))).
