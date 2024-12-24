Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1053103 : forall b : Prop, forall x : nat, (NUMSUM b x) = (@COND nat b (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x)).
