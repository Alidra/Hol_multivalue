Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem128433 : forall n : nat, Coq.Arith.PeanoNat.Nat.Odd (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n)).
