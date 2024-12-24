Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem204779 : (forall n : nat, (Nat.div (Nat.mul (NUMERAL (BIT0 (BIT1 0))) n) (NUMERAL (BIT0 (BIT1 0)))) = n) /\ (forall n : nat, (Nat.div (Nat.mul n (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = n).
