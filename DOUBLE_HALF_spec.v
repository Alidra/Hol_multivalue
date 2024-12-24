Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem205347 : (forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.div n (NUMERAL (BIT0 (BIT1 0))))) = n) /\ (forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (Nat.mul (Nat.div n (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL (BIT0 (BIT1 0)))) = n).
