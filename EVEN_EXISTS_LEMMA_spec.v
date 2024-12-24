Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem128768 : forall n : nat, ((Coq.Arith.PeanoNat.Nat.Even n) -> exists m : nat, n = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) m)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even n)) -> exists m : nat, n = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) m))).
