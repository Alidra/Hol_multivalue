Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem128828 : forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) = (exists m : nat, n = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) m)).
