Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem204487 : forall n : nat, (Nat.modulo n (NUMERAL (BIT0 (BIT1 0)))) = (@COND nat (Coq.Arith.PeanoNat.Nat.Even n) (NUMERAL 0) (NUMERAL (BIT1 0))).
