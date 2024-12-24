Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem184261 : forall m : nat, forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) -> (Nat.modulo (Nat.modulo m n) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo m (NUMERAL (BIT0 (BIT1 0)))).
