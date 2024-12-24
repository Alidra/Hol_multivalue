Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem201634 : forall n : nat, (Coq.Arith.PeanoNat.Nat.Even n) = ((Nat.modulo n (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
