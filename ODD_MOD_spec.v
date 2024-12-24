Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem202889 : forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd n) = ((Nat.modulo n (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL (BIT1 0))).
