Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513550 : (forall n : nat, (Nat.pred (NUMERAL n)) = (NUMERAL (Nat.pred n))) /\ (((Nat.pred 0) = 0) /\ ((forall n : nat, (Nat.pred (BIT0 n)) = (@COND nat (n = 0) 0 (BIT1 (Nat.pred n)))) /\ (forall n : nat, (Nat.pred (BIT1 n)) = (BIT0 n)))).
