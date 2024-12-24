Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516555 : True = ((forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL n)) = (Coq.Arith.PeanoNat.Nat.Odd n)) /\ (((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ ((forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 n)) = False) /\ (forall n : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 n)) = True)))).
