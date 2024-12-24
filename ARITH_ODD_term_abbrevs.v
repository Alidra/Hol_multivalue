Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0)) /\ (((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True))).
