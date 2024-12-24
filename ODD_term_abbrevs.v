Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := ((Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))).
Definition term0 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term1 := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0).
