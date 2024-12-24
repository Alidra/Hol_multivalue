Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term2 := ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term0 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
