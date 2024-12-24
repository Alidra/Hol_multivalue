Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0.
