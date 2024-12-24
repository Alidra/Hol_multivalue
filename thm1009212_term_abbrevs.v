Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (NUMERAL x0) (NUMERAL x1)).
Definition term1 (x0 : nat) := Nat.pow (NUMERAL x0).
Definition term0 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term4 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := Nat.pow (NUMERAL x0) (NUMERAL x1).
