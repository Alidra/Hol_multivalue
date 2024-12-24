Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x0 x1).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x1 x2)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (S (Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 x2))))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 (S x2))))) = (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := S (Nat.add x0 (Nat.add x1 (Nat.add x1 x2))).
Definition term7 (x0 : nat) (x1 : nat) := S (Nat.add x0 (Nat.add x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 (S x2))))) = (NUMERAL 0)) -> False.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 (S x2)))).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (S (Nat.add x1 (Nat.add x1 x2))).
Definition term5 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x0 (S x1)).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (S (Nat.add x0 (Nat.add x1 (Nat.add x1 x2)))).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 (Nat.add x1 (S x2))).
Definition term6 (x0 : nat) (x1 : nat) := Nat.add x0 (S (Nat.add x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := S (Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 x2)))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 (S x2))))).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x0 (Nat.add x1 (Nat.add x1 x2))).
