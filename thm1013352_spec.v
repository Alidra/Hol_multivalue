Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1013352 : forall (m : nat) (p : nat) (n : nat) (h1 : (S (Nat.add m p)) = n), ((NUMERAL n) = (NUMERAL p)) = False.
