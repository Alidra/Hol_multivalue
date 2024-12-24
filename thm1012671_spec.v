Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1012671 : forall (m : nat) (n : nat) (p : nat) (h1 : (S (Nat.add m n)) = p), ((NUMERAL n) = (NUMERAL p)) = False.
