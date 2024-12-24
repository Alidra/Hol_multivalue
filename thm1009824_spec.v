Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1009824 : forall (m : nat) (n : nat) (p : nat) (h1 : (S (Nat.add m n)) = p), (Peano.lt (NUMERAL n) (NUMERAL p)) = True.
