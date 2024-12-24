Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1011471 : forall (m : nat) (n : nat) (p : nat) (h1 : (Nat.add m n) = p), (Peano.le (NUMERAL n) (NUMERAL p)) = True.
