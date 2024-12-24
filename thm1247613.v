Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247613_term_abbrevs.
Lemma lem1247613 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : (Nat.add m n) = (term0 p q d)) : (Nat.add m n) = (term0 p q d).
Proof. exact (h1). Qed.
