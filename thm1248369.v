Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248369_term_abbrevs.
Lemma lem1248369 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : (Nat.add m n) = (term0 m d q d')) : (Nat.add m n) = (term0 m d q d').
Proof. exact (h1). Qed.
