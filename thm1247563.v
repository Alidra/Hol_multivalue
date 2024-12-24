Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247563_term_abbrevs.
Lemma lem1247563 (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (term0 m d d'')) : (Nat.add m d') = (term0 m d d'').
Proof. exact (h1). Qed.
