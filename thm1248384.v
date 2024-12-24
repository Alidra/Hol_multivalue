Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248384_term_abbrevs.
Lemma lem1248384 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : (term0 m d q) = (term0 m n d')) : (term0 m d q) = (term0 m n d').
Proof. exact (h1). Qed.
