Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247513_term_abbrevs.
Lemma lem1247513 (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (term0 n d' d d'')) : n = (term0 n d' d d'').
Proof. exact (h1). Qed.
