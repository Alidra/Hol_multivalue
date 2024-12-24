Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247430_term_abbrevs.
Lemma lem1247430 (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (term0 p d d' d'')) : p = (term0 p d d' d'').
Proof. exact (h1). Qed.
