Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNIQUE_DEF_term_abbrevs.
Lemma lem99 {A : Type'} : (@ex1 A) = (term0 A).
Proof. exact (@ex1_def A). Qed.