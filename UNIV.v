Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIV_term_abbrevs.
Lemma lem3187417 {A : Type'} : (@UNIV A) = (term0 A).
Proof. exact (@UNIV_def A). Qed.
