Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARB_term_abbrevs.
Lemma lem4381730 {A : Type'} : (@ARB A) = (term0 A).
Proof. exact (@ARB_def A). Qed.
