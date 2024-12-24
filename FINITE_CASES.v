Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CASES_term_abbrevs.
Require Import thm3197564_spec.
Lemma lem3197566 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem3197564 A)). Qed.
