Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_term_abbrevs.
Lemma lem3185621 {A : Type'} : (@EMPTY A) = (term0 A).
Proof. exact (@EMPTY_def A). Qed.
