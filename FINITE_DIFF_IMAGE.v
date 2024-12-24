Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_DIFF_IMAGE_term_abbrevs.
Require Import thm7673122_spec.
Require Import thm7689527_spec.
Lemma lem7689528 {A B : Type'} : (@UNIV (finite_diff A B)) = (term0 A B).
Proof. exact (EQ_MP (@lem7673122 A B) (@lem7689527 A B)). Qed.
