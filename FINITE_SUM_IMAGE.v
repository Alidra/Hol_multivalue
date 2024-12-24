Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUM_IMAGE_term_abbrevs.
Require Import thm7635341_spec.
Require Import thm7637129_spec.
Lemma lem7637130 {A B : Type'} : (@UNIV (finite_sum A B)) = (term0 A B).
Proof. exact (EQ_MP (@lem7635341 A B) (@lem7637129 A B)). Qed.
