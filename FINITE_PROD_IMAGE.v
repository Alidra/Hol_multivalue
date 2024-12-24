Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_PROD_IMAGE_term_abbrevs.
Require Import thm7919719_spec.
Require Import thm7921507_spec.
Lemma lem7921508 {A B : Type'} : (@UNIV (finite_prod A B)) = (term0 A B).
Proof. exact (EQ_MP (@lem7919719 A B) (@lem7921507 A B)). Qed.
