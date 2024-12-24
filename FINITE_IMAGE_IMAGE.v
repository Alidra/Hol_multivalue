Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_IMAGE_term_abbrevs.
Require Import thm7603578_spec.
Require Import thm7604549_spec.
Lemma lem7604550 {A : Type'} : (@UNIV (finite_image A)) = (term0 A).
Proof. exact (EQ_MP (@lem7603578 A) (@lem7604549 A)). Qed.
