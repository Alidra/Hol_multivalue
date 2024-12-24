Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18392_term_abbrevs.
Require Import thm17991_spec.
Require Import thm18041_spec.
Lemma lem18392 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem17991 A P) (@lem18041 A P)). Qed.
