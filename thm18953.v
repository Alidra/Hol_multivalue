Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18953_term_abbrevs.
Lemma lem18953 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = ((term1 A P Q) = (term2 A P Q)).
Proof. exact (eq_refl (term0 A P Q)). Qed.