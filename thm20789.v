Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20789_term_abbrevs.
Lemma lem20789 (a : Prop) (b : Prop) : ((term0 a b) = (term1 a b)) = ((term0 a b) = (term1 a b)).
Proof. exact (eq_refl ((term0 a b) = (term1 a b))). Qed.
