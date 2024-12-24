Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6898616_term_abbrevs.
Lemma lem6898616 {A : Type'} (P : A -> Prop) (x : A) : (term0 A P x) = (term1 A P x).
Proof. exact (eq_refl (term0 A P x)). Qed.
