Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17961_term_abbrevs.
Lemma lem17961 {A : Type'} (P : A -> Prop) : (term0 A P) = ((term1 A P) = (term2 A P)).
Proof. exact (eq_refl (term0 A P)). Qed.
