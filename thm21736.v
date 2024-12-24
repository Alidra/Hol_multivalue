Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21736_term_abbrevs.
Lemma lem21736 {A : Type'} (t : Prop) : (term0 A t) = ((term1 A t) = t).
Proof. exact (eq_refl (term0 A t)). Qed.
