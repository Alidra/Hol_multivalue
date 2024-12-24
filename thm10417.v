Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10417_term_abbrevs.
Lemma lem10417 (t : Prop) : (term0 t) = ((term1 t) = t).
Proof. exact (eq_refl (term0 t)). Qed.
