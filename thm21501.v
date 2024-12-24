Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21501_term_abbrevs.
Lemma lem21501 (b : Prop) (a : Prop) : (term0 b a) = (term0 b a).
Proof. exact (eq_refl (term0 b a)). Qed.
