Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20682_term_abbrevs.
Lemma lem20682 (b : Prop) (a : Prop) : ((a \/ b) = (term0 b a)) = ((a \/ b) = (term0 b a)).
Proof. exact (eq_refl ((a \/ b) = (term0 b a))). Qed.
