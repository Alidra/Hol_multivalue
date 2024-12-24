Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338106_term_abbrevs.
Lemma lem1338106 (P : real -> Prop) : (term0 P) = ((term1 P) = (term2 P)).
Proof. exact (eq_refl (term0 P)). Qed.
