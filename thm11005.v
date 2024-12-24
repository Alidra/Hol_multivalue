Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm11005_term_abbrevs.
Require Import thm32_spec.
Lemma lem11005 (P : Prop -> Prop) : (term0 P) = ((term1 P) = (term2 P)).
Proof. exact (@lem32 (term1 P) (term2 P)). Qed.
