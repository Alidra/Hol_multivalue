Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070926_term_abbrevs.
Lemma lem3070926 (x : int) : (term0 x) = ((term1 x) = (int_abs x)).
Proof. exact (eq_refl (term0 x)). Qed.
