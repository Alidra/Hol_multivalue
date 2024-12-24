Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318542_term_abbrevs.
Lemma lem2318542 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
