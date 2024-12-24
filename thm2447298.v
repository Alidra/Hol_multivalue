Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447298_term_abbrevs.
Lemma lem2447298 (b : int) (a : int) : (term0 b a) = ((int_divides a b) = (term1 b a)).
Proof. exact (eq_refl (term0 b a)). Qed.
