Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267745_term_abbrevs.
Lemma lem2267745 (a : int) : (term0 a) = ((term1 a) = a).
Proof. exact (eq_refl (term0 a)). Qed.
