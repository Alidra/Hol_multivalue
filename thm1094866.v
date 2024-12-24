Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1094866_term_abbrevs.
Lemma lem1094866 {A : Type'} (t : list A) (h : A) : (term0 A t h) = ((term1 A h t) = h).
Proof. exact (eq_refl (term0 A t h)). Qed.
