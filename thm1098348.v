Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098348_term_abbrevs.
Lemma lem1098348 {A : Type'} (h : A) (t : list A) : (term0 A h t) = ((term1 A h t) = (term2 A h t)).
Proof. exact (eq_refl (term0 A h t)). Qed.
