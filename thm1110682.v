Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110682_term_abbrevs.
Lemma lem1110682 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term0 A h r t) = ((term1 A r h t) = (term2 A h r t)).
Proof. exact (eq_refl (term0 A h r t)). Qed.
