Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17935_term_abbrevs.
Lemma lem17935 {A : Type'} (y : A) (x : A) : (term0 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term0 A x y)). Qed.
