Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447307_term_abbrevs.
Lemma lem2447307 (x : int) (y : int) (n : int) : (term0 x y n) = ((term1 x y n) = (term2 x y n)).
Proof. exact (eq_refl (term0 x y n)). Qed.
