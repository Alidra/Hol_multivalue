Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841622_term_abbrevs.
Lemma lem2841622 (x : int) (y : int) : (term0 x y) = ((x = y) = ((real_of_int x) = (real_of_int y))).
Proof. exact (eq_refl (term0 x y)). Qed.
