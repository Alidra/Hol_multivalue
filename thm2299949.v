Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299949_term_abbrevs.
Lemma lem2299949 (x : int) (y : int) : (term0 x y) = (((real_of_int x) = (real_of_int y)) = (x = y)).
Proof. exact (eq_refl (term0 x y)). Qed.
