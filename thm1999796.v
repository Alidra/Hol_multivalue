Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1999796_term_abbrevs.
Lemma lem1999796 (x : real) (y : real) : ((real_lt x y) = (term0 x y)) = ((real_lt x y) = (term0 x y)).
Proof. exact (eq_refl ((real_lt x y) = (term0 x y))). Qed.
