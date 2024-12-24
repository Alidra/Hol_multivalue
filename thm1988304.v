Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988304_term_abbrevs.
Require Import thm1988302_spec.
Lemma lem1988304 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1988302 x y)). Qed.
