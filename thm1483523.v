Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483523_term_abbrevs.
Require Import thm1483520_spec.
Lemma lem1483523 (y : real) (x : real) : (real_le x y) = (term0 y x).
Proof. exact (proj1 (@lem1483520 x y)). Qed.
