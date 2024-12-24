Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483546_term_abbrevs.
Require Import thm1483544_spec.
Lemma lem1483546 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1483544 x y)). Qed.
