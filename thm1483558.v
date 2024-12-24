Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483558_term_abbrevs.
Require Import thm1483556_spec.
Lemma lem1483558 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1483556 x y)). Qed.
