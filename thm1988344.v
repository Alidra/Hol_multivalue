Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988344_term_abbrevs.
Require Import thm1988342_spec.
Lemma lem1988344 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1988342 x y)). Qed.
