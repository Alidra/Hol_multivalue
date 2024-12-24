Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988296_term_abbrevs.
Require Import thm1988294_spec.
Lemma lem1988296 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1988294 x y)). Qed.
