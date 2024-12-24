Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483584_term_abbrevs.
Require Import thm1483582_spec.
Lemma lem1483584 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1483582 x y)). Qed.
