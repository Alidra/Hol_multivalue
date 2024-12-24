Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988292_term_abbrevs.
Require Import thm1988290_spec.
Lemma lem1988292 (x : real) (y : real) : term0 x y.
Proof. exact (proj2 (@lem1988290 x y)). Qed.
