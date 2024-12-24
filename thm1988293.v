Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988293_term_abbrevs.
Require Import thm1988290_spec.
Lemma lem1988293 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (proj1 (@lem1988290 x y)). Qed.
