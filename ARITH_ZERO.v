Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_ZERO_term_abbrevs.
Require Import thm0_spec.
Require Import thm512818_spec.
Lemma lem512819 : term0.
Proof. exact (EQ_MP (@lem512818) (@lem0)). Qed.
