Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NEUTRAL_INT_ADD_term_abbrevs.
Require Import thm6914239_spec.
Require Import thm6915505_spec.
Lemma lem6915506 : (@neutral int int_add) = term0.
Proof. exact (EQ_MP (@lem6914239) (@lem6915505)). Qed.
