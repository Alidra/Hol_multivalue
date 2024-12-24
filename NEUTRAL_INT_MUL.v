Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NEUTRAL_INT_MUL_term_abbrevs.
Require Import thm6904637_spec.
Require Import thm6905935_spec.
Lemma lem6905936 : (@neutral int int_mul) = term0.
Proof. exact (EQ_MP (@lem6904637) (@lem6905935)). Qed.
