Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NEUTRAL_REAL_ADD_term_abbrevs.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Lemma lem7065438 : (@neutral real real_add) = term0.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
