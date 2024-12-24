Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_SUB_term_abbrevs.
Require Import thm522778_spec.
Require Import thm523589_spec.
Lemma lem523590 : term0.
Proof. exact (EQ_MP (@lem522778) (@lem523589)). Qed.
