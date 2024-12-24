Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_EQ_term_abbrevs.
Require Import thm521920_spec.
Require Import thm522075_spec.
Lemma lem522076 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
