Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_SUC_term_abbrevs.
Require Import thm0_spec.
Require Import thm513079_spec.
Lemma lem513080 : term0.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
