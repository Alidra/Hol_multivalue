Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_ODD_term_abbrevs.
Require Import thm0_spec.
Require Import thm516555_spec.
Lemma lem516556 : term0.
Proof. exact (EQ_MP (@lem516555) (@lem0)). Qed.
