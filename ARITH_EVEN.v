Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_EVEN_term_abbrevs.
Require Import thm0_spec.
Require Import thm516372_spec.
Lemma lem516373 : term0.
Proof. exact (EQ_MP (@lem516372) (@lem0)). Qed.
