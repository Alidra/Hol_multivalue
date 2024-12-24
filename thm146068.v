Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm146068_term_abbrevs.
Lemma lem146068 : Factorial.fact = term0.
Proof. exact (@FACT_def). Qed.
