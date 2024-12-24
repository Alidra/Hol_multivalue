Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm70521_term_abbrevs.
Lemma lem70521 : IND_SUC = term0.
Proof. exact (@IND_SUC_def). Qed.
