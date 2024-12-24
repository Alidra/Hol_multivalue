Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import AND_DEF_term_abbrevs.
Lemma lem8 : and = term0.
Proof. exact (@and_def). Qed.
