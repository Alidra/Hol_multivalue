Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMP_DEF_term_abbrevs.
Lemma lem9 : imp = term0.
Proof. exact (@imp_def). Qed.
