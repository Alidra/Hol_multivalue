Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1052447_term_abbrevs.
Lemma lem1052447 : NUMFST = term0.
Proof. exact (@NUMFST_def). Qed.
