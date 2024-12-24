Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm89943_term_abbrevs.
Lemma lem89943 : Peano.lt = term0.
Proof. exact (@lt_def). Qed.
