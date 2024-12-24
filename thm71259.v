Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_REP_RULES_spec.
Lemma lem71259 : NUM_REP IND_0.
Proof. exact (proj1 (@lem71256)). Qed.
