Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1344310_term_abbrevs.
Require Import thm1344307_spec.
Lemma lem1344309 : term0.
Proof. exact (proj1 (@lem1344307)). Qed.
Lemma lem1344310 (x : real) : term1 x.
Proof. exact (@lem1344309 x). Qed.
