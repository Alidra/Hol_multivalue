Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm913187_term_abbrevs.
Require Import thm737721_spec.
Require Import thm737741_spec.
Lemma lem913187 : term0 = term1.
Proof. exact (TRANS (@lem737721) (@lem737741)). Qed.
