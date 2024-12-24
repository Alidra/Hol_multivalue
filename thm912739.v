Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm912739_term_abbrevs.
Require Import thm708946_spec.
Require Import thm708948_spec.
Lemma lem912739 : term0 = (BIT1 0).
Proof. exact (TRANS (@lem708946) (@lem708948)). Qed.
