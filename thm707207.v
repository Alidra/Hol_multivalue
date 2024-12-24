Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm707207_term_abbrevs.
Require Import thm546243_spec.
Require Import thm546265_spec.
Lemma lem707207 : term0 = term1.
Proof. exact (TRANS (@lem546243) (@lem546265)). Qed.
