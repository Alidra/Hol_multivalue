Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm707091_term_abbrevs.
Require Import thm538911_spec.
Require Import thm538928_spec.
Lemma lem707091 : term0 = term1.
Proof. exact (TRANS (@lem538911) (@lem538928)). Qed.
