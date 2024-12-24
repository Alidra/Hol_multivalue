Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm707079_term_abbrevs.
Require Import thm538319_spec.
Require Import thm538330_spec.
Lemma lem707079 : term0 = term1.
Proof. exact (TRANS (@lem538319) (@lem538330)). Qed.
