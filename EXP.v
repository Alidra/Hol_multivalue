Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_term_abbrevs.
Require Import thm86199_spec.
Lemma lem86200 : term0.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem86201 : term1.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem86202 : term2.
Proof. exact (conj (@lem86201) (@lem86200)). Qed.
