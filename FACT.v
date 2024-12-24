Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FACT_term_abbrevs.
Require Import thm146107_spec.
Lemma lem146108 : term0.
Proof. exact (proj2 (@lem146107)). Qed.
Lemma lem146109 : term1 = term2.
Proof. exact (proj1 (@lem146107)). Qed.
Lemma lem146110 : term3.
Proof. exact (conj (@lem146109) (@lem146108)). Qed.
