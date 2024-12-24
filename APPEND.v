Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import APPEND_term_abbrevs.
Require Import thm1095962_spec.
Lemma lem1095963 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1095964 {A : Type'} : term1 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1095965 {A : Type'} : term2 A.
Proof. exact (conj (@lem1095964 A) (@lem1095963 A)). Qed.
