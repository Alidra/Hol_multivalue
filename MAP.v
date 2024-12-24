Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_term_abbrevs.
Require Import thm1097797_spec.
Lemma lem1097798 {A B : Type'} : term0 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1097799 {A B : Type'} : term1 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1097800 {A B : Type'} : term2 A B.
Proof. exact (conj (@lem1097799 A B) (@lem1097798 A B)). Qed.
