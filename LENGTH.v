Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LENGTH_term_abbrevs.
Require Import thm1097080_spec.
Lemma lem1097081 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1097082 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1097083 {A : Type'} : term1 A.
Proof. exact (conj (@lem1097082 A) (@lem1097081 A)). Qed.
