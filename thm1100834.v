Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100834_term_abbrevs.
Require Import thm1100831_spec.
Lemma lem1100833 {_25307 : Type'} : term0 _25307.
Proof. exact (proj1 (@lem1100831 _25307)). Qed.
Lemma lem1100834 {_25307 : Type'} (P : _25307 -> Prop) : term1 _25307 P.
Proof. exact (@lem1100833 _25307 P). Qed.
