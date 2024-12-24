Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FCONS_term_abbrevs.
Require Import thm1066089_spec.
Lemma lem1066090 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1066089 A)). Qed.
Lemma lem1066091 {A : Type'} : term1 A.
Proof. exact (proj1 (@lem1066089 A)). Qed.
Lemma lem1066092 {A : Type'} : term2 A.
Proof. exact (conj (@lem1066091 A) (@lem1066090 A)). Qed.
