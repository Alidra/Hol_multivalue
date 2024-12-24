Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_term_abbrevs.
Require Import thm77238_spec.
Lemma lem77239 : term0.
Proof. exact (proj2 (@lem77238)). Qed.
Lemma lem77240 : term1.
Proof. exact (proj1 (@lem77238)). Qed.
Lemma lem77241 : term2.
Proof. exact (conj (@lem77240) (@lem77239)). Qed.
