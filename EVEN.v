Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_term_abbrevs.
Require Import thm124233_spec.
Lemma lem124234 : term0.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem124235 : term1 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem124236 : term2.
Proof. exact (conj (@lem124235) (@lem124234)). Qed.
