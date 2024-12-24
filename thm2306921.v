Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306921_term_abbrevs.
Require Import thm2306888_spec.
Require Import thm2306920_spec.
Lemma lem2306921 : term0.
Proof. exact (conj (@lem2306920) (@lem2306888)). Qed.
