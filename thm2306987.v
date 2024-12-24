Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306987_term_abbrevs.
Require Import thm2306954_spec.
Require Import thm2306986_spec.
Lemma lem2306987 : term0.
Proof. exact (conj (@lem2306986) (@lem2306954)). Qed.
