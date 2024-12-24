Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365106_term_abbrevs.
Require Import thm1365074_spec.
Require Import thm1365083_spec.
Lemma lem1365106 : term0.
Proof. exact (conj (@lem1365074) (@lem1365083)). Qed.
