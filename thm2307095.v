Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307095_term_abbrevs.
Require Import thm2307068_spec.
Require Import thm2307094_spec.
Lemma lem2307095 : term0.
Proof. exact (conj (@lem2307094) (@lem2307068)). Qed.
