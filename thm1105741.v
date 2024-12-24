Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105741_term_abbrevs.
Require Import thm1105738_spec.
Lemma lem1105740 {_25569 : Type'} : term0 _25569.
Proof. exact (proj1 (@lem1105738 _25569)). Qed.
Lemma lem1105741 {_25569 : Type'} (l : list _25569) : term1 _25569 l.
Proof. exact (@lem1105740 _25569 l). Qed.
