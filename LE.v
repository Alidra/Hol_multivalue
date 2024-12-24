Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_term_abbrevs.
Require Import thm89498_spec.
Lemma lem89499 : term0.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem89500 : term1.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem89501 : term2.
Proof. exact (conj (@lem89500) (@lem89499)). Qed.
