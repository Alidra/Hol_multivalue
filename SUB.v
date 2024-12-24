Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_term_abbrevs.
Require Import thm135075_spec.
Lemma lem135076 : term0.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135077 : term1.
Proof. exact (proj1 (@lem135075)). Qed.
Lemma lem135078 : term2.
Proof. exact (conj (@lem135077) (@lem135076)). Qed.
