Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516724_term_abbrevs.
Require Import thm516702_spec.
Lemma lem516723 : term0.
Proof. exact (proj1 (@lem516702)). Qed.
Lemma lem516724 (n : nat) : term1 n.
Proof. exact (@lem516723 n). Qed.
