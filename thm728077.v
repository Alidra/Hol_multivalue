Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm728077_term_abbrevs.
Require Import thm728071_spec.
Lemma lem728076 : term0.
Proof. exact (proj1 (@lem728071)). Qed.
Lemma lem728077 (n : nat) : term1 n.
Proof. exact (@lem728076 n). Qed.
