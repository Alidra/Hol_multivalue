Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm715537_term_abbrevs.
Require Import thm715530_spec.
Lemma lem715531 : term0.
Proof. exact (proj2 (@lem715530)). Qed.
Lemma lem715536 : term1.
Proof. exact (proj1 (@lem715531)). Qed.
Lemma lem715537 (n : nat) : term2 n.
Proof. exact (@lem715536 n). Qed.
