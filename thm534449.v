Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm534449_term_abbrevs.
Require Import thm534447_spec.
Lemma lem534448 : term0.
Proof. exact (proj2 (@lem534447)). Qed.
Lemma lem534449 (n : nat) : term1 n.
Proof. exact (@lem534448 n). Qed.
