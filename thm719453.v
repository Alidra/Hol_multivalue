Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm719453_term_abbrevs.
Require Import thm719451_spec.
Lemma lem719452 : term0.
Proof. exact (proj2 (@lem719451)). Qed.
Lemma lem719453 (n : nat) : term1 n.
Proof. exact (@lem719452 n). Qed.
