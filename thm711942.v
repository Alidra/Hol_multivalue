Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm711942_term_abbrevs.
Require Import thm711940_spec.
Lemma lem711941 : term0.
Proof. exact (proj2 (@lem711940)). Qed.
Lemma lem711942 (n : nat) : term1 n.
Proof. exact (@lem711941 n). Qed.
