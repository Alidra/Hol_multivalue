Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm546218_term_abbrevs.
Require Import thm546185_spec.
Lemma lem546217 : term0.
Proof. exact (proj1 (@lem546185)). Qed.
Lemma lem546218 (n : nat) : term1 n.
Proof. exact (@lem546217 n). Qed.
