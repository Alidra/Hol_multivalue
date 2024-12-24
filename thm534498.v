Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm534498_term_abbrevs.
Require Import thm534465_spec.
Lemma lem534497 : term0.
Proof. exact (proj1 (@lem534465)). Qed.
Lemma lem534498 (n : nat) : term1 n.
Proof. exact (@lem534497 n). Qed.
