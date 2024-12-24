Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161353_term_abbrevs.
Require Import thm159134_spec.
Require Import thm159245_spec.
Require Import thm161351_spec.
Lemma lem161353 (n : nat) (m : nat) : (term0 m n) = m.
Proof. exact (or_elim (@lem159134 n) (fun h0 : n = (NUMERAL 0) => @lem159245 m n h0) (fun h0 : term1 n => @lem161351 m n h0)). Qed.
