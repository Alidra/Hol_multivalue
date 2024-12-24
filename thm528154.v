Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528154_term_abbrevs.
Require Import thm528111_spec.
Lemma lem528153 : term0.
Proof. exact (proj1 (@lem528111)). Qed.
Lemma lem528154 (n : nat) : term1 n.
Proof. exact (@lem528153 n). Qed.
