Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302536_term_abbrevs.
Require Import thm82_spec.
Lemma lem302536 (n : nat) : term0 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
