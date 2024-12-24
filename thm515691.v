Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515691_term_abbrevs.
Require Import BIT0_spec.
Lemma lem515691 (n : nat) : term0 n.
Proof. exact (@lem80084 n). Qed.
