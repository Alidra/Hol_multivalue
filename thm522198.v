Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522198_term_abbrevs.
Require Import BIT0_spec.
Lemma lem522198 (n : nat) : term0 n.
Proof. exact (@lem80084 n). Qed.
