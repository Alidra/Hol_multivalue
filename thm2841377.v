Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841377_term_abbrevs.
Require Import thm2841336_spec.
Lemma lem2841377 (k : nat) (n : nat) : term0 k n.
Proof. exact (@lem2841336 k n). Qed.
