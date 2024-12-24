Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516885_term_abbrevs.
Require Import thm516863_spec.
Lemma lem516885 (n : nat) : term0 n.
Proof. exact (@lem516863 n). Qed.
