Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm159136_term_abbrevs.
Lemma lem159136 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
