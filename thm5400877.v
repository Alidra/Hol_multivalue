Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400877_term_abbrevs.
Lemma lem5400877 (m : nat) (n : nat) (h1 : term0 m n) : term0 m n.
Proof. exact (h1). Qed.
