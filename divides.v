Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import divides_term_abbrevs.
Require Import thm3073436_spec.
Require Import thm3074596_spec.
Lemma lem3074597 (b : nat) (a : nat) : (num_divides a b) = (term0 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
