Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032092_term_abbrevs.
Require Import thm1032089_spec.
Lemma lem1032092 (a : nat) (b : nat) (c : nat) : (term0 a b c) = (term1 a b c).
Proof. exact (proj1 (@lem1032089 b a c (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
