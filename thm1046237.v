Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1046237_term_abbrevs.
Lemma lem1046237 (a : nat) (d : nat) (b : nat) (c : nat) : (term0 a b c d) = ((term1 a b c d) = (term2 a d b c)).
Proof. exact (eq_refl (term0 a b c d)). Qed.
