Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841384_term_abbrevs.
Lemma lem2841384 (m : nat) (n : nat) : (term0 m n) = ((term1 m n) = (term2 m n)).
Proof. exact (eq_refl (term0 m n)). Qed.
