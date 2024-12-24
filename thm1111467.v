Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111467_term_abbrevs.
Lemma lem1111467 {A : Type'} (s : nat -> A) (n : nat) : (term0 A s n) = ((term1 A s n) = (term2 A s n)).
Proof. exact (eq_refl (term0 A s n)). Qed.
