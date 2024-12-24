Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111461_term_abbrevs.
Lemma lem1111461 {A : Type'} (s : nat -> A) : (term0 A s) = ((term1 A s) = (@nil A)).
Proof. exact (eq_refl (term0 A s)). Qed.
