Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117502_term_abbrevs.
Lemma lem3117502 (x : nat) (y : nat) (n : nat) : (term0 x y n) = ((term1 x y n) = (term2 x y n)).
Proof. exact (eq_refl (term0 x y n)). Qed.
