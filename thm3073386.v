Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3073386_term_abbrevs.
Lemma lem3073386 (m : nat) (n : nat) : (term0 m n) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (eq_refl (term0 m n)). Qed.