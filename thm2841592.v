Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841592_term_abbrevs.
Lemma lem2841592 (n : nat) : (term0 n) = ((term1 n) = (real_of_num n)).
Proof. exact (eq_refl (term0 n)). Qed.
