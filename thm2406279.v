Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406279_term_abbrevs.
Require Import thm2406276_spec.
Lemma lem2406279 (m : nat) (n : nat) : (term0 n m) = (int_of_num n).
Proof. exact (proj1 (@lem2406276 m n)). Qed.
