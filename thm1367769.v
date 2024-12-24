Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367769_term_abbrevs.
Require Import thm1367766_spec.
Lemma lem1367769 (m : nat) (n : nat) : (term0 n m) = (real_of_num n).
Proof. exact (proj1 (@lem1367766 m n)). Qed.
