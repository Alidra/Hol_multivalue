Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367765_term_abbrevs.
Require Import thm1367762_spec.
Lemma lem1367765 (m : nat) (n : nat) : (term0 m n) = (real_of_num n).
Proof. exact (proj1 (@lem1367762 m n)). Qed.
