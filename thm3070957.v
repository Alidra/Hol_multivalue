Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070957_term_abbrevs.
Require Import thm2954598_spec.
Lemma lem3070957 (m : nat) (n : nat) : (term0 m n) = (((int_of_num m) = (int_of_num n)) = ((term1 m) = (term1 n))).
Proof. exact (@lem2954598 (((int_of_num m) = (int_of_num n)) = ((term1 m) = (term1 n)))). Qed.
