Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367767_term_abbrevs.
Require Import thm1367764_spec.
Lemma lem1367767 (m : nat) (n : nat) : (term0 n m) = (term1 n).
Proof. exact (proj1 (@lem1367764 m n)). Qed.
