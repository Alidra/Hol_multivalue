Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515641_term_abbrevs.
Lemma lem515641 (n : nat) (m : nat) (p : nat) : (term0 n m p) = ((term1 m n p) = (term2 n m p)).
Proof. exact (eq_refl (term0 n m p)). Qed.
