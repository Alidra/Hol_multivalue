Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246909_term_abbrevs.
Lemma lem1246909 (m : nat) (n : nat) : (term0 m n) = ((Peano.le n m) = (term1 m n)).
Proof. exact (eq_refl (term0 m n)). Qed.