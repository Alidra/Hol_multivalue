Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400782_term_abbrevs.
Lemma lem5400782 (m : nat) (p : nat) (n : nat) : (term0 m n p) = ((term1 p m n) = (term2 m p n)).
Proof. exact (eq_refl (term0 m n p)). Qed.
