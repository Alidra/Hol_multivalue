Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522132_term_abbrevs.
Lemma lem522132 (n : nat) (m : nat) : (term0 m n) = ((term1 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term0 m n)). Qed.
