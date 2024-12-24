Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009213_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009212_spec.
Lemma lem1009213 (m : nat) (n : nat) : (term0 m n) = (Nat.pow m n).
Proof. exact (EQ_MP (@lem1009212 m n) (@lem0)). Qed.
