Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528257_term_abbrevs.
Require Import thm528207_spec.
Require Import thm528208_spec.
Lemma lem528256 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem528208 m n) (@lem528207 m n)). Qed.
Lemma lem528257 : term2 = term3.
Proof. exact (@lem528256 0 (BIT1 0)). Qed.
