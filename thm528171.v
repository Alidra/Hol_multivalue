Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528171_term_abbrevs.
Require Import thm528128_spec.
Require Import thm528129_spec.
Lemma lem528170 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem528129 m n) (@lem528128 m n)). Qed.
Lemma lem528171 : term2 = term3.
Proof. exact (@lem528170 0 (BIT1 0)). Qed.
