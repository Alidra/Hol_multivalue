Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538319_term_abbrevs.
Require Import thm538290_spec.
Require Import thm538291_spec.
Lemma lem538318 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem538291 m n) (@lem538290 m n)). Qed.
Lemma lem538319 : term2 = term3.
Proof. exact (@lem538318 term4 (BIT1 0)). Qed.
