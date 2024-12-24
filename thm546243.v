Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm546243_term_abbrevs.
Require Import thm546214_spec.
Require Import thm546215_spec.
Lemma lem546242 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem546215 m n) (@lem546214 m n)). Qed.
Lemma lem546243 : term2 = term3.
Proof. exact (@lem546242 term4 (BIT1 0)). Qed.
