Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302789_term_abbrevs.
Require Import thm302598_spec.
Require Import thm302784_spec.
Lemma lem302789 (m : nat) (n : nat) : (m = n) = ((BIT0 m) = (term0 n)).
Proof. exact (EQ_MP (@lem302598 m n) (@lem302784 m n)). Qed.
