Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm715612_term_abbrevs.
Require Import thm715537_spec.
Require Import thm715538_spec.
Lemma lem715611 (n : nat) : (term0 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem715538 n) (@lem715537 n)). Qed.
Lemma lem715612 : term1 = term2.
Proof. exact (@lem715611 (BIT1 0)). Qed.
