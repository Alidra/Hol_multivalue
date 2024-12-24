Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302788_term_abbrevs.
Require Import thm302608_spec.
Require Import thm302783_spec.
Lemma lem302788 (m : nat) (n : nat) : (m = n) = ((BIT1 m) = (term0 n)).
Proof. exact (EQ_MP (@lem302608 m n) (@lem302783 m n)). Qed.
