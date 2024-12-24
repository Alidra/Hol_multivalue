Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302782_term_abbrevs.
Require Import thm302684_spec.
Require Import thm302741_spec.
Lemma lem302782 (m : nat) (n : nat) : (m = n) = ((term0 m) = (term0 n)).
Proof. exact (EQ_MP (@lem302684 m n) (@lem302741 m n)). Qed.
