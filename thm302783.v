Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302783_term_abbrevs.
Require Import thm302666_spec.
Require Import thm302781_spec.
Lemma lem302783 (m : nat) (n : nat) : (m = n) = ((term0 m) = (term1 n)).
Proof. exact (EQ_MP (@lem302666 m n) (@lem302781 m n)). Qed.
