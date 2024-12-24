Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111462_term_abbrevs.
Require Import thm1111460_spec.
Require Import thm1111461_spec.
Lemma lem1111462 {A : Type'} (s : nat -> A) : (term0 A s) = (@nil A).
Proof. exact (EQ_MP (@lem1111461 A s) (@lem1111460 A s)). Qed.
