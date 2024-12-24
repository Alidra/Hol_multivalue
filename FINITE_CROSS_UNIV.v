Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_CROSS_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm4333669_spec.
Lemma lem4333670 {A B : Type'} : (@FINITE (prod A B) (@UNIV (prod A B))) = (term0 A B).
Proof. exact (EQ_MP (@lem4333669 A B) (@lem0)). Qed.
