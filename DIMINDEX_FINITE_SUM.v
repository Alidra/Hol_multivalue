Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_FINITE_SUM_term_abbrevs.
Require Import thm7640410_spec.
Require Import thm7640437_spec.
Lemma lem7640438 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term0 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
