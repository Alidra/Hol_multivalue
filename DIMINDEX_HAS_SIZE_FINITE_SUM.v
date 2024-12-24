Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIMINDEX_HAS_SIZE_FINITE_SUM_term_abbrevs.
Require Import thm7637206_spec.
Require Import thm7640378_spec.
Lemma lem7640379 {M N : Type'} : term0 M N.
Proof. exact (EQ_MP (@lem7637206 M N) (@lem7640378 M N)). Qed.
