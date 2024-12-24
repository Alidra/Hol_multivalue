Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_TYBIT0_term_abbrevs.
Require Import thm7932146_spec.
Require Import thm7932263_spec.
Lemma lem7932264 {A : Type'} : term0 A.
Proof. exact (EQ_MP (@lem7932263 A) (@lem7932146 A)). Qed.
