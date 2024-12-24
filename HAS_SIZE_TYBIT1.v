Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_TYBIT1_term_abbrevs.
Require Import thm7932948_spec.
Require Import thm7933086_spec.
Lemma lem7933087 {A : Type'} : term0 A.
Proof. exact (EQ_MP (@lem7933086 A) (@lem7932948 A)). Qed.
