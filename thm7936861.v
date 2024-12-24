Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7936861_term_abbrevs.
Require Import DIMINDEX_CLAUSES_spec.
Lemma lem7936861 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem7933204 A)). Qed.
