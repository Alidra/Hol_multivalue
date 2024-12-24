Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637146_term_abbrevs.
Require Import DIMINDEX_UNIV_spec.
Lemma lem7637146 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem7594688 A s). Qed.
