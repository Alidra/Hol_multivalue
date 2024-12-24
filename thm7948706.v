Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7948706_term_abbrevs.
Require Import thm7948704_spec.
Lemma lem7948706 {A : Type'} (n : nat) : term0 A n.
Proof. exact (proj2 (@lem7948704 A n)). Qed.
