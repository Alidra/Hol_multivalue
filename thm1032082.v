Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032082_term_abbrevs.
Require Import thm1032079_spec.
Lemma lem1032082 (lx : nat) (ly : nat) (rx : nat) : (term0 lx ly rx) = (term1 lx ly rx).
Proof. exact (proj1 (@lem1032079 ly rx lx (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
