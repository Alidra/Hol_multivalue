Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032046_term_abbrevs.
Require Import thm1032044_spec.
Lemma lem1032046 (x : nat) : (term0 x) = x.
Proof. exact (proj1 (@lem1032044 (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) x (@el nat))). Qed.
