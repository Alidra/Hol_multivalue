Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032081_spec.
Lemma lem1032084 (rx : nat) (lx : nat) : (Nat.mul lx rx) = (Nat.mul rx lx).
Proof. exact (proj1 (@lem1032081 rx lx (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
