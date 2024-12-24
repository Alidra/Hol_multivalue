Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032059_spec.
Lemma lem1032062 (b : nat) (a : nat) : (Nat.mul a b) = (Nat.mul b a).
Proof. exact (proj1 (@lem1032059 (@el nat) (@el nat) (@el nat) (@el nat) b a (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat) (@el nat))). Qed.
