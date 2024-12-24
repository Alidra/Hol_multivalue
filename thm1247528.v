Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247528_term_abbrevs.
Lemma lem1247528 (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (term0 n d' d) = (Nat.add n d'')) : (term0 n d' d) = (Nat.add n d'').
Proof. exact (h1). Qed.
