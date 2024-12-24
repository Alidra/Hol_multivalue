Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7948704_spec.
Lemma lem7948707 {A : Type'} (n : nat) : ((@dimindex A (@UNIV A)) = n) = ((@dimindex (tybit0 A) (@UNIV (tybit0 A))) = (BIT0 n)).
Proof. exact (proj1 (@lem7948704 A n)). Qed.
