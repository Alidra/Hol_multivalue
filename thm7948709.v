Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7948706_spec.
Lemma lem7948709 {A : Type'} (n : nat) : ((@dimindex A (@UNIV A)) = n) = ((@dimindex (tybit1 A) (@UNIV (tybit1 A))) = (BIT1 n)).
Proof. exact (proj1 (@lem7948706 A n)). Qed.
