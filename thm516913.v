Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7_spec.
Lemma lem516913 (n : nat) : (Peano.le 0 n) = ((Peano.le 0 n) = True).
Proof. exact (@lem7 (Peano.le 0 n)). Qed.
