Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841383_term_abbrevs.
Require Import thm2841326_spec.
Lemma lem2841380 (m : nat) : term0 m.
Proof. exact (@lem2841326 m). Qed.
Lemma lem2841381 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2841382 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2841381 m) (@lem2841380 m)). Qed.
Lemma lem2841383 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2841382 m n). Qed.
