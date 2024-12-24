Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841413_term_abbrevs.
Require Import thm2841256_spec.
Lemma lem2841410 (m : nat) : term0 m.
Proof. exact (@lem2841256 m). Qed.
Lemma lem2841411 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2841412 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2841411 m) (@lem2841410 m)). Qed.
Lemma lem2841413 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2841412 m n). Qed.
