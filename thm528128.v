Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528128_term_abbrevs.
Require Import thm528115_spec.
Lemma lem528116 : term0.
Proof. exact (proj2 (@lem528115)). Qed.
Lemma lem528124 : term1.
Proof. exact (proj1 (@lem528116)). Qed.
Lemma lem528125 (m : nat) : term2 m.
Proof. exact (@lem528124 m). Qed.
Lemma lem528126 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem528127 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem528126 m) (@lem528125 m)). Qed.
Lemma lem528128 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem528127 m n). Qed.
