Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528207_term_abbrevs.
Require Import thm528202_spec.
Lemma lem528203 : term0.
Proof. exact (proj2 (@lem528202)). Qed.
Lemma lem528204 (m : nat) : term1 m.
Proof. exact (@lem528203 m). Qed.
Lemma lem528205 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem528206 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem528205 m) (@lem528204 m)). Qed.
Lemma lem528207 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem528206 m n). Qed.
