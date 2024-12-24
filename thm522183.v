Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522183_term_abbrevs.
Require Import LEFT_SUB_DISTRIB_spec.
Lemma lem522177 (m : nat) : term0 m.
Proof. exact (@lem137035 m). Qed.
Lemma lem522178 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem522179 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem522178 m) (@lem522177 m)). Qed.
Lemma lem522180 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem522179 m n). Qed.
Lemma lem522181 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem522182 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem522181 n m) (@lem522180 m n)). Qed.
Lemma lem522183 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem522182 n m p). Qed.
