Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522116_term_abbrevs.
Require Import LEFT_ADD_DISTRIB_spec.
Lemma lem522110 (m : nat) : term0 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem522111 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem522112 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem522111 m) (@lem522110 m)). Qed.
Lemma lem522113 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem522112 m n). Qed.
Lemma lem522114 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem522115 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem522114 n m) (@lem522113 m n)). Qed.
Lemma lem522116 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem522115 n m p). Qed.
