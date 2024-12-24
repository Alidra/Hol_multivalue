Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515640_term_abbrevs.
Require Import EXP_ADD_spec.
Lemma lem515634 (m : nat) : term0 m.
Proof. exact (@lem87724 m). Qed.
Lemma lem515635 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem515636 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem515635 m) (@lem515634 m)). Qed.
Lemma lem515637 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem515636 m n). Qed.
Lemma lem515638 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem515639 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem515638 n m) (@lem515637 m n)). Qed.
Lemma lem515640 (n : nat) (m : nat) (p : nat) : term4 n m p.
Proof. exact (@lem515639 n m p). Qed.
