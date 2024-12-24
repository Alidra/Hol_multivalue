Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302702_term_abbrevs.
Require Import thm302555_spec.
Require Import thm302556_spec.
Lemma lem302690 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term0 m n p).
Proof. exact (EQ_MP (@lem302556 m n p) (@lem302555 m n p)). Qed.
Lemma lem302691 (m : nat) (n : nat) : ((term1 m) = (term1 n)) = (term2 m n).
Proof. exact (@lem302690 term3 m n). Qed.
Lemma lem302698 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem302699 (m : nat) (n : nat) : ((m = n) = ((term1 m) = (term1 n))) = ((m = n) = (term2 m n)).
Proof. exact (MK_COMB (@lem302698 m n) (@lem302691 m n)). Qed.
Lemma lem302702 (m : nat) (n : nat) : ((m = n) = (term2 m n)) = ((m = n) = ((term1 m) = (term1 n))).
Proof. exact (SYM (@lem302699 m n)). Qed.
