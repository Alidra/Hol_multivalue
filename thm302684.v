Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302684_term_abbrevs.
Require Import thm302555_spec.
Require Import thm302556_spec.
Lemma lem302672 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term0 m n p).
Proof. exact (EQ_MP (@lem302556 m n p) (@lem302555 m n p)). Qed.
Lemma lem302673 (m : nat) (n : nat) : ((term1 m) = (term1 n)) = (term2 m n).
Proof. exact (@lem302672 term3 m n). Qed.
Lemma lem302680 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem302681 (m : nat) (n : nat) : ((m = n) = ((term1 m) = (term1 n))) = ((m = n) = (term2 m n)).
Proof. exact (MK_COMB (@lem302680 m n) (@lem302673 m n)). Qed.
Lemma lem302684 (m : nat) (n : nat) : ((m = n) = (term2 m n)) = ((m = n) = ((term1 m) = (term1 n))).
Proof. exact (SYM (@lem302681 m n)). Qed.
