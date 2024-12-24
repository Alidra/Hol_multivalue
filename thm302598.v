Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302598_term_abbrevs.
Require Import BIT0_spec.
Lemma lem302586 (n : nat) : term0 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem302587 (n : nat) : (term0 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem302590 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem302587 n) (@lem302586 n)). Qed.
Lemma lem302591 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem302590 m). Qed.
Lemma lem302592 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem302593 (m : nat) : (term1 m) = (term2 m).
Proof. exact (MK_COMB (@lem302592) (@lem302591 m)). Qed.
Lemma lem302594 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem302595 (m : nat) (n : nat) : ((BIT0 m) = (term3 n)) = ((Nat.add m m) = (term3 n)).
Proof. exact (MK_COMB (@lem302593 m) (@lem302594 n)). Qed.
Lemma lem302596 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem302597 (m : nat) (n : nat) : ((m = n) = ((BIT0 m) = (term3 n))) = ((m = n) = ((Nat.add m m) = (term3 n))).
Proof. exact (MK_COMB (@lem302596 m n) (@lem302595 m n)). Qed.
Lemma lem302598 (m : nat) (n : nat) : ((m = n) = ((Nat.add m m) = (term3 n))) = ((m = n) = ((BIT0 m) = (term3 n))).
Proof. exact (SYM (@lem302597 m n)). Qed.
