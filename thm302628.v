Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302628_term_abbrevs.
Require Import thm302568_spec.
Require Import thm302569_spec.
Lemma lem302616 (n : nat) : (Nat.add n n) = (term0 n).
Proof. exact (EQ_MP (@lem302569 n) (@lem302568 n)). Qed.
Lemma lem302617 (m : nat) : (Nat.add m m) = (term0 m).
Proof. exact (@lem302616 m). Qed.
Lemma lem302618 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem302619 (m : nat) : (term1 m) = (term2 m).
Proof. exact (MK_COMB (@lem302618) (@lem302617 m)). Qed.
Lemma lem302620 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem302621 (m : nat) (n : nat) : ((Nat.add m m) = (term0 n)) = ((term0 m) = (term0 n)).
Proof. exact (MK_COMB (@lem302619 m) (@lem302620 n)). Qed.
Lemma lem302624 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem302625 (m : nat) (n : nat) : ((m = n) = ((Nat.add m m) = (term0 n))) = ((m = n) = ((term0 m) = (term0 n))).
Proof. exact (MK_COMB (@lem302624 m n) (@lem302621 m n)). Qed.
Lemma lem302628 (m : nat) (n : nat) : ((m = n) = ((term0 m) = (term0 n))) = ((m = n) = ((Nat.add m m) = (term0 n))).
Proof. exact (SYM (@lem302625 m n)). Qed.
