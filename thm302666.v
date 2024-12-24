Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302666_term_abbrevs.
Require Import thm302568_spec.
Require Import thm302569_spec.
Require Import thm302577_spec.
Require Import thm302578_spec.
Require Import thm302580_spec.
Require Import thm302581_spec.
Lemma lem302636 (m : nat) : (S m) = (term0 m).
Proof. exact (EQ_MP (@lem302581 m) (@lem302580 m)). Qed.
Lemma lem302637 (m : nat) : (term1 m) = (term2 m).
Proof. exact (@lem302636 (Nat.add m m)). Qed.
Lemma lem302641 (n : nat) : (Nat.add n n) = (term3 n).
Proof. exact (EQ_MP (@lem302569 n) (@lem302568 n)). Qed.
Lemma lem302642 (m : nat) : (Nat.add m m) = (term3 m).
Proof. exact (@lem302641 m). Qed.
Lemma lem302643 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem302644 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem302643) (@lem302642 m)). Qed.
Lemma lem302645 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem302646 (m : nat) : (term2 m) = (term7 m).
Proof. exact (MK_COMB (@lem302644 m) (@lem302645)). Qed.
Lemma lem302649 (m : nat) : (term1 m) = (term7 m).
Proof. exact (TRANS (@lem302637 m) (@lem302646 m)). Qed.
Lemma lem302650 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem302651 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem302650) (@lem302649 m)). Qed.
Lemma lem302654 (n : nat) : (term7 n) = (term7 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem302655 (m : nat) (n : nat) : ((term1 m) = (term7 n)) = ((term7 m) = (term7 n)).
Proof. exact (MK_COMB (@lem302651 m) (@lem302654 n)). Qed.
Lemma lem302657 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem302578 p m n) (@lem302577 m n p)). Qed.
Lemma lem302658 (m : nat) (n : nat) : ((term7 m) = (term7 n)) = ((term3 m) = (term3 n)).
Proof. exact (@lem302657 term6 (term3 m) (term3 n)). Qed.
Lemma lem302661 (m : nat) (n : nat) : ((term1 m) = (term7 n)) = ((term3 m) = (term3 n)).
Proof. exact (TRANS (@lem302655 m n) (@lem302658 m n)). Qed.
Lemma lem302662 (m : nat) (n : nat) : (term10 m n) = (term10 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem302663 (m : nat) (n : nat) : ((m = n) = ((term1 m) = (term7 n))) = ((m = n) = ((term3 m) = (term3 n))).
Proof. exact (MK_COMB (@lem302662 m n) (@lem302661 m n)). Qed.
Lemma lem302666 (m : nat) (n : nat) : ((m = n) = ((term3 m) = (term3 n))) = ((m = n) = ((term1 m) = (term7 n))).
Proof. exact (SYM (@lem302663 m n)). Qed.
