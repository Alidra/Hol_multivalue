Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_2_term_abbrevs.
Require Import BIT0_THM_spec.
Require Import MULT_CLAUSES_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem84914 (m : nat) : term0 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem84915 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem84916 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem84915 m) (@lem84914 m)). Qed.
Lemma lem84917 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem84916 m n). Qed.
Lemma lem84918 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem84919 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem84918 m n) (@lem84917 m n)). Qed.
Lemma lem84920 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem84919 m n p). Qed.
Lemma lem84921 (m : nat) (n : nat) (p : nat) : (term4 m n p) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem84923 : term7.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem84924 : term8.
Proof. exact (proj2 (@lem84923)). Qed.
Lemma lem84945 : term9.
Proof. exact (proj1 (@lem84924)). Qed.
Lemma lem84946 (n : nat) : term10 n.
Proof. exact (@lem84945 n). Qed.
Lemma lem84947 (n : nat) : (term10 n) = ((term11 n) = n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem84957 (n : nat) : term12 n.
Proof. exact (@lem80165 n). Qed.
Lemma lem84958 (n : nat) : (term12 n) = ((term13 n) = (term14 n)).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem84963 (n : nat) : (term13 n) = (term14 n).
Proof. exact (EQ_MP (@lem84958 n) (@lem84957 n)). Qed.
Lemma lem84964 : term15 = term16.
Proof. exact (@lem84963 (BIT1 0)). Qed.
Lemma lem84965 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem84966 : term17 = term18.
Proof. exact (MK_COMB (@lem84965) (@lem84964)). Qed.
Lemma lem84967 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem84968 (n : nat) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem84966) (@lem84967 n)). Qed.
Lemma lem84970 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem84921 m n p) (@lem84920 m n p)). Qed.
Lemma lem84971 (n : nat) : (term20 n) = (term21 n).
Proof. exact (@lem84970 term22 term22 n). Qed.
Lemma lem84973 (n : nat) : (term11 n) = n.
Proof. exact (EQ_MP (@lem84947 n) (@lem84946 n)). Qed.
Lemma lem84974 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem84975 (n : nat) : (term23 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem84974) (@lem84973 n)). Qed.
Lemma lem84977 (n : nat) : (term11 n) = n.
Proof. exact (EQ_MP (@lem84947 n) (@lem84946 n)). Qed.
Lemma lem84978 (n : nat) : (term21 n) = (Nat.add n n).
Proof. exact (MK_COMB (@lem84975 n) (@lem84977 n)). Qed.
Lemma lem84979 (n : nat) : (term20 n) = (Nat.add n n).
Proof. exact (TRANS (@lem84971 n) (@lem84978 n)). Qed.
Lemma lem84980 (n : nat) : (term19 n) = (Nat.add n n).
Proof. exact (TRANS (@lem84968 n) (@lem84979 n)). Qed.
Lemma lem84981 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem84982 (n : nat) : (term24 n) = (term25 n).
Proof. exact (MK_COMB (@lem84981) (@lem84980 n)). Qed.
Lemma lem84983 (n : nat) : (Nat.add n n) = (Nat.add n n).
Proof. exact (eq_refl (Nat.add n n)). Qed.
Lemma lem84984 (n : nat) : ((term19 n) = (Nat.add n n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (MK_COMB (@lem84982 n) (@lem84983 n)). Qed.
Lemma lem84986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem84987 (x : nat) : (x = x) = True.
Proof. exact (@lem84986 nat x). Qed.
Lemma lem84988 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem84987 (Nat.add n n)). Qed.
Lemma lem84989 (n : nat) : ((term19 n) = (Nat.add n n)) = True.
Proof. exact (TRANS (@lem84984 n) (@lem84988 n)). Qed.
Lemma lem84990 (n : nat) : True = ((term19 n) = (Nat.add n n)).
Proof. exact (SYM (@lem84989 n)). Qed.
Lemma lem84991 (n : nat) : (term19 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem84990 n) (@lem0)). Qed.
Lemma lem84996 : term26.
Proof. exact (fun n : nat => @lem84991 n). Qed.
