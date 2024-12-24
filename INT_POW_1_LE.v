Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_1_LE_term_abbrevs.
Require Import REAL_POW_1_LE_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2307627 (n : nat) : term0 n.
Proof. exact (@lem1636868 n). Qed.
Lemma lem2307628 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2307629 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2307628 n) (@lem2307627 n)). Qed.
Lemma lem2307630 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2307629 n (real_of_int x)). Qed.
Lemma lem2307631 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2307632 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2307631 x n) (@lem2307630 n x)). Qed.
Lemma lem2307634 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307635 : term5 = term6.
Proof. exact (@lem2307634 (NUMERAL 0)). Qed.
Lemma lem2307636 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307637 : term7 = term8.
Proof. exact (MK_COMB (@lem2307636) (@lem2307635)). Qed.
Lemma lem2307638 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2307639 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2307637) (@lem2307638 x)). Qed.
Lemma lem2307641 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307642 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2307641 term13 x). Qed.
Lemma lem2307643 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2307639 x) (@lem2307642 x)). Qed.
Lemma lem2307644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2307645 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2307644) (@lem2307643 x)). Qed.
Lemma lem2307647 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307648 : term16 = term17.
Proof. exact (@lem2307647 term18). Qed.
Lemma lem2307649 (x : int) : (term19 x) = (term19 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2307650 (x : int) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem2307649 x) (@lem2307648)). Qed.
Lemma lem2307652 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307653 (x : int) : (term21 x) = (term22 x).
Proof. exact (@lem2307652 x term23). Qed.
Lemma lem2307654 (x : int) : (term20 x) = (term22 x).
Proof. exact (TRANS (@lem2307650 x) (@lem2307653 x)). Qed.
Lemma lem2307655 (x : int) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem2307645 x) (@lem2307654 x)). Qed.
Lemma lem2307656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307657 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2307656) (@lem2307655 x)). Qed.
Lemma lem2307659 (x : int) (n : nat) : (term28 x n) = (term29 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307660 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307661 (x : int) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (MK_COMB (@lem2307660) (@lem2307659 x n)). Qed.
Lemma lem2307663 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307664 : term16 = term17.
Proof. exact (@lem2307663 term18). Qed.
Lemma lem2307665 (x : int) (n : nat) : (term32 x n) = (term33 x n).
Proof. exact (MK_COMB (@lem2307661 x n) (@lem2307664)). Qed.
Lemma lem2307667 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307668 (x : int) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (@lem2307667 (int_pow x n) term23). Qed.
Lemma lem2307669 (x : int) (n : nat) : (term32 x n) = (term34 x n).
Proof. exact (TRANS (@lem2307665 x n) (@lem2307668 x n)). Qed.
Lemma lem2307670 (x : int) (n : nat) : (term3 x n) = (term35 x n).
Proof. exact (MK_COMB (@lem2307657 x) (@lem2307669 x n)). Qed.
Lemma lem2307671 (x : int) (n : nat) : term35 x n.
Proof. exact (EQ_MP (@lem2307670 x n) (@lem2307632 x n)). Qed.
Lemma lem2307672 (n : nat) : term36 n.
Proof. exact (fun x : int => @lem2307671 x n). Qed.
Lemma lem2307673 : term37.
Proof. exact (fun n : nat => @lem2307672 n). Qed.
