Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_MUL_term_abbrevs.
Require Import REAL_POW_MUL_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308729 (x : int) : term0 x.
Proof. exact (@lem1595570 (real_of_int x)). Qed.
Lemma lem2308730 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308731 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2308730 x) (@lem2308729 x)). Qed.
Lemma lem2308732 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2308731 x (real_of_int y)). Qed.
Lemma lem2308733 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2308734 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2308733 x y) (@lem2308732 x y)). Qed.
Lemma lem2308735 (x : int) (y : int) (n : nat) : term4 x y n.
Proof. exact (@lem2308734 x y n). Qed.
Lemma lem2308736 (x : int) (y : int) (n : nat) : (term4 x y n) = ((term5 x y n) = (term6 x y n)).
Proof. exact (eq_refl (term4 x y n)). Qed.
Lemma lem2308737 (x : int) (y : int) (n : nat) : (term5 x y n) = (term6 x y n).
Proof. exact (EQ_MP (@lem2308736 x y n) (@lem2308735 x y n)). Qed.
Lemma lem2308739 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2308740 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2308741 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2308740) (@lem2308739 x y)). Qed.
Lemma lem2308742 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2308743 (x : int) (y : int) (n : nat) : (term5 x y n) = (term11 x y n).
Proof. exact (MK_COMB (@lem2308741 x y) (@lem2308742 n)). Qed.
Lemma lem2308745 (x : int) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308746 (x : int) (y : int) (n : nat) : (term11 x y n) = (term14 x y n).
Proof. exact (@lem2308745 (int_mul x y) n). Qed.
Lemma lem2308747 (x : int) (y : int) (n : nat) : (term5 x y n) = (term14 x y n).
Proof. exact (TRANS (@lem2308743 x y n) (@lem2308746 x y n)). Qed.
Lemma lem2308748 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308749 (x : int) (y : int) (n : nat) : (term15 x y n) = (term16 x y n).
Proof. exact (MK_COMB (@lem2308748) (@lem2308747 x y n)). Qed.
Lemma lem2308751 (x : int) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2308753 (x : int) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (MK_COMB (@lem2308752) (@lem2308751 x n)). Qed.
Lemma lem2308755 (x : int) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308756 (y : int) (n : nat) : (term12 y n) = (term13 y n).
Proof. exact (@lem2308755 y n). Qed.
Lemma lem2308757 (x : int) (y : int) (n : nat) : (term6 x y n) = (term19 x y n).
Proof. exact (MK_COMB (@lem2308753 x n) (@lem2308756 y n)). Qed.
Lemma lem2308759 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2308760 (x : int) (y : int) (n : nat) : (term19 x y n) = (term20 x y n).
Proof. exact (@lem2308759 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308761 (x : int) (y : int) (n : nat) : (term6 x y n) = (term20 x y n).
Proof. exact (TRANS (@lem2308757 x y n) (@lem2308760 x y n)). Qed.
Lemma lem2308762 (x : int) (y : int) (n : nat) : ((term5 x y n) = (term6 x y n)) = ((term14 x y n) = (term20 x y n)).
Proof. exact (MK_COMB (@lem2308749 x y n) (@lem2308761 x y n)). Qed.
Lemma lem2308764 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308765 (x : int) (y : int) (n : nat) : ((term14 x y n) = (term20 x y n)) = ((term21 x y n) = (term22 x y n)).
Proof. exact (@lem2308764 (term21 x y n) (term22 x y n)). Qed.
Lemma lem2308766 (x : int) (y : int) (n : nat) : ((term5 x y n) = (term6 x y n)) = ((term21 x y n) = (term22 x y n)).
Proof. exact (TRANS (@lem2308762 x y n) (@lem2308765 x y n)). Qed.
Lemma lem2308767 (x : int) (y : int) (n : nat) : (term21 x y n) = (term22 x y n).
Proof. exact (EQ_MP (@lem2308766 x y n) (@lem2308737 x y n)). Qed.
Lemma lem2308768 (x : int) (y : int) : term23 x y.
Proof. exact (fun n : nat => @lem2308767 x y n). Qed.
Lemma lem2308769 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2308768 x y). Qed.
Lemma lem2308770 : term25.
Proof. exact (fun x : int => @lem2308769 x). Qed.
