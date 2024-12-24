Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_term_abbrevs.
Require Import REAL_POW_EQ_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307776 (n : nat) : term0 n.
Proof. exact (@lem1653383 n). Qed.
Lemma lem2307777 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2307778 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2307777 n) (@lem2307776 n)). Qed.
Lemma lem2307779 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2307778 n (real_of_int x)). Qed.
Lemma lem2307780 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2307781 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2307780 n x) (@lem2307779 n x)). Qed.
Lemma lem2307782 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2307781 n x (real_of_int y)). Qed.
Lemma lem2307783 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2307784 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2307783 n x y) (@lem2307782 n x y)). Qed.
Lemma lem2307786 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307787 : term7 = term8.
Proof. exact (@lem2307786 (NUMERAL 0)). Qed.
Lemma lem2307788 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307789 : term9 = term10.
Proof. exact (MK_COMB (@lem2307788) (@lem2307787)). Qed.
Lemma lem2307790 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2307791 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2307789) (@lem2307790 x)). Qed.
Lemma lem2307793 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307794 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2307793 term15 x). Qed.
Lemma lem2307795 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2307791 x) (@lem2307794 x)). Qed.
Lemma lem2307796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2307797 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2307796) (@lem2307795 x)). Qed.
Lemma lem2307799 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307800 : term7 = term8.
Proof. exact (@lem2307799 (NUMERAL 0)). Qed.
Lemma lem2307801 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307802 : term9 = term10.
Proof. exact (MK_COMB (@lem2307801) (@lem2307800)). Qed.
Lemma lem2307803 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2307804 (y : int) : (term11 y) = (term12 y).
Proof. exact (MK_COMB (@lem2307802) (@lem2307803 y)). Qed.
Lemma lem2307806 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307807 (y : int) : (term12 y) = (term14 y).
Proof. exact (@lem2307806 term15 y). Qed.
Lemma lem2307808 (y : int) : (term11 y) = (term14 y).
Proof. exact (TRANS (@lem2307804 y) (@lem2307807 y)). Qed.
Lemma lem2307809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2307810 (y : int) : (term16 y) = (term17 y).
Proof. exact (MK_COMB (@lem2307809) (@lem2307808 y)). Qed.
Lemma lem2307812 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307813 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307814 (x : int) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (MK_COMB (@lem2307813) (@lem2307812 x n)). Qed.
Lemma lem2307816 (x : int) (n : nat) : (term18 x n) = (term19 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307817 (y : int) (n : nat) : (term18 y n) = (term19 y n).
Proof. exact (@lem2307816 y n). Qed.
Lemma lem2307818 (x : int) (y : int) (n : nat) : ((term18 x n) = (term18 y n)) = ((term19 x n) = (term19 y n)).
Proof. exact (MK_COMB (@lem2307814 x n) (@lem2307817 y n)). Qed.
Lemma lem2307820 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307821 (x : int) (y : int) (n : nat) : ((term19 x n) = (term19 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (@lem2307820 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2307822 (x : int) (y : int) (n : nat) : ((term18 x n) = (term18 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (TRANS (@lem2307818 x y n) (@lem2307821 x y n)). Qed.
Lemma lem2307823 (x : int) (y : int) (n : nat) : (term22 x y n) = (term23 x y n).
Proof. exact (MK_COMB (@lem2307810 y) (@lem2307822 x y n)). Qed.
Lemma lem2307824 (x : int) (y : int) (n : nat) : (term24 x y n) = (term25 x y n).
Proof. exact (MK_COMB (@lem2307797 x) (@lem2307823 x y n)). Qed.
Lemma lem2307825 (n : nat) : (term26 n) = (term26 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem2307826 (x : int) (y : int) (n : nat) : (term27 x y n) = (term28 x y n).
Proof. exact (MK_COMB (@lem2307825 n) (@lem2307824 x y n)). Qed.
Lemma lem2307827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307828 (x : int) (y : int) (n : nat) : (term29 x y n) = (term30 x y n).
Proof. exact (MK_COMB (@lem2307827) (@lem2307826 x y n)). Qed.
Lemma lem2307830 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307831 (n : nat) (x : int) (y : int) : (term5 n x y) = (term31 n x y).
Proof. exact (MK_COMB (@lem2307828 x y n) (@lem2307830 x y)). Qed.
Lemma lem2307832 (n : nat) (x : int) (y : int) : term31 n x y.
Proof. exact (EQ_MP (@lem2307831 n x y) (@lem2307784 n x y)). Qed.
Lemma lem2307833 (n : nat) (x : int) : term32 n x.
Proof. exact (fun y : int => @lem2307832 n x y). Qed.
Lemma lem2307834 (n : nat) : term33 n.
Proof. exact (fun x : int => @lem2307833 n x). Qed.
Lemma lem2307835 : term34.
Proof. exact (fun n : nat => @lem2307834 n). Qed.
