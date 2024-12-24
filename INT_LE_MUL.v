Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_MUL_term_abbrevs.
Require Import thm1340049_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302698 (x : int) : term0 x.
Proof. exact (@lem1340049 (real_of_int x)). Qed.
Lemma lem2302699 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302700 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302699 x) (@lem2302698 x)). Qed.
Lemma lem2302701 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302700 x (real_of_int y)). Qed.
Lemma lem2302702 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302703 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302702 x y) (@lem2302701 x y)). Qed.
Lemma lem2302705 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302706 : term5 = term6.
Proof. exact (@lem2302705 (NUMERAL 0)). Qed.
Lemma lem2302707 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302708 : term7 = term8.
Proof. exact (MK_COMB (@lem2302707) (@lem2302706)). Qed.
Lemma lem2302709 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302710 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2302708) (@lem2302709 x)). Qed.
Lemma lem2302712 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302713 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2302712 term13 x). Qed.
Lemma lem2302714 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2302710 x) (@lem2302713 x)). Qed.
Lemma lem2302715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302716 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2302715) (@lem2302714 x)). Qed.
Lemma lem2302718 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302719 : term5 = term6.
Proof. exact (@lem2302718 (NUMERAL 0)). Qed.
Lemma lem2302720 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302721 : term7 = term8.
Proof. exact (MK_COMB (@lem2302720) (@lem2302719)). Qed.
Lemma lem2302722 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302723 (y : int) : (term9 y) = (term10 y).
Proof. exact (MK_COMB (@lem2302721) (@lem2302722 y)). Qed.
Lemma lem2302725 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302726 (y : int) : (term10 y) = (term12 y).
Proof. exact (@lem2302725 term13 y). Qed.
Lemma lem2302727 (y : int) : (term9 y) = (term12 y).
Proof. exact (TRANS (@lem2302723 y) (@lem2302726 y)). Qed.
Lemma lem2302728 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2302716 x) (@lem2302727 y)). Qed.
Lemma lem2302729 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302730 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2302729) (@lem2302728 x y)). Qed.
Lemma lem2302732 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302733 : term5 = term6.
Proof. exact (@lem2302732 (NUMERAL 0)). Qed.
Lemma lem2302734 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302735 : term7 = term8.
Proof. exact (MK_COMB (@lem2302734) (@lem2302733)). Qed.
Lemma lem2302737 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302738 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2302735) (@lem2302737 x y)). Qed.
Lemma lem2302740 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302741 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (@lem2302740 term13 (int_mul x y)). Qed.
Lemma lem2302742 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (TRANS (@lem2302738 x y) (@lem2302741 x y)). Qed.
Lemma lem2302743 (x : int) (y : int) : (term3 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2302730 x y) (@lem2302742 x y)). Qed.
Lemma lem2302744 (x : int) (y : int) : term25 x y.
Proof. exact (EQ_MP (@lem2302743 x y) (@lem2302703 x y)). Qed.
Lemma lem2302745 (x : int) : term26 x.
Proof. exact (fun y : int => @lem2302744 x y). Qed.
Lemma lem2302746 : term27.
Proof. exact (fun x : int => @lem2302745 x). Qed.
