Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_1_LT_term_abbrevs.
Require Import REAL_POW_1_LT_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2307674 (n : nat) : term0 n.
Proof. exact (@lem1638553 n). Qed.
Lemma lem2307675 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2307676 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2307675 n) (@lem2307674 n)). Qed.
Lemma lem2307677 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2307676 n (real_of_int x)). Qed.
Lemma lem2307678 (x : int) (n : nat) : (term2 n x) = (term3 x n).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2307679 (x : int) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem2307678 x n) (@lem2307677 n x)). Qed.
Lemma lem2307681 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307682 : term5 = term6.
Proof. exact (@lem2307681 (NUMERAL 0)). Qed.
Lemma lem2307683 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307684 : term7 = term8.
Proof. exact (MK_COMB (@lem2307683) (@lem2307682)). Qed.
Lemma lem2307685 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2307686 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2307684) (@lem2307685 x)). Qed.
Lemma lem2307688 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307689 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2307688 term13 x). Qed.
Lemma lem2307690 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2307686 x) (@lem2307689 x)). Qed.
Lemma lem2307691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2307692 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2307691) (@lem2307690 x)). Qed.
Lemma lem2307694 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307695 : term16 = term17.
Proof. exact (@lem2307694 term18). Qed.
Lemma lem2307696 (x : int) : (term19 x) = (term19 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2307697 (x : int) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem2307696 x) (@lem2307695)). Qed.
Lemma lem2307699 (x : int) (y : int) : (term22 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2307700 (x : int) : (term21 x) = (term23 x).
Proof. exact (@lem2307699 x term24). Qed.
Lemma lem2307701 (x : int) : (term20 x) = (term23 x).
Proof. exact (TRANS (@lem2307697 x) (@lem2307700 x)). Qed.
Lemma lem2307702 (x : int) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem2307692 x) (@lem2307701 x)). Qed.
Lemma lem2307703 (n : nat) : (term27 n) = (term27 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem2307704 (n : nat) (x : int) : (term28 n x) = (term29 n x).
Proof. exact (MK_COMB (@lem2307703 n) (@lem2307702 x)). Qed.
Lemma lem2307705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307706 (n : nat) (x : int) : (term30 n x) = (term31 n x).
Proof. exact (MK_COMB (@lem2307705) (@lem2307704 n x)). Qed.
Lemma lem2307708 (x : int) (n : nat) : (term32 x n) = (term33 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307709 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2307710 (x : int) (n : nat) : (term34 x n) = (term35 x n).
Proof. exact (MK_COMB (@lem2307709) (@lem2307708 x n)). Qed.
Lemma lem2307712 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307713 : term16 = term17.
Proof. exact (@lem2307712 term18). Qed.
Lemma lem2307714 (x : int) (n : nat) : (term36 x n) = (term37 x n).
Proof. exact (MK_COMB (@lem2307710 x n) (@lem2307713)). Qed.
Lemma lem2307716 (x : int) (y : int) : (term22 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2307717 (x : int) (n : nat) : (term37 x n) = (term38 x n).
Proof. exact (@lem2307716 (int_pow x n) term24). Qed.
Lemma lem2307718 (x : int) (n : nat) : (term36 x n) = (term38 x n).
Proof. exact (TRANS (@lem2307714 x n) (@lem2307717 x n)). Qed.
Lemma lem2307719 (x : int) (n : nat) : (term3 x n) = (term39 x n).
Proof. exact (MK_COMB (@lem2307706 n x) (@lem2307718 x n)). Qed.
Lemma lem2307720 (x : int) (n : nat) : term39 x n.
Proof. exact (EQ_MP (@lem2307719 x n) (@lem2307679 x n)). Qed.
Lemma lem2307721 (n : nat) : term40 n.
Proof. exact (fun x : int => @lem2307720 x n). Qed.
Lemma lem2307722 : term41.
Proof. exact (fun n : nat => @lem2307721 n). Qed.
