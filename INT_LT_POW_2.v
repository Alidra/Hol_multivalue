Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_POW_2_term_abbrevs.
Require Import REAL_LT_POW_2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2304661 (x : int) : term0 x.
Proof. exact (@lem1647411 (real_of_int x)). Qed.
Lemma lem2304662 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304663 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2304662 x) (@lem2304661 x)). Qed.
Lemma lem2304665 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304666 : term4 = term5.
Proof. exact (@lem2304665 (NUMERAL 0)). Qed.
Lemma lem2304667 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304668 : term6 = term7.
Proof. exact (MK_COMB (@lem2304667) (@lem2304666)). Qed.
Lemma lem2304670 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2304671 (x : int) : (term10 x) = (term11 x).
Proof. exact (@lem2304670 x term12). Qed.
Lemma lem2304672 (x : int) : (term1 x) = (term13 x).
Proof. exact (MK_COMB (@lem2304668) (@lem2304671 x)). Qed.
Lemma lem2304674 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304675 (x : int) : (term13 x) = (term15 x).
Proof. exact (@lem2304674 term16 (term17 x)). Qed.
Lemma lem2304676 (x : int) : (term1 x) = (term15 x).
Proof. exact (TRANS (@lem2304672 x) (@lem2304675 x)). Qed.
Lemma lem2304677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304678 (x : int) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem2304677) (@lem2304676 x)). Qed.
Lemma lem2304680 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304681 : term4 = term5.
Proof. exact (@lem2304680 (NUMERAL 0)). Qed.
Lemma lem2304682 (x : int) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2304683 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term5).
Proof. exact (MK_COMB (@lem2304682 x) (@lem2304681)). Qed.
Lemma lem2304685 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2304686 (x : int) : ((real_of_int x) = term5) = (x = term16).
Proof. exact (@lem2304685 x term16). Qed.
Lemma lem2304687 (x : int) : ((real_of_int x) = term4) = (x = term16).
Proof. exact (TRANS (@lem2304683 x) (@lem2304686 x)). Qed.
Lemma lem2304688 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2304689 (x : int) : (term2 x) = (term21 x).
Proof. exact (MK_COMB (@lem2304688) (@lem2304687 x)). Qed.
Lemma lem2304690 (x : int) : ((term1 x) = (term2 x)) = ((term15 x) = (term21 x)).
Proof. exact (MK_COMB (@lem2304678 x) (@lem2304689 x)). Qed.
Lemma lem2304691 (x : int) : (term15 x) = (term21 x).
Proof. exact (EQ_MP (@lem2304690 x) (@lem2304663 x)). Qed.
Lemma lem2304692 : term22.
Proof. exact (fun x : int => @lem2304691 x). Qed.
