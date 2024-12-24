Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LET_ADD_term_abbrevs.
Require Import REAL_LET_ADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302005 (x : int) : term0 x.
Proof. exact (@lem1381641 (real_of_int x)). Qed.
Lemma lem2302006 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302007 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302006 x) (@lem2302005 x)). Qed.
Lemma lem2302008 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302007 x (real_of_int y)). Qed.
Lemma lem2302009 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302010 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302009 x y) (@lem2302008 x y)). Qed.
Lemma lem2302012 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302013 : term5 = term6.
Proof. exact (@lem2302012 (NUMERAL 0)). Qed.
Lemma lem2302014 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302015 : term7 = term8.
Proof. exact (MK_COMB (@lem2302014) (@lem2302013)). Qed.
Lemma lem2302016 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302017 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2302015) (@lem2302016 x)). Qed.
Lemma lem2302019 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302020 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2302019 term13 x). Qed.
Lemma lem2302021 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2302017 x) (@lem2302020 x)). Qed.
Lemma lem2302022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302023 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2302022) (@lem2302021 x)). Qed.
Lemma lem2302025 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302026 : term5 = term6.
Proof. exact (@lem2302025 (NUMERAL 0)). Qed.
Lemma lem2302027 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302028 : term16 = term17.
Proof. exact (MK_COMB (@lem2302027) (@lem2302026)). Qed.
Lemma lem2302029 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302030 (y : int) : (term18 y) = (term19 y).
Proof. exact (MK_COMB (@lem2302028) (@lem2302029 y)). Qed.
Lemma lem2302032 (x : int) (y : int) : (term20 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302033 (y : int) : (term19 y) = (term21 y).
Proof. exact (@lem2302032 term13 y). Qed.
Lemma lem2302034 (y : int) : (term18 y) = (term21 y).
Proof. exact (TRANS (@lem2302030 y) (@lem2302033 y)). Qed.
Lemma lem2302035 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2302023 x) (@lem2302034 y)). Qed.
Lemma lem2302036 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302037 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2302036) (@lem2302035 x y)). Qed.
Lemma lem2302039 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302040 : term5 = term6.
Proof. exact (@lem2302039 (NUMERAL 0)). Qed.
Lemma lem2302041 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302042 : term16 = term17.
Proof. exact (MK_COMB (@lem2302041) (@lem2302040)). Qed.
Lemma lem2302044 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302045 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem2302042) (@lem2302044 x y)). Qed.
Lemma lem2302047 (x : int) (y : int) : (term20 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302048 (x : int) (y : int) : (term29 x y) = (term30 x y).
Proof. exact (@lem2302047 term13 (int_add x y)). Qed.
Lemma lem2302049 (x : int) (y : int) : (term28 x y) = (term30 x y).
Proof. exact (TRANS (@lem2302045 x y) (@lem2302048 x y)). Qed.
Lemma lem2302050 (x : int) (y : int) : (term3 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem2302037 x y) (@lem2302049 x y)). Qed.
Lemma lem2302051 (x : int) (y : int) : term31 x y.
Proof. exact (EQ_MP (@lem2302050 x y) (@lem2302010 x y)). Qed.
Lemma lem2302052 (x : int) : term32 x.
Proof. exact (fun y : int => @lem2302051 x y). Qed.
Lemma lem2302053 : term33.
Proof. exact (fun x : int => @lem2302052 x). Qed.
