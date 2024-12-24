Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_ABS_term_abbrevs.
Require Import REAL_POW_EQ_ABS_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307967 (n : nat) : term0 n.
Proof. exact (@lem1653544 n). Qed.
Lemma lem2307968 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2307969 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2307968 n) (@lem2307967 n)). Qed.
Lemma lem2307970 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2307969 n (real_of_int x)). Qed.
Lemma lem2307971 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2307972 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2307971 n x) (@lem2307970 n x)). Qed.
Lemma lem2307973 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2307972 n x (real_of_int y)). Qed.
Lemma lem2307974 (n : nat) (x : int) (y : int) : (term4 n x y) = (term5 n x y).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2307975 (n : nat) (x : int) (y : int) : term5 n x y.
Proof. exact (EQ_MP (@lem2307974 n x y) (@lem2307973 n x y)). Qed.
Lemma lem2307977 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307978 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307979 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2307978) (@lem2307977 x n)). Qed.
Lemma lem2307981 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307982 (y : int) (n : nat) : (term6 y n) = (term7 y n).
Proof. exact (@lem2307981 y n). Qed.
Lemma lem2307983 (x : int) (y : int) (n : nat) : ((term6 x n) = (term6 y n)) = ((term7 x n) = (term7 y n)).
Proof. exact (MK_COMB (@lem2307979 x n) (@lem2307982 y n)). Qed.
Lemma lem2307985 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307986 (x : int) (y : int) (n : nat) : ((term7 x n) = (term7 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (@lem2307985 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2307987 (x : int) (y : int) (n : nat) : ((term6 x n) = (term6 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (TRANS (@lem2307983 x y n) (@lem2307986 x y n)). Qed.
Lemma lem2307988 (n : nat) : (term10 n) = (term10 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem2307989 (x : int) (y : int) (n : nat) : (term11 x y n) = (term12 x y n).
Proof. exact (MK_COMB (@lem2307988 n) (@lem2307987 x y n)). Qed.
Lemma lem2307990 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307991 (x : int) (y : int) (n : nat) : (term13 x y n) = (term14 x y n).
Proof. exact (MK_COMB (@lem2307990) (@lem2307989 x y n)). Qed.
Lemma lem2307993 (x : int) : (term15 x) = (term16 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2307994 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307995 (x : int) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem2307994) (@lem2307993 x)). Qed.
Lemma lem2307997 (x : int) : (term15 x) = (term16 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2307998 (y : int) : (term15 y) = (term16 y).
Proof. exact (@lem2307997 y). Qed.
Lemma lem2307999 (x : int) (y : int) : ((term15 x) = (term15 y)) = ((term16 x) = (term16 y)).
Proof. exact (MK_COMB (@lem2307995 x) (@lem2307998 y)). Qed.
Lemma lem2308001 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308002 (x : int) (y : int) : ((term16 x) = (term16 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (@lem2308001 (int_abs x) (int_abs y)). Qed.
Lemma lem2308003 (x : int) (y : int) : ((term15 x) = (term15 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (TRANS (@lem2307999 x y) (@lem2308002 x y)). Qed.
Lemma lem2308004 (n : nat) (x : int) (y : int) : (term5 n x y) = (term19 n x y).
Proof. exact (MK_COMB (@lem2307991 x y n) (@lem2308003 x y)). Qed.
Lemma lem2308005 (n : nat) (x : int) (y : int) : term19 n x y.
Proof. exact (EQ_MP (@lem2308004 n x y) (@lem2307975 n x y)). Qed.
Lemma lem2308006 (n : nat) (x : int) : term20 n x.
Proof. exact (fun y : int => @lem2308005 n x y). Qed.
Lemma lem2308007 (n : nat) : term21 n.
Proof. exact (fun x : int => @lem2308006 n x). Qed.
Lemma lem2308008 : term22.
Proof. exact (fun n : nat => @lem2308007 n). Qed.
