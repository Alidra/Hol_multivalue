Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_1_IMP_term_abbrevs.
Require Import REAL_POW_EQ_1_IMP_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307929 (x : int) : term0 x.
Proof. exact (@lem1653669 (real_of_int x)). Qed.
Lemma lem2307930 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307931 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2307930 x) (@lem2307929 x)). Qed.
Lemma lem2307932 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2307931 x n). Qed.
Lemma lem2307933 (n : nat) (x : int) : (term2 x n) = (term3 n x).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem2307934 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2307933 n x) (@lem2307932 x n)). Qed.
Lemma lem2307936 (x : int) (n : nat) : (term4 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2307937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307938 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (MK_COMB (@lem2307937) (@lem2307936 x n)). Qed.
Lemma lem2307940 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307941 : term9 = term10.
Proof. exact (@lem2307940 term11). Qed.
Lemma lem2307942 (x : int) (n : nat) : ((term4 x n) = term9) = ((term5 x n) = term10).
Proof. exact (MK_COMB (@lem2307938 x n) (@lem2307941)). Qed.
Lemma lem2307944 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307945 (x : int) (n : nat) : ((term5 x n) = term10) = ((int_pow x n) = term12).
Proof. exact (@lem2307944 (int_pow x n) term12). Qed.
Lemma lem2307946 (x : int) (n : nat) : ((term4 x n) = term9) = ((int_pow x n) = term12).
Proof. exact (TRANS (@lem2307942 x n) (@lem2307945 x n)). Qed.
Lemma lem2307947 (n : nat) : (term13 n) = (term13 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem2307948 (x : int) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem2307947 n) (@lem2307946 x n)). Qed.
Lemma lem2307949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307950 (x : int) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem2307949) (@lem2307948 x n)). Qed.
Lemma lem2307952 (x : int) : (term18 x) = (term19 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2307953 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307954 (x : int) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem2307953) (@lem2307952 x)). Qed.
Lemma lem2307956 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307957 : term9 = term10.
Proof. exact (@lem2307956 term11). Qed.
Lemma lem2307958 (x : int) : ((term18 x) = term9) = ((term19 x) = term10).
Proof. exact (MK_COMB (@lem2307954 x) (@lem2307957)). Qed.
Lemma lem2307960 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307961 (x : int) : ((term19 x) = term10) = ((int_abs x) = term12).
Proof. exact (@lem2307960 (int_abs x) term12). Qed.
Lemma lem2307962 (x : int) : ((term18 x) = term9) = ((int_abs x) = term12).
Proof. exact (TRANS (@lem2307958 x) (@lem2307961 x)). Qed.
Lemma lem2307963 (n : nat) (x : int) : (term3 n x) = (term22 n x).
Proof. exact (MK_COMB (@lem2307950 x n) (@lem2307962 x)). Qed.
Lemma lem2307964 (n : nat) (x : int) : term22 n x.
Proof. exact (EQ_MP (@lem2307963 n x) (@lem2307934 n x)). Qed.
Lemma lem2307965 (x : int) : term23 x.
Proof. exact (fun n : nat => @lem2307964 n x). Qed.
Lemma lem2307966 : term24.
Proof. exact (fun x : int => @lem2307965 x). Qed.
