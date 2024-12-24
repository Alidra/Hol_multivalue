Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_POW_2_term_abbrevs.
Require Import REAL_LE_POW_2_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303056 (x : int) : term0 x.
Proof. exact (@lem1646060 (real_of_int x)). Qed.
Lemma lem2303057 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303058 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303057 x) (@lem2303056 x)). Qed.
Lemma lem2303060 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303061 : term3 = term4.
Proof. exact (@lem2303060 (NUMERAL 0)). Qed.
Lemma lem2303062 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303063 : term5 = term6.
Proof. exact (MK_COMB (@lem2303062) (@lem2303061)). Qed.
Lemma lem2303065 (x : int) (n : nat) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2303066 (x : int) : (term9 x) = (term10 x).
Proof. exact (@lem2303065 x term11). Qed.
Lemma lem2303067 (x : int) : (term1 x) = (term12 x).
Proof. exact (MK_COMB (@lem2303063) (@lem2303066 x)). Qed.
Lemma lem2303069 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303070 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2303069 term15 (term16 x)). Qed.
Lemma lem2303071 (x : int) : (term1 x) = (term14 x).
Proof. exact (TRANS (@lem2303067 x) (@lem2303070 x)). Qed.
Lemma lem2303072 (x : int) : term14 x.
Proof. exact (EQ_MP (@lem2303071 x) (@lem2303058 x)). Qed.
Lemma lem2303073 : term17.
Proof. exact (fun x : int => @lem2303072 x). Qed.
