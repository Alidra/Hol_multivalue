Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_ZERO_term_abbrevs.
Require Import REAL_POW_ZERO_spec.
Require Import thm2299672_spec.
Require Import thm2299871_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308911 (n : nat) : term0 n.
Proof. exact (@lem1648695 n). Qed.
Lemma lem2308912 (n : nat) : (term0 n) = ((term1 n) = (term2 n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308913 (n : nat) : (term1 n) = (term2 n).
Proof. exact (EQ_MP (@lem2308912 n) (@lem2308911 n)). Qed.
Lemma lem2308915 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308916 : term4 = term5.
Proof. exact (@lem2308915 (NUMERAL 0)). Qed.
Lemma lem2308917 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem2308918 : term6 = term7.
Proof. exact (MK_COMB (@lem2308917) (@lem2308916)). Qed.
Lemma lem2308919 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2308920 (n : nat) : (term1 n) = (term8 n).
Proof. exact (MK_COMB (@lem2308918) (@lem2308919 n)). Qed.
Lemma lem2308922 (x : int) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308923 (n : nat) : (term8 n) = (term11 n).
Proof. exact (@lem2308922 term12 n). Qed.
Lemma lem2308924 (n : nat) : (term1 n) = (term11 n).
Proof. exact (TRANS (@lem2308920 n) (@lem2308923 n)). Qed.
Lemma lem2308925 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308926 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem2308925) (@lem2308924 n)). Qed.
Lemma lem2308928 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308929 : term15 = term16.
Proof. exact (@lem2308928 term17). Qed.
Lemma lem2308930 (n : nat) : (term18 n) = (term18 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem2308931 (n : nat) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem2308930 n) (@lem2308929)). Qed.
Lemma lem2308933 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308934 : term4 = term5.
Proof. exact (@lem2308933 (NUMERAL 0)). Qed.
Lemma lem2308935 (n : nat) : (term2 n) = (term21 n).
Proof. exact (MK_COMB (@lem2308931 n) (@lem2308934)). Qed.
Lemma lem2308937 (b : Prop) (x : int) (y : int) : (term22 b x y) = (term23 b x y).
Proof. exact (EQ_MP (@lem2299871 b x y) (@lem2299672 b x y)). Qed.
Lemma lem2308938 (n : nat) : (term21 n) = (term24 n).
Proof. exact (@lem2308937 (n = (NUMERAL 0)) term25 term12). Qed.
Lemma lem2308939 (n : nat) : (term2 n) = (term24 n).
Proof. exact (TRANS (@lem2308935 n) (@lem2308938 n)). Qed.
Lemma lem2308940 (n : nat) : ((term1 n) = (term2 n)) = ((term11 n) = (term24 n)).
Proof. exact (MK_COMB (@lem2308926 n) (@lem2308939 n)). Qed.
Lemma lem2308942 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308943 (n : nat) : ((term11 n) = (term24 n)) = ((term26 n) = (term27 n)).
Proof. exact (@lem2308942 (term26 n) (term27 n)). Qed.
Lemma lem2308944 (n : nat) : ((term1 n) = (term2 n)) = ((term26 n) = (term27 n)).
Proof. exact (TRANS (@lem2308940 n) (@lem2308943 n)). Qed.
Lemma lem2308945 (n : nat) : (term26 n) = (term27 n).
Proof. exact (EQ_MP (@lem2308944 n) (@lem2308913 n)). Qed.
Lemma lem2308946 : term28.
Proof. exact (fun n : nat => @lem2308945 n). Qed.
