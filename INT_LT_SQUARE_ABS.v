Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_SQUARE_ABS_term_abbrevs.
Require Import REAL_LT_SQUARE_ABS_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304934 (x : int) : term0 x.
Proof. exact (@lem1645942 (real_of_int x)). Qed.
Lemma lem2304935 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304936 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304935 x) (@lem2304934 x)). Qed.
Lemma lem2304937 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304936 x (real_of_int y)). Qed.
Lemma lem2304938 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304939 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2304938 x y) (@lem2304937 x y)). Qed.
Lemma lem2304941 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2304942 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304943 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2304942) (@lem2304941 x)). Qed.
Lemma lem2304945 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2304946 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2304945 y). Qed.
Lemma lem2304947 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2304943 x) (@lem2304946 y)). Qed.
Lemma lem2304949 (x : int) (y : int) : (term10 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304950 (x : int) (y : int) : (term9 x y) = (term11 x y).
Proof. exact (@lem2304949 (int_abs x) (int_abs y)). Qed.
Lemma lem2304951 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2304947 x y) (@lem2304950 x y)). Qed.
Lemma lem2304952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304953 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2304952) (@lem2304951 x y)). Qed.
Lemma lem2304955 (x : int) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2304956 (x : int) : (term16 x) = (term17 x).
Proof. exact (@lem2304955 x term18). Qed.
Lemma lem2304957 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304958 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2304957) (@lem2304956 x)). Qed.
Lemma lem2304960 (x : int) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2304961 (y : int) : (term16 y) = (term17 y).
Proof. exact (@lem2304960 y term18). Qed.
Lemma lem2304962 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2304958 x) (@lem2304961 y)). Qed.
Lemma lem2304964 (x : int) (y : int) : (term10 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304965 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2304964 (term23 x) (term23 y)). Qed.
Lemma lem2304966 (x : int) (y : int) : (term4 x y) = (term22 x y).
Proof. exact (TRANS (@lem2304962 x y) (@lem2304965 x y)). Qed.
Lemma lem2304967 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term22 x y)).
Proof. exact (MK_COMB (@lem2304953 x y) (@lem2304966 x y)). Qed.
Lemma lem2304968 (x : int) (y : int) : (term11 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2304967 x y) (@lem2304939 x y)). Qed.
Lemma lem2304969 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2304968 x y). Qed.
Lemma lem2304970 : term25.
Proof. exact (fun x : int => @lem2304969 x). Qed.
