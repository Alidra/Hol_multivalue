Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_SQUARE_ABS_term_abbrevs.
Require Import REAL_LE_SQUARE_ABS_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303299 (x : int) : term0 x.
Proof. exact (@lem1645868 (real_of_int x)). Qed.
Lemma lem2303300 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303301 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303300 x) (@lem2303299 x)). Qed.
Lemma lem2303302 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303301 x (real_of_int y)). Qed.
Lemma lem2303303 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303304 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2303303 x y) (@lem2303302 x y)). Qed.
Lemma lem2303306 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2303307 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303308 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2303307) (@lem2303306 x)). Qed.
Lemma lem2303310 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2303311 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2303310 y). Qed.
Lemma lem2303312 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2303308 x) (@lem2303311 y)). Qed.
Lemma lem2303314 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303315 (x : int) (y : int) : (term9 x y) = (term11 x y).
Proof. exact (@lem2303314 (int_abs x) (int_abs y)). Qed.
Lemma lem2303316 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2303312 x y) (@lem2303315 x y)). Qed.
Lemma lem2303317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303318 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2303317) (@lem2303316 x y)). Qed.
Lemma lem2303320 (x : int) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2303321 (x : int) : (term16 x) = (term17 x).
Proof. exact (@lem2303320 x term18). Qed.
Lemma lem2303322 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303323 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2303322) (@lem2303321 x)). Qed.
Lemma lem2303325 (x : int) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2303326 (y : int) : (term16 y) = (term17 y).
Proof. exact (@lem2303325 y term18). Qed.
Lemma lem2303327 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2303323 x) (@lem2303326 y)). Qed.
Lemma lem2303329 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303330 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2303329 (term23 x) (term23 y)). Qed.
Lemma lem2303331 (x : int) (y : int) : (term4 x y) = (term22 x y).
Proof. exact (TRANS (@lem2303327 x y) (@lem2303330 x y)). Qed.
Lemma lem2303332 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term22 x y)).
Proof. exact (MK_COMB (@lem2303318 x y) (@lem2303331 x y)). Qed.
Lemma lem2303333 (x : int) (y : int) : (term11 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2303332 x y) (@lem2303304 x y)). Qed.
Lemma lem2303334 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2303333 x y). Qed.
Lemma lem2303335 : term25.
Proof. exact (fun x : int => @lem2303334 x). Qed.
