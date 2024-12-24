Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_MIN_term_abbrevs.
Require Import REAL_MAX_MIN_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305380 (x : int) : term0 x.
Proof. exact (@lem1557027 (real_of_int x)). Qed.
Lemma lem2305381 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305382 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305381 x) (@lem2305380 x)). Qed.
Lemma lem2305383 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305382 x (real_of_int y)). Qed.
Lemma lem2305384 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305385 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2305384 x y) (@lem2305383 x y)). Qed.
Lemma lem2305387 (x : int) (y : int) : (term3 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305388 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305389 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2305388) (@lem2305387 x y)). Qed.
Lemma lem2305391 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305392 : real_min = real_min.
Proof. exact (eq_refl real_min). Qed.
Lemma lem2305393 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2305392) (@lem2305391 x)). Qed.
Lemma lem2305395 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305396 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2305395 y). Qed.
Lemma lem2305397 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2305393 x) (@lem2305396 y)). Qed.
Lemma lem2305399 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305400 (x : int) (y : int) : (term13 x y) = (term16 x y).
Proof. exact (@lem2305399 (int_neg x) (int_neg y)). Qed.
Lemma lem2305401 (x : int) (y : int) : (term12 x y) = (term16 x y).
Proof. exact (TRANS (@lem2305397 x y) (@lem2305400 x y)). Qed.
Lemma lem2305402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2305403 (x : int) (y : int) : (term4 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2305402) (@lem2305401 x y)). Qed.
Lemma lem2305405 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305406 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (@lem2305405 (term19 x y)). Qed.
Lemma lem2305407 (x : int) (y : int) : (term4 x y) = (term18 x y).
Proof. exact (TRANS (@lem2305403 x y) (@lem2305406 x y)). Qed.
Lemma lem2305408 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term5 x y) = (term18 x y)).
Proof. exact (MK_COMB (@lem2305389 x y) (@lem2305407 x y)). Qed.
Lemma lem2305410 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305411 (x : int) (y : int) : ((term5 x y) = (term18 x y)) = ((int_max x y) = (term20 x y)).
Proof. exact (@lem2305410 (int_max x y) (term20 x y)). Qed.
Lemma lem2305412 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((int_max x y) = (term20 x y)).
Proof. exact (TRANS (@lem2305408 x y) (@lem2305411 x y)). Qed.
Lemma lem2305413 (x : int) (y : int) : (int_max x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2305412 x y) (@lem2305385 x y)). Qed.
Lemma lem2305414 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2305413 x y). Qed.
Lemma lem2305415 : term22.
Proof. exact (fun x : int => @lem2305414 x). Qed.
