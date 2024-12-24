Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_RNEG_term_abbrevs.
Require Import REAL_SUB_RNEG_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310398 (x : int) : term0 x.
Proof. exact (@lem1519527 (real_of_int x)). Qed.
Lemma lem2310399 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310400 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310399 x) (@lem2310398 x)). Qed.
Lemma lem2310401 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310400 x (real_of_int y)). Qed.
Lemma lem2310402 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310403 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2310402 x y) (@lem2310401 x y)). Qed.
Lemma lem2310405 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310406 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2310405 y). Qed.
Lemma lem2310407 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2310408 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2310407 x) (@lem2310406 y)). Qed.
Lemma lem2310410 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310411 (x : int) (y : int) : (term8 x y) = (term11 x y).
Proof. exact (@lem2310410 x (int_neg y)). Qed.
Lemma lem2310412 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2310408 x y) (@lem2310411 x y)). Qed.
Lemma lem2310413 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310414 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2310413) (@lem2310412 x y)). Qed.
Lemma lem2310416 (x : int) (y : int) : (term4 x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2310417 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term14 x y)).
Proof. exact (MK_COMB (@lem2310414 x y) (@lem2310416 x y)). Qed.
Lemma lem2310419 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310420 (x : int) (y : int) : ((term11 x y) = (term14 x y)) = ((term15 x y) = (int_add x y)).
Proof. exact (@lem2310419 (term15 x y) (int_add x y)). Qed.
Lemma lem2310421 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term15 x y) = (int_add x y)).
Proof. exact (TRANS (@lem2310417 x y) (@lem2310420 x y)). Qed.
Lemma lem2310422 (x : int) (y : int) : (term15 x y) = (int_add x y).
Proof. exact (EQ_MP (@lem2310421 x y) (@lem2310403 x y)). Qed.
Lemma lem2310423 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2310422 x y). Qed.
Lemma lem2310424 : term17.
Proof. exact (fun x : int => @lem2310423 x). Qed.
