Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_BOUNDS_LT_term_abbrevs.
Require Import REAL_BOUNDS_LT_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2301360 (x : int) : term0 x.
Proof. exact (@lem1554983 (real_of_int x)). Qed.
Lemma lem2301361 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301362 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301361 x) (@lem2301360 x)). Qed.
Lemma lem2301363 (x : int) (k : int) : term2 x k.
Proof. exact (@lem2301362 x (real_of_int k)). Qed.
Lemma lem2301364 (x : int) (k : int) : (term2 x k) = ((term3 x k) = (term4 x k)).
Proof. exact (eq_refl (term2 x k)). Qed.
Lemma lem2301365 (x : int) (k : int) : (term3 x k) = (term4 x k).
Proof. exact (EQ_MP (@lem2301364 x k) (@lem2301363 x k)). Qed.
Lemma lem2301367 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301368 (k : int) : (term5 k) = (term6 k).
Proof. exact (@lem2301367 k). Qed.
Lemma lem2301369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2301370 (k : int) : (term7 k) = (term8 k).
Proof. exact (MK_COMB (@lem2301369) (@lem2301368 k)). Qed.
Lemma lem2301371 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301372 (k : int) (x : int) : (term9 k x) = (term10 k x).
Proof. exact (MK_COMB (@lem2301370 k) (@lem2301371 x)). Qed.
Lemma lem2301374 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2301375 (k : int) (x : int) : (term10 k x) = (term12 k x).
Proof. exact (@lem2301374 (int_neg k) x). Qed.
Lemma lem2301376 (k : int) (x : int) : (term9 k x) = (term12 k x).
Proof. exact (TRANS (@lem2301372 k x) (@lem2301375 k x)). Qed.
Lemma lem2301377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2301378 (k : int) (x : int) : (term13 k x) = (term14 k x).
Proof. exact (MK_COMB (@lem2301377) (@lem2301376 k x)). Qed.
Lemma lem2301380 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2301381 (x : int) (k : int) : (term11 x k) = (int_lt x k).
Proof. exact (@lem2301380 x k). Qed.
Lemma lem2301382 (x : int) (k : int) : (term3 x k) = (term15 x k).
Proof. exact (MK_COMB (@lem2301378 k x) (@lem2301381 x k)). Qed.
Lemma lem2301383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301384 (x : int) (k : int) : (term16 x k) = (term17 x k).
Proof. exact (MK_COMB (@lem2301383) (@lem2301382 x k)). Qed.
Lemma lem2301386 (x : int) : (term18 x) = (term19 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301387 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2301388 (x : int) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem2301387) (@lem2301386 x)). Qed.
Lemma lem2301389 (k : int) : (real_of_int k) = (real_of_int k).
Proof. exact (eq_refl (real_of_int k)). Qed.
Lemma lem2301390 (x : int) (k : int) : (term4 x k) = (term22 x k).
Proof. exact (MK_COMB (@lem2301388 x) (@lem2301389 k)). Qed.
Lemma lem2301392 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2301393 (x : int) (k : int) : (term22 x k) = (term23 x k).
Proof. exact (@lem2301392 (int_abs x) k). Qed.
Lemma lem2301394 (x : int) (k : int) : (term4 x k) = (term23 x k).
Proof. exact (TRANS (@lem2301390 x k) (@lem2301393 x k)). Qed.
Lemma lem2301395 (x : int) (k : int) : ((term3 x k) = (term4 x k)) = ((term15 x k) = (term23 x k)).
Proof. exact (MK_COMB (@lem2301384 x k) (@lem2301394 x k)). Qed.
Lemma lem2301396 (x : int) (k : int) : (term15 x k) = (term23 x k).
Proof. exact (EQ_MP (@lem2301395 x k) (@lem2301365 x k)). Qed.
Lemma lem2301397 (x : int) : term24 x.
Proof. exact (fun k : int => @lem2301396 x k). Qed.
Lemma lem2301398 : term25.
Proof. exact (fun x : int => @lem2301397 x). Qed.
