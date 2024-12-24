Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_BOUNDS_LE_term_abbrevs.
Require Import REAL_BOUNDS_LE_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2301321 (x : int) : term0 x.
Proof. exact (@lem1553652 (real_of_int x)). Qed.
Lemma lem2301322 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301323 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301322 x) (@lem2301321 x)). Qed.
Lemma lem2301324 (x : int) (k : int) : term2 x k.
Proof. exact (@lem2301323 x (real_of_int k)). Qed.
Lemma lem2301325 (x : int) (k : int) : (term2 x k) = ((term3 x k) = (term4 x k)).
Proof. exact (eq_refl (term2 x k)). Qed.
Lemma lem2301326 (x : int) (k : int) : (term3 x k) = (term4 x k).
Proof. exact (EQ_MP (@lem2301325 x k) (@lem2301324 x k)). Qed.
Lemma lem2301328 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301329 (k : int) : (term5 k) = (term6 k).
Proof. exact (@lem2301328 k). Qed.
Lemma lem2301330 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2301331 (k : int) : (term7 k) = (term8 k).
Proof. exact (MK_COMB (@lem2301330) (@lem2301329 k)). Qed.
Lemma lem2301332 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301333 (k : int) (x : int) : (term9 k x) = (term10 k x).
Proof. exact (MK_COMB (@lem2301331 k) (@lem2301332 x)). Qed.
Lemma lem2301335 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2301336 (k : int) (x : int) : (term10 k x) = (term12 k x).
Proof. exact (@lem2301335 (int_neg k) x). Qed.
Lemma lem2301337 (k : int) (x : int) : (term9 k x) = (term12 k x).
Proof. exact (TRANS (@lem2301333 k x) (@lem2301336 k x)). Qed.
Lemma lem2301338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2301339 (k : int) (x : int) : (term13 k x) = (term14 k x).
Proof. exact (MK_COMB (@lem2301338) (@lem2301337 k x)). Qed.
Lemma lem2301341 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2301342 (x : int) (k : int) : (term11 x k) = (int_le x k).
Proof. exact (@lem2301341 x k). Qed.
Lemma lem2301343 (x : int) (k : int) : (term3 x k) = (term15 x k).
Proof. exact (MK_COMB (@lem2301339 k x) (@lem2301342 x k)). Qed.
Lemma lem2301344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301345 (x : int) (k : int) : (term16 x k) = (term17 x k).
Proof. exact (MK_COMB (@lem2301344) (@lem2301343 x k)). Qed.
Lemma lem2301347 (x : int) : (term18 x) = (term19 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2301348 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2301349 (x : int) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem2301348) (@lem2301347 x)). Qed.
Lemma lem2301350 (k : int) : (real_of_int k) = (real_of_int k).
Proof. exact (eq_refl (real_of_int k)). Qed.
Lemma lem2301351 (x : int) (k : int) : (term4 x k) = (term22 x k).
Proof. exact (MK_COMB (@lem2301349 x) (@lem2301350 k)). Qed.
Lemma lem2301353 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2301354 (x : int) (k : int) : (term22 x k) = (term23 x k).
Proof. exact (@lem2301353 (int_abs x) k). Qed.
Lemma lem2301355 (x : int) (k : int) : (term4 x k) = (term23 x k).
Proof. exact (TRANS (@lem2301351 x k) (@lem2301354 x k)). Qed.
Lemma lem2301356 (x : int) (k : int) : ((term3 x k) = (term4 x k)) = ((term15 x k) = (term23 x k)).
Proof. exact (MK_COMB (@lem2301345 x k) (@lem2301355 x k)). Qed.
Lemma lem2301357 (x : int) (k : int) : (term15 x k) = (term23 x k).
Proof. exact (EQ_MP (@lem2301356 x k) (@lem2301326 x k)). Qed.
Lemma lem2301358 (x : int) : term24 x.
Proof. exact (fun k : int => @lem2301357 x k). Qed.
Lemma lem2301359 : term25.
Proof. exact (fun x : int => @lem2301358 x). Qed.
