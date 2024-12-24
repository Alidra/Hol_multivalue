Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_BOUNDS_term_abbrevs.
Require Import REAL_ABS_BOUNDS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2300257 (x : int) : term0 x.
Proof. exact (@lem1552321 (real_of_int x)). Qed.
Lemma lem2300258 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300259 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300258 x) (@lem2300257 x)). Qed.
Lemma lem2300260 (x : int) (k : int) : term2 x k.
Proof. exact (@lem2300259 x (real_of_int k)). Qed.
Lemma lem2300261 (x : int) (k : int) : (term2 x k) = ((term3 x k) = (term4 x k)).
Proof. exact (eq_refl (term2 x k)). Qed.
Lemma lem2300262 (x : int) (k : int) : (term3 x k) = (term4 x k).
Proof. exact (EQ_MP (@lem2300261 x k) (@lem2300260 x k)). Qed.
Lemma lem2300264 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300265 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2300266 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2300265) (@lem2300264 x)). Qed.
Lemma lem2300267 (k : int) : (real_of_int k) = (real_of_int k).
Proof. exact (eq_refl (real_of_int k)). Qed.
Lemma lem2300268 (x : int) (k : int) : (term3 x k) = (term9 x k).
Proof. exact (MK_COMB (@lem2300266 x) (@lem2300267 k)). Qed.
Lemma lem2300270 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300271 (x : int) (k : int) : (term9 x k) = (term11 x k).
Proof. exact (@lem2300270 (int_abs x) k). Qed.
Lemma lem2300272 (x : int) (k : int) : (term3 x k) = (term11 x k).
Proof. exact (TRANS (@lem2300268 x k) (@lem2300271 x k)). Qed.
Lemma lem2300273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2300274 (x : int) (k : int) : (term12 x k) = (term13 x k).
Proof. exact (MK_COMB (@lem2300273) (@lem2300272 x k)). Qed.
Lemma lem2300276 (x : int) : (term14 x) = (term15 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2300277 (k : int) : (term14 k) = (term15 k).
Proof. exact (@lem2300276 k). Qed.
Lemma lem2300278 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2300279 (k : int) : (term16 k) = (term17 k).
Proof. exact (MK_COMB (@lem2300278) (@lem2300277 k)). Qed.
Lemma lem2300280 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2300281 (k : int) (x : int) : (term18 k x) = (term19 k x).
Proof. exact (MK_COMB (@lem2300279 k) (@lem2300280 x)). Qed.
Lemma lem2300283 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300284 (k : int) (x : int) : (term19 k x) = (term20 k x).
Proof. exact (@lem2300283 (int_neg k) x). Qed.
Lemma lem2300285 (k : int) (x : int) : (term18 k x) = (term20 k x).
Proof. exact (TRANS (@lem2300281 k x) (@lem2300284 k x)). Qed.
Lemma lem2300286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2300287 (k : int) (x : int) : (term21 k x) = (term22 k x).
Proof. exact (MK_COMB (@lem2300286) (@lem2300285 k x)). Qed.
Lemma lem2300289 (x : int) (y : int) : (term10 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300290 (x : int) (k : int) : (term10 x k) = (int_le x k).
Proof. exact (@lem2300289 x k). Qed.
Lemma lem2300291 (x : int) (k : int) : (term4 x k) = (term23 x k).
Proof. exact (MK_COMB (@lem2300287 k x) (@lem2300290 x k)). Qed.
Lemma lem2300292 (x : int) (k : int) : ((term3 x k) = (term4 x k)) = ((term11 x k) = (term23 x k)).
Proof. exact (MK_COMB (@lem2300274 x k) (@lem2300291 x k)). Qed.
Lemma lem2300293 (x : int) (k : int) : (term11 x k) = (term23 x k).
Proof. exact (EQ_MP (@lem2300292 x k) (@lem2300262 x k)). Qed.
Lemma lem2300294 (x : int) : term24 x.
Proof. exact (fun k : int => @lem2300293 x k). Qed.
Lemma lem2300295 : term25.
Proof. exact (fun x : int => @lem2300294 x). Qed.
