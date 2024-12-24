Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_INV_term_abbrevs.
Require Import REAL_ABS_INV_spec.
Require Import REAL_POW_INV_spec.
Require Import REAL_SGN_INV_spec.
Require Import SQRT_UNIQUE_GEN_spec.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1947280 (x : real) : term0 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1947281 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1947282 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1947281 x) (@lem1947280 x)). Qed.
Lemma lem1947285 (x : real) : term2 x.
Proof. exact (@lem1594832 x). Qed.
Lemma lem1947286 (x : real) : (term2 x) = ((term3 x) = (term4 x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1947288 (x : real) : term5 x.
Proof. exact (@lem1595679 x). Qed.
Lemma lem1947289 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1947290 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1947289 x) (@lem1947288 x)). Qed.
Lemma lem1947291 (x : real) (n : nat) : term7 x n.
Proof. exact (@lem1947290 x n). Qed.
Lemma lem1947292 (x : real) (n : nat) : (term7 x n) = ((term8 x n) = (term9 x n)).
Proof. exact (eq_refl (term7 x n)). Qed.
Lemma lem1947294 (x : real) : term10 x.
Proof. exact (@lem1734683 x). Qed.
Lemma lem1947295 (x : real) : (term10 x) = ((term11 x) = (real_sgn x)).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1947297 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1947298 (x : real) (h1 : term12) : term13 x.
Proof. exact (@lem1947297 h1 x). Qed.
Lemma lem1947299 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1947300 (x : real) (h1 : term12) : term14 x.
Proof. exact (EQ_MP (@lem1947299 x) (@lem1947298 x h1)). Qed.
Lemma lem1947301 (x : real) (y : real) (h1 : term12) : term15 x y.
Proof. exact (@lem1947300 x h1 y). Qed.
Lemma lem1947302 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1947303 (x : real) (y : real) (h1 : term12) : term16 x y.
Proof. exact (EQ_MP (@lem1947302 x y) (@lem1947301 x y h1)). Qed.
Lemma lem1947304 (y : real) (x : real) (h1 : term17 y x) : term17 y x.
Proof. exact (h1). Qed.
Lemma lem1947305 (y : real) (x : real) (h1 : term12) (h2 : term17 y x) : (sqrt x) = y.
Proof. exact (@lem1947303 x y h1 (@lem1947304 y x h2)). Qed.
Lemma lem1947306 (y : real) (x : real) (h1 : term17 y x) : term18 x y.
Proof. exact (fun h0 : term12 => @lem1947305 y x h0 h1). Qed.
Lemma lem1947307 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1947308 (y : real) (x : real) (h1 : term12) (h2 : term17 y x) : (sqrt x) = y.
Proof. exact (@lem1947306 y x h2 (@lem1947307 h1)). Qed.
Lemma lem1947309 (x : real) (y : real) (h1 : term12) : term16 x y.
Proof. exact (fun h0 : term17 y x => @lem1947308 y x h1 h0). Qed.
Lemma lem1947310 (x : real) (h1 : term12) : term14 x.
Proof. exact (fun y : real => @lem1947309 x y h1). Qed.
Lemma lem1947311 (h1 : term12) : term12.
Proof. exact (fun x : real => @lem1947310 x h1). Qed.
Lemma lem1947312 : term19.
Proof. exact (fun h0 : term12 => @lem1947311 h0). Qed.
Lemma lem1947313 : term12.
Proof. exact (@lem1947312 (@lem1921051)). Qed.
Lemma lem1947314 (x : real) : term13 x.
Proof. exact (@lem1947313 x). Qed.
Lemma lem1947315 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1947316 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1947315 x) (@lem1947314 x)). Qed.
Lemma lem1947317 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1947316 x y). Qed.
Lemma lem1947318 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1947321 (x : real) (y : real) : term16 x y.
Proof. exact (EQ_MP (@lem1947318 x y) (@lem1947317 x y)). Qed.
Lemma lem1947322 (x : real) : term20 x.
Proof. exact (@lem1947321 (real_inv x) (term21 x)). Qed.
Lemma lem1947328 (x : real) : (term11 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem1947295 x) (@lem1947294 x)). Qed.
Lemma lem1947329 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1947328 (sqrt x)). Qed.
Lemma lem1947331 (x : real) : (term23 x) = (real_sgn x).
Proof. exact (proj1 (@lem1947282 x)). Qed.
Lemma lem1947332 (x : real) : (term22 x) = (real_sgn x).
Proof. exact (TRANS (@lem1947329 x) (@lem1947331 x)). Qed.
Lemma lem1947333 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947334 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1947333) (@lem1947332 x)). Qed.
Lemma lem1947336 (x : real) : (term11 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem1947295 x) (@lem1947294 x)). Qed.
Lemma lem1947337 (x : real) : ((term22 x) = (term11 x)) = ((real_sgn x) = (real_sgn x)).
Proof. exact (MK_COMB (@lem1947334 x) (@lem1947336 x)). Qed.
Lemma lem1947339 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947340 (x : real) : (x = x) = True.
Proof. exact (@lem1947339 real x). Qed.
Lemma lem1947341 (x : real) : ((real_sgn x) = (real_sgn x)) = True.
Proof. exact (@lem1947340 (real_sgn x)). Qed.
Lemma lem1947342 (x : real) : ((term22 x) = (term11 x)) = True.
Proof. exact (TRANS (@lem1947337 x) (@lem1947341 x)). Qed.
Lemma lem1947343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947344 (x : real) : (term26 x) = (and True).
Proof. exact (MK_COMB (@lem1947343) (@lem1947342 x)). Qed.
Lemma lem1947348 (x : real) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (EQ_MP (@lem1947292 x n) (@lem1947291 x n)). Qed.
Lemma lem1947349 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem1947348 (sqrt x) term29). Qed.
Lemma lem1947351 (x : real) : (term30 x) = (real_abs x).
Proof. exact (proj2 (@lem1947282 x)). Qed.
Lemma lem1947352 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1947353 (x : real) : (term28 x) = (term4 x).
Proof. exact (MK_COMB (@lem1947352) (@lem1947351 x)). Qed.
Lemma lem1947354 (x : real) : (term27 x) = (term4 x).
Proof. exact (TRANS (@lem1947349 x) (@lem1947353 x)). Qed.
Lemma lem1947355 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947356 (x : real) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem1947355) (@lem1947354 x)). Qed.
Lemma lem1947358 (x : real) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem1947286 x) (@lem1947285 x)). Qed.
Lemma lem1947359 (x : real) : ((term27 x) = (term3 x)) = ((term4 x) = (term4 x)).
Proof. exact (MK_COMB (@lem1947356 x) (@lem1947358 x)). Qed.
Lemma lem1947361 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947362 (x : real) : (x = x) = True.
Proof. exact (@lem1947361 real x). Qed.
Lemma lem1947363 (x : real) : ((term4 x) = (term4 x)) = True.
Proof. exact (@lem1947362 (term4 x)). Qed.
Lemma lem1947364 (x : real) : ((term27 x) = (term3 x)) = True.
Proof. exact (TRANS (@lem1947359 x) (@lem1947363 x)). Qed.
Lemma lem1947365 (x : real) : (term33 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1947344 x) (@lem1947364 x)). Qed.
Lemma lem1947367 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1947368 : (True /\ True) = True.
Proof. exact (@lem1947367 True). Qed.
Lemma lem1947369 (x : real) : (term33 x) = True.
Proof. exact (TRANS (@lem1947365 x) (@lem1947368)). Qed.
Lemma lem1947370 (x : real) : True = (term33 x).
Proof. exact (SYM (@lem1947369 x)). Qed.
Lemma lem1947371 (x : real) : term33 x.
Proof. exact (EQ_MP (@lem1947370 x) (@lem0)). Qed.
Lemma lem1947372 (x : real) : (term34 x) = (term21 x).
Proof. exact (@lem1947322 x (@lem1947371 x)). Qed.
Lemma lem1947377 : term35.
Proof. exact (fun x : real => @lem1947372 x). Qed.
