Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_max_th_term_abbrevs.
Require Import int_max_spec.
Require Import real_max_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Lemma lem2292271 (n : real) : term0 n.
Proof. exact (@lem1345564 n). Qed.
Lemma lem2292272 (n : real) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2292273 (n : real) : term1 n.
Proof. exact (EQ_MP (@lem2292272 n) (@lem2292271 n)). Qed.
Lemma lem2292274 (n : real) (m : real) : term2 n m.
Proof. exact (@lem2292273 n m). Qed.
Lemma lem2292275 (n : real) (m : real) : (term2 n m) = ((real_max m n) = (term3 n m)).
Proof. exact (eq_refl (term2 n m)). Qed.
Lemma lem2292277 (x : int) : term4 x.
Proof. exact (@lem2292270 x). Qed.
Lemma lem2292278 (x : int) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2292279 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2292278 x) (@lem2292277 x)). Qed.
Lemma lem2292280 (x : int) (y : int) : term6 x y.
Proof. exact (@lem2292279 x y). Qed.
Lemma lem2292281 (x : int) (y : int) : (term6 x y) = ((int_max x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem2292286 (x : int) (y : int) : (int_max x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2292281 x y) (@lem2292280 x y)). Qed.
Lemma lem2292288 (n : real) (m : real) : (real_max m n) = (term3 n m).
Proof. exact (EQ_MP (@lem2292275 n m) (@lem2292274 n m)). Qed.
Lemma lem2292289 (y : int) (x : int) : (term8 x y) = (term9 y x).
Proof. exact (@lem2292288 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2292290 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2292291 (y : int) (x : int) : (term7 x y) = (term10 y x).
Proof. exact (MK_COMB (@lem2292290) (@lem2292289 y x)). Qed.
Lemma lem2292292 (y : int) (x : int) : (int_max x y) = (term10 y x).
Proof. exact (TRANS (@lem2292286 x y) (@lem2292291 y x)). Qed.
Lemma lem2292293 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2292294 (y : int) (x : int) : (term11 x y) = (term12 y x).
Proof. exact (MK_COMB (@lem2292293) (@lem2292292 y x)). Qed.
Lemma lem2292295 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2292296 (y : int) (x : int) : (term13 x y) = (term14 y x).
Proof. exact (MK_COMB (@lem2292295) (@lem2292294 y x)). Qed.
Lemma lem2292298 (n : real) (m : real) : (real_max m n) = (term3 n m).
Proof. exact (EQ_MP (@lem2292275 n m) (@lem2292274 n m)). Qed.
Lemma lem2292299 (y : int) (x : int) : (term8 x y) = (term9 y x).
Proof. exact (@lem2292298 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2292300 (y : int) (x : int) : ((term11 x y) = (term8 x y)) = ((term12 y x) = (term9 y x)).
Proof. exact (MK_COMB (@lem2292296 y x) (@lem2292299 y x)). Qed.
Lemma lem2292303 (x : int) (y : int) : ((term12 y x) = (term9 y x)) = ((term11 x y) = (term8 x y)).
Proof. exact (SYM (@lem2292300 y x)). Qed.
Lemma lem2292304 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term15 _476 _475 _474 _477) = (term16 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem2292305 (_474 : real) (_475 : Prop) (_477 : real) : (term17 _475 _474 _477) = (term18 _474 _475 _477).
Proof. exact (@lem2292304 _474 _475 term19 _477). Qed.
Lemma lem2292306 (y : int) (x : int) : (term20 y x) = (term21 y x).
Proof. exact (@lem2292305 (real_of_int y) (term22 x y) (real_of_int x)). Qed.
Lemma lem2292307 (x : int) : (term23 x) = ((term24 x) = (real_of_int x)).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2292308 (x : int) (y : int) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2292309 (y : int) (x : int) : (term26 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem2292308 x y) (@lem2292307 x)). Qed.
Lemma lem2292310 (y : int) : (term23 y) = ((term24 y) = (real_of_int y)).
Proof. exact (eq_refl (term23 y)). Qed.
Lemma lem2292311 (x : int) (y : int) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem2292312 (x : int) (y : int) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem2292311 x y) (@lem2292310 y)). Qed.
Lemma lem2292313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2292314 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem2292313) (@lem2292312 x y)). Qed.
Lemma lem2292315 (y : int) (x : int) : (term21 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem2292314 x y) (@lem2292309 y x)). Qed.
Lemma lem2292316 (y : int) (x : int) : (term20 y x) = ((term12 y x) = (term9 y x)).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem2292317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2292318 (y : int) (x : int) : (term34 y x) = (term35 y x).
Proof. exact (MK_COMB (@lem2292317) (@lem2292316 y x)). Qed.
Lemma lem2292319 (y : int) (x : int) : ((term20 y x) = (term21 y x)) = (((term12 y x) = (term9 y x)) = (term33 y x)).
Proof. exact (MK_COMB (@lem2292318 y x) (@lem2292315 y x)). Qed.
Lemma lem2292320 (y : int) (x : int) : ((term12 y x) = (term9 y x)) = (term33 y x).
Proof. exact (EQ_MP (@lem2292319 y x) (@lem2292306 y x)). Qed.
Lemma lem2292321 (y : int) (x : int) : (term33 y x) = ((term12 y x) = (term9 y x)).
Proof. exact (SYM (@lem2292320 y x)). Qed.
Lemma lem2292359 (a : int) : (term36 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2292360 (y : int) : (term36 y) = y.
Proof. exact (@lem2292359 y). Qed.
Lemma lem2292361 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2292362 (y : int) : (term24 y) = (real_of_int y).
Proof. exact (MK_COMB (@lem2292361) (@lem2292360 y)). Qed.
Lemma lem2292363 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2292364 (y : int) : (term37 y) = (term38 y).
Proof. exact (MK_COMB (@lem2292363) (@lem2292362 y)). Qed.
Lemma lem2292365 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2292366 (y : int) : ((term24 y) = (real_of_int y)) = ((real_of_int y) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2292364 y) (@lem2292365 y)). Qed.
Lemma lem2292368 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2292369 (x : real) : (x = x) = True.
Proof. exact (@lem2292368 real x). Qed.
Lemma lem2292370 (y : int) : ((real_of_int y) = (real_of_int y)) = True.
Proof. exact (@lem2292369 (real_of_int y)). Qed.
Lemma lem2292371 (y : int) : ((term24 y) = (real_of_int y)) = True.
Proof. exact (TRANS (@lem2292366 y) (@lem2292370 y)). Qed.
Lemma lem2292372 (y : int) : True = ((term24 y) = (real_of_int y)).
Proof. exact (SYM (@lem2292371 y)). Qed.
Lemma lem2292377 (a : int) : (term36 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2292378 (x : int) : (term36 x) = x.
Proof. exact (@lem2292377 x). Qed.
Lemma lem2292379 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2292380 (x : int) : (term24 x) = (real_of_int x).
Proof. exact (MK_COMB (@lem2292379) (@lem2292378 x)). Qed.
Lemma lem2292381 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2292382 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2292381) (@lem2292380 x)). Qed.
Lemma lem2292383 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2292384 (x : int) : ((term24 x) = (real_of_int x)) = ((real_of_int x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2292382 x) (@lem2292383 x)). Qed.
Lemma lem2292386 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2292387 (x : real) : (x = x) = True.
Proof. exact (@lem2292386 real x). Qed.
Lemma lem2292388 (x : int) : ((real_of_int x) = (real_of_int x)) = True.
Proof. exact (@lem2292387 (real_of_int x)). Qed.
Lemma lem2292389 (x : int) : ((term24 x) = (real_of_int x)) = True.
Proof. exact (TRANS (@lem2292384 x) (@lem2292388 x)). Qed.
Lemma lem2292390 (x : int) : True = ((term24 x) = (real_of_int x)).
Proof. exact (SYM (@lem2292389 x)). Qed.
Lemma lem2292392 (x : int) : (term24 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2292390 x) (@lem0)). Qed.
Lemma lem2292393 (y : int) (x : int) : term27 y x.
Proof. exact (fun h0 : term39 x y => @lem2292392 x). Qed.
Lemma lem2292394 (y : int) : (term24 y) = (real_of_int y).
Proof. exact (EQ_MP (@lem2292372 y) (@lem0)). Qed.
Lemma lem2292395 (x : int) (y : int) : term30 x y.
Proof. exact (fun h0 : term22 x y => @lem2292394 y). Qed.
Lemma lem2292396 (y : int) (x : int) : term33 y x.
Proof. exact (conj (@lem2292395 x y) (@lem2292393 y x)). Qed.
Lemma lem2292397 (y : int) (x : int) : (term12 y x) = (term9 y x).
Proof. exact (EQ_MP (@lem2292321 y x) (@lem2292396 y x)). Qed.
Lemma lem2292398 (x : int) (y : int) : (term11 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2292303 x y) (@lem2292397 y x)). Qed.
Lemma lem2292403 (x : int) : term40 x.
Proof. exact (fun y : int => @lem2292398 x y). Qed.
Lemma lem2292408 : term41.
Proof. exact (fun x : int => @lem2292403 x). Qed.
