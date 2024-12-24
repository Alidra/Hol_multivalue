Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_CIRCLE_term_abbrevs.
Require Import REAL_ABS_CIRCLE_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300325 (x : int) : term0 x.
Proof. exact (@lem1544390 (real_of_int x)). Qed.
Lemma lem2300326 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300327 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300326 x) (@lem2300325 x)). Qed.
Lemma lem2300328 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300327 x (real_of_int y)). Qed.
Lemma lem2300329 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300330 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2300329 x y) (@lem2300328 x y)). Qed.
Lemma lem2300331 (x : int) (y : int) (h : int) : term4 x y h.
Proof. exact (@lem2300330 x y (real_of_int h)). Qed.
Lemma lem2300332 (x : int) (h : int) (y : int) : (term4 x y h) = (term5 x h y).
Proof. exact (eq_refl (term4 x y h)). Qed.
Lemma lem2300333 (x : int) (h : int) (y : int) : term5 x h y.
Proof. exact (EQ_MP (@lem2300332 x h y) (@lem2300331 x y h)). Qed.
Lemma lem2300335 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300336 (h : int) : (term6 h) = (term7 h).
Proof. exact (@lem2300335 h). Qed.
Lemma lem2300337 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300338 (h : int) : (term8 h) = (term9 h).
Proof. exact (MK_COMB (@lem2300337) (@lem2300336 h)). Qed.
Lemma lem2300340 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300341 (y : int) : (term6 y) = (term7 y).
Proof. exact (@lem2300340 y). Qed.
Lemma lem2300342 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2300343 (y : int) : (term10 y) = (term11 y).
Proof. exact (MK_COMB (@lem2300342) (@lem2300341 y)). Qed.
Lemma lem2300345 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300346 (y : int) (x : int) : (term12 y x) = (term13 y x).
Proof. exact (MK_COMB (@lem2300343 y) (@lem2300345 x)). Qed.
Lemma lem2300348 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300349 (y : int) (x : int) : (term13 y x) = (term16 y x).
Proof. exact (@lem2300348 (int_abs y) (int_abs x)). Qed.
Lemma lem2300350 (y : int) (x : int) : (term12 y x) = (term16 y x).
Proof. exact (TRANS (@lem2300346 y x) (@lem2300349 y x)). Qed.
Lemma lem2300351 (h : int) (y : int) (x : int) : (term17 h y x) = (term18 h y x).
Proof. exact (MK_COMB (@lem2300338 h) (@lem2300350 y x)). Qed.
Lemma lem2300353 (x : int) (y : int) : (term19 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300354 (h : int) (y : int) (x : int) : (term18 h y x) = (term20 h y x).
Proof. exact (@lem2300353 (int_abs h) (term21 y x)). Qed.
Lemma lem2300355 (h : int) (y : int) (x : int) : (term17 h y x) = (term20 h y x).
Proof. exact (TRANS (@lem2300351 h y x) (@lem2300354 h y x)). Qed.
Lemma lem2300356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300357 (h : int) (y : int) (x : int) : (term22 h y x) = (term23 h y x).
Proof. exact (MK_COMB (@lem2300356) (@lem2300355 h y x)). Qed.
Lemma lem2300359 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300360 (x : int) (h : int) : (term24 x h) = (term25 x h).
Proof. exact (@lem2300359 x h). Qed.
Lemma lem2300361 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300362 (x : int) (h : int) : (term26 x h) = (term27 x h).
Proof. exact (MK_COMB (@lem2300361) (@lem2300360 x h)). Qed.
Lemma lem2300364 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300365 (x : int) (h : int) : (term27 x h) = (term28 x h).
Proof. exact (@lem2300364 (int_add x h)). Qed.
Lemma lem2300366 (x : int) (h : int) : (term26 x h) = (term28 x h).
Proof. exact (TRANS (@lem2300362 x h) (@lem2300365 x h)). Qed.
Lemma lem2300367 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300368 (x : int) (h : int) : (term29 x h) = (term30 x h).
Proof. exact (MK_COMB (@lem2300367) (@lem2300366 x h)). Qed.
Lemma lem2300370 (x : int) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300371 (y : int) : (term6 y) = (term7 y).
Proof. exact (@lem2300370 y). Qed.
Lemma lem2300372 (x : int) (h : int) (y : int) : (term31 x h y) = (term32 x h y).
Proof. exact (MK_COMB (@lem2300368 x h) (@lem2300371 y)). Qed.
Lemma lem2300374 (x : int) (y : int) : (term19 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300375 (x : int) (h : int) (y : int) : (term32 x h y) = (term33 x h y).
Proof. exact (@lem2300374 (term34 x h) (int_abs y)). Qed.
Lemma lem2300376 (x : int) (h : int) (y : int) : (term31 x h y) = (term33 x h y).
Proof. exact (TRANS (@lem2300372 x h y) (@lem2300375 x h y)). Qed.
Lemma lem2300377 (x : int) (h : int) (y : int) : (term5 x h y) = (term35 x h y).
Proof. exact (MK_COMB (@lem2300357 h y x) (@lem2300376 x h y)). Qed.
Lemma lem2300378 (x : int) (h : int) (y : int) : term35 x h y.
Proof. exact (EQ_MP (@lem2300377 x h y) (@lem2300333 x h y)). Qed.
Lemma lem2300379 (x : int) (y : int) : term36 x y.
Proof. exact (fun h : int => @lem2300378 x h y). Qed.
Lemma lem2300380 (x : int) : term37 x.
Proof. exact (fun y : int => @lem2300379 x y). Qed.
Lemma lem2300381 : term38.
Proof. exact (fun x : int => @lem2300380 x). Qed.
