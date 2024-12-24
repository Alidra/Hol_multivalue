Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_MUL2_term_abbrevs.
Require Import REAL_LE_LMUL_spec.
Require Import REAL_LE_RMUL_spec.
Require Import thm0_spec.
Require Import thm1339577_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1630284 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630285 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1630284 h1 x). Qed.
Lemma lem1630286 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1630287 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1630286 x) (@lem1630285 x h1)). Qed.
Lemma lem1630288 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1630287 x h1 y). Qed.
Lemma lem1630289 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1630290 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1630289 y x) (@lem1630288 x y h1)). Qed.
Lemma lem1630291 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1630290 y x h1 z). Qed.
Lemma lem1630292 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1630293 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1630292 y x z) (@lem1630291 y x z h1)). Qed.
Lemma lem1630294 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1630295 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_le x z.
Proof. exact (@lem1630293 y x z h1 (@lem1630294 x y z h2)). Qed.
Lemma lem1630296 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1630295 x y z h0 h1). Qed.
Lemma lem1630297 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1630298 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1630297 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1630296 x y z h0)). Qed.
Lemma lem1630299 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630300 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_le x z.
Proof. exact (@lem1630298 x z h2 (@lem1630299 h1)). Qed.
Lemma lem1630301 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1630300 x z h1 h0). Qed.
Lemma lem1630302 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1630301 x z h1). Qed.
Lemma lem1630303 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1630302 x h1). Qed.
Lemma lem1630304 : term14.
Proof. exact (fun h0 : term0 => @lem1630303 h0). Qed.
Lemma lem1630305 : term13.
Proof. exact (@lem1630304 (@lem1339577)). Qed.
Lemma lem1630306 (x : real) : term15 x.
Proof. exact (@lem1630305 x). Qed.
Lemma lem1630307 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1630308 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1630307 x) (@lem1630306 x)). Qed.
Lemma lem1630309 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1630308 x z). Qed.
Lemma lem1630310 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1630312 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1630313 (x : real) (h1 : term17) : term18 x.
Proof. exact (@lem1630312 h1 x). Qed.
Lemma lem1630314 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1630315 (x : real) (h1 : term17) : term19 x.
Proof. exact (EQ_MP (@lem1630314 x) (@lem1630313 x h1)). Qed.
Lemma lem1630316 (x : real) (y : real) (h1 : term17) : term20 x y.
Proof. exact (@lem1630315 x h1 y). Qed.
Lemma lem1630317 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1630318 (x : real) (y : real) (h1 : term17) : term21 x y.
Proof. exact (EQ_MP (@lem1630317 x y) (@lem1630316 x y h1)). Qed.
Lemma lem1630319 (x : real) (y : real) (z : real) (h1 : term17) : term22 x y z.
Proof. exact (@lem1630318 x y h1 z). Qed.
Lemma lem1630320 (x : real) (y : real) (z : real) : (term22 x y z) = (term23 x y z).
Proof. exact (eq_refl (term22 x y z)). Qed.
Lemma lem1630321 (x : real) (y : real) (z : real) (h1 : term17) : term23 x y z.
Proof. exact (EQ_MP (@lem1630320 x y z) (@lem1630319 x y z h1)). Qed.
Lemma lem1630322 (x : real) (y : real) (z : real) (h1 : term24 x y z) : term24 x y z.
Proof. exact (h1). Qed.
Lemma lem1630323 (x : real) (y : real) (z : real) (h1 : term17) (h2 : term24 x y z) : term25 x y z.
Proof. exact (@lem1630321 x y z h1 (@lem1630322 x y z h2)). Qed.
Lemma lem1630324 (x : real) (y : real) (z : real) (h1 : term24 x y z) : term26 x y z.
Proof. exact (fun h0 : term17 => @lem1630323 x y z h0 h1). Qed.
Lemma lem1630325 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1630326 (x : real) (y : real) (z : real) (h1 : term17) (h2 : term24 x y z) : term25 x y z.
Proof. exact (@lem1630324 x y z h2 (@lem1630325 h1)). Qed.
Lemma lem1630327 (x : real) (y : real) (z : real) (h1 : term17) : term23 x y z.
Proof. exact (fun h0 : term24 x y z => @lem1630326 x y z h1 h0). Qed.
Lemma lem1630328 (x : real) (y : real) (h1 : term17) : term21 x y.
Proof. exact (fun z : real => @lem1630327 x y z h1). Qed.
Lemma lem1630329 (x : real) (h1 : term17) : term19 x.
Proof. exact (fun y : real => @lem1630328 x y h1). Qed.
Lemma lem1630330 (h1 : term17) : term17.
Proof. exact (fun x : real => @lem1630329 x h1). Qed.
Lemma lem1630331 : term27.
Proof. exact (fun h0 : term17 => @lem1630330 h0). Qed.
Lemma lem1630332 : term17.
Proof. exact (@lem1630331 (@lem1584226)). Qed.
Lemma lem1630333 (x : real) : term18 x.
Proof. exact (@lem1630332 x). Qed.
Lemma lem1630334 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1630335 (x : real) : term19 x.
Proof. exact (EQ_MP (@lem1630334 x) (@lem1630333 x)). Qed.
Lemma lem1630336 (x : real) (y : real) : term20 x y.
Proof. exact (@lem1630335 x y). Qed.
Lemma lem1630337 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1630338 (x : real) (y : real) : term21 x y.
Proof. exact (EQ_MP (@lem1630337 x y) (@lem1630336 x y)). Qed.
Lemma lem1630339 (x : real) (y : real) (z : real) : term22 x y z.
Proof. exact (@lem1630338 x y z). Qed.
Lemma lem1630340 (x : real) (y : real) (z : real) : (term22 x y z) = (term23 x y z).
Proof. exact (eq_refl (term22 x y z)). Qed.
Lemma lem1630342 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1630343 (x : real) (h1 : term28) : term29 x.
Proof. exact (@lem1630342 h1 x). Qed.
Lemma lem1630344 (x : real) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1630345 (x : real) (h1 : term28) : term30 x.
Proof. exact (EQ_MP (@lem1630344 x) (@lem1630343 x h1)). Qed.
Lemma lem1630346 (x : real) (y : real) (h1 : term28) : term31 x y.
Proof. exact (@lem1630345 x h1 y). Qed.
Lemma lem1630347 (y : real) (x : real) : (term31 x y) = (term32 y x).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1630348 (y : real) (x : real) (h1 : term28) : term32 y x.
Proof. exact (EQ_MP (@lem1630347 y x) (@lem1630346 x y h1)). Qed.
Lemma lem1630349 (y : real) (x : real) (z : real) (h1 : term28) : term33 y x z.
Proof. exact (@lem1630348 y x h1 z). Qed.
Lemma lem1630350 (y : real) (x : real) (z : real) : (term33 y x z) = (term34 y x z).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem1630351 (y : real) (x : real) (z : real) (h1 : term28) : term34 y x z.
Proof. exact (EQ_MP (@lem1630350 y x z) (@lem1630349 y x z h1)). Qed.
Lemma lem1630352 (x : real) (y : real) (z : real) (h1 : term35 x y z) : term35 x y z.
Proof. exact (h1). Qed.
Lemma lem1630353 (x : real) (y : real) (z : real) (h1 : term28) (h2 : term35 x y z) : term36 y x z.
Proof. exact (@lem1630351 y x z h1 (@lem1630352 x y z h2)). Qed.
Lemma lem1630354 (x : real) (y : real) (z : real) (h1 : term35 x y z) : term37 y x z.
Proof. exact (fun h0 : term28 => @lem1630353 x y z h0 h1). Qed.
Lemma lem1630355 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1630356 (x : real) (y : real) (z : real) (h1 : term28) (h2 : term35 x y z) : term36 y x z.
Proof. exact (@lem1630354 x y z h2 (@lem1630355 h1)). Qed.
Lemma lem1630357 (y : real) (x : real) (z : real) (h1 : term28) : term34 y x z.
Proof. exact (fun h0 : term35 x y z => @lem1630356 x y z h1 h0). Qed.
Lemma lem1630358 (y : real) (x : real) (h1 : term28) : term32 y x.
Proof. exact (fun z : real => @lem1630357 y x z h1). Qed.
Lemma lem1630359 (y : real) (h1 : term28) : term38 y.
Proof. exact (fun x : real => @lem1630358 y x h1). Qed.
Lemma lem1630360 (h1 : term28) : term39.
Proof. exact (fun y : real => @lem1630359 y h1). Qed.
Lemma lem1630361 : term40.
Proof. exact (fun h0 : term28 => @lem1630360 h0). Qed.
Lemma lem1630362 : term39.
Proof. exact (@lem1630361 (@lem1583207)). Qed.
Lemma lem1630363 (y : real) : term41 y.
Proof. exact (@lem1630362 y). Qed.
Lemma lem1630364 (y : real) : (term41 y) = (term38 y).
Proof. exact (eq_refl (term41 y)). Qed.
Lemma lem1630365 (y : real) : term38 y.
Proof. exact (EQ_MP (@lem1630364 y) (@lem1630363 y)). Qed.
Lemma lem1630366 (y : real) (x : real) : term42 y x.
Proof. exact (@lem1630365 y x). Qed.
Lemma lem1630367 (y : real) (x : real) : (term42 y x) = (term32 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem1630368 (y : real) (x : real) : term32 y x.
Proof. exact (EQ_MP (@lem1630367 y x) (@lem1630366 y x)). Qed.
Lemma lem1630369 (y : real) (x : real) (z : real) : term33 y x z.
Proof. exact (@lem1630368 y x z). Qed.
Lemma lem1630370 (y : real) (x : real) (z : real) : (term33 y x z) = (term34 y x z).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem1630372 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630373 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1630372 h1 x). Qed.
Lemma lem1630374 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1630375 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1630374 x) (@lem1630373 x h1)). Qed.
Lemma lem1630376 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1630375 x h1 y). Qed.
Lemma lem1630377 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1630378 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1630377 y x) (@lem1630376 x y h1)). Qed.
Lemma lem1630379 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1630378 y x h1 z). Qed.
Lemma lem1630380 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1630381 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1630380 y x z) (@lem1630379 y x z h1)). Qed.
Lemma lem1630382 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1630383 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : real_le x z.
Proof. exact (@lem1630381 y x z h1 (@lem1630382 x y z h2)). Qed.
Lemma lem1630384 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term8 x z.
Proof. exact (fun h0 : term0 => @lem1630383 x y z h0 h1). Qed.
Lemma lem1630385 (x : real) (z : real) (h1 : term9 x z) : term9 x z.
Proof. exact (h1). Qed.
Lemma lem1630386 (x : real) (z : real) (h1 : term9 x z) : term8 x z.
Proof. exact (ex_elim (@lem1630385 x z h1) (fun y : real => fun h0 : term10 x z y => @lem1630384 x y z h0)). Qed.
Lemma lem1630387 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1630388 (x : real) (z : real) (h1 : term0) (h2 : term9 x z) : real_le x z.
Proof. exact (@lem1630386 x z h2 (@lem1630387 h1)). Qed.
Lemma lem1630389 (x : real) (z : real) (h1 : term0) : term11 x z.
Proof. exact (fun h0 : term9 x z => @lem1630388 x z h1 h0). Qed.
Lemma lem1630390 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun z : real => @lem1630389 x z h1). Qed.
Lemma lem1630391 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1630390 x h1). Qed.
Lemma lem1630392 : term14.
Proof. exact (fun h0 : term0 => @lem1630391 h0). Qed.
Lemma lem1630393 : term13.
Proof. exact (@lem1630392 (@lem1339577)). Qed.
Lemma lem1630394 (x : real) : term15 x.
Proof. exact (@lem1630393 x). Qed.
Lemma lem1630395 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1630396 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1630395 x) (@lem1630394 x)). Qed.
Lemma lem1630397 (x : real) (z : real) : term16 x z.
Proof. exact (@lem1630396 x z). Qed.
Lemma lem1630398 (x : real) (z : real) : (term16 x z) = (term11 x z).
Proof. exact (eq_refl (term16 x z)). Qed.
Lemma lem1630400 (w : real) (x : real) (y : real) (z : real) (h1 : term43 w x y z) : term43 w x y z.
Proof. exact (h1). Qed.
Lemma lem1630401 (w : real) (x : real) (y : real) (z : real) (h1 : term44 w x y z) : term44 w x y z.
Proof. exact (h1). Qed.
Lemma lem1630402 (w : real) (h1 : term45 w) : term45 w.
Proof. exact (h1). Qed.
Lemma lem1630403 (y : real) (z : real) (h1 : term46 y z) : term46 y z.
Proof. exact (h1). Qed.
Lemma lem1630404 (w : real) (x : real) (h1 : real_le w x) : real_le w x.
Proof. exact (h1). Qed.
Lemma lem1630405 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1630406 (y : real) (h1 : term45 y) : term45 y.
Proof. exact (h1). Qed.
Lemma lem1630408 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1630398 x z) (@lem1630397 x z)). Qed.
Lemma lem1630409 (w : real) (y : real) (x : real) (z : real) : term47 w y x z.
Proof. exact (@lem1630408 (real_mul w y) (real_mul x z)). Qed.
Lemma lem1630411 (y : real) (x : real) (z : real) : term34 y x z.
Proof. exact (EQ_MP (@lem1630370 y x z) (@lem1630369 y x z)). Qed.
Lemma lem1630412 (y : real) (w : real) (z : real) : term34 y w z.
Proof. exact (@lem1630411 y w z). Qed.
Lemma lem1630414 (x : real) (y : real) (z : real) : term23 x y z.
Proof. exact (EQ_MP (@lem1630340 x y z) (@lem1630339 x y z)). Qed.
Lemma lem1630415 (w : real) (x : real) (z : real) : term23 w x z.
Proof. exact (@lem1630414 w x z). Qed.
Lemma lem1630416 (w : real) : (term45 w) = ((term45 w) = True).
Proof. exact (@lem7 (term45 w)). Qed.
Lemma lem1630422 (y : real) (z : real) : (real_le y z) = ((real_le y z) = True).
Proof. exact (@lem7 (real_le y z)). Qed.
Lemma lem1630427 (w : real) (h1 : term45 w) : (term45 w) = True.
Proof. exact (EQ_MP (@lem1630416 w) (@lem1630402 w h1)). Qed.
Lemma lem1630428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630429 (w : real) (h1 : term45 w) : (term48 w) = (and True).
Proof. exact (MK_COMB (@lem1630428) (@lem1630427 w h1)). Qed.
Lemma lem1630431 (y : real) (z : real) (h1 : real_le y z) : (real_le y z) = True.
Proof. exact (EQ_MP (@lem1630422 y z) (@lem1630405 y z h1)). Qed.
Lemma lem1630432 (y : real) (z : real) (w : real) (h1 : real_le y z) (h2 : term45 w) : (term35 w y z) = (True /\ True).
Proof. exact (MK_COMB (@lem1630429 w h2) (@lem1630431 y z h1)). Qed.
Lemma lem1630434 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630435 : (True /\ True) = True.
Proof. exact (@lem1630434 True). Qed.
Lemma lem1630436 (y : real) (z : real) (w : real) (h1 : real_le y z) (h2 : term45 w) : (term35 w y z) = True.
Proof. exact (TRANS (@lem1630432 y z w h1 h2) (@lem1630435)). Qed.
Lemma lem1630437 (y : real) (z : real) (w : real) (h1 : real_le y z) (h2 : term45 w) : True = (term35 w y z).
Proof. exact (SYM (@lem1630436 y z w h1 h2)). Qed.
Lemma lem1630438 (y : real) (z : real) (w : real) (h1 : real_le y z) (h2 : term45 w) : term35 w y z.
Proof. exact (EQ_MP (@lem1630437 y z w h1 h2) (@lem0)). Qed.
Lemma lem1630441 (w : real) (x : real) : (real_le w x) = ((real_le w x) = True).
Proof. exact (@lem7 (real_le w x)). Qed.
Lemma lem1630450 (w : real) (x : real) (h1 : real_le w x) : (real_le w x) = True.
Proof. exact (EQ_MP (@lem1630441 w x) (@lem1630404 w x h1)). Qed.
Lemma lem1630451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630452 (w : real) (x : real) (h1 : real_le w x) : (term49 w x) = (and True).
Proof. exact (MK_COMB (@lem1630451) (@lem1630450 w x h1)). Qed.
Lemma lem1630453 (z : real) : (term45 z) = (term45 z).
Proof. exact (eq_refl (term45 z)). Qed.
Lemma lem1630454 (z : real) (w : real) (x : real) (h1 : real_le w x) : (term24 w x z) = (term50 z).
Proof. exact (MK_COMB (@lem1630452 w x h1) (@lem1630453 z)). Qed.
Lemma lem1630456 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630457 (z : real) : (term50 z) = (term45 z).
Proof. exact (@lem1630456 (term45 z)). Qed.
Lemma lem1630458 (z : real) (w : real) (x : real) (h1 : real_le w x) : (term24 w x z) = (term45 z).
Proof. exact (TRANS (@lem1630454 z w x h1) (@lem1630457 z)). Qed.
Lemma lem1630459 (z : real) (w : real) (x : real) (h1 : real_le w x) : (term45 z) = (term24 w x z).
Proof. exact (SYM (@lem1630458 z w x h1)). Qed.
Lemma lem1630461 (x : real) (z : real) : term11 x z.
Proof. exact (EQ_MP (@lem1630310 x z) (@lem1630309 x z)). Qed.
Lemma lem1630462 (z : real) : term51 z.
Proof. exact (@lem1630461 term52 z). Qed.
Lemma lem1630467 (y : real) : (term45 y) = ((term45 y) = True).
Proof. exact (@lem7 (term45 y)). Qed.
Lemma lem1630469 (y : real) (z : real) : (real_le y z) = ((real_le y z) = True).
Proof. exact (@lem7 (real_le y z)). Qed.
Lemma lem1630474 (y : real) (h1 : term45 y) : (term45 y) = True.
Proof. exact (EQ_MP (@lem1630467 y) (@lem1630406 y h1)). Qed.
Lemma lem1630475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1630476 (y : real) (h1 : term45 y) : (term48 y) = (and True).
Proof. exact (MK_COMB (@lem1630475) (@lem1630474 y h1)). Qed.
Lemma lem1630478 (y : real) (z : real) (h1 : real_le y z) : (real_le y z) = True.
Proof. exact (EQ_MP (@lem1630469 y z) (@lem1630405 y z h1)). Qed.
Lemma lem1630479 (z : real) (y : real) (h1 : real_le y z) (h2 : term45 y) : (term46 y z) = (True /\ True).
Proof. exact (MK_COMB (@lem1630476 y h2) (@lem1630478 y z h1)). Qed.
Lemma lem1630481 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1630482 : (True /\ True) = True.
Proof. exact (@lem1630481 True). Qed.
Lemma lem1630483 (z : real) (y : real) (h1 : real_le y z) (h2 : term45 y) : (term46 y z) = True.
Proof. exact (TRANS (@lem1630479 z y h1 h2) (@lem1630482)). Qed.
Lemma lem1630484 (z : real) (y : real) (h1 : real_le y z) (h2 : term45 y) : True = (term46 y z).
Proof. exact (SYM (@lem1630483 z y h1 h2)). Qed.
Lemma lem1630485 (z : real) (y : real) (h1 : real_le y z) (h2 : term45 y) : term46 y z.
Proof. exact (EQ_MP (@lem1630484 z y h1 h2) (@lem0)). Qed.
Lemma lem1630486 (z : real) (y : real) (h1 : real_le y z) (h2 : term45 y) : term53 z.
Proof. exact (ex_intro (term54 z) y (@lem1630485 z y h1 h2)). Qed.
Lemma lem1630487 (z : real) (y : real) (h1 : real_le y z) (h2 : term45 y) : term45 z.
Proof. exact (@lem1630462 z (@lem1630486 z y h1 h2)). Qed.
Lemma lem1630488 (w : real) (x : real) (z : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 y) : term24 w x z.
Proof. exact (EQ_MP (@lem1630459 z w x h1) (@lem1630487 z y h2 h3)). Qed.
Lemma lem1630489 (w : real) (x : real) (z : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 y) : term25 w x z.
Proof. exact (@lem1630415 w x z (@lem1630488 w x z y h1 h2 h3)). Qed.
Lemma lem1630490 (y : real) (z : real) (w : real) (h1 : real_le y z) (h2 : term45 w) : term36 y w z.
Proof. exact (@lem1630412 y w z (@lem1630438 y z w h1 h2)). Qed.
Lemma lem1630491 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : term55 y w x z.
Proof. exact (conj (@lem1630490 y z w h2 h3) (@lem1630489 w x z y h1 h2 h4)). Qed.
Lemma lem1630492 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : term56 w y x z.
Proof. exact (ex_intro (term57 w y x z) (real_mul w z) (@lem1630491 x z w y h1 h2 h3 h4)). Qed.
Lemma lem1630493 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : term58 w y x z.
Proof. exact (@lem1630409 w y x z (@lem1630492 x z w y h1 h2 h3 h4)). Qed.
Lemma lem1630494 (w : real) (x : real) (y : real) (z : real) (h1 : term43 w x y z) : term44 w x y z.
Proof. exact (proj2 (@lem1630400 w x y z h1)). Qed.
Lemma lem1630495 (w : real) (x : real) (y : real) (z : real) (h1 : term43 w x y z) : term45 w.
Proof. exact (proj1 (@lem1630400 w x y z h1)). Qed.
Lemma lem1630496 (w : real) (x : real) (y : real) (z : real) (h1 : term44 w x y z) : term46 y z.
Proof. exact (proj2 (@lem1630401 w x y z h1)). Qed.
Lemma lem1630497 (w : real) (x : real) (y : real) (z : real) (h1 : term44 w x y z) : real_le w x.
Proof. exact (proj1 (@lem1630401 w x y z h1)). Qed.
Lemma lem1630498 (y : real) (z : real) (h1 : term46 y z) : real_le y z.
Proof. exact (proj2 (@lem1630403 y z h1)). Qed.
Lemma lem1630499 (y : real) (z : real) (h1 : term46 y z) : term45 y.
Proof. exact (proj1 (@lem1630403 y z h1)). Qed.
Lemma lem1630500 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : (real_le y z) = (term58 w y x z).
Proof. exact (prop_ext (fun h5 : real_le y z => @lem1630493 x z w y h1 h2 h3 h4) (fun h5 : term58 w y x z => @lem1630405 y z h2)). Qed.
Lemma lem1630501 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630500 x z w y h1 h2 h3 h4) (@lem1630405 y z h2)). Qed.
Lemma lem1630502 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : (term45 y) = (term58 w y x z).
Proof. exact (prop_ext (fun h5 : term45 y => @lem1630501 x z w y h1 h2 h3 h4) (fun h5 : term58 w y x z => @lem1630406 y h4)). Qed.
Lemma lem1630503 (x : real) (z : real) (w : real) (y : real) (h1 : real_le w x) (h2 : real_le y z) (h3 : term45 w) (h4 : term45 y) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630502 x z w y h1 h2 h3 h4) (@lem1630406 y h4)). Qed.
Lemma lem1630504 (z : real) (x : real) (w : real) (y : real) (h1 : term46 y z) (h2 : real_le w x) (h3 : term45 w) (h4 : term45 y) : (real_le y z) = (term58 w y x z).
Proof. exact (prop_ext (fun h5 : real_le y z => @lem1630503 x z w y h2 h5 h3 h4) (fun h5 : term58 w y x z => @lem1630498 y z h1)). Qed.
Lemma lem1630505 (z : real) (x : real) (w : real) (y : real) (h1 : term46 y z) (h2 : real_le w x) (h3 : term45 w) (h4 : term45 y) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630504 z x w y h1 h2 h3 h4) (@lem1630498 y z h1)). Qed.
Lemma lem1630506 (y : real) (z : real) (x : real) (w : real) (h1 : term46 y z) (h2 : real_le w x) (h3 : term45 w) : (term45 y) = (term58 w y x z).
Proof. exact (prop_ext (fun h4 : term45 y => @lem1630505 z x w y h1 h2 h3 h4) (fun h4 : term58 w y x z => @lem1630499 y z h1)). Qed.
Lemma lem1630507 (y : real) (z : real) (x : real) (w : real) (h1 : term46 y z) (h2 : real_le w x) (h3 : term45 w) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630506 y z x w h1 h2 h3) (@lem1630499 y z h1)). Qed.
Lemma lem1630508 (y : real) (z : real) (x : real) (w : real) (h1 : term46 y z) (h2 : real_le w x) (h3 : term45 w) : (real_le w x) = (term58 w y x z).
Proof. exact (prop_ext (fun h4 : real_le w x => @lem1630507 y z x w h1 h2 h3) (fun h4 : term58 w y x z => @lem1630404 w x h2)). Qed.
Lemma lem1630509 (y : real) (z : real) (x : real) (w : real) (h1 : term46 y z) (h2 : real_le w x) (h3 : term45 w) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630508 y z x w h1 h2 h3) (@lem1630404 w x h2)). Qed.
Lemma lem1630510 (y : real) (z : real) (x : real) (w : real) (h1 : term44 w x y z) (h2 : real_le w x) (h3 : term45 w) : (term46 y z) = (term58 w y x z).
Proof. exact (prop_ext (fun h4 : term46 y z => @lem1630509 y z x w h4 h2 h3) (fun h4 : term58 w y x z => @lem1630496 w x y z h1)). Qed.
Lemma lem1630511 (y : real) (z : real) (x : real) (w : real) (h1 : term44 w x y z) (h2 : real_le w x) (h3 : term45 w) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630510 y z x w h1 h2 h3) (@lem1630496 w x y z h1)). Qed.
Lemma lem1630512 (x : real) (y : real) (z : real) (w : real) (h1 : term44 w x y z) (h2 : term45 w) : (real_le w x) = (term58 w y x z).
Proof. exact (prop_ext (fun h3 : real_le w x => @lem1630511 y z x w h1 h3 h2) (fun h3 : term58 w y x z => @lem1630497 w x y z h1)). Qed.
Lemma lem1630513 (x : real) (y : real) (z : real) (w : real) (h1 : term44 w x y z) (h2 : term45 w) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630512 x y z w h1 h2) (@lem1630497 w x y z h1)). Qed.
Lemma lem1630514 (x : real) (y : real) (z : real) (w : real) (h1 : term44 w x y z) (h2 : term45 w) : (term45 w) = (term58 w y x z).
Proof. exact (prop_ext (fun h3 : term45 w => @lem1630513 x y z w h1 h2) (fun h3 : term58 w y x z => @lem1630402 w h2)). Qed.
Lemma lem1630515 (x : real) (y : real) (z : real) (w : real) (h1 : term44 w x y z) (h2 : term45 w) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630514 x y z w h1 h2) (@lem1630402 w h2)). Qed.
Lemma lem1630516 (x : real) (y : real) (z : real) (w : real) (h1 : term43 w x y z) (h2 : term45 w) : (term44 w x y z) = (term58 w y x z).
Proof. exact (prop_ext (fun h3 : term44 w x y z => @lem1630515 x y z w h3 h2) (fun h3 : term58 w y x z => @lem1630494 w x y z h1)). Qed.
Lemma lem1630517 (x : real) (y : real) (z : real) (w : real) (h1 : term43 w x y z) (h2 : term45 w) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630516 x y z w h1 h2) (@lem1630494 w x y z h1)). Qed.
Lemma lem1630518 (w : real) (x : real) (y : real) (z : real) (h1 : term43 w x y z) : (term45 w) = (term58 w y x z).
Proof. exact (prop_ext (fun h2 : term45 w => @lem1630517 x y z w h1 h2) (fun h2 : term58 w y x z => @lem1630495 w x y z h1)). Qed.
Lemma lem1630519 (w : real) (x : real) (y : real) (z : real) (h1 : term43 w x y z) : term58 w y x z.
Proof. exact (EQ_MP (@lem1630518 w x y z h1) (@lem1630495 w x y z h1)). Qed.
Lemma lem1630520 (w : real) (y : real) (x : real) (z : real) : term59 w y x z.
Proof. exact (fun h0 : term43 w x y z => @lem1630519 w x y z h0). Qed.
Lemma lem1630525 (w : real) (y : real) (x : real) : term60 w y x.
Proof. exact (fun z : real => @lem1630520 w y x z). Qed.
Lemma lem1630530 (w : real) (x : real) : term61 w x.
Proof. exact (fun y : real => @lem1630525 w y x). Qed.
Lemma lem1630535 (w : real) : term62 w.
Proof. exact (fun x : real => @lem1630530 w x). Qed.
Lemma lem1630540 : term63.
Proof. exact (fun w : real => @lem1630535 w). Qed.
