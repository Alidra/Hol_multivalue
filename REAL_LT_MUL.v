Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_MUL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ENTIRE_spec.
Require Import REAL_LT_LE_spec.
Require Import thm0_spec.
Require Import thm1340049_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1487295 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1487296 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1487295 h1 x). Qed.
Lemma lem1487297 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1487298 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1487297 x) (@lem1487296 x h1)). Qed.
Lemma lem1487299 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1487298 x h1 y). Qed.
Lemma lem1487300 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1487301 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1487300 x y) (@lem1487299 x y h1)). Qed.
Lemma lem1487302 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1487303 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1487301 x y h1 (@lem1487302 x y h2)). Qed.
Lemma lem1487304 (x : real) (y : real) (h1 : term5 x y) : term7 x y.
Proof. exact (fun h0 : term0 => @lem1487303 x y h0 h1). Qed.
Lemma lem1487305 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1487306 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 x y.
Proof. exact (@lem1487304 x y h2 (@lem1487305 h1)). Qed.
Lemma lem1487307 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : term5 x y => @lem1487306 x y h1 h0). Qed.
Lemma lem1487308 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1487307 x y h1). Qed.
Lemma lem1487309 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1487308 x h1). Qed.
Lemma lem1487310 : term8.
Proof. exact (fun h0 : term0 => @lem1487309 h0). Qed.
Lemma lem1487311 : term0.
Proof. exact (@lem1487310 (@lem1340049)). Qed.
Lemma lem1487312 (x : real) : term1 x.
Proof. exact (@lem1487311 x). Qed.
Lemma lem1487313 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1487314 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1487313 x) (@lem1487312 x)). Qed.
Lemma lem1487315 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1487314 x y). Qed.
Lemma lem1487316 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1487318 (x : real) : term9 x.
Proof. exact (@lem1379381 x). Qed.
Lemma lem1487319 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1487320 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1487319 x) (@lem1487318 x)). Qed.
Lemma lem1487321 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1487320 x y). Qed.
Lemma lem1487322 (x : real) (y : real) : (term11 x y) = ((real_lt x y) = (term12 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1487329 (x : real) (y : real) : (real_lt x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1487322 x y) (@lem1487321 x y)). Qed.
Lemma lem1487330 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1487329 term15 x). Qed.
Lemma lem1487335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1487336 (x : real) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1487335) (@lem1487330 x)). Qed.
Lemma lem1487338 (x : real) (y : real) : (real_lt x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1487322 x y) (@lem1487321 x y)). Qed.
Lemma lem1487339 (y : real) : (term13 y) = (term14 y).
Proof. exact (@lem1487338 term15 y). Qed.
Lemma lem1487344 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem1487336 x) (@lem1487339 y)). Qed.
Lemma lem1487347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1487348 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1487347) (@lem1487344 x y)). Qed.
Lemma lem1487350 (x : real) (y : real) : (real_lt x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1487322 x y) (@lem1487321 x y)). Qed.
Lemma lem1487351 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1487350 term15 (real_mul x y)). Qed.
Lemma lem1487356 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1487348 x y) (@lem1487351 x y)). Qed.
Lemma lem1487359 (x : real) (y : real) : (term25 x y) = (term24 x y).
Proof. exact (SYM (@lem1487356 x y)). Qed.
Lemma lem1487365 (x : real) (h1 : term15 = x) : term15 = x.
Proof. exact (h1). Qed.
Lemma lem1487366 (x : real) (h1 : term15 = x) : x = term15.
Proof. exact (SYM (@lem1487365 x h1)). Qed.
Lemma lem1487367 (x : real) (h1 : x = term15) : x = term15.
Proof. exact (h1). Qed.
Lemma lem1487368 (x : real) (h1 : x = term15) : term15 = x.
Proof. exact (SYM (@lem1487367 x h1)). Qed.
Lemma lem1487369 (x : real) : (term15 = x) = (x = term15).
Proof. exact (prop_ext (fun h1 : term15 = x => @lem1487366 x h1) (fun h1 : x = term15 => @lem1487368 x h1)). Qed.
Lemma lem1487370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487371 (x : real) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem1487370) (@lem1487369 x)). Qed.
Lemma lem1487372 (x : real) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1487373 (x : real) : (term14 x) = (term29 x).
Proof. exact (MK_COMB (@lem1487372 x) (@lem1487371 x)). Qed.
Lemma lem1487374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1487375 (x : real) : (term17 x) = (term30 x).
Proof. exact (MK_COMB (@lem1487374) (@lem1487373 x)). Qed.
Lemma lem1487379 (y : real) (h1 : term15 = y) : term15 = y.
Proof. exact (h1). Qed.
Lemma lem1487380 (y : real) (h1 : term15 = y) : y = term15.
Proof. exact (SYM (@lem1487379 y h1)). Qed.
Lemma lem1487381 (y : real) (h1 : y = term15) : y = term15.
Proof. exact (h1). Qed.
Lemma lem1487382 (y : real) (h1 : y = term15) : term15 = y.
Proof. exact (SYM (@lem1487381 y h1)). Qed.
Lemma lem1487383 (y : real) : (term15 = y) = (y = term15).
Proof. exact (prop_ext (fun h1 : term15 = y => @lem1487380 y h1) (fun h1 : y = term15 => @lem1487382 y h1)). Qed.
Lemma lem1487384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487385 (y : real) : (term26 y) = (term27 y).
Proof. exact (MK_COMB (@lem1487384) (@lem1487383 y)). Qed.
Lemma lem1487386 (y : real) : (term28 y) = (term28 y).
Proof. exact (eq_refl (term28 y)). Qed.
Lemma lem1487387 (y : real) : (term14 y) = (term29 y).
Proof. exact (MK_COMB (@lem1487386 y) (@lem1487385 y)). Qed.
Lemma lem1487388 (x : real) (y : real) : (term19 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1487375 x) (@lem1487387 y)). Qed.
Lemma lem1487389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1487390 (x : real) (y : real) : (term21 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1487389) (@lem1487388 x y)). Qed.
Lemma lem1487394 (x : real) (y : real) (h1 : term15 = (real_mul x y)) : term15 = (real_mul x y).
Proof. exact (h1). Qed.
Lemma lem1487395 (x : real) (y : real) (h1 : term15 = (real_mul x y)) : (real_mul x y) = term15.
Proof. exact (SYM (@lem1487394 x y h1)). Qed.
Lemma lem1487396 (x : real) (y : real) (h1 : (real_mul x y) = term15) : (real_mul x y) = term15.
Proof. exact (h1). Qed.
Lemma lem1487397 (x : real) (y : real) (h1 : (real_mul x y) = term15) : term15 = (real_mul x y).
Proof. exact (SYM (@lem1487396 x y h1)). Qed.
Lemma lem1487398 (x : real) (y : real) : (term15 = (real_mul x y)) = ((real_mul x y) = term15).
Proof. exact (prop_ext (fun h1 : term15 = (real_mul x y) => @lem1487395 x y h1) (fun h1 : (real_mul x y) = term15 => @lem1487397 x y h1)). Qed.
Lemma lem1487399 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487400 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1487399) (@lem1487398 x y)). Qed.
Lemma lem1487401 (x : real) (y : real) : (term35 x y) = (term35 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem1487402 (x : real) (y : real) : (term23 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1487401 x y) (@lem1487400 x y)). Qed.
Lemma lem1487403 (x : real) (y : real) : (term25 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1487390 x y) (@lem1487402 x y)). Qed.
Lemma lem1487404 (x : real) (y : real) : (term37 x y) = (term25 x y).
Proof. exact (SYM (@lem1487403 x y)). Qed.
Lemma lem1487405 (x : real) (y : real) (h1 : term31 x y) : term31 x y.
Proof. exact (h1). Qed.
Lemma lem1487406 (y : real) (h1 : term29 y) : term29 y.
Proof. exact (h1). Qed.
Lemma lem1487407 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1487408 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1487409 (x : real) (h1 : term38 x) : term38 x.
Proof. exact (h1). Qed.
Lemma lem1487410 (y : real) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1487411 (y : real) (h1 : term38 y) : term38 y.
Proof. exact (h1). Qed.
Lemma lem1487412 (x : real) : term39 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1487413 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1487414 (x : real) : term40 x.
Proof. exact (EQ_MP (@lem1487413 x) (@lem1487412 x)). Qed.
Lemma lem1487415 (x : real) (y : real) : term41 x y.
Proof. exact (@lem1487414 x y). Qed.
Lemma lem1487416 (x : real) (y : real) : (term41 x y) = (((real_mul x y) = term15) = (term42 x y)).
Proof. exact (eq_refl (term41 x y)). Qed.
Lemma lem1487420 (x : real) : term43 x.
Proof. exact (@lem82 (x = term15)). Qed.
Lemma lem1487435 (y : real) : term43 y.
Proof. exact (@lem82 (y = term15)). Qed.
Lemma lem1487451 (x : real) (y : real) : ((real_mul x y) = term15) = (term42 x y).
Proof. exact (EQ_MP (@lem1487416 x y) (@lem1487415 x y)). Qed.
Lemma lem1487455 (x : real) (h1 : term27 x) : (x = term15) = False.
Proof. exact (@lem1487420 x (@lem1487408 x h1)). Qed.
Lemma lem1487456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1487457 (x : real) (h1 : term27 x) : (term44 x) = (or False).
Proof. exact (MK_COMB (@lem1487456) (@lem1487455 x h1)). Qed.
Lemma lem1487459 (y : real) (h1 : term27 y) : (y = term15) = False.
Proof. exact (@lem1487435 y (@lem1487410 y h1)). Qed.
Lemma lem1487460 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term42 x y) = (False \/ False).
Proof. exact (MK_COMB (@lem1487457 x h1) (@lem1487459 y h2)). Qed.
Lemma lem1487462 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1487463 : (False \/ False) = False.
Proof. exact (@lem1487462 False). Qed.
Lemma lem1487464 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term42 x y) = False.
Proof. exact (TRANS (@lem1487460 x y h1 h2) (@lem1487463)). Qed.
Lemma lem1487465 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : ((real_mul x y) = term15) = False.
Proof. exact (TRANS (@lem1487451 x y) (@lem1487464 x y h1 h2)). Qed.
Lemma lem1487466 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487467 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term34 x y) = (~ False).
Proof. exact (MK_COMB (@lem1487466) (@lem1487465 x y h1 h2)). Qed.
Lemma lem1487469 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1487470 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term34 x y) = True.
Proof. exact (TRANS (@lem1487467 x y h1 h2) (@lem1487469)). Qed.
Lemma lem1487471 (x : real) (y : real) : (term35 x y) = (term35 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem1487472 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term36 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1487471 x y) (@lem1487470 x y h1 h2)). Qed.
Lemma lem1487474 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1487475 (x : real) (y : real) : (term45 x y) = (term6 x y).
Proof. exact (@lem1487474 (term6 x y)). Qed.
Lemma lem1487476 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term36 x y) = (term6 x y).
Proof. exact (TRANS (@lem1487472 x y h1 h2) (@lem1487475 x y)). Qed.
Lemma lem1487477 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) : (term6 x y) = (term36 x y).
Proof. exact (SYM (@lem1487476 x y h1 h2)). Qed.
Lemma lem1487479 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1487316 x y) (@lem1487315 x y)). Qed.
Lemma lem1487480 (x : real) : (term38 x) = ((term38 x) = True).
Proof. exact (@lem7 (term38 x)). Qed.
Lemma lem1487495 (y : real) : (term38 y) = ((term38 y) = True).
Proof. exact (@lem7 (term38 y)). Qed.
Lemma lem1487513 (x : real) (h1 : term38 x) : (term38 x) = True.
Proof. exact (EQ_MP (@lem1487480 x) (@lem1487409 x h1)). Qed.
Lemma lem1487514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1487515 (x : real) (h1 : term38 x) : (term28 x) = (and True).
Proof. exact (MK_COMB (@lem1487514) (@lem1487513 x h1)). Qed.
Lemma lem1487517 (y : real) (h1 : term38 y) : (term38 y) = True.
Proof. exact (EQ_MP (@lem1487495 y) (@lem1487411 y h1)). Qed.
Lemma lem1487518 (x : real) (y : real) (h1 : term38 x) (h2 : term38 y) : (term5 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1487515 x h1) (@lem1487517 y h2)). Qed.
Lemma lem1487520 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1487521 : (True /\ True) = True.
Proof. exact (@lem1487520 True). Qed.
Lemma lem1487522 (x : real) (y : real) (h1 : term38 x) (h2 : term38 y) : (term5 x y) = True.
Proof. exact (TRANS (@lem1487518 x y h1 h2) (@lem1487521)). Qed.
Lemma lem1487523 (x : real) (y : real) (h1 : term38 x) (h2 : term38 y) : True = (term5 x y).
Proof. exact (SYM (@lem1487522 x y h1 h2)). Qed.
Lemma lem1487524 (x : real) (y : real) (h1 : term38 x) (h2 : term38 y) : term5 x y.
Proof. exact (EQ_MP (@lem1487523 x y h1 h2) (@lem0)). Qed.
Lemma lem1487525 (x : real) (y : real) (h1 : term38 x) (h2 : term38 y) : term6 x y.
Proof. exact (@lem1487479 x y (@lem1487524 x y h1 h2)). Qed.
Lemma lem1487526 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) (h3 : term38 x) (h4 : term38 y) : term36 x y.
Proof. exact (EQ_MP (@lem1487477 x y h1 h2) (@lem1487525 x y h3 h4)). Qed.
Lemma lem1487527 (x : real) (y : real) (h1 : term31 x y) : term29 y.
Proof. exact (proj2 (@lem1487405 x y h1)). Qed.
Lemma lem1487528 (x : real) (y : real) (h1 : term31 x y) : term29 x.
Proof. exact (proj1 (@lem1487405 x y h1)). Qed.
Lemma lem1487529 (y : real) (h1 : term29 y) : term27 y.
Proof. exact (proj2 (@lem1487406 y h1)). Qed.
Lemma lem1487530 (y : real) (h1 : term29 y) : term38 y.
Proof. exact (proj1 (@lem1487406 y h1)). Qed.
Lemma lem1487531 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) (h3 : term38 x) (h4 : term38 y) : (term27 y) = (term36 x y).
Proof. exact (prop_ext (fun h5 : term27 y => @lem1487526 x y h1 h2 h3 h4) (fun h5 : term36 x y => @lem1487410 y h2)). Qed.
Lemma lem1487532 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) (h3 : term38 x) (h4 : term38 y) : term36 x y.
Proof. exact (EQ_MP (@lem1487531 x y h1 h2 h3 h4) (@lem1487410 y h2)). Qed.
Lemma lem1487533 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) (h3 : term38 x) (h4 : term38 y) : (term38 y) = (term36 x y).
Proof. exact (prop_ext (fun h5 : term38 y => @lem1487532 x y h1 h2 h3 h4) (fun h5 : term36 x y => @lem1487411 y h4)). Qed.
Lemma lem1487534 (x : real) (y : real) (h1 : term27 x) (h2 : term27 y) (h3 : term38 x) (h4 : term38 y) : term36 x y.
Proof. exact (EQ_MP (@lem1487533 x y h1 h2 h3 h4) (@lem1487411 y h4)). Qed.
Lemma lem1487535 (x : real) (y : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) (h4 : term38 y) : (term27 y) = (term36 x y).
Proof. exact (prop_ext (fun h5 : term27 y => @lem1487534 x y h1 h5 h3 h4) (fun h5 : term36 x y => @lem1487529 y h2)). Qed.
Lemma lem1487536 (x : real) (y : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) (h4 : term38 y) : term36 x y.
Proof. exact (EQ_MP (@lem1487535 x y h1 h2 h3 h4) (@lem1487529 y h2)). Qed.
Lemma lem1487537 (y : real) (x : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) : (term38 y) = (term36 x y).
Proof. exact (prop_ext (fun h4 : term38 y => @lem1487536 x y h1 h2 h3 h4) (fun h4 : term36 x y => @lem1487530 y h2)). Qed.
Lemma lem1487538 (y : real) (x : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) : term36 x y.
Proof. exact (EQ_MP (@lem1487537 y x h1 h2 h3) (@lem1487530 y h2)). Qed.
Lemma lem1487539 (x : real) (h1 : term29 x) : term27 x.
Proof. exact (proj2 (@lem1487407 x h1)). Qed.
Lemma lem1487540 (x : real) (h1 : term29 x) : term38 x.
Proof. exact (proj1 (@lem1487407 x h1)). Qed.
Lemma lem1487541 (y : real) (x : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) : (term27 x) = (term36 x y).
Proof. exact (prop_ext (fun h4 : term27 x => @lem1487538 y x h1 h2 h3) (fun h4 : term36 x y => @lem1487408 x h1)). Qed.
Lemma lem1487542 (y : real) (x : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) : term36 x y.
Proof. exact (EQ_MP (@lem1487541 y x h1 h2 h3) (@lem1487408 x h1)). Qed.
Lemma lem1487543 (y : real) (x : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) : (term38 x) = (term36 x y).
Proof. exact (prop_ext (fun h4 : term38 x => @lem1487542 y x h1 h2 h3) (fun h4 : term36 x y => @lem1487409 x h3)). Qed.
Lemma lem1487544 (y : real) (x : real) (h1 : term27 x) (h2 : term29 y) (h3 : term38 x) : term36 x y.
Proof. exact (EQ_MP (@lem1487543 y x h1 h2 h3) (@lem1487409 x h3)). Qed.
Lemma lem1487545 (y : real) (x : real) (h1 : term29 x) (h2 : term29 y) (h3 : term38 x) : (term27 x) = (term36 x y).
Proof. exact (prop_ext (fun h4 : term27 x => @lem1487544 y x h4 h2 h3) (fun h4 : term36 x y => @lem1487539 x h1)). Qed.
Lemma lem1487546 (y : real) (x : real) (h1 : term29 x) (h2 : term29 y) (h3 : term38 x) : term36 x y.
Proof. exact (EQ_MP (@lem1487545 y x h1 h2 h3) (@lem1487539 x h1)). Qed.
Lemma lem1487547 (x : real) (y : real) (h1 : term29 x) (h2 : term29 y) : (term38 x) = (term36 x y).
Proof. exact (prop_ext (fun h3 : term38 x => @lem1487546 y x h1 h2 h3) (fun h3 : term36 x y => @lem1487540 x h1)). Qed.
Lemma lem1487548 (x : real) (y : real) (h1 : term29 x) (h2 : term29 y) : term36 x y.
Proof. exact (EQ_MP (@lem1487547 x y h1 h2) (@lem1487540 x h1)). Qed.
Lemma lem1487549 (y : real) (x : real) (h1 : term31 x y) (h2 : term29 x) : (term29 y) = (term36 x y).
Proof. exact (prop_ext (fun h3 : term29 y => @lem1487548 x y h2 h3) (fun h3 : term36 x y => @lem1487527 x y h1)). Qed.
Lemma lem1487550 (y : real) (x : real) (h1 : term31 x y) (h2 : term29 x) : term36 x y.
Proof. exact (EQ_MP (@lem1487549 y x h1 h2) (@lem1487527 x y h1)). Qed.
Lemma lem1487551 (x : real) (y : real) (h1 : term31 x y) : (term29 x) = (term36 x y).
Proof. exact (prop_ext (fun h2 : term29 x => @lem1487550 y x h1 h2) (fun h2 : term36 x y => @lem1487528 x y h1)). Qed.
Lemma lem1487552 (x : real) (y : real) (h1 : term31 x y) : term36 x y.
Proof. exact (EQ_MP (@lem1487551 x y h1) (@lem1487528 x y h1)). Qed.
Lemma lem1487553 (x : real) (y : real) : term37 x y.
Proof. exact (fun h0 : term31 x y => @lem1487552 x y h0). Qed.
Lemma lem1487554 (x : real) (y : real) : term25 x y.
Proof. exact (EQ_MP (@lem1487404 x y) (@lem1487553 x y)). Qed.
Lemma lem1487555 (x : real) (y : real) : term24 x y.
Proof. exact (EQ_MP (@lem1487359 x y) (@lem1487554 x y)). Qed.
Lemma lem1487560 (x : real) : term46 x.
Proof. exact (fun y : real => @lem1487555 x y). Qed.
Lemma lem1487565 : term47.
Proof. exact (fun x : real => @lem1487560 x). Qed.
