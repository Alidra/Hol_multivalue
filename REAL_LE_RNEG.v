Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RNEG_term_abbrevs.
Require Import REAL_LE_LNEG_spec.
Require Import REAL_LE_NEG2_spec.
Require Import REAL_NEG_ADD_spec.
Require Import REAL_NEG_NEG_spec.
Require Import thm1338238_spec.
Require Import thm1338588_spec.
Lemma lem1362292 (x : real) : term0 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1362293 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1362295 (x : real) : term2 x.
Proof. exact (@lem1361095 x). Qed.
Lemma lem1362296 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1362297 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1362296 x) (@lem1362295 x)). Qed.
Lemma lem1362298 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1362297 x y). Qed.
Lemma lem1362299 (x : real) (y : real) : (term4 x y) = ((term5 x y) = (term6 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1362302 (x : real) (h1 : (term7 x) = term8) : (term7 x) = term8.
Proof. exact (h1). Qed.
Lemma lem1362303 (x : real) (h1 : (term7 x) = term8) : term8 = (term7 x).
Proof. exact (SYM (@lem1362302 x h1)). Qed.
Lemma lem1362304 (x : real) (h1 : term8 = (term7 x)) : term8 = (term7 x).
Proof. exact (h1). Qed.
Lemma lem1362305 (x : real) (h1 : term8 = (term7 x)) : (term7 x) = term8.
Proof. exact (SYM (@lem1362304 x h1)). Qed.
Lemma lem1362306 (x : real) : ((term7 x) = term8) = (term8 = (term7 x)).
Proof. exact (prop_ext (fun h1 : (term7 x) = term8 => @lem1362303 x h1) (fun h1 : term8 = (term7 x) => @lem1362305 x h1)). Qed.
Lemma lem1362307 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1362306 x)). Qed.
Lemma lem1362308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362309 : term11 = term12.
Proof. exact (MK_COMB (@lem1362308) (@lem1362307)). Qed.
Lemma lem1362310 : term12.
Proof. exact (EQ_MP (@lem1362309) (@lem1338588)). Qed.
Lemma lem1362311 (x : real) : term13 x.
Proof. exact (@lem1362310 x). Qed.
Lemma lem1362312 (x : real) : (term13 x) = (term8 = (term7 x)).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1362316 (y : real) (x : real) (h1 : (term14 x y) = (real_le y x)) : (term14 x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem1362317 (y : real) (x : real) (h1 : (term14 x y) = (real_le y x)) : (real_le y x) = (term14 x y).
Proof. exact (SYM (@lem1362316 y x h1)). Qed.
Lemma lem1362318 (x : real) (y : real) (h1 : (real_le y x) = (term14 x y)) : (real_le y x) = (term14 x y).
Proof. exact (h1). Qed.
Lemma lem1362319 (x : real) (y : real) (h1 : (real_le y x) = (term14 x y)) : (term14 x y) = (real_le y x).
Proof. exact (SYM (@lem1362318 x y h1)). Qed.
Lemma lem1362320 (x : real) (y : real) : ((term14 x y) = (real_le y x)) = ((real_le y x) = (term14 x y)).
Proof. exact (prop_ext (fun h1 : (term14 x y) = (real_le y x) => @lem1362317 y x h1) (fun h1 : (real_le y x) = (term14 x y) => @lem1362319 x y h1)). Qed.
Lemma lem1362321 (x : real) : (term15 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1362320 x y)). Qed.
Lemma lem1362322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362323 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1362322) (@lem1362321 x)). Qed.
Lemma lem1362324 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1362323 x)). Qed.
Lemma lem1362325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362326 : term21 = term22.
Proof. exact (MK_COMB (@lem1362325) (@lem1362324)). Qed.
Lemma lem1362327 : term22.
Proof. exact (EQ_MP (@lem1362326) (@lem1362291)). Qed.
Lemma lem1362328 (x : real) : term23 x.
Proof. exact (@lem1362327 x). Qed.
Lemma lem1362329 (x : real) : (term23 x) = (term18 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1362330 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem1362329 x) (@lem1362328 x)). Qed.
Lemma lem1362331 (x : real) (y : real) : term24 x y.
Proof. exact (@lem1362330 x y). Qed.
Lemma lem1362332 (x : real) (y : real) : (term24 x y) = ((real_le y x) = (term14 x y)).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1362336 (x : real) (y : real) (h1 : (term5 x y) = (term6 x y)) : (term5 x y) = (term6 x y).
Proof. exact (h1). Qed.
Lemma lem1362337 (x : real) (y : real) (h1 : (term5 x y) = (term6 x y)) : (term6 x y) = (term5 x y).
Proof. exact (SYM (@lem1362336 x y h1)). Qed.
Lemma lem1362338 (x : real) (y : real) (h1 : (term6 x y) = (term5 x y)) : (term6 x y) = (term5 x y).
Proof. exact (h1). Qed.
Lemma lem1362339 (x : real) (y : real) (h1 : (term6 x y) = (term5 x y)) : (term5 x y) = (term6 x y).
Proof. exact (SYM (@lem1362338 x y h1)). Qed.
Lemma lem1362340 (x : real) (y : real) : ((term5 x y) = (term6 x y)) = ((term6 x y) = (term5 x y)).
Proof. exact (prop_ext (fun h1 : (term5 x y) = (term6 x y) => @lem1362337 x y h1) (fun h1 : (term6 x y) = (term5 x y) => @lem1362339 x y h1)). Qed.
Lemma lem1362341 (x : real) : (term25 x) = (term26 x).
Proof. exact (fun_ext (fun y : real => @lem1362340 x y)). Qed.
Lemma lem1362342 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362343 (x : real) : (term3 x) = (term27 x).
Proof. exact (MK_COMB (@lem1362342) (@lem1362341 x)). Qed.
Lemma lem1362344 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1362343 x)). Qed.
Lemma lem1362345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362346 : term30 = term31.
Proof. exact (MK_COMB (@lem1362345) (@lem1362344)). Qed.
Lemma lem1362347 : term31.
Proof. exact (EQ_MP (@lem1362346) (@lem1361095)). Qed.
Lemma lem1362348 (x : real) : term32 x.
Proof. exact (@lem1362347 x). Qed.
Lemma lem1362349 (x : real) : (term32 x) = (term27 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1362350 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1362349 x) (@lem1362348 x)). Qed.
Lemma lem1362351 (x : real) (y : real) : term33 x y.
Proof. exact (@lem1362350 x y). Qed.
Lemma lem1362352 (x : real) (y : real) : (term33 x y) = ((term6 x y) = (term5 x y)).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1362354 (x : real) : term34 x.
Proof. exact (@lem1362225 x). Qed.
Lemma lem1362355 (x : real) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem1362356 (x : real) : term35 x.
Proof. exact (EQ_MP (@lem1362355 x) (@lem1362354 x)). Qed.
Lemma lem1362357 (x : real) (y : real) : term36 x y.
Proof. exact (@lem1362356 x y). Qed.
Lemma lem1362358 (x : real) (y : real) : (term36 x y) = ((term37 x y) = (term38 x y)).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1362361 (x : real) (h1 : (term1 x) = x) : (term1 x) = x.
Proof. exact (h1). Qed.
Lemma lem1362362 (x : real) (h1 : (term1 x) = x) : x = (term1 x).
Proof. exact (SYM (@lem1362361 x h1)). Qed.
Lemma lem1362363 (x : real) (h1 : x = (term1 x)) : x = (term1 x).
Proof. exact (h1). Qed.
Lemma lem1362364 (x : real) (h1 : x = (term1 x)) : (term1 x) = x.
Proof. exact (SYM (@lem1362363 x h1)). Qed.
Lemma lem1362365 (x : real) : ((term1 x) = x) = (x = (term1 x)).
Proof. exact (prop_ext (fun h1 : (term1 x) = x => @lem1362362 x h1) (fun h1 : x = (term1 x) => @lem1362364 x h1)). Qed.
Lemma lem1362366 : term39 = term40.
Proof. exact (fun_ext (fun x : real => @lem1362365 x)). Qed.
Lemma lem1362367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362368 : term41 = term42.
Proof. exact (MK_COMB (@lem1362367) (@lem1362366)). Qed.
Lemma lem1362369 : term42.
Proof. exact (EQ_MP (@lem1362368) (@lem1358662)). Qed.
Lemma lem1362370 (x : real) : term43 x.
Proof. exact (@lem1362369 x). Qed.
Lemma lem1362371 (x : real) : (term43 x) = (x = (term1 x)).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1362374 (x : real) : x = (term1 x).
Proof. exact (EQ_MP (@lem1362371 x) (@lem1362370 x)). Qed.
Lemma lem1362375 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1362376 (x : real) : (real_le x) = (term44 x).
Proof. exact (MK_COMB (@lem1362375) (@lem1362374 x)). Qed.
Lemma lem1362377 (y : real) : (real_neg y) = (real_neg y).
Proof. exact (eq_refl (real_neg y)). Qed.
Lemma lem1362378 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1362376 x) (@lem1362377 y)). Qed.
Lemma lem1362379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1362380 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1362379) (@lem1362378 x y)). Qed.
Lemma lem1362381 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1362382 (x : real) (y : real) : ((term45 x y) = (term49 x y)) = ((term46 x y) = (term49 x y)).
Proof. exact (MK_COMB (@lem1362380 x y) (@lem1362381 x y)). Qed.
Lemma lem1362383 (x : real) (y : real) : ((term46 x y) = (term49 x y)) = ((term45 x y) = (term49 x y)).
Proof. exact (SYM (@lem1362382 x y)). Qed.
Lemma lem1362387 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (EQ_MP (@lem1362358 x y) (@lem1362357 x y)). Qed.
Lemma lem1362388 (x : real) (y : real) : (term46 x y) = (term50 x y).
Proof. exact (@lem1362387 (real_neg x) (real_neg y)). Qed.
Lemma lem1362390 (x : real) (y : real) : (term6 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1362352 x y) (@lem1362351 x y)). Qed.
Lemma lem1362391 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1362392 (x : real) (y : real) : (term50 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1362391) (@lem1362390 x y)). Qed.
Lemma lem1362393 (x : real) (y : real) : (term46 x y) = (term52 x y).
Proof. exact (TRANS (@lem1362388 x y) (@lem1362392 x y)). Qed.
Lemma lem1362394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1362395 (x : real) (y : real) : (term48 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1362394) (@lem1362393 x y)). Qed.
Lemma lem1362396 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1362397 (x : real) (y : real) : ((term46 x y) = (term49 x y)) = ((term52 x y) = (term49 x y)).
Proof. exact (MK_COMB (@lem1362395 x y) (@lem1362396 x y)). Qed.
Lemma lem1362400 (x : real) (y : real) : ((term52 x y) = (term49 x y)) = ((term46 x y) = (term49 x y)).
Proof. exact (SYM (@lem1362397 x y)). Qed.
Lemma lem1362402 (x : real) (y : real) : (real_le y x) = (term14 x y).
Proof. exact (EQ_MP (@lem1362332 x y) (@lem1362331 x y)). Qed.
Lemma lem1362403 (x : real) (y : real) : (term49 x y) = (term54 x y).
Proof. exact (@lem1362402 term8 (real_add x y)). Qed.
Lemma lem1362404 (x : real) (y : real) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem1362405 (x : real) (y : real) : ((term52 x y) = (term49 x y)) = ((term52 x y) = (term54 x y)).
Proof. exact (MK_COMB (@lem1362404 x y) (@lem1362403 x y)). Qed.
Lemma lem1362406 (x : real) (y : real) : ((term52 x y) = (term54 x y)) = ((term52 x y) = (term49 x y)).
Proof. exact (SYM (@lem1362405 x y)). Qed.
Lemma lem1362407 (x : real) (y : real) : (term5 x y) = (term5 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1362408 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1362412 (x : real) : term8 = (term7 x).
Proof. exact (EQ_MP (@lem1362312 x) (@lem1362311 x)). Qed.
Lemma lem1362413 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362414 (x : real) : term55 = (term56 x).
Proof. exact (MK_COMB (@lem1362413) (@lem1362412 x)). Qed.
Lemma lem1362416 (x : real) : term8 = (term7 x).
Proof. exact (EQ_MP (@lem1362312 x) (@lem1362311 x)). Qed.
Lemma lem1362417 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1362418 (x : real) : term57 = (term58 x).
Proof. exact (MK_COMB (@lem1362417) (@lem1362416 x)). Qed.
Lemma lem1362419 (x : real) : (term8 = term57) = ((term7 x) = (term58 x)).
Proof. exact (MK_COMB (@lem1362414 x) (@lem1362418 x)). Qed.
Lemma lem1362422 (x : real) : ((term7 x) = (term58 x)) = (term8 = term57).
Proof. exact (SYM (@lem1362419 x)). Qed.
Lemma lem1362426 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1362299 x y) (@lem1362298 x y)). Qed.
Lemma lem1362427 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1362426 (real_neg x) x). Qed.
Lemma lem1362429 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1362293 x) (@lem1362292 x)). Qed.
Lemma lem1362430 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1362431 (x : real) : (term60 x) = (real_add x).
Proof. exact (MK_COMB (@lem1362430) (@lem1362429 x)). Qed.
Lemma lem1362432 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1362433 (x : real) : (term59 x) = (term61 x).
Proof. exact (MK_COMB (@lem1362431 x) (@lem1362432 x)). Qed.
Lemma lem1362434 (x : real) : (term58 x) = (term61 x).
Proof. exact (TRANS (@lem1362427 x) (@lem1362433 x)). Qed.
Lemma lem1362435 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1362436 (x : real) : ((term7 x) = (term58 x)) = ((term7 x) = (term61 x)).
Proof. exact (MK_COMB (@lem1362435 x) (@lem1362434 x)). Qed.
Lemma lem1362439 (x : real) : ((term7 x) = (term61 x)) = ((term7 x) = (term58 x)).
Proof. exact (SYM (@lem1362436 x)). Qed.
Lemma lem1362440 (x : real) : term62 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1362441 (x : real) : (term62 x) = (term63 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1362442 (x : real) : term63 x.
Proof. exact (EQ_MP (@lem1362441 x) (@lem1362440 x)). Qed.
Lemma lem1362443 (x : real) (y : real) : term64 x y.
Proof. exact (@lem1362442 x y). Qed.
Lemma lem1362444 (y : real) (x : real) : (term64 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1362447 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1362444 y x) (@lem1362443 x y)). Qed.
Lemma lem1362448 (x : real) : (term7 x) = (term61 x).
Proof. exact (@lem1362447 x (real_neg x)). Qed.
Lemma lem1362449 (x : real) : (term7 x) = (term58 x).
Proof. exact (EQ_MP (@lem1362439 x) (@lem1362448 x)). Qed.
Lemma lem1362450 : term8 = term57.
Proof. exact (EQ_MP (@lem1362422 (@el real)) (@lem1362449 (@el real))). Qed.
Lemma lem1362451 : term51 = term65.
Proof. exact (MK_COMB (@lem1362408) (@lem1362450)). Qed.
Lemma lem1362452 (x : real) (y : real) : (term52 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1362451) (@lem1362407 x y)). Qed.
Lemma lem1362453 (x : real) (y : real) : (term52 x y) = (term49 x y).
Proof. exact (EQ_MP (@lem1362406 x y) (@lem1362452 x y)). Qed.
Lemma lem1362454 (x : real) (y : real) : (term46 x y) = (term49 x y).
Proof. exact (EQ_MP (@lem1362400 x y) (@lem1362453 x y)). Qed.
Lemma lem1362455 (x : real) (y : real) : (term45 x y) = (term49 x y).
Proof. exact (EQ_MP (@lem1362383 x y) (@lem1362454 x y)). Qed.
Lemma lem1362460 (x : real) : term66 x.
Proof. exact (fun y : real => @lem1362455 x y). Qed.
Lemma lem1362465 : term67.
Proof. exact (fun x : real => @lem1362460 x). Qed.
