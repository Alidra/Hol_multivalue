Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_RNEG_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1519290 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519291 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1519290 (term4 x)). Qed.
Lemma lem1519292 (x : real) (y : real) : (term5 x y) = ((term6 x y) = (real_add x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1519293 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519295 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1519293) (@lem1519292 x y)). Qed.
Lemma lem1519296 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1519295 x y)). Qed.
Lemma lem1519297 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519298 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1519297) (@lem1519296 x)). Qed.
Lemma lem1519299 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1519291 x) (@lem1519298 x)). Qed.
Lemma lem1519300 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519301 : term12 = term13.
Proof. exact (@lem1519300 term14). Qed.
Lemma lem1519302 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1519303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519304 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1519303) (@lem1519302 x)). Qed.
Lemma lem1519305 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1519304 x) (@lem1519299 x)). Qed.
Lemma lem1519306 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1519305 x)). Qed.
Lemma lem1519307 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519308 : term13 = term20.
Proof. exact (MK_COMB (@lem1519307) (@lem1519306)). Qed.
Lemma lem1519310 : term12 = term20.
Proof. exact (TRANS (@lem1519301) (@lem1519308)). Qed.
Lemma lem1519313 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1519314 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1519313 x y)). Qed.
Lemma lem1519315 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519316 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1519315) (@lem1519314 x)). Qed.
Lemma lem1519317 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1519316 x)). Qed.
Lemma lem1519318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519319 : term20 = term20.
Proof. exact (MK_COMB (@lem1519318) (@lem1519317)). Qed.
Lemma lem1519320 : term12 = term20.
Proof. exact (TRANS (@lem1519310) (@lem1519319)). Qed.
Lemma lem1519321 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (term6 x y) (real_add x y)). Qed.
Lemma lem1519328 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (eq_refl (real_add x y)). Qed.
Lemma lem1519335 (y : real) : (real_neg y) = (term22 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1519338 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1519339 (x : real) (y : real) : (term6 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1519338 x) (@lem1519335 y)). Qed.
Lemma lem1519340 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (@lem1483519 x (term22 y)). Qed.
Lemma lem1519341 (y : real) : (term25 y) = (term26 y).
Proof. exact (@lem1483476 term27 term27 y). Qed.
Lemma lem1519343 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1519344 : term30 = term31.
Proof. exact (@lem1519343 term32 term32). Qed.
Lemma lem1519345 : (term33 = (BIT1 0)) = (term34 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1519346 : term34 = term32.
Proof. exact (EQ_MP (@lem1519345) (@lem940073)). Qed.
Lemma lem1519347 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1519348 : term31 = term35.
Proof. exact (MK_COMB (@lem1519347) (@lem1519346)). Qed.
Lemma lem1519349 : term30 = term35.
Proof. exact (TRANS (@lem1519344) (@lem1519348)). Qed.
Lemma lem1519350 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519351 : term36 = term37.
Proof. exact (MK_COMB (@lem1519350) (@lem1519349)). Qed.
Lemma lem1519352 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519353 (y : real) : (term26 y) = (term38 y).
Proof. exact (MK_COMB (@lem1519351) (@lem1519352 y)). Qed.
Lemma lem1519354 (y : real) : (term25 y) = (term38 y).
Proof. exact (TRANS (@lem1519341 y) (@lem1519353 y)). Qed.
Lemma lem1519355 (y : real) : (term38 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1519356 (y : real) : (term25 y) = y.
Proof. exact (TRANS (@lem1519354 y) (@lem1519355 y)). Qed.
Lemma lem1519357 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1519360 (x : real) (y : real) : (term24 x y) = (real_add x y).
Proof. exact (MK_COMB (@lem1519357 x) (@lem1519356 y)). Qed.
Lemma lem1519361 (x : real) (y : real) : (term23 x y) = (real_add x y).
Proof. exact (TRANS (@lem1519340 x y) (@lem1519360 x y)). Qed.
Lemma lem1519362 (x : real) (y : real) : (term6 x y) = (real_add x y).
Proof. exact (TRANS (@lem1519339 x y) (@lem1519361 x y)). Qed.
Lemma lem1519363 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1519364 (x : real) (y : real) : (term39 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1519363) (@lem1519362 x y)). Qed.
Lemma lem1519365 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem1519364 x y) (@lem1519328 x y)). Qed.
Lemma lem1519366 (x : real) (y : real) : (term42 x y) = (term43 x y).
Proof. exact (@lem1483519 (real_add x y) (real_add x y)). Qed.
Lemma lem1519373 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (@lem1483508 x term27 y). Qed.
Lemma lem1519374 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1519375 (x : real) (y : real) : (term43 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1519374 x y) (@lem1519373 x y)). Qed.
Lemma lem1519376 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (@lem1483480 x (term22 x) y (term22 y)). Qed.
Lemma lem1519377 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1483442 term27 x). Qed.
Lemma lem1519379 (m : nat) : (term51 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519380 : term53 = term52.
Proof. exact (@lem1519379 term32). Qed.
Lemma lem1519381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519382 : term54 = term55.
Proof. exact (MK_COMB (@lem1519381) (@lem1519380)). Qed.
Lemma lem1519383 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1519384 (x : real) : (term50 x) = (term56 x).
Proof. exact (MK_COMB (@lem1519382) (@lem1519383 x)). Qed.
Lemma lem1519385 (x : real) : (term49 x) = (term56 x).
Proof. exact (TRANS (@lem1519377 x) (@lem1519384 x)). Qed.
Lemma lem1519386 (x : real) : (term56 x) = term52.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1519387 (x : real) : (term49 x) = term52.
Proof. exact (TRANS (@lem1519385 x) (@lem1519386 x)). Qed.
Lemma lem1519388 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519389 (x : real) : (term57 x) = term58.
Proof. exact (MK_COMB (@lem1519388) (@lem1519387 x)). Qed.
Lemma lem1519390 (y : real) : (term49 y) = (term50 y).
Proof. exact (@lem1483442 term27 y). Qed.
Lemma lem1519392 (m : nat) : (term51 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519393 : term53 = term52.
Proof. exact (@lem1519392 term32). Qed.
Lemma lem1519394 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519395 : term54 = term55.
Proof. exact (MK_COMB (@lem1519394) (@lem1519393)). Qed.
Lemma lem1519396 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519397 (y : real) : (term50 y) = (term56 y).
Proof. exact (MK_COMB (@lem1519395) (@lem1519396 y)). Qed.
Lemma lem1519398 (y : real) : (term49 y) = (term56 y).
Proof. exact (TRANS (@lem1519390 y) (@lem1519397 y)). Qed.
Lemma lem1519399 (y : real) : (term56 y) = term52.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1519400 (y : real) : (term49 y) = term52.
Proof. exact (TRANS (@lem1519398 y) (@lem1519399 y)). Qed.
Lemma lem1519401 (x : real) (y : real) : (term48 x y) = term59.
Proof. exact (MK_COMB (@lem1519389 x) (@lem1519400 y)). Qed.
Lemma lem1519402 (x : real) (y : real) : (term47 x y) = term59.
Proof. exact (TRANS (@lem1519376 x y) (@lem1519401 x y)). Qed.
Lemma lem1519403 : term59 = term52.
Proof. exact (@lem1483448 term52). Qed.
Lemma lem1519404 (x : real) (y : real) : (term47 x y) = term52.
Proof. exact (TRANS (@lem1519402 x y) (@lem1519403)). Qed.
Lemma lem1519405 (x : real) (y : real) : (term43 x y) = term52.
Proof. exact (TRANS (@lem1519375 x y) (@lem1519404 x y)). Qed.
Lemma lem1519406 (x : real) (y : real) : (term42 x y) = term52.
Proof. exact (TRANS (@lem1519366 x y) (@lem1519405 x y)). Qed.
Lemma lem1519407 (x : real) (y : real) : (term41 x y) = term52.
Proof. exact (TRANS (@lem1519365 x y) (@lem1519406 x y)). Qed.
Lemma lem1519408 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1519409 (x : real) (y : real) : (term60 x y) = term61.
Proof. exact (MK_COMB (@lem1519408) (@lem1519407 x y)). Qed.
Lemma lem1519410 : term61 = term62.
Proof. exact (@lem1483512 term52). Qed.
Lemma lem1519412 (x : nat) : (term63 x) = term52.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1519413 : term62 = term52.
Proof. exact (@lem1519412 term32). Qed.
Lemma lem1519414 : term61 = term52.
Proof. exact (TRANS (@lem1519410) (@lem1519413)). Qed.
Lemma lem1519415 (x : real) (y : real) : (term64 x y) = (term64 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1519416 (x : real) (y : real) : ((term60 x y) = term61) = ((term60 x y) = term52).
Proof. exact (MK_COMB (@lem1519415 x y) (@lem1519414)). Qed.
Lemma lem1519417 (x : real) (y : real) : (term60 x y) = term52.
Proof. exact (EQ_MP (@lem1519416 x y) (@lem1519409 x y)). Qed.
Lemma lem1519418 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1519419 (x : real) (y : real) : (term65 x y) = term66.
Proof. exact (MK_COMB (@lem1519418) (@lem1519417 x y)). Qed.
Lemma lem1519420 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1519421 (x : real) (y : real) : (term67 x y) = term68.
Proof. exact (MK_COMB (@lem1519419 x y) (@lem1519420)). Qed.
Lemma lem1519422 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1519423 (x : real) (y : real) : (term69 x y) = term66.
Proof. exact (MK_COMB (@lem1519422) (@lem1519407 x y)). Qed.
Lemma lem1519424 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem1519425 (x : real) (y : real) : (term70 x y) = term68.
Proof. exact (MK_COMB (@lem1519423 x y) (@lem1519424)). Qed.
Lemma lem1519426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519427 (x : real) (y : real) : (term71 x y) = term72.
Proof. exact (MK_COMB (@lem1519426) (@lem1519425 x y)). Qed.
Lemma lem1519428 (x : real) (y : real) : (term21 x y) = term73.
Proof. exact (MK_COMB (@lem1519427 x y) (@lem1519421 x y)). Qed.
Lemma lem1519429 (x : real) (y : real) : (term8 x y) = term73.
Proof. exact (TRANS (@lem1519321 x y) (@lem1519428 x y)). Qed.
Lemma lem1519430 (x : real) : (term10 x) = term74.
Proof. exact (fun_ext (fun y : real => @lem1519429 x y)). Qed.
Lemma lem1519431 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519432 (x : real) : (term11 x) = term75.
Proof. exact (MK_COMB (@lem1519431) (@lem1519430 x)). Qed.
Lemma lem1519433 : term19 = term76.
Proof. exact (fun_ext (fun x : real => @lem1519432 x)). Qed.
Lemma lem1519434 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519435 : term20 = term77.
Proof. exact (MK_COMB (@lem1519434) (@lem1519433)). Qed.
Lemma lem1519436 : term12 = term77.
Proof. exact (TRANS (@lem1519320) (@lem1519435)). Qed.
Lemma lem1519438 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519439 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1519438 real t). Qed.
Lemma lem1519440 : term77 = term75.
Proof. exact (@lem1519439 term75). Qed.
Lemma lem1519442 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1519443 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1519442 real P Q). Qed.
Lemma lem1519444 : term84 = term85.
Proof. exact (@lem1519443 term86 term86). Qed.
Lemma lem1519445 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1519446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519447 (y : real) : (term88 y) = term72.
Proof. exact (MK_COMB (@lem1519446) (@lem1519445 y)). Qed.
Lemma lem1519448 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1519449 (y : real) : (term89 y) = term73.
Proof. exact (MK_COMB (@lem1519447 y) (@lem1519448 y)). Qed.
Lemma lem1519450 : term90 = term74.
Proof. exact (fun_ext (fun y : real => @lem1519449 y)). Qed.
Lemma lem1519451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519452 : term84 = term75.
Proof. exact (MK_COMB (@lem1519451) (@lem1519450)). Qed.
Lemma lem1519453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1519454 : term91 = term92.
Proof. exact (MK_COMB (@lem1519453) (@lem1519452)). Qed.
Lemma lem1519455 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1519456 : term93 = term86.
Proof. exact (fun_ext (fun y : real => @lem1519455 y)). Qed.
Lemma lem1519457 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519458 : term94 = term95.
Proof. exact (MK_COMB (@lem1519457) (@lem1519456)). Qed.
Lemma lem1519459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519460 : term96 = term97.
Proof. exact (MK_COMB (@lem1519459) (@lem1519458)). Qed.
Lemma lem1519461 (y : real) : (term87 y) = term68.
Proof. exact (eq_refl (term87 y)). Qed.
Lemma lem1519462 : term93 = term86.
Proof. exact (fun_ext (fun y : real => @lem1519461 y)). Qed.
Lemma lem1519463 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519464 : term94 = term95.
Proof. exact (MK_COMB (@lem1519463) (@lem1519462)). Qed.
Lemma lem1519465 : term85 = term98.
Proof. exact (MK_COMB (@lem1519460) (@lem1519464)). Qed.
Lemma lem1519466 : (term84 = term85) = (term75 = term98).
Proof. exact (MK_COMB (@lem1519454) (@lem1519465)). Qed.
Lemma lem1519467 : term75 = term98.
Proof. exact (EQ_MP (@lem1519466) (@lem1519444)). Qed.
Lemma lem1519468 : term77 = term98.
Proof. exact (TRANS (@lem1519440) (@lem1519467)). Qed.
Lemma lem1519470 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519471 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1519470 real t). Qed.
Lemma lem1519472 : term95 = term68.
Proof. exact (@lem1519471 term68). Qed.
Lemma lem1519473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519474 : term97 = term72.
Proof. exact (MK_COMB (@lem1519473) (@lem1519472)). Qed.
Lemma lem1519476 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519477 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1519476 real t). Qed.
Lemma lem1519478 : term95 = term68.
Proof. exact (@lem1519477 term68). Qed.
Lemma lem1519479 : term98 = term73.
Proof. exact (MK_COMB (@lem1519474) (@lem1519478)). Qed.
Lemma lem1519482 : term77 = term73.
Proof. exact (TRANS (@lem1519468) (@lem1519479)). Qed.
Lemma lem1519491 : term12 = term73.
Proof. exact (TRANS (@lem1519436) (@lem1519482)). Qed.
Lemma lem1519501 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1519502 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem1519504 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1519505 : term68 = term100.
Proof. exact (@lem1519504 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1519506 : term100 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1519507 : term68 = False.
Proof. exact (TRANS (@lem1519505) (@lem1519506)). Qed.
Lemma lem1519508 (h1 : term68) : False.
Proof. exact (EQ_MP (@lem1519507) (@lem1519502 h1)). Qed.
Lemma lem1519509 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem1519511 (n : nat) (m : nat) : (term99 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1519512 : term68 = term100.
Proof. exact (@lem1519511 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1519513 : term100 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1519514 : term68 = False.
Proof. exact (TRANS (@lem1519512) (@lem1519513)). Qed.
Lemma lem1519515 (h1 : term68) : False.
Proof. exact (EQ_MP (@lem1519514) (@lem1519509 h1)). Qed.
Lemma lem1519516 (h1 : term73) : False.
Proof. exact (or_elim (@lem1519501 h1) (fun h0 : term68 => @lem1519508 h0) (fun h0 : term68 => @lem1519515 h0)). Qed.
Lemma lem1519518 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1519519 (h1 : term73) : term73 = False.
Proof. exact (prop_ext (fun h2 : term73 => @lem1519516 h1) (fun h2 : False => @lem1519518 h1)). Qed.
Lemma lem1519520 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1519519 h1) (@lem1519518 h1)). Qed.
Lemma lem1519521 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1519522 (h1 : term12) : term73.
Proof. exact (EQ_MP (@lem1519491) (@lem1519521 h1)). Qed.
Lemma lem1519523 (h1 : term12) : term73 = False.
Proof. exact (prop_ext (fun h2 : term73 => @lem1519520 h2) (fun h2 : False => @lem1519522 h1)). Qed.
Lemma lem1519524 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1519523 h1) (@lem1519522 h1)). Qed.
Lemma lem1519525 : term101.
Proof. exact (fun h0 : term12 => @lem1519524 h0). Qed.
Lemma lem1519526 : term102.
Proof. exact (@lem1386578 term103). Qed.
Lemma lem1519527 : term103.
Proof. exact (@lem1519526 (@lem1519525)). Qed.
