Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_ADD_RCANCEL_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483482_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Lemma lem1488328 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17646 ((real_add x y) = y) (x = term2)). Qed.
Lemma lem1488329 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1488330 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1488329 (term7 x)). Qed.
Lemma lem1488331 (y : real) (x : real) : (term8 x y) = (((real_add x y) = y) = (x = term2)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1488332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1488333 (y : real) (x : real) : (term9 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1488332) (@lem1488331 y x)). Qed.
Lemma lem1488334 (y : real) (x : real) : (term9 x y) = (term1 y x).
Proof. exact (TRANS (@lem1488333 y x) (@lem1488328 y x)). Qed.
Lemma lem1488335 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1488334 y x)). Qed.
Lemma lem1488336 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488337 (x : real) : (term6 x) = (term12 x).
Proof. exact (MK_COMB (@lem1488336) (@lem1488335 x)). Qed.
Lemma lem1488338 (x : real) : (term5 x) = (term12 x).
Proof. exact (TRANS (@lem1488330 x) (@lem1488337 x)). Qed.
Lemma lem1488339 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1488340 : term13 = term14.
Proof. exact (@lem1488339 term15). Qed.
Lemma lem1488341 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1488342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1488343 (x : real) : (term18 x) = (term5 x).
Proof. exact (MK_COMB (@lem1488342) (@lem1488341 x)). Qed.
Lemma lem1488344 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1488343 x) (@lem1488338 x)). Qed.
Lemma lem1488345 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1488344 x)). Qed.
Lemma lem1488346 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488347 : term14 = term21.
Proof. exact (MK_COMB (@lem1488346) (@lem1488345)). Qed.
Lemma lem1488349 : term13 = term21.
Proof. exact (TRANS (@lem1488340) (@lem1488347)). Qed.
Lemma lem1488366 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1488367 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1488366 y x)). Qed.
Lemma lem1488368 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488369 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1488368) (@lem1488367 x)). Qed.
Lemma lem1488370 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1488369 x)). Qed.
Lemma lem1488371 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488372 : term21 = term21.
Proof. exact (MK_COMB (@lem1488371) (@lem1488370)). Qed.
Lemma lem1488373 : term13 = term21.
Proof. exact (TRANS (@lem1488349) (@lem1488372)). Qed.
Lemma lem1488374 (x : real) (y : real) : ((real_add x y) = y) = ((term22 x y) = term2).
Proof. exact (@lem1483529 (real_add x y) y). Qed.
Lemma lem1488386 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1483519 (real_add x y) y). Qed.
Lemma lem1488390 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (@lem1483482 x y (term25 y)). Qed.
Lemma lem1488391 (y : real) : (term26 y) = (term27 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1488393 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488394 : term30 = term2.
Proof. exact (@lem1488393 term31). Qed.
Lemma lem1488395 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488396 : term32 = term33.
Proof. exact (MK_COMB (@lem1488395) (@lem1488394)). Qed.
Lemma lem1488397 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1488398 (y : real) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem1488396) (@lem1488397 y)). Qed.
Lemma lem1488399 (y : real) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem1488391 y) (@lem1488398 y)). Qed.
Lemma lem1488400 (y : real) : (term34 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1488401 (y : real) : (term26 y) = term2.
Proof. exact (TRANS (@lem1488399 y) (@lem1488400 y)). Qed.
Lemma lem1488402 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1488403 (y : real) (x : real) : (term24 x y) = (term35 x).
Proof. exact (MK_COMB (@lem1488402 x) (@lem1488401 y)). Qed.
Lemma lem1488404 (y : real) (x : real) : (term23 x y) = (term35 x).
Proof. exact (TRANS (@lem1488390 x y) (@lem1488403 y x)). Qed.
Lemma lem1488405 (x : real) : (term35 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1488407 (y : real) (x : real) : (term23 x y) = x.
Proof. exact (TRANS (@lem1488404 y x) (@lem1488405 x)). Qed.
Lemma lem1488409 (y : real) (x : real) : (term22 x y) = x.
Proof. exact (TRANS (@lem1488386 x y) (@lem1488407 y x)). Qed.
Lemma lem1488410 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1488411 (y : real) (x : real) : (term36 x y) = (@eq real x).
Proof. exact (MK_COMB (@lem1488410) (@lem1488409 y x)). Qed.
Lemma lem1488412 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488413 (y : real) (x : real) : ((term22 x y) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1488411 y x) (@lem1488412)). Qed.
Lemma lem1488414 (y : real) (x : real) : ((real_add x y) = y) = (x = term2).
Proof. exact (TRANS (@lem1488374 x y) (@lem1488413 y x)). Qed.
Lemma lem1488415 (x : real) : (term37 x) = (term38 x).
Proof. exact (@lem1483554 x term2). Qed.
Lemma lem1488421 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1488423 (x : nat) : (term41 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1488424 : term42 = term2.
Proof. exact (@lem1488423 term31). Qed.
Lemma lem1488425 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1488426 (x : real) : (term40 x) = (term35 x).
Proof. exact (MK_COMB (@lem1488425 x) (@lem1488424)). Qed.
Lemma lem1488427 (x : real) : (term35 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1488428 (x : real) : (term40 x) = x.
Proof. exact (TRANS (@lem1488426 x) (@lem1488427 x)). Qed.
Lemma lem1488430 (x : real) : (term39 x) = x.
Proof. exact (TRANS (@lem1488421 x) (@lem1488428 x)). Qed.
Lemma lem1488431 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1488432 (x : real) : (term43 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1488431) (@lem1488430 x)). Qed.
Lemma lem1488435 (x : real) : (real_neg x) = (term25 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1488436 (x : real) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1488437 (x : real) : ((term43 x) = (real_neg x)) = ((term43 x) = (term25 x)).
Proof. exact (MK_COMB (@lem1488436 x) (@lem1488435 x)). Qed.
Lemma lem1488438 (x : real) : (term43 x) = (term25 x).
Proof. exact (EQ_MP (@lem1488437 x) (@lem1488432 x)). Qed.
Lemma lem1488439 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488440 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1488439) (@lem1488438 x)). Qed.
Lemma lem1488441 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488442 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem1488440 x) (@lem1488441)). Qed.
Lemma lem1488443 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488444 (x : real) : (term49 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1488443) (@lem1488430 x)). Qed.
Lemma lem1488445 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488446 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1488444 x) (@lem1488445)). Qed.
Lemma lem1488447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488448 (x : real) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1488447) (@lem1488446 x)). Qed.
Lemma lem1488449 (x : real) : (term38 x) = (term54 x).
Proof. exact (MK_COMB (@lem1488448 x) (@lem1488442 x)). Qed.
Lemma lem1488450 (x : real) : (term37 x) = (term54 x).
Proof. exact (TRANS (@lem1488415 x) (@lem1488449 x)). Qed.
Lemma lem1488451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1488452 (y : real) (x : real) : (term55 x y) = (term56 x).
Proof. exact (MK_COMB (@lem1488451) (@lem1488414 y x)). Qed.
Lemma lem1488453 (y : real) (x : real) : (term57 y x) = (term58 x).
Proof. exact (MK_COMB (@lem1488452 y x) (@lem1488450 x)). Qed.
Lemma lem1488454 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (@lem1483554 (real_add x y) y). Qed.
Lemma lem1488466 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (@lem1483519 (real_add x y) y). Qed.
Lemma lem1488470 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (@lem1483482 x y (term25 y)). Qed.
Lemma lem1488471 (y : real) : (term26 y) = (term27 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1488473 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488474 : term30 = term2.
Proof. exact (@lem1488473 term31). Qed.
Lemma lem1488475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488476 : term32 = term33.
Proof. exact (MK_COMB (@lem1488475) (@lem1488474)). Qed.
Lemma lem1488477 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1488478 (y : real) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem1488476) (@lem1488477 y)). Qed.
Lemma lem1488479 (y : real) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem1488471 y) (@lem1488478 y)). Qed.
Lemma lem1488480 (y : real) : (term34 y) = term2.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1488481 (y : real) : (term26 y) = term2.
Proof. exact (TRANS (@lem1488479 y) (@lem1488480 y)). Qed.
Lemma lem1488482 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1488483 (y : real) (x : real) : (term24 x y) = (term35 x).
Proof. exact (MK_COMB (@lem1488482 x) (@lem1488481 y)). Qed.
Lemma lem1488484 (y : real) (x : real) : (term23 x y) = (term35 x).
Proof. exact (TRANS (@lem1488470 x y) (@lem1488483 y x)). Qed.
Lemma lem1488485 (x : real) : (term35 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1488487 (y : real) (x : real) : (term23 x y) = x.
Proof. exact (TRANS (@lem1488484 y x) (@lem1488485 x)). Qed.
Lemma lem1488489 (y : real) (x : real) : (term22 x y) = x.
Proof. exact (TRANS (@lem1488466 x y) (@lem1488487 y x)). Qed.
Lemma lem1488490 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1488491 (y : real) (x : real) : (term61 x y) = (real_neg x).
Proof. exact (MK_COMB (@lem1488490) (@lem1488489 y x)). Qed.
Lemma lem1488494 (x : real) : (real_neg x) = (term25 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1488495 (x : real) (y : real) : (term62 x y) = (term62 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1488496 (y : real) (x : real) : ((term61 x y) = (real_neg x)) = ((term61 x y) = (term25 x)).
Proof. exact (MK_COMB (@lem1488495 x y) (@lem1488494 x)). Qed.
Lemma lem1488497 (y : real) (x : real) : (term61 x y) = (term25 x).
Proof. exact (EQ_MP (@lem1488496 y x) (@lem1488491 y x)). Qed.
Lemma lem1488498 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488499 (y : real) (x : real) : (term63 x y) = (term46 x).
Proof. exact (MK_COMB (@lem1488498) (@lem1488497 y x)). Qed.
Lemma lem1488500 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488501 (y : real) (x : real) : (term64 x y) = (term48 x).
Proof. exact (MK_COMB (@lem1488499 y x) (@lem1488500)). Qed.
Lemma lem1488502 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488503 (y : real) (x : real) : (term65 x y) = (real_gt x).
Proof. exact (MK_COMB (@lem1488502) (@lem1488489 y x)). Qed.
Lemma lem1488504 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488505 (y : real) (x : real) : (term66 x y) = (term51 x).
Proof. exact (MK_COMB (@lem1488503 y x) (@lem1488504)). Qed.
Lemma lem1488506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488507 (y : real) (x : real) : (term67 x y) = (term53 x).
Proof. exact (MK_COMB (@lem1488506) (@lem1488505 y x)). Qed.
Lemma lem1488508 (y : real) (x : real) : (term60 x y) = (term54 x).
Proof. exact (MK_COMB (@lem1488507 y x) (@lem1488501 y x)). Qed.
Lemma lem1488509 (y : real) (x : real) : (term59 x y) = (term54 x).
Proof. exact (TRANS (@lem1488454 x y) (@lem1488508 y x)). Qed.
Lemma lem1488510 (x : real) : (x = term2) = ((term39 x) = term2).
Proof. exact (@lem1483529 x term2). Qed.
Lemma lem1488516 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1488518 (x : nat) : (term41 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1488519 : term42 = term2.
Proof. exact (@lem1488518 term31). Qed.
Lemma lem1488520 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1488521 (x : real) : (term40 x) = (term35 x).
Proof. exact (MK_COMB (@lem1488520 x) (@lem1488519)). Qed.
Lemma lem1488522 (x : real) : (term35 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1488523 (x : real) : (term40 x) = x.
Proof. exact (TRANS (@lem1488521 x) (@lem1488522 x)). Qed.
Lemma lem1488525 (x : real) : (term39 x) = x.
Proof. exact (TRANS (@lem1488516 x) (@lem1488523 x)). Qed.
Lemma lem1488526 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1488527 (x : real) : (term68 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1488526) (@lem1488525 x)). Qed.
Lemma lem1488528 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488529 (x : real) : ((term39 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1488527 x) (@lem1488528)). Qed.
Lemma lem1488530 (x : real) : (x = term2) = (x = term2).
Proof. exact (TRANS (@lem1488510 x) (@lem1488529 x)). Qed.
Lemma lem1488531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1488532 (y : real) (x : real) : (term69 x y) = (term70 x).
Proof. exact (MK_COMB (@lem1488531) (@lem1488509 y x)). Qed.
Lemma lem1488533 (y : real) (x : real) : (term71 y x) = (term72 x).
Proof. exact (MK_COMB (@lem1488532 y x) (@lem1488530 x)). Qed.
Lemma lem1488534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488535 (y : real) (x : real) : (term73 y x) = (term74 x).
Proof. exact (MK_COMB (@lem1488534) (@lem1488453 y x)). Qed.
Lemma lem1488536 (y : real) (x : real) : (term1 y x) = (term75 x).
Proof. exact (MK_COMB (@lem1488535 y x) (@lem1488533 y x)). Qed.
Lemma lem1488537 (x : real) : (term11 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1488536 y x)). Qed.
Lemma lem1488538 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488539 (x : real) : (term12 x) = (term77 x).
Proof. exact (MK_COMB (@lem1488538) (@lem1488537 x)). Qed.
Lemma lem1488540 : term20 = term78.
Proof. exact (fun_ext (fun x : real => @lem1488539 x)). Qed.
Lemma lem1488541 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488542 : term21 = term79.
Proof. exact (MK_COMB (@lem1488541) (@lem1488540)). Qed.
Lemma lem1488543 : term13 = term79.
Proof. exact (TRANS (@lem1488373) (@lem1488542)). Qed.
Lemma lem1488549 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1488550 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1488549 real P Q). Qed.
Lemma lem1488551 (x : real) : (term84 x) = (term85 x).
Proof. exact (@lem1488550 (term86 x) (term87 x)). Qed.
Lemma lem1488552 (y : real) (x : real) : (term88 x y) = (term58 x).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1488553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488554 (y : real) (x : real) : (term89 x y) = (term74 x).
Proof. exact (MK_COMB (@lem1488553) (@lem1488552 y x)). Qed.
Lemma lem1488555 (y : real) (x : real) : (term90 x y) = (term72 x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1488556 (y : real) (x : real) : (term91 x y) = (term75 x).
Proof. exact (MK_COMB (@lem1488554 y x) (@lem1488555 y x)). Qed.
Lemma lem1488557 (x : real) : (term92 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1488556 y x)). Qed.
Lemma lem1488558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488559 (x : real) : (term84 x) = (term77 x).
Proof. exact (MK_COMB (@lem1488558) (@lem1488557 x)). Qed.
Lemma lem1488560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1488561 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1488560) (@lem1488559 x)). Qed.
Lemma lem1488562 (y : real) (x : real) : (term88 x y) = (term58 x).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1488563 (x : real) : (term95 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1488562 y x)). Qed.
Lemma lem1488564 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488565 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1488564) (@lem1488563 x)). Qed.
Lemma lem1488566 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488567 (x : real) : (term98 x) = (term99 x).
Proof. exact (MK_COMB (@lem1488566) (@lem1488565 x)). Qed.
Lemma lem1488568 (y : real) (x : real) : (term90 x y) = (term72 x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1488569 (x : real) : (term100 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1488568 y x)). Qed.
Lemma lem1488570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488571 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1488570) (@lem1488569 x)). Qed.
Lemma lem1488572 (x : real) : (term85 x) = (term103 x).
Proof. exact (MK_COMB (@lem1488567 x) (@lem1488571 x)). Qed.
Lemma lem1488573 (x : real) : ((term84 x) = (term85 x)) = ((term77 x) = (term103 x)).
Proof. exact (MK_COMB (@lem1488561 x) (@lem1488572 x)). Qed.
Lemma lem1488574 (x : real) : (term77 x) = (term103 x).
Proof. exact (EQ_MP (@lem1488573 x) (@lem1488551 x)). Qed.
Lemma lem1488576 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1488577 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1488576 real P Q). Qed.
Lemma lem1488578 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1488577 (x = term2) (term110 x)). Qed.
Lemma lem1488579 (y : real) (x : real) : (term111 x y) = (term54 x).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1488580 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1488581 (y : real) (x : real) : (term112 x y) = (term58 x).
Proof. exact (MK_COMB (@lem1488580 x) (@lem1488579 y x)). Qed.
Lemma lem1488582 (x : real) : (term113 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1488581 y x)). Qed.
Lemma lem1488583 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488584 (x : real) : (term108 x) = (term97 x).
Proof. exact (MK_COMB (@lem1488583) (@lem1488582 x)). Qed.
Lemma lem1488585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1488586 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1488585) (@lem1488584 x)). Qed.
Lemma lem1488587 (y : real) (x : real) : (term111 x y) = (term54 x).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1488588 (x : real) : (term116 x) = (term110 x).
Proof. exact (fun_ext (fun y : real => @lem1488587 y x)). Qed.
Lemma lem1488589 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488590 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1488589) (@lem1488588 x)). Qed.
Lemma lem1488591 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1488592 (x : real) : (term109 x) = (term119 x).
Proof. exact (MK_COMB (@lem1488591 x) (@lem1488590 x)). Qed.
Lemma lem1488593 (x : real) : ((term108 x) = (term109 x)) = ((term97 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1488586 x) (@lem1488592 x)). Qed.
Lemma lem1488594 (x : real) : (term97 x) = (term119 x).
Proof. exact (EQ_MP (@lem1488593 x) (@lem1488578 x)). Qed.
Lemma lem1488596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1488597 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1488596 real P Q). Qed.
Lemma lem1488598 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1488597 (term122 x) (term123 x)). Qed.
Lemma lem1488599 (y : real) (x : real) : (term124 x y) = (term51 x).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem1488600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488601 (y : real) (x : real) : (term125 x y) = (term53 x).
Proof. exact (MK_COMB (@lem1488600) (@lem1488599 y x)). Qed.
Lemma lem1488602 (y : real) (x : real) : (term126 x y) = (term48 x).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem1488603 (y : real) (x : real) : (term127 x y) = (term54 x).
Proof. exact (MK_COMB (@lem1488601 y x) (@lem1488602 y x)). Qed.
Lemma lem1488604 (x : real) : (term128 x) = (term110 x).
Proof. exact (fun_ext (fun y : real => @lem1488603 y x)). Qed.
Lemma lem1488605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488606 (x : real) : (term120 x) = (term118 x).
Proof. exact (MK_COMB (@lem1488605) (@lem1488604 x)). Qed.
Lemma lem1488607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1488608 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1488607) (@lem1488606 x)). Qed.
Lemma lem1488609 (y : real) (x : real) : (term124 x y) = (term51 x).
Proof. exact (eq_refl (term124 x y)). Qed.
Lemma lem1488610 (x : real) : (term131 x) = (term122 x).
Proof. exact (fun_ext (fun y : real => @lem1488609 y x)). Qed.
Lemma lem1488611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488612 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1488611) (@lem1488610 x)). Qed.
Lemma lem1488613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488614 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1488613) (@lem1488612 x)). Qed.
Lemma lem1488615 (y : real) (x : real) : (term126 x y) = (term48 x).
Proof. exact (eq_refl (term126 x y)). Qed.
Lemma lem1488616 (x : real) : (term136 x) = (term123 x).
Proof. exact (fun_ext (fun y : real => @lem1488615 y x)). Qed.
Lemma lem1488617 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488618 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1488617) (@lem1488616 x)). Qed.
Lemma lem1488619 (x : real) : (term121 x) = (term139 x).
Proof. exact (MK_COMB (@lem1488614 x) (@lem1488618 x)). Qed.
Lemma lem1488620 (x : real) : ((term120 x) = (term121 x)) = ((term118 x) = (term139 x)).
Proof. exact (MK_COMB (@lem1488608 x) (@lem1488619 x)). Qed.
Lemma lem1488621 (x : real) : (term118 x) = (term139 x).
Proof. exact (EQ_MP (@lem1488620 x) (@lem1488598 x)). Qed.
Lemma lem1488623 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1488624 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1488623 real t). Qed.
Lemma lem1488625 (x : real) : (term133 x) = (term51 x).
Proof. exact (@lem1488624 (term51 x)). Qed.
Lemma lem1488626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488627 (x : real) : (term135 x) = (term53 x).
Proof. exact (MK_COMB (@lem1488626) (@lem1488625 x)). Qed.
Lemma lem1488629 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1488630 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1488629 real t). Qed.
Lemma lem1488631 (x : real) : (term138 x) = (term48 x).
Proof. exact (@lem1488630 (term48 x)). Qed.
Lemma lem1488632 (x : real) : (term139 x) = (term54 x).
Proof. exact (MK_COMB (@lem1488627 x) (@lem1488631 x)). Qed.
Lemma lem1488633 (x : real) : (term118 x) = (term54 x).
Proof. exact (TRANS (@lem1488621 x) (@lem1488632 x)). Qed.
Lemma lem1488634 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1488635 (x : real) : (term119 x) = (term58 x).
Proof. exact (MK_COMB (@lem1488634 x) (@lem1488633 x)). Qed.
Lemma lem1488636 (x : real) : (term97 x) = (term58 x).
Proof. exact (TRANS (@lem1488594 x) (@lem1488635 x)). Qed.
Lemma lem1488637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488638 (x : real) : (term99 x) = (term74 x).
Proof. exact (MK_COMB (@lem1488637) (@lem1488636 x)). Qed.
Lemma lem1488640 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1488641 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1488640 real P Q). Qed.
Lemma lem1488642 (x : real) : (term142 x) = (term143 x).
Proof. exact (@lem1488641 (term54 x) (term144 x)). Qed.
Lemma lem1488643 (y : real) (x : real) : (term145 x y) = (x = term2).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1488644 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1488645 (y : real) (x : real) : (term146 x y) = (term72 x).
Proof. exact (MK_COMB (@lem1488644 x) (@lem1488643 y x)). Qed.
Lemma lem1488646 (x : real) : (term147 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1488645 y x)). Qed.
Lemma lem1488647 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488648 (x : real) : (term142 x) = (term102 x).
Proof. exact (MK_COMB (@lem1488647) (@lem1488646 x)). Qed.
Lemma lem1488649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1488650 (x : real) : (term148 x) = (term149 x).
Proof. exact (MK_COMB (@lem1488649) (@lem1488648 x)). Qed.
Lemma lem1488651 (y : real) (x : real) : (term145 x y) = (x = term2).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1488652 (x : real) : (term150 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1488651 y x)). Qed.
Lemma lem1488653 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488654 (x : real) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem1488653) (@lem1488652 x)). Qed.
Lemma lem1488655 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1488656 (x : real) : (term143 x) = (term153 x).
Proof. exact (MK_COMB (@lem1488655 x) (@lem1488654 x)). Qed.
Lemma lem1488657 (x : real) : ((term142 x) = (term143 x)) = ((term102 x) = (term153 x)).
Proof. exact (MK_COMB (@lem1488650 x) (@lem1488656 x)). Qed.
Lemma lem1488658 (x : real) : (term102 x) = (term153 x).
Proof. exact (EQ_MP (@lem1488657 x) (@lem1488642 x)). Qed.
Lemma lem1488660 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1488661 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1488660 real t). Qed.
Lemma lem1488662 (x : real) : (term152 x) = (x = term2).
Proof. exact (@lem1488661 (x = term2)). Qed.
Lemma lem1488663 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1488664 (x : real) : (term153 x) = (term72 x).
Proof. exact (MK_COMB (@lem1488663 x) (@lem1488662 x)). Qed.
Lemma lem1488665 (x : real) : (term102 x) = (term72 x).
Proof. exact (TRANS (@lem1488658 x) (@lem1488664 x)). Qed.
Lemma lem1488666 (x : real) : (term103 x) = (term75 x).
Proof. exact (MK_COMB (@lem1488638 x) (@lem1488665 x)). Qed.
Lemma lem1488667 (x : real) : (term77 x) = (term75 x).
Proof. exact (TRANS (@lem1488574 x) (@lem1488666 x)). Qed.
Lemma lem1488668 : term78 = term154.
Proof. exact (fun_ext (fun x : real => @lem1488667 x)). Qed.
Lemma lem1488669 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488670 : term79 = term155.
Proof. exact (MK_COMB (@lem1488669) (@lem1488668)). Qed.
Lemma lem1488672 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1488673 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1488672 real P Q). Qed.
Lemma lem1488674 : term156 = term157.
Proof. exact (@lem1488673 term158 term159). Qed.
Lemma lem1488675 (x : real) : (term160 x) = (term58 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1488676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488677 (x : real) : (term161 x) = (term74 x).
Proof. exact (MK_COMB (@lem1488676) (@lem1488675 x)). Qed.
Lemma lem1488678 (x : real) : (term162 x) = (term72 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1488679 (x : real) : (term163 x) = (term75 x).
Proof. exact (MK_COMB (@lem1488677 x) (@lem1488678 x)). Qed.
Lemma lem1488680 : term164 = term154.
Proof. exact (fun_ext (fun x : real => @lem1488679 x)). Qed.
Lemma lem1488681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488682 : term156 = term155.
Proof. exact (MK_COMB (@lem1488681) (@lem1488680)). Qed.
Lemma lem1488683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1488684 : term165 = term166.
Proof. exact (MK_COMB (@lem1488683) (@lem1488682)). Qed.
Lemma lem1488685 (x : real) : (term160 x) = (term58 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1488686 : term167 = term158.
Proof. exact (fun_ext (fun x : real => @lem1488685 x)). Qed.
Lemma lem1488687 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488688 : term168 = term169.
Proof. exact (MK_COMB (@lem1488687) (@lem1488686)). Qed.
Lemma lem1488689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488690 : term170 = term171.
Proof. exact (MK_COMB (@lem1488689) (@lem1488688)). Qed.
Lemma lem1488691 (x : real) : (term162 x) = (term72 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1488692 : term172 = term159.
Proof. exact (fun_ext (fun x : real => @lem1488691 x)). Qed.
Lemma lem1488693 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488694 : term173 = term174.
Proof. exact (MK_COMB (@lem1488693) (@lem1488692)). Qed.
Lemma lem1488695 : term157 = term175.
Proof. exact (MK_COMB (@lem1488690) (@lem1488694)). Qed.
Lemma lem1488696 : (term156 = term157) = (term155 = term175).
Proof. exact (MK_COMB (@lem1488684) (@lem1488695)). Qed.
Lemma lem1488697 : term155 = term175.
Proof. exact (EQ_MP (@lem1488696) (@lem1488674)). Qed.
Lemma lem1488794 : term79 = term175.
Proof. exact (TRANS (@lem1488670) (@lem1488697)). Qed.
Lemma lem1488796 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1488797 (P : real -> Prop) (Q : real -> Prop) : (term83 P Q) = (term82 P Q).
Proof. exact (@lem1488796 real P Q). Qed.
Lemma lem1488798 : term157 = term156.
Proof. exact (@lem1488797 term158 term159). Qed.
Lemma lem1488799 (x : real) : (term160 x) = (term58 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1488800 : term167 = term158.
Proof. exact (fun_ext (fun x : real => @lem1488799 x)). Qed.
Lemma lem1488801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488802 : term168 = term169.
Proof. exact (MK_COMB (@lem1488801) (@lem1488800)). Qed.
Lemma lem1488803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488804 : term170 = term171.
Proof. exact (MK_COMB (@lem1488803) (@lem1488802)). Qed.
Lemma lem1488805 (x : real) : (term162 x) = (term72 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1488806 : term172 = term159.
Proof. exact (fun_ext (fun x : real => @lem1488805 x)). Qed.
Lemma lem1488807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488808 : term173 = term174.
Proof. exact (MK_COMB (@lem1488807) (@lem1488806)). Qed.
Lemma lem1488809 : term157 = term175.
Proof. exact (MK_COMB (@lem1488804) (@lem1488808)). Qed.
Lemma lem1488810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1488811 : term176 = term177.
Proof. exact (MK_COMB (@lem1488810) (@lem1488809)). Qed.
Lemma lem1488812 (x : real) : (term160 x) = (term58 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1488813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488814 (x : real) : (term161 x) = (term74 x).
Proof. exact (MK_COMB (@lem1488813) (@lem1488812 x)). Qed.
Lemma lem1488815 (x : real) : (term162 x) = (term72 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1488816 (x : real) : (term163 x) = (term75 x).
Proof. exact (MK_COMB (@lem1488814 x) (@lem1488815 x)). Qed.
Lemma lem1488817 : term164 = term154.
Proof. exact (fun_ext (fun x : real => @lem1488816 x)). Qed.
Lemma lem1488818 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488819 : term156 = term155.
Proof. exact (MK_COMB (@lem1488818) (@lem1488817)). Qed.
Lemma lem1488820 : (term157 = term156) = (term175 = term155).
Proof. exact (MK_COMB (@lem1488811) (@lem1488819)). Qed.
Lemma lem1488821 : term175 = term155.
Proof. exact (EQ_MP (@lem1488820) (@lem1488798)). Qed.
Lemma lem1488822 : term79 = term155.
Proof. exact (TRANS (@lem1488794) (@lem1488821)). Qed.
Lemma lem1488825 : term13 = term155.
Proof. exact (TRANS (@lem1488543) (@lem1488822)). Qed.
Lemma lem1488842 (x : real) : (term72 x) = (term178 x).
Proof. exact (@lem19367 (term51 x) (term48 x) (x = term2)). Qed.
Lemma lem1488859 (x : real) : (term58 x) = (term179 x).
Proof. exact (@lem19158 (term51 x) (x = term2) (term48 x)). Qed.
Lemma lem1488860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1488861 (x : real) : (term74 x) = (term180 x).
Proof. exact (MK_COMB (@lem1488860) (@lem1488859 x)). Qed.
Lemma lem1488862 (x : real) : (term75 x) = (term181 x).
Proof. exact (MK_COMB (@lem1488861 x) (@lem1488842 x)). Qed.
Lemma lem1488863 : term154 = term182.
Proof. exact (fun_ext (fun x : real => @lem1488862 x)). Qed.
Lemma lem1488864 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1488865 : term155 = term183.
Proof. exact (MK_COMB (@lem1488864) (@lem1488863)). Qed.
Lemma lem1488866 : term13 = term183.
Proof. exact (TRANS (@lem1488825) (@lem1488865)). Qed.
Lemma lem1488888 (x : real) (h1 : term181 x) : term181 x.
Proof. exact (h1). Qed.
Lemma lem1488889 (x : real) (h1 : term179 x) : term179 x.
Proof. exact (h1). Qed.
Lemma lem1488890 (x : real) (h1 : term184 x) : term184 x.
Proof. exact (h1). Qed.
Lemma lem1488891 (x : real) (h1 : term184 x) : term51 x.
Proof. exact (proj2 (@lem1488890 x h1)). Qed.
Lemma lem1488892 (x : real) (h1 : term184 x) : x = term2.
Proof. exact (proj1 (@lem1488890 x h1)). Qed.
Lemma lem1488894 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488895 : term186 = term187.
Proof. exact (@lem1488894 (NUMERAL 0) term31). Qed.
Lemma lem1488896 : term188 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1488897 (h1 : term188 = (BIT1 0)) : term187 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1488898 : (term188 = (BIT1 0)) = (term187 = True).
Proof. exact (prop_ext (fun h1 : term188 = (BIT1 0) => @lem1488897 h1) (fun h1 : term187 = True => @lem1488896)). Qed.
Lemma lem1488899 : term187 = True.
Proof. exact (EQ_MP (@lem1488898) (@lem1488896)). Qed.
Lemma lem1488900 : term186 = True.
Proof. exact (TRANS (@lem1488895) (@lem1488899)). Qed.
Lemma lem1488901 : True = term186.
Proof. exact (SYM (@lem1488900)). Qed.
Lemma lem1488902 : term186.
Proof. exact (EQ_MP (@lem1488901) (@lem0)). Qed.
Lemma lem1488903 (x : real) (h1 : term184 x) : term189 x.
Proof. exact (conj (@lem1488902) (@lem1488891 x h1)). Qed.
Lemma lem1488905 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1488906 (x : real) : term191 x.
Proof. exact (@lem1488905 term192 x). Qed.
Lemma lem1488907 (x : real) (h1 : term184 x) : term193 x.
Proof. exact (@lem1488906 x (@lem1488903 x h1)). Qed.
Lemma lem1488908 (x : real) : (term194 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1488909 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488910 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1488909) (@lem1488908 x)). Qed.
Lemma lem1488911 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488912 (x : real) : (term193 x) = (term51 x).
Proof. exact (MK_COMB (@lem1488910 x) (@lem1488911)). Qed.
Lemma lem1488913 (x : real) (h1 : term184 x) : term51 x.
Proof. exact (EQ_MP (@lem1488912 x) (@lem1488907 x h1)). Qed.
Lemma lem1488915 (y : real) : term196 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1488916 (x : real) : term196 x.
Proof. exact (@lem1488915 x). Qed.
Lemma lem1488917 (x : real) (h1 : term184 x) : term197 x.
Proof. exact (@lem1488916 x (@lem1488892 x h1)). Qed.
Lemma lem1488918 (x : real) (h1 : term184 x) : term198 x.
Proof. exact (@lem1488917 x h1 term28). Qed.
Lemma lem1488919 (x : real) : (term198 x) = ((term25 x) = term2).
Proof. exact (eq_refl (term198 x)). Qed.
Lemma lem1488926 (x : real) (h1 : term184 x) : (term25 x) = term2.
Proof. exact (EQ_MP (@lem1488919 x) (@lem1488918 x h1)). Qed.
Lemma lem1488927 (x : real) (h1 : term184 x) : term199 x.
Proof. exact (conj (@lem1488926 x h1) (@lem1488913 x h1)). Qed.
Lemma lem1488929 (x : real) (y : real) : term200 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1488930 (x : real) : term201 x.
Proof. exact (@lem1488929 (term25 x) x). Qed.
Lemma lem1488931 (x : real) (h1 : term184 x) : term202 x.
Proof. exact (@lem1488930 x (@lem1488927 x h1)). Qed.
Lemma lem1488932 (x : real) : (term203 x) = (term27 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1488934 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488935 : term30 = term2.
Proof. exact (@lem1488934 term31). Qed.
Lemma lem1488936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1488937 : term32 = term33.
Proof. exact (MK_COMB (@lem1488936) (@lem1488935)). Qed.
Lemma lem1488938 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1488939 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1488937) (@lem1488938 x)). Qed.
Lemma lem1488940 (x : real) : (term203 x) = (term34 x).
Proof. exact (TRANS (@lem1488932 x) (@lem1488939 x)). Qed.
Lemma lem1488941 (x : real) : (term34 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1488942 (x : real) : (term203 x) = term2.
Proof. exact (TRANS (@lem1488940 x) (@lem1488941 x)). Qed.
Lemma lem1488943 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488944 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1488943) (@lem1488942 x)). Qed.
Lemma lem1488945 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488946 (x : real) : (term202 x) = term206.
Proof. exact (MK_COMB (@lem1488944 x) (@lem1488945)). Qed.
Lemma lem1488947 (x : real) (h1 : term184 x) : term206.
Proof. exact (EQ_MP (@lem1488946 x) (@lem1488931 x h1)). Qed.
Lemma lem1488949 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488950 : term206 = term207.
Proof. exact (@lem1488949 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1488951 : term207 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1488952 : term206 = False.
Proof. exact (TRANS (@lem1488950) (@lem1488951)). Qed.
Lemma lem1488953 (x : real) (h1 : term184 x) : False.
Proof. exact (EQ_MP (@lem1488952) (@lem1488947 x h1)). Qed.
Lemma lem1488954 (x : real) (h1 : term208 x) : term208 x.
Proof. exact (h1). Qed.
Lemma lem1488955 (x : real) (h1 : term208 x) : term48 x.
Proof. exact (proj2 (@lem1488954 x h1)). Qed.
Lemma lem1488956 (x : real) (h1 : term208 x) : x = term2.
Proof. exact (proj1 (@lem1488954 x h1)). Qed.
Lemma lem1488958 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1488959 : term186 = term187.
Proof. exact (@lem1488958 (NUMERAL 0) term31). Qed.
Lemma lem1488960 : term188 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1488961 (h1 : term188 = (BIT1 0)) : term187 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1488962 : (term188 = (BIT1 0)) = (term187 = True).
Proof. exact (prop_ext (fun h1 : term188 = (BIT1 0) => @lem1488961 h1) (fun h1 : term187 = True => @lem1488960)). Qed.
Lemma lem1488963 : term187 = True.
Proof. exact (EQ_MP (@lem1488962) (@lem1488960)). Qed.
Lemma lem1488964 : term186 = True.
Proof. exact (TRANS (@lem1488959) (@lem1488963)). Qed.
Lemma lem1488965 : True = term186.
Proof. exact (SYM (@lem1488964)). Qed.
Lemma lem1488966 : term186.
Proof. exact (EQ_MP (@lem1488965) (@lem0)). Qed.
Lemma lem1488967 (x : real) (h1 : term208 x) : term209 x.
Proof. exact (conj (@lem1488966) (@lem1488955 x h1)). Qed.
Lemma lem1488969 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1488970 (x : real) : term210 x.
Proof. exact (@lem1488969 term192 (term25 x)). Qed.
Lemma lem1488971 (x : real) (h1 : term208 x) : term211 x.
Proof. exact (@lem1488970 x (@lem1488967 x h1)). Qed.
Lemma lem1488972 (x : real) : (term212 x) = (term25 x).
Proof. exact (@lem1483460 (term25 x)). Qed.
Lemma lem1488973 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1488974 (x : real) : (term213 x) = (term46 x).
Proof. exact (MK_COMB (@lem1488973) (@lem1488972 x)). Qed.
Lemma lem1488975 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488976 (x : real) : (term211 x) = (term48 x).
Proof. exact (MK_COMB (@lem1488974 x) (@lem1488975)). Qed.
Lemma lem1488977 (x : real) (h1 : term208 x) : term48 x.
Proof. exact (EQ_MP (@lem1488976 x) (@lem1488971 x h1)). Qed.
Lemma lem1488979 (y : real) : term196 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1488980 (x : real) : term196 x.
Proof. exact (@lem1488979 x). Qed.
Lemma lem1488981 (x : real) (h1 : term208 x) : term197 x.
Proof. exact (@lem1488980 x (@lem1488956 x h1)). Qed.
Lemma lem1488982 (x : real) (h1 : term208 x) : term214 x.
Proof. exact (@lem1488981 x h1 term192). Qed.
Lemma lem1488983 (x : real) : (term214 x) = ((term194 x) = term2).
Proof. exact (eq_refl (term214 x)). Qed.
Lemma lem1488984 (x : real) (h1 : term208 x) : (term194 x) = term2.
Proof. exact (EQ_MP (@lem1488983 x) (@lem1488982 x h1)). Qed.
Lemma lem1488985 (x : real) : (term194 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1488986 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1488987 (x : real) : (term215 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1488986) (@lem1488985 x)). Qed.
Lemma lem1488988 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1488989 (x : real) : ((term194 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1488987 x) (@lem1488988)). Qed.
Lemma lem1488990 (x : real) (h1 : term208 x) : x = term2.
Proof. exact (EQ_MP (@lem1488989 x) (@lem1488984 x h1)). Qed.
Lemma lem1488991 (x : real) (h1 : term208 x) : term208 x.
Proof. exact (conj (@lem1488990 x h1) (@lem1488977 x h1)). Qed.
Lemma lem1488993 (x : real) (y : real) : term200 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1488994 (x : real) : term216 x.
Proof. exact (@lem1488993 x (term25 x)). Qed.
Lemma lem1488995 (x : real) (h1 : term208 x) : term217 x.
Proof. exact (@lem1488994 x (@lem1488991 x h1)). Qed.
Lemma lem1488996 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1488998 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1488999 : term30 = term2.
Proof. exact (@lem1488998 term31). Qed.
Lemma lem1489000 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489001 : term32 = term33.
Proof. exact (MK_COMB (@lem1489000) (@lem1488999)). Qed.
Lemma lem1489002 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1489003 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1489001) (@lem1489002 x)). Qed.
Lemma lem1489004 (x : real) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem1488996 x) (@lem1489003 x)). Qed.
Lemma lem1489005 (x : real) : (term34 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1489006 (x : real) : (term26 x) = term2.
Proof. exact (TRANS (@lem1489004 x) (@lem1489005 x)). Qed.
Lemma lem1489007 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489008 (x : real) : (term218 x) = term205.
Proof. exact (MK_COMB (@lem1489007) (@lem1489006 x)). Qed.
Lemma lem1489009 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489010 (x : real) : (term217 x) = term206.
Proof. exact (MK_COMB (@lem1489008 x) (@lem1489009)). Qed.
Lemma lem1489011 (x : real) (h1 : term208 x) : term206.
Proof. exact (EQ_MP (@lem1489010 x) (@lem1488995 x h1)). Qed.
Lemma lem1489013 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489014 : term206 = term207.
Proof. exact (@lem1489013 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1489015 : term207 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1489016 : term206 = False.
Proof. exact (TRANS (@lem1489014) (@lem1489015)). Qed.
Lemma lem1489017 (x : real) (h1 : term208 x) : False.
Proof. exact (EQ_MP (@lem1489016) (@lem1489011 x h1)). Qed.
Lemma lem1489018 (x : real) (h1 : term179 x) : False.
Proof. exact (or_elim (@lem1488889 x h1) (fun h0 : term184 x => @lem1488953 x h0) (fun h0 : term208 x => @lem1489017 x h0)). Qed.
Lemma lem1489019 (x : real) (h1 : term178 x) : term178 x.
Proof. exact (h1). Qed.
Lemma lem1489020 (x : real) (h1 : term219 x) : term219 x.
Proof. exact (h1). Qed.
Lemma lem1489021 (x : real) (h1 : term219 x) : x = term2.
Proof. exact (proj2 (@lem1489020 x h1)). Qed.
Lemma lem1489022 (x : real) (h1 : term219 x) : term51 x.
Proof. exact (proj1 (@lem1489020 x h1)). Qed.
Lemma lem1489024 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489025 : term186 = term187.
Proof. exact (@lem1489024 (NUMERAL 0) term31). Qed.
Lemma lem1489026 : term188 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1489027 (h1 : term188 = (BIT1 0)) : term187 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1489028 : (term188 = (BIT1 0)) = (term187 = True).
Proof. exact (prop_ext (fun h1 : term188 = (BIT1 0) => @lem1489027 h1) (fun h1 : term187 = True => @lem1489026)). Qed.
Lemma lem1489029 : term187 = True.
Proof. exact (EQ_MP (@lem1489028) (@lem1489026)). Qed.
Lemma lem1489030 : term186 = True.
Proof. exact (TRANS (@lem1489025) (@lem1489029)). Qed.
Lemma lem1489031 : True = term186.
Proof. exact (SYM (@lem1489030)). Qed.
Lemma lem1489032 : term186.
Proof. exact (EQ_MP (@lem1489031) (@lem0)). Qed.
Lemma lem1489033 (x : real) (h1 : term219 x) : term189 x.
Proof. exact (conj (@lem1489032) (@lem1489022 x h1)). Qed.
Lemma lem1489035 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1489036 (x : real) : term191 x.
Proof. exact (@lem1489035 term192 x). Qed.
Lemma lem1489037 (x : real) (h1 : term219 x) : term193 x.
Proof. exact (@lem1489036 x (@lem1489033 x h1)). Qed.
Lemma lem1489038 (x : real) : (term194 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1489039 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489040 (x : real) : (term195 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1489039) (@lem1489038 x)). Qed.
Lemma lem1489041 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489042 (x : real) : (term193 x) = (term51 x).
Proof. exact (MK_COMB (@lem1489040 x) (@lem1489041)). Qed.
Lemma lem1489043 (x : real) (h1 : term219 x) : term51 x.
Proof. exact (EQ_MP (@lem1489042 x) (@lem1489037 x h1)). Qed.
Lemma lem1489045 (y : real) : term196 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1489046 (x : real) : term196 x.
Proof. exact (@lem1489045 x). Qed.
Lemma lem1489047 (x : real) (h1 : term219 x) : term197 x.
Proof. exact (@lem1489046 x (@lem1489021 x h1)). Qed.
Lemma lem1489048 (x : real) (h1 : term219 x) : term198 x.
Proof. exact (@lem1489047 x h1 term28). Qed.
Lemma lem1489049 (x : real) : (term198 x) = ((term25 x) = term2).
Proof. exact (eq_refl (term198 x)). Qed.
Lemma lem1489056 (x : real) (h1 : term219 x) : (term25 x) = term2.
Proof. exact (EQ_MP (@lem1489049 x) (@lem1489048 x h1)). Qed.
Lemma lem1489057 (x : real) (h1 : term219 x) : term199 x.
Proof. exact (conj (@lem1489056 x h1) (@lem1489043 x h1)). Qed.
Lemma lem1489059 (x : real) (y : real) : term200 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1489060 (x : real) : term201 x.
Proof. exact (@lem1489059 (term25 x) x). Qed.
Lemma lem1489061 (x : real) (h1 : term219 x) : term202 x.
Proof. exact (@lem1489060 x (@lem1489057 x h1)). Qed.
Lemma lem1489062 (x : real) : (term203 x) = (term27 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1489064 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1489065 : term30 = term2.
Proof. exact (@lem1489064 term31). Qed.
Lemma lem1489066 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489067 : term32 = term33.
Proof. exact (MK_COMB (@lem1489066) (@lem1489065)). Qed.
Lemma lem1489068 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1489069 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1489067) (@lem1489068 x)). Qed.
Lemma lem1489070 (x : real) : (term203 x) = (term34 x).
Proof. exact (TRANS (@lem1489062 x) (@lem1489069 x)). Qed.
Lemma lem1489071 (x : real) : (term34 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1489072 (x : real) : (term203 x) = term2.
Proof. exact (TRANS (@lem1489070 x) (@lem1489071 x)). Qed.
Lemma lem1489073 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489074 (x : real) : (term204 x) = term205.
Proof. exact (MK_COMB (@lem1489073) (@lem1489072 x)). Qed.
Lemma lem1489075 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489076 (x : real) : (term202 x) = term206.
Proof. exact (MK_COMB (@lem1489074 x) (@lem1489075)). Qed.
Lemma lem1489077 (x : real) (h1 : term219 x) : term206.
Proof. exact (EQ_MP (@lem1489076 x) (@lem1489061 x h1)). Qed.
Lemma lem1489079 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489080 : term206 = term207.
Proof. exact (@lem1489079 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1489081 : term207 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1489082 : term206 = False.
Proof. exact (TRANS (@lem1489080) (@lem1489081)). Qed.
Lemma lem1489083 (x : real) (h1 : term219 x) : False.
Proof. exact (EQ_MP (@lem1489082) (@lem1489077 x h1)). Qed.
Lemma lem1489084 (x : real) (h1 : term220 x) : term220 x.
Proof. exact (h1). Qed.
Lemma lem1489085 (x : real) (h1 : term220 x) : x = term2.
Proof. exact (proj2 (@lem1489084 x h1)). Qed.
Lemma lem1489086 (x : real) (h1 : term220 x) : term48 x.
Proof. exact (proj1 (@lem1489084 x h1)). Qed.
Lemma lem1489088 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489089 : term186 = term187.
Proof. exact (@lem1489088 (NUMERAL 0) term31). Qed.
Lemma lem1489090 : term188 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1489091 (h1 : term188 = (BIT1 0)) : term187 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1489092 : (term188 = (BIT1 0)) = (term187 = True).
Proof. exact (prop_ext (fun h1 : term188 = (BIT1 0) => @lem1489091 h1) (fun h1 : term187 = True => @lem1489090)). Qed.
Lemma lem1489093 : term187 = True.
Proof. exact (EQ_MP (@lem1489092) (@lem1489090)). Qed.
Lemma lem1489094 : term186 = True.
Proof. exact (TRANS (@lem1489089) (@lem1489093)). Qed.
Lemma lem1489095 : True = term186.
Proof. exact (SYM (@lem1489094)). Qed.
Lemma lem1489096 : term186.
Proof. exact (EQ_MP (@lem1489095) (@lem0)). Qed.
Lemma lem1489097 (x : real) (h1 : term220 x) : term209 x.
Proof. exact (conj (@lem1489096) (@lem1489086 x h1)). Qed.
Lemma lem1489099 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1489100 (x : real) : term210 x.
Proof. exact (@lem1489099 term192 (term25 x)). Qed.
Lemma lem1489101 (x : real) (h1 : term220 x) : term211 x.
Proof. exact (@lem1489100 x (@lem1489097 x h1)). Qed.
Lemma lem1489102 (x : real) : (term212 x) = (term25 x).
Proof. exact (@lem1483460 (term25 x)). Qed.
Lemma lem1489103 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489104 (x : real) : (term213 x) = (term46 x).
Proof. exact (MK_COMB (@lem1489103) (@lem1489102 x)). Qed.
Lemma lem1489105 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489106 (x : real) : (term211 x) = (term48 x).
Proof. exact (MK_COMB (@lem1489104 x) (@lem1489105)). Qed.
Lemma lem1489107 (x : real) (h1 : term220 x) : term48 x.
Proof. exact (EQ_MP (@lem1489106 x) (@lem1489101 x h1)). Qed.
Lemma lem1489109 (y : real) : term196 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1489110 (x : real) : term196 x.
Proof. exact (@lem1489109 x). Qed.
Lemma lem1489111 (x : real) (h1 : term220 x) : term197 x.
Proof. exact (@lem1489110 x (@lem1489085 x h1)). Qed.
Lemma lem1489112 (x : real) (h1 : term220 x) : term214 x.
Proof. exact (@lem1489111 x h1 term192). Qed.
Lemma lem1489113 (x : real) : (term214 x) = ((term194 x) = term2).
Proof. exact (eq_refl (term214 x)). Qed.
Lemma lem1489114 (x : real) (h1 : term220 x) : (term194 x) = term2.
Proof. exact (EQ_MP (@lem1489113 x) (@lem1489112 x h1)). Qed.
Lemma lem1489115 (x : real) : (term194 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1489116 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1489117 (x : real) : (term215 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1489116) (@lem1489115 x)). Qed.
Lemma lem1489118 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489119 (x : real) : ((term194 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1489117 x) (@lem1489118)). Qed.
Lemma lem1489120 (x : real) (h1 : term220 x) : x = term2.
Proof. exact (EQ_MP (@lem1489119 x) (@lem1489114 x h1)). Qed.
Lemma lem1489121 (x : real) (h1 : term220 x) : term208 x.
Proof. exact (conj (@lem1489120 x h1) (@lem1489107 x h1)). Qed.
Lemma lem1489123 (x : real) (y : real) : term200 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1489124 (x : real) : term216 x.
Proof. exact (@lem1489123 x (term25 x)). Qed.
Lemma lem1489125 (x : real) (h1 : term220 x) : term217 x.
Proof. exact (@lem1489124 x (@lem1489121 x h1)). Qed.
Lemma lem1489126 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1489128 (m : nat) : (term29 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1489129 : term30 = term2.
Proof. exact (@lem1489128 term31). Qed.
Lemma lem1489130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1489131 : term32 = term33.
Proof. exact (MK_COMB (@lem1489130) (@lem1489129)). Qed.
Lemma lem1489132 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1489133 (x : real) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem1489131) (@lem1489132 x)). Qed.
Lemma lem1489134 (x : real) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem1489126 x) (@lem1489133 x)). Qed.
Lemma lem1489135 (x : real) : (term34 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1489136 (x : real) : (term26 x) = term2.
Proof. exact (TRANS (@lem1489134 x) (@lem1489135 x)). Qed.
Lemma lem1489137 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1489138 (x : real) : (term218 x) = term205.
Proof. exact (MK_COMB (@lem1489137) (@lem1489136 x)). Qed.
Lemma lem1489139 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1489140 (x : real) : (term217 x) = term206.
Proof. exact (MK_COMB (@lem1489138 x) (@lem1489139)). Qed.
Lemma lem1489141 (x : real) (h1 : term220 x) : term206.
Proof. exact (EQ_MP (@lem1489140 x) (@lem1489125 x h1)). Qed.
Lemma lem1489143 (n : nat) (m : nat) : (term185 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1489144 : term206 = term207.
Proof. exact (@lem1489143 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1489145 : term207 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1489146 : term206 = False.
Proof. exact (TRANS (@lem1489144) (@lem1489145)). Qed.
Lemma lem1489147 (x : real) (h1 : term220 x) : False.
Proof. exact (EQ_MP (@lem1489146) (@lem1489141 x h1)). Qed.
Lemma lem1489148 (x : real) (h1 : term178 x) : False.
Proof. exact (or_elim (@lem1489019 x h1) (fun h0 : term219 x => @lem1489083 x h0) (fun h0 : term220 x => @lem1489147 x h0)). Qed.
Lemma lem1489149 (x : real) (h1 : term181 x) : False.
Proof. exact (or_elim (@lem1488888 x h1) (fun h0 : term179 x => @lem1489018 x h0) (fun h0 : term178 x => @lem1489148 x h0)). Qed.
Lemma lem1489151 (x : real) (h1 : term181 x) : term181 x.
Proof. exact (h1). Qed.
Lemma lem1489152 (x : real) (h1 : term181 x) : (term181 x) = False.
Proof. exact (prop_ext (fun h2 : term181 x => @lem1489149 x h1) (fun h2 : False => @lem1489151 x h1)). Qed.
Lemma lem1489153 (x : real) (h1 : term181 x) : False.
Proof. exact (EQ_MP (@lem1489152 x h1) (@lem1489151 x h1)). Qed.
Lemma lem1489154 (h1 : term183) : term183.
Proof. exact (h1). Qed.
Lemma lem1489155 (h1 : term183) : False.
Proof. exact (ex_elim (@lem1489154 h1) (fun x : real => fun h0 : term182 x => @lem1489153 x h0)). Qed.
Lemma lem1489156 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1489157 (h1 : term13) : term183.
Proof. exact (EQ_MP (@lem1488866) (@lem1489156 h1)). Qed.
Lemma lem1489158 (h1 : term13) : term183 = False.
Proof. exact (prop_ext (fun h2 : term183 => @lem1489155 h2) (fun h2 : False => @lem1489157 h1)). Qed.
Lemma lem1489159 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1489158 h1) (@lem1489157 h1)). Qed.
Lemma lem1489160 : term221.
Proof. exact (fun h0 : term13 => @lem1489159 h0). Qed.
Lemma lem1489161 : term222.
Proof. exact (@lem1386578 term223). Qed.
Lemma lem1489162 : term223.
Proof. exact (@lem1489161 (@lem1489160)). Qed.
