Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_TOTAL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm18392_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1498349 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17160 (real_lt x y) (real_lt y x)). Qed.
Lemma lem1498351 (x : real) (y : real) : (term2 x y) = (term2 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1498352 (y : real) (x : real) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1498351 x y) (@lem1498349 y x)). Qed.
Lemma lem1498353 (y : real) (x : real) : (term5 y x) = (term3 y x).
Proof. exact (@lem17160 (x = y) (term6 y x)). Qed.
Lemma lem1498354 (y : real) (x : real) : (term5 y x) = (term4 y x).
Proof. exact (TRANS (@lem1498353 y x) (@lem1498352 y x)). Qed.
Lemma lem1498355 (P : real -> Prop) : (term7 P) = (term8 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1498356 (x : real) : (term9 x) = (term10 x).
Proof. exact (@lem1498355 (term11 x)). Qed.
Lemma lem1498357 (y : real) (x : real) : (term12 x y) = (term13 y x).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1498358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1498359 (y : real) (x : real) : (term14 x y) = (term5 y x).
Proof. exact (MK_COMB (@lem1498358) (@lem1498357 y x)). Qed.
Lemma lem1498360 (y : real) (x : real) : (term14 x y) = (term4 y x).
Proof. exact (TRANS (@lem1498359 y x) (@lem1498354 y x)). Qed.
Lemma lem1498361 (x : real) : (term15 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1498360 y x)). Qed.
Lemma lem1498362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498363 (x : real) : (term10 x) = (term17 x).
Proof. exact (MK_COMB (@lem1498362) (@lem1498361 x)). Qed.
Lemma lem1498364 (x : real) : (term9 x) = (term17 x).
Proof. exact (TRANS (@lem1498356 x) (@lem1498363 x)). Qed.
Lemma lem1498365 (P : real -> Prop) : (term7 P) = (term8 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1498366 : term18 = term19.
Proof. exact (@lem1498365 term20). Qed.
Lemma lem1498367 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1498368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1498369 (x : real) : (term23 x) = (term9 x).
Proof. exact (MK_COMB (@lem1498368) (@lem1498367 x)). Qed.
Lemma lem1498370 (x : real) : (term23 x) = (term17 x).
Proof. exact (TRANS (@lem1498369 x) (@lem1498364 x)). Qed.
Lemma lem1498371 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem1498370 x)). Qed.
Lemma lem1498372 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498373 : term19 = term26.
Proof. exact (MK_COMB (@lem1498372) (@lem1498371)). Qed.
Lemma lem1498375 : term18 = term26.
Proof. exact (TRANS (@lem1498366) (@lem1498373)). Qed.
Lemma lem1498390 (y : real) (x : real) : (term4 y x) = (term4 y x).
Proof. exact (eq_refl (term4 y x)). Qed.
Lemma lem1498391 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1498390 y x)). Qed.
Lemma lem1498392 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498393 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1498392) (@lem1498391 x)). Qed.
Lemma lem1498394 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1498393 x)). Qed.
Lemma lem1498395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498396 : term26 = term26.
Proof. exact (MK_COMB (@lem1498395) (@lem1498394)). Qed.
Lemma lem1498397 : term18 = term26.
Proof. exact (TRANS (@lem1498375) (@lem1498396)). Qed.
Lemma lem1498398 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (@lem1483554 x y). Qed.
Lemma lem1498411 (x : real) (y : real) : (real_sub x y) = (term29 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1498412 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1498413 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1498412) (@lem1498411 x y)). Qed.
Lemma lem1498414 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (@lem1483512 (term29 x y)). Qed.
Lemma lem1498415 (x : real) (y : real) : (term32 x y) = (term33 x y).
Proof. exact (@lem1483508 x term34 (term35 y)). Qed.
Lemma lem1498416 (y : real) : (term36 y) = (term37 y).
Proof. exact (@lem1483476 term34 term34 y). Qed.
Lemma lem1498418 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1498419 : term40 = term41.
Proof. exact (@lem1498418 term42 term42). Qed.
Lemma lem1498420 : (term43 = (BIT1 0)) = (term44 = term42).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1498421 : term44 = term42.
Proof. exact (EQ_MP (@lem1498420) (@lem940073)). Qed.
Lemma lem1498422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1498423 : term41 = term45.
Proof. exact (MK_COMB (@lem1498422) (@lem1498421)). Qed.
Lemma lem1498424 : term40 = term45.
Proof. exact (TRANS (@lem1498419) (@lem1498423)). Qed.
Lemma lem1498425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498426 : term46 = term47.
Proof. exact (MK_COMB (@lem1498425) (@lem1498424)). Qed.
Lemma lem1498427 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1498428 (y : real) : (term37 y) = (term48 y).
Proof. exact (MK_COMB (@lem1498426) (@lem1498427 y)). Qed.
Lemma lem1498429 (y : real) : (term36 y) = (term48 y).
Proof. exact (TRANS (@lem1498416 y) (@lem1498428 y)). Qed.
Lemma lem1498430 (y : real) : (term48 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1498431 (y : real) : (term36 y) = y.
Proof. exact (TRANS (@lem1498429 y) (@lem1498430 y)). Qed.
Lemma lem1498434 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1498435 (x : real) (y : real) : (term33 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1498434 x) (@lem1498431 y)). Qed.
Lemma lem1498436 (x : real) (y : real) : (term32 x y) = (term50 x y).
Proof. exact (TRANS (@lem1498415 x y) (@lem1498435 x y)). Qed.
Lemma lem1498437 (x : real) (y : real) : (term31 x y) = (term50 x y).
Proof. exact (TRANS (@lem1498414 x y) (@lem1498436 x y)). Qed.
Lemma lem1498438 (x : real) (y : real) : (term51 x y) = (term51 x y).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1498439 (x : real) (y : real) : ((term30 x y) = (term31 x y)) = ((term30 x y) = (term50 x y)).
Proof. exact (MK_COMB (@lem1498438 x y) (@lem1498437 x y)). Qed.
Lemma lem1498440 (x : real) (y : real) : (term30 x y) = (term50 x y).
Proof. exact (EQ_MP (@lem1498439 x y) (@lem1498413 x y)). Qed.
Lemma lem1498441 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498442 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1498441) (@lem1498440 x y)). Qed.
Lemma lem1498443 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498444 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1498442 x y) (@lem1498443)). Qed.
Lemma lem1498445 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498446 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1498445) (@lem1498411 x y)). Qed.
Lemma lem1498447 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498448 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1498446 x y) (@lem1498447)). Qed.
Lemma lem1498449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1498450 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1498449) (@lem1498448 x y)). Qed.
Lemma lem1498451 (x : real) (y : real) : (term28 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1498450 x y) (@lem1498444 x y)). Qed.
Lemma lem1498452 (x : real) (y : real) : (term27 x y) = (term63 x y).
Proof. exact (TRANS (@lem1498398 x y) (@lem1498451 x y)). Qed.
Lemma lem1498453 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (@lem1483531 x y). Qed.
Lemma lem1498466 (x : real) (y : real) : (real_sub x y) = (term29 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1498467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498468 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1498467) (@lem1498466 x y)). Qed.
Lemma lem1498469 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498470 (x : real) (y : real) : (term65 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1498468 x y) (@lem1498469)). Qed.
Lemma lem1498471 (x : real) (y : real) : (term64 x y) = (term68 x y).
Proof. exact (TRANS (@lem1498453 x y) (@lem1498470 x y)). Qed.
Lemma lem1498472 (y : real) (x : real) : (term64 y x) = (term65 y x).
Proof. exact (@lem1483531 y x). Qed.
Lemma lem1498478 (y : real) (x : real) : (real_sub y x) = (term29 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1498483 (x : real) (y : real) : (term29 y x) = (term50 x y).
Proof. exact (@lem1483488 (term35 x) y). Qed.
Lemma lem1498485 (x : real) (y : real) : (real_sub y x) = (term50 x y).
Proof. exact (TRANS (@lem1498478 y x) (@lem1498483 x y)). Qed.
Lemma lem1498486 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498487 (x : real) (y : real) : (term66 y x) = (term69 x y).
Proof. exact (MK_COMB (@lem1498486) (@lem1498485 x y)). Qed.
Lemma lem1498488 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498489 (x : real) (y : real) : (term65 y x) = (term70 x y).
Proof. exact (MK_COMB (@lem1498487 x y) (@lem1498488)). Qed.
Lemma lem1498490 (x : real) (y : real) : (term64 y x) = (term70 x y).
Proof. exact (TRANS (@lem1498472 y x) (@lem1498489 x y)). Qed.
Lemma lem1498491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1498492 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1498491) (@lem1498471 x y)). Qed.
Lemma lem1498493 (x : real) (y : real) : (term1 y x) = (term73 x y).
Proof. exact (MK_COMB (@lem1498492 x y) (@lem1498490 x y)). Qed.
Lemma lem1498494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1498495 (x : real) (y : real) : (term2 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1498494) (@lem1498452 x y)). Qed.
Lemma lem1498496 (x : real) (y : real) : (term4 y x) = (term75 x y).
Proof. exact (MK_COMB (@lem1498495 x y) (@lem1498493 x y)). Qed.
Lemma lem1498497 (x : real) : (term16 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1498496 x y)). Qed.
Lemma lem1498498 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498499 (x : real) : (term17 x) = (term77 x).
Proof. exact (MK_COMB (@lem1498498) (@lem1498497 x)). Qed.
Lemma lem1498500 : term25 = term78.
Proof. exact (fun_ext (fun x : real => @lem1498499 x)). Qed.
Lemma lem1498501 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498502 : term26 = term79.
Proof. exact (MK_COMB (@lem1498501) (@lem1498500)). Qed.
Lemma lem1498561 : term18 = term79.
Proof. exact (TRANS (@lem1498397) (@lem1498502)). Qed.
Lemma lem1498584 (x : real) (y : real) : (term75 x y) = (term80 x y).
Proof. exact (@lem19367 (term60 x y) (term56 x y) (term73 x y)). Qed.
Lemma lem1498585 (x : real) : (term76 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1498584 x y)). Qed.
Lemma lem1498586 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498587 (x : real) : (term77 x) = (term82 x).
Proof. exact (MK_COMB (@lem1498586) (@lem1498585 x)). Qed.
Lemma lem1498588 : term78 = term83.
Proof. exact (fun_ext (fun x : real => @lem1498587 x)). Qed.
Lemma lem1498589 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498590 : term79 = term84.
Proof. exact (MK_COMB (@lem1498589) (@lem1498588)). Qed.
Lemma lem1498591 : term18 = term84.
Proof. exact (TRANS (@lem1498561) (@lem1498590)). Qed.
Lemma lem1498601 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (h1). Qed.
Lemma lem1498602 (x : real) (y : real) (h1 : term85 x y) : term85 x y.
Proof. exact (h1). Qed.
Lemma lem1498603 (x : real) (y : real) (h1 : term85 x y) : term73 x y.
Proof. exact (proj2 (@lem1498602 x y h1)). Qed.
Lemma lem1498604 (x : real) (y : real) (h1 : term85 x y) : term60 x y.
Proof. exact (proj1 (@lem1498602 x y h1)). Qed.
Lemma lem1498605 (x : real) (y : real) (h1 : term85 x y) : term70 x y.
Proof. exact (proj2 (@lem1498603 x y h1)). Qed.
Lemma lem1498608 (n : nat) (m : nat) : (term86 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498609 : term87 = term88.
Proof. exact (@lem1498608 (NUMERAL 0) term42). Qed.
Lemma lem1498610 : term89 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498611 (h1 : term89 = (BIT1 0)) : term88 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498612 : (term89 = (BIT1 0)) = (term88 = True).
Proof. exact (prop_ext (fun h1 : term89 = (BIT1 0) => @lem1498611 h1) (fun h1 : term88 = True => @lem1498610)). Qed.
Lemma lem1498613 : term88 = True.
Proof. exact (EQ_MP (@lem1498612) (@lem1498610)). Qed.
Lemma lem1498614 : term87 = True.
Proof. exact (TRANS (@lem1498609) (@lem1498613)). Qed.
Lemma lem1498615 : True = term87.
Proof. exact (SYM (@lem1498614)). Qed.
Lemma lem1498616 : term87.
Proof. exact (EQ_MP (@lem1498615) (@lem0)). Qed.
Lemma lem1498617 (x : real) (y : real) (h1 : term85 x y) : term90 x y.
Proof. exact (conj (@lem1498616) (@lem1498605 x y h1)). Qed.
Lemma lem1498619 (x : real) (y : real) : term91 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1498620 (x : real) (y : real) : term92 x y.
Proof. exact (@lem1498619 term45 (term50 x y)). Qed.
Lemma lem1498621 (x : real) (y : real) (h1 : term85 x y) : term93 x y.
Proof. exact (@lem1498620 x y (@lem1498617 x y h1)). Qed.
Lemma lem1498622 (x : real) (y : real) : (term94 x y) = (term50 x y).
Proof. exact (@lem1483460 (term50 x y)). Qed.
Lemma lem1498623 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498624 (x : real) (y : real) : (term95 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1498623) (@lem1498622 x y)). Qed.
Lemma lem1498625 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498626 (x : real) (y : real) : (term93 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1498624 x y) (@lem1498625)). Qed.
Lemma lem1498627 (x : real) (y : real) (h1 : term85 x y) : term70 x y.
Proof. exact (EQ_MP (@lem1498626 x y) (@lem1498621 x y h1)). Qed.
Lemma lem1498629 (n : nat) (m : nat) : (term86 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498630 : term87 = term88.
Proof. exact (@lem1498629 (NUMERAL 0) term42). Qed.
Lemma lem1498631 : term89 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498632 (h1 : term89 = (BIT1 0)) : term88 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498633 : (term89 = (BIT1 0)) = (term88 = True).
Proof. exact (prop_ext (fun h1 : term89 = (BIT1 0) => @lem1498632 h1) (fun h1 : term88 = True => @lem1498631)). Qed.
Lemma lem1498634 : term88 = True.
Proof. exact (EQ_MP (@lem1498633) (@lem1498631)). Qed.
Lemma lem1498635 : term87 = True.
Proof. exact (TRANS (@lem1498630) (@lem1498634)). Qed.
Lemma lem1498636 : True = term87.
Proof. exact (SYM (@lem1498635)). Qed.
Lemma lem1498637 : term87.
Proof. exact (EQ_MP (@lem1498636) (@lem0)). Qed.
Lemma lem1498638 (x : real) (y : real) (h1 : term85 x y) : term96 x y.
Proof. exact (conj (@lem1498637) (@lem1498604 x y h1)). Qed.
Lemma lem1498640 (x : real) (y : real) : term97 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1498641 (x : real) (y : real) : term98 x y.
Proof. exact (@lem1498640 term45 (term29 x y)). Qed.
Lemma lem1498642 (x : real) (y : real) (h1 : term85 x y) : term99 x y.
Proof. exact (@lem1498641 x y (@lem1498638 x y h1)). Qed.
Lemma lem1498643 (x : real) (y : real) : (term100 x y) = (term29 x y).
Proof. exact (@lem1483460 (term29 x y)). Qed.
Lemma lem1498644 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498645 (x : real) (y : real) : (term101 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1498644) (@lem1498643 x y)). Qed.
Lemma lem1498646 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498647 (x : real) (y : real) : (term99 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1498645 x y) (@lem1498646)). Qed.
Lemma lem1498648 (x : real) (y : real) (h1 : term85 x y) : term60 x y.
Proof. exact (EQ_MP (@lem1498647 x y) (@lem1498642 x y h1)). Qed.
Lemma lem1498649 (x : real) (y : real) (h1 : term85 x y) : term102 x y.
Proof. exact (conj (@lem1498648 x y h1) (@lem1498627 x y h1)). Qed.
Lemma lem1498651 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1498652 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1498651 (term29 x y) (term50 x y)). Qed.
Lemma lem1498653 (x : real) (y : real) (h1 : term85 x y) : term105 x y.
Proof. exact (@lem1498652 x y (@lem1498649 x y h1)). Qed.
Lemma lem1498654 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1483480 x (term35 x) (term35 y) y). Qed.
Lemma lem1498655 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1483442 term34 x). Qed.
Lemma lem1498657 (m : nat) : (term110 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1498658 : term111 = term54.
Proof. exact (@lem1498657 term42). Qed.
Lemma lem1498659 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498660 : term112 = term113.
Proof. exact (MK_COMB (@lem1498659) (@lem1498658)). Qed.
Lemma lem1498661 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1498662 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1498660) (@lem1498661 x)). Qed.
Lemma lem1498663 (x : real) : (term108 x) = (term114 x).
Proof. exact (TRANS (@lem1498655 x) (@lem1498662 x)). Qed.
Lemma lem1498664 (x : real) : (term114 x) = term54.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1498665 (x : real) : (term108 x) = term54.
Proof. exact (TRANS (@lem1498663 x) (@lem1498664 x)). Qed.
Lemma lem1498666 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1498667 (x : real) : (term115 x) = term116.
Proof. exact (MK_COMB (@lem1498666) (@lem1498665 x)). Qed.
Lemma lem1498668 (y : real) : (term117 y) = (term109 y).
Proof. exact (@lem1483440 term34 y). Qed.
Lemma lem1498670 (m : nat) : (term110 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1498671 : term111 = term54.
Proof. exact (@lem1498670 term42). Qed.
Lemma lem1498672 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498673 : term112 = term113.
Proof. exact (MK_COMB (@lem1498672) (@lem1498671)). Qed.
Lemma lem1498674 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1498675 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1498673) (@lem1498674 y)). Qed.
Lemma lem1498676 (y : real) : (term117 y) = (term114 y).
Proof. exact (TRANS (@lem1498668 y) (@lem1498675 y)). Qed.
Lemma lem1498677 (y : real) : (term114 y) = term54.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1498678 (y : real) : (term117 y) = term54.
Proof. exact (TRANS (@lem1498676 y) (@lem1498677 y)). Qed.
Lemma lem1498679 (x : real) (y : real) : (term107 x y) = term118.
Proof. exact (MK_COMB (@lem1498667 x) (@lem1498678 y)). Qed.
Lemma lem1498680 (x : real) (y : real) : (term106 x y) = term118.
Proof. exact (TRANS (@lem1498654 x y) (@lem1498679 x y)). Qed.
Lemma lem1498681 : term118 = term54.
Proof. exact (@lem1483448 term54). Qed.
Lemma lem1498682 (x : real) (y : real) : (term106 x y) = term54.
Proof. exact (TRANS (@lem1498680 x y) (@lem1498681)). Qed.
Lemma lem1498683 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498684 (x : real) (y : real) : (term119 x y) = term120.
Proof. exact (MK_COMB (@lem1498683) (@lem1498682 x y)). Qed.
Lemma lem1498685 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498686 (x : real) (y : real) : (term105 x y) = term121.
Proof. exact (MK_COMB (@lem1498684 x y) (@lem1498685)). Qed.
Lemma lem1498687 (x : real) (y : real) (h1 : term85 x y) : term121.
Proof. exact (EQ_MP (@lem1498686 x y) (@lem1498653 x y h1)). Qed.
Lemma lem1498689 (n : nat) (m : nat) : (term86 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498690 : term121 = term122.
Proof. exact (@lem1498689 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1498691 : term122 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1498692 : term121 = False.
Proof. exact (TRANS (@lem1498690) (@lem1498691)). Qed.
Lemma lem1498693 (x : real) (y : real) (h1 : term85 x y) : False.
Proof. exact (EQ_MP (@lem1498692) (@lem1498687 x y h1)). Qed.
Lemma lem1498694 (x : real) (y : real) (h1 : term123 x y) : term123 x y.
Proof. exact (h1). Qed.
Lemma lem1498695 (x : real) (y : real) (h1 : term123 x y) : term73 x y.
Proof. exact (proj2 (@lem1498694 x y h1)). Qed.
Lemma lem1498696 (x : real) (y : real) (h1 : term123 x y) : term56 x y.
Proof. exact (proj1 (@lem1498694 x y h1)). Qed.
Lemma lem1498698 (x : real) (y : real) (h1 : term123 x y) : term68 x y.
Proof. exact (proj1 (@lem1498695 x y h1)). Qed.
Lemma lem1498700 (n : nat) (m : nat) : (term86 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498701 : term87 = term88.
Proof. exact (@lem1498700 (NUMERAL 0) term42). Qed.
Lemma lem1498702 : term89 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498703 (h1 : term89 = (BIT1 0)) : term88 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498704 : (term89 = (BIT1 0)) = (term88 = True).
Proof. exact (prop_ext (fun h1 : term89 = (BIT1 0) => @lem1498703 h1) (fun h1 : term88 = True => @lem1498702)). Qed.
Lemma lem1498705 : term88 = True.
Proof. exact (EQ_MP (@lem1498704) (@lem1498702)). Qed.
Lemma lem1498706 : term87 = True.
Proof. exact (TRANS (@lem1498701) (@lem1498705)). Qed.
Lemma lem1498707 : True = term87.
Proof. exact (SYM (@lem1498706)). Qed.
Lemma lem1498708 : term87.
Proof. exact (EQ_MP (@lem1498707) (@lem0)). Qed.
Lemma lem1498709 (x : real) (y : real) (h1 : term123 x y) : term124 x y.
Proof. exact (conj (@lem1498708) (@lem1498698 x y h1)). Qed.
Lemma lem1498711 (x : real) (y : real) : term91 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1498712 (x : real) (y : real) : term125 x y.
Proof. exact (@lem1498711 term45 (term29 x y)). Qed.
Lemma lem1498713 (x : real) (y : real) (h1 : term123 x y) : term126 x y.
Proof. exact (@lem1498712 x y (@lem1498709 x y h1)). Qed.
Lemma lem1498714 (x : real) (y : real) : (term100 x y) = (term29 x y).
Proof. exact (@lem1483460 (term29 x y)). Qed.
Lemma lem1498715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498716 (x : real) (y : real) : (term127 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1498715) (@lem1498714 x y)). Qed.
Lemma lem1498717 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498718 (x : real) (y : real) : (term126 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1498716 x y) (@lem1498717)). Qed.
Lemma lem1498719 (x : real) (y : real) (h1 : term123 x y) : term68 x y.
Proof. exact (EQ_MP (@lem1498718 x y) (@lem1498713 x y h1)). Qed.
Lemma lem1498721 (n : nat) (m : nat) : (term86 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498722 : term87 = term88.
Proof. exact (@lem1498721 (NUMERAL 0) term42). Qed.
Lemma lem1498723 : term89 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498724 (h1 : term89 = (BIT1 0)) : term88 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498725 : (term89 = (BIT1 0)) = (term88 = True).
Proof. exact (prop_ext (fun h1 : term89 = (BIT1 0) => @lem1498724 h1) (fun h1 : term88 = True => @lem1498723)). Qed.
Lemma lem1498726 : term88 = True.
Proof. exact (EQ_MP (@lem1498725) (@lem1498723)). Qed.
Lemma lem1498727 : term87 = True.
Proof. exact (TRANS (@lem1498722) (@lem1498726)). Qed.
Lemma lem1498728 : True = term87.
Proof. exact (SYM (@lem1498727)). Qed.
Lemma lem1498729 : term87.
Proof. exact (EQ_MP (@lem1498728) (@lem0)). Qed.
Lemma lem1498730 (x : real) (y : real) (h1 : term123 x y) : term128 x y.
Proof. exact (conj (@lem1498729) (@lem1498696 x y h1)). Qed.
Lemma lem1498732 (x : real) (y : real) : term97 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1498733 (x : real) (y : real) : term129 x y.
Proof. exact (@lem1498732 term45 (term50 x y)). Qed.
Lemma lem1498734 (x : real) (y : real) (h1 : term123 x y) : term130 x y.
Proof. exact (@lem1498733 x y (@lem1498730 x y h1)). Qed.
Lemma lem1498735 (x : real) (y : real) : (term94 x y) = (term50 x y).
Proof. exact (@lem1483460 (term50 x y)). Qed.
Lemma lem1498736 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498737 (x : real) (y : real) : (term131 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1498736) (@lem1498735 x y)). Qed.
Lemma lem1498738 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498739 (x : real) (y : real) : (term130 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1498737 x y) (@lem1498738)). Qed.
Lemma lem1498740 (x : real) (y : real) (h1 : term123 x y) : term56 x y.
Proof. exact (EQ_MP (@lem1498739 x y) (@lem1498734 x y h1)). Qed.
Lemma lem1498741 (x : real) (y : real) (h1 : term123 x y) : term132 x y.
Proof. exact (conj (@lem1498740 x y h1) (@lem1498719 x y h1)). Qed.
Lemma lem1498743 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1498744 (x : real) (y : real) : term133 x y.
Proof. exact (@lem1498743 (term50 x y) (term29 x y)). Qed.
Lemma lem1498745 (x : real) (y : real) (h1 : term123 x y) : term134 x y.
Proof. exact (@lem1498744 x y (@lem1498741 x y h1)). Qed.
Lemma lem1498746 (x : real) (y : real) : (term135 x y) = (term136 x y).
Proof. exact (@lem1483480 (term35 x) x y (term35 y)). Qed.
Lemma lem1498747 (x : real) : (term117 x) = (term109 x).
Proof. exact (@lem1483440 term34 x). Qed.
Lemma lem1498749 (m : nat) : (term110 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1498750 : term111 = term54.
Proof. exact (@lem1498749 term42). Qed.
Lemma lem1498751 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498752 : term112 = term113.
Proof. exact (MK_COMB (@lem1498751) (@lem1498750)). Qed.
Lemma lem1498753 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1498754 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1498752) (@lem1498753 x)). Qed.
Lemma lem1498755 (x : real) : (term117 x) = (term114 x).
Proof. exact (TRANS (@lem1498747 x) (@lem1498754 x)). Qed.
Lemma lem1498756 (x : real) : (term114 x) = term54.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1498757 (x : real) : (term117 x) = term54.
Proof. exact (TRANS (@lem1498755 x) (@lem1498756 x)). Qed.
Lemma lem1498758 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1498759 (x : real) : (term137 x) = term116.
Proof. exact (MK_COMB (@lem1498758) (@lem1498757 x)). Qed.
Lemma lem1498760 (y : real) : (term108 y) = (term109 y).
Proof. exact (@lem1483442 term34 y). Qed.
Lemma lem1498762 (m : nat) : (term110 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1498763 : term111 = term54.
Proof. exact (@lem1498762 term42). Qed.
Lemma lem1498764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498765 : term112 = term113.
Proof. exact (MK_COMB (@lem1498764) (@lem1498763)). Qed.
Lemma lem1498766 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1498767 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1498765) (@lem1498766 y)). Qed.
Lemma lem1498768 (y : real) : (term108 y) = (term114 y).
Proof. exact (TRANS (@lem1498760 y) (@lem1498767 y)). Qed.
Lemma lem1498769 (y : real) : (term114 y) = term54.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1498770 (y : real) : (term108 y) = term54.
Proof. exact (TRANS (@lem1498768 y) (@lem1498769 y)). Qed.
Lemma lem1498771 (x : real) (y : real) : (term136 x y) = term118.
Proof. exact (MK_COMB (@lem1498759 x) (@lem1498770 y)). Qed.
Lemma lem1498772 (x : real) (y : real) : (term135 x y) = term118.
Proof. exact (TRANS (@lem1498746 x y) (@lem1498771 x y)). Qed.
Lemma lem1498773 : term118 = term54.
Proof. exact (@lem1483448 term54). Qed.
Lemma lem1498774 (x : real) (y : real) : (term135 x y) = term54.
Proof. exact (TRANS (@lem1498772 x y) (@lem1498773)). Qed.
Lemma lem1498775 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498776 (x : real) (y : real) : (term138 x y) = term120.
Proof. exact (MK_COMB (@lem1498775) (@lem1498774 x y)). Qed.
Lemma lem1498777 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1498778 (x : real) (y : real) : (term134 x y) = term121.
Proof. exact (MK_COMB (@lem1498776 x y) (@lem1498777)). Qed.
Lemma lem1498779 (x : real) (y : real) (h1 : term123 x y) : term121.
Proof. exact (EQ_MP (@lem1498778 x y) (@lem1498745 x y h1)). Qed.
Lemma lem1498781 (n : nat) (m : nat) : (term86 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498782 : term121 = term122.
Proof. exact (@lem1498781 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1498783 : term122 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1498784 : term121 = False.
Proof. exact (TRANS (@lem1498782) (@lem1498783)). Qed.
Lemma lem1498785 (x : real) (y : real) (h1 : term123 x y) : False.
Proof. exact (EQ_MP (@lem1498784) (@lem1498779 x y h1)). Qed.
Lemma lem1498786 (x : real) (y : real) (h1 : term80 x y) : False.
Proof. exact (or_elim (@lem1498601 x y h1) (fun h0 : term85 x y => @lem1498693 x y h0) (fun h0 : term123 x y => @lem1498785 x y h0)). Qed.
Lemma lem1498788 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (h1). Qed.
Lemma lem1498789 (x : real) (y : real) (h1 : term80 x y) : (term80 x y) = False.
Proof. exact (prop_ext (fun h2 : term80 x y => @lem1498786 x y h1) (fun h2 : False => @lem1498788 x y h1)). Qed.
Lemma lem1498790 (x : real) (y : real) (h1 : term80 x y) : False.
Proof. exact (EQ_MP (@lem1498789 x y h1) (@lem1498788 x y h1)). Qed.
Lemma lem1498791 (x : real) (h1 : term82 x) : term82 x.
Proof. exact (h1). Qed.
Lemma lem1498792 (x : real) (h1 : term82 x) : False.
Proof. exact (ex_elim (@lem1498791 x h1) (fun y : real => fun h0 : term81 x y => @lem1498790 x y h0)). Qed.
Lemma lem1498793 (h1 : term84) : term84.
Proof. exact (h1). Qed.
Lemma lem1498794 (h1 : term84) : False.
Proof. exact (ex_elim (@lem1498793 h1) (fun x : real => fun h0 : term83 x => @lem1498792 x h0)). Qed.
Lemma lem1498795 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1498796 (h1 : term18) : term84.
Proof. exact (EQ_MP (@lem1498591) (@lem1498795 h1)). Qed.
Lemma lem1498797 (h1 : term18) : term84 = False.
Proof. exact (prop_ext (fun h2 : term84 => @lem1498794 h2) (fun h2 : False => @lem1498796 h1)). Qed.
Lemma lem1498798 (h1 : term18) : False.
Proof. exact (EQ_MP (@lem1498797 h1) (@lem1498796 h1)). Qed.
Lemma lem1498799 : term139.
Proof. exact (fun h0 : term18 => @lem1498798 h0). Qed.
Lemma lem1498800 : term140.
Proof. exact (@lem1386578 term141). Qed.
Lemma lem1498801 : term141.
Proof. exact (@lem1498800 (@lem1498799)). Qed.
