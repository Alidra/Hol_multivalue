Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_CIRCLE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482679_spec.
Require Import thm1482703_spec.
Require Import thm1482705_spec.
Require Import thm1482981_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1542372 (x : real) (h : real) (y : real) : (term0 x h y) = (term1 x h y).
Proof. exact (@lem17362 (term2 h y x) (term3 x h y)). Qed.
Lemma lem1542373 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1542374 (x : real) (y : real) : (term6 x y) = (term7 x y).
Proof. exact (@lem1542373 (term8 x y)). Qed.
Lemma lem1542375 (x : real) (h : real) (y : real) : (term9 x y h) = (term10 x h y).
Proof. exact (eq_refl (term9 x y h)). Qed.
Lemma lem1542376 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1542377 (x : real) (h : real) (y : real) : (term11 x y h) = (term0 x h y).
Proof. exact (MK_COMB (@lem1542376) (@lem1542375 x h y)). Qed.
Lemma lem1542378 (x : real) (h : real) (y : real) : (term11 x y h) = (term1 x h y).
Proof. exact (TRANS (@lem1542377 x h y) (@lem1542372 x h y)). Qed.
Lemma lem1542379 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (fun_ext (fun h : real => @lem1542378 x h y)). Qed.
Lemma lem1542380 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542381 (x : real) (y : real) : (term7 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1542380) (@lem1542379 x y)). Qed.
Lemma lem1542382 (x : real) (y : real) : (term6 x y) = (term14 x y).
Proof. exact (TRANS (@lem1542374 x y) (@lem1542381 x y)). Qed.
Lemma lem1542383 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1542384 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1542383 (term17 x)). Qed.
Lemma lem1542385 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1542386 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1542387 (x : real) (y : real) : (term20 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem1542386) (@lem1542385 x y)). Qed.
Lemma lem1542388 (x : real) (y : real) : (term20 x y) = (term14 x y).
Proof. exact (TRANS (@lem1542387 x y) (@lem1542382 x y)). Qed.
Lemma lem1542389 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1542388 x y)). Qed.
Lemma lem1542390 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542391 (x : real) : (term16 x) = (term23 x).
Proof. exact (MK_COMB (@lem1542390) (@lem1542389 x)). Qed.
Lemma lem1542392 (x : real) : (term15 x) = (term23 x).
Proof. exact (TRANS (@lem1542384 x) (@lem1542391 x)). Qed.
Lemma lem1542393 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1542394 : term24 = term25.
Proof. exact (@lem1542393 term26). Qed.
Lemma lem1542395 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1542396 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1542397 (x : real) : (term29 x) = (term15 x).
Proof. exact (MK_COMB (@lem1542396) (@lem1542395 x)). Qed.
Lemma lem1542398 (x : real) : (term29 x) = (term23 x).
Proof. exact (TRANS (@lem1542397 x) (@lem1542392 x)). Qed.
Lemma lem1542399 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1542398 x)). Qed.
Lemma lem1542400 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542401 : term25 = term32.
Proof. exact (MK_COMB (@lem1542400) (@lem1542399)). Qed.
Lemma lem1542403 : term24 = term32.
Proof. exact (TRANS (@lem1542394) (@lem1542401)). Qed.
Lemma lem1542410 (x : real) (h : real) (y : real) : (term1 x h y) = (term1 x h y).
Proof. exact (eq_refl (term1 x h y)). Qed.
Lemma lem1542411 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (fun_ext (fun h : real => @lem1542410 x h y)). Qed.
Lemma lem1542412 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542413 (x : real) (y : real) : (term14 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem1542412) (@lem1542411 x y)). Qed.
Lemma lem1542414 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1542413 x y)). Qed.
Lemma lem1542415 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542416 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1542415) (@lem1542414 x)). Qed.
Lemma lem1542417 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1542416 x)). Qed.
Lemma lem1542418 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542419 : term32 = term32.
Proof. exact (MK_COMB (@lem1542418) (@lem1542417)). Qed.
Lemma lem1542420 : term24 = term32.
Proof. exact (TRANS (@lem1542403) (@lem1542419)). Qed.
Lemma lem1542421 (y : real) (x : real) (h : real) : (term2 h y x) = (term33 y x h).
Proof. exact (@lem1483521 (term34 y x) (real_abs h)). Qed.
Lemma lem1542422 (h : real) : (real_abs h) = (real_abs h).
Proof. exact (eq_refl (real_abs h)). Qed.
Lemma lem1542428 (y : real) (x : real) : (term34 y x) = (term35 y x).
Proof. exact (@lem1483519 (real_abs y) (real_abs x)). Qed.
Lemma lem1542433 (x : real) (y : real) : (term35 y x) = (term36 x y).
Proof. exact (@lem1483488 (term37 x) (real_abs y)). Qed.
Lemma lem1542435 (x : real) (y : real) : (term34 y x) = (term36 x y).
Proof. exact (TRANS (@lem1542428 y x) (@lem1542433 x y)). Qed.
Lemma lem1542436 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1542437 (x : real) (y : real) : (term38 y x) = (term39 x y).
Proof. exact (MK_COMB (@lem1542436) (@lem1542435 x y)). Qed.
Lemma lem1542438 (x : real) (y : real) (h : real) : (term40 y x h) = (term41 x y h).
Proof. exact (MK_COMB (@lem1542437 x y) (@lem1542422 h)). Qed.
Lemma lem1542439 (x : real) (y : real) (h : real) : (term41 x y h) = (term42 x y h).
Proof. exact (@lem1483519 (term36 x y) (real_abs h)). Qed.
Lemma lem1542444 (h : real) (x : real) (y : real) : (term42 x y h) = (term43 h x y).
Proof. exact (@lem1483488 (term37 h) (term36 x y)). Qed.
Lemma lem1542445 (h : real) (x : real) (y : real) : (term41 x y h) = (term43 h x y).
Proof. exact (TRANS (@lem1542439 x y h) (@lem1542444 h x y)). Qed.
Lemma lem1542446 (h : real) (x : real) (y : real) : (term40 y x h) = (term43 h x y).
Proof. exact (TRANS (@lem1542438 x y h) (@lem1542445 h x y)). Qed.
Lemma lem1542447 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542448 (h : real) (x : real) (y : real) : (term44 y x h) = (term45 h x y).
Proof. exact (MK_COMB (@lem1542447) (@lem1542446 h x y)). Qed.
Lemma lem1542449 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542450 (h : real) (x : real) (y : real) : (term33 y x h) = (term47 h x y).
Proof. exact (MK_COMB (@lem1542448 h x y) (@lem1542449)). Qed.
Lemma lem1542451 (h : real) (x : real) (y : real) : (term2 h y x) = (term47 h x y).
Proof. exact (TRANS (@lem1542421 y x h) (@lem1542450 h x y)). Qed.
Lemma lem1542452 (x : real) (h : real) (y : real) : (term48 x h y) = (term49 x h y).
Proof. exact (@lem1483531 (term50 x h) (real_abs y)). Qed.
Lemma lem1542458 (x : real) (h : real) (y : real) : (term51 x h y) = (term52 x h y).
Proof. exact (@lem1483519 (term50 x h) (real_abs y)). Qed.
Lemma lem1542463 (y : real) (x : real) (h : real) : (term52 x h y) = (term53 y x h).
Proof. exact (@lem1483488 (term37 y) (term50 x h)). Qed.
Lemma lem1542465 (y : real) (x : real) (h : real) : (term51 x h y) = (term53 y x h).
Proof. exact (TRANS (@lem1542458 x h y) (@lem1542463 y x h)). Qed.
Lemma lem1542466 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1542467 (y : real) (x : real) (h : real) : (term54 x h y) = (term55 y x h).
Proof. exact (MK_COMB (@lem1542466) (@lem1542465 y x h)). Qed.
Lemma lem1542468 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542469 (y : real) (x : real) (h : real) : (term49 x h y) = (term56 y x h).
Proof. exact (MK_COMB (@lem1542467 y x h) (@lem1542468)). Qed.
Lemma lem1542470 (y : real) (x : real) (h : real) : (term48 x h y) = (term56 y x h).
Proof. exact (TRANS (@lem1542452 x h y) (@lem1542469 y x h)). Qed.
Lemma lem1542471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542472 (h : real) (x : real) (y : real) : (term57 h y x) = (term58 h x y).
Proof. exact (MK_COMB (@lem1542471) (@lem1542451 h x y)). Qed.
Lemma lem1542473 (y : real) (x : real) (h : real) : (term1 x h y) = (term59 y x h).
Proof. exact (MK_COMB (@lem1542472 h x y) (@lem1542470 y x h)). Qed.
Lemma lem1542474 (y : real) (x : real) : (term13 x y) = (term60 y x).
Proof. exact (fun_ext (fun h : real => @lem1542473 y x h)). Qed.
Lemma lem1542475 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542476 (y : real) (x : real) : (term14 x y) = (term61 y x).
Proof. exact (MK_COMB (@lem1542475) (@lem1542474 y x)). Qed.
Lemma lem1542477 (x : real) : (term22 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1542476 y x)). Qed.
Lemma lem1542478 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542479 (x : real) : (term23 x) = (term63 x).
Proof. exact (MK_COMB (@lem1542478) (@lem1542477 x)). Qed.
Lemma lem1542480 : term31 = term64.
Proof. exact (fun_ext (fun x : real => @lem1542479 x)). Qed.
Lemma lem1542481 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542482 : term32 = term65.
Proof. exact (MK_COMB (@lem1542481) (@lem1542480)). Qed.
Lemma lem1542545 : term24 = term65.
Proof. exact (TRANS (@lem1542420) (@lem1542482)). Qed.
Lemma lem1542552 (y : real) (x : real) (h : real) : (term59 y x h) = (term59 y x h).
Proof. exact (eq_refl (term59 y x h)). Qed.
Lemma lem1542553 (y : real) (x : real) : (term60 y x) = (term60 y x).
Proof. exact (fun_ext (fun h : real => @lem1542552 y x h)). Qed.
Lemma lem1542554 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542555 (y : real) (x : real) : (term61 y x) = (term61 y x).
Proof. exact (MK_COMB (@lem1542554) (@lem1542553 y x)). Qed.
Lemma lem1542556 (x : real) : (term62 x) = (term62 x).
Proof. exact (fun_ext (fun y : real => @lem1542555 y x)). Qed.
Lemma lem1542557 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542558 (x : real) : (term63 x) = (term63 x).
Proof. exact (MK_COMB (@lem1542557) (@lem1542556 x)). Qed.
Lemma lem1542559 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1542558 x)). Qed.
Lemma lem1542560 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1542561 : term65 = term65.
Proof. exact (MK_COMB (@lem1542560) (@lem1542559)). Qed.
Lemma lem1542562 : term24 = term65.
Proof. exact (TRANS (@lem1542545) (@lem1542561)). Qed.
Lemma lem1542564 (a : real) (x : real) (r : real) : (term66 x a r) = (term67 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1542565 (x : real) (y : real) (h : real) : (term47 h x y) = (term68 x y h).
Proof. exact (@lem1542564 (term36 x y) h term46). Qed.
Lemma lem1542572 (h : real) : (term69 h) = h.
Proof. exact (@lem1483460 h). Qed.
Lemma lem1542587 (x : real) (y : real) : (term70 x y) = (term70 x y).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem1542588 (x : real) (y : real) (h : real) : (term71 x y h) = (term72 x y h).
Proof. exact (MK_COMB (@lem1542587 x y) (@lem1542572 h)). Qed.
Lemma lem1542589 (h : real) (x : real) (y : real) : (term72 x y h) = (term73 h x y).
Proof. exact (@lem1483488 h (term36 x y)). Qed.
Lemma lem1542590 (h : real) (x : real) (y : real) : (term71 x y h) = (term73 h x y).
Proof. exact (TRANS (@lem1542588 x y h) (@lem1542589 h x y)). Qed.
Lemma lem1542591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542592 (h : real) (x : real) (y : real) : (term74 x y h) = (term75 h x y).
Proof. exact (MK_COMB (@lem1542591) (@lem1542590 h x y)). Qed.
Lemma lem1542593 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542594 (h : real) (x : real) (y : real) : (term76 x y h) = (term77 h x y).
Proof. exact (MK_COMB (@lem1542592 h x y) (@lem1542593)). Qed.
Lemma lem1542619 (h : real) (x : real) (y : real) : (term78 x y h) = (term79 h x y).
Proof. exact (@lem1483488 (term80 h) (term36 x y)). Qed.
Lemma lem1542620 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542621 (h : real) (x : real) (y : real) : (term81 x y h) = (term82 h x y).
Proof. exact (MK_COMB (@lem1542620) (@lem1542619 h x y)). Qed.
Lemma lem1542622 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542623 (h : real) (x : real) (y : real) : (term83 x y h) = (term84 h x y).
Proof. exact (MK_COMB (@lem1542621 h x y) (@lem1542622)). Qed.
Lemma lem1542624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542625 (h : real) (x : real) (y : real) : (term85 x y h) = (term86 h x y).
Proof. exact (MK_COMB (@lem1542624) (@lem1542623 h x y)). Qed.
Lemma lem1542626 (h : real) (x : real) (y : real) : (term68 x y h) = (term87 h x y).
Proof. exact (MK_COMB (@lem1542625 h x y) (@lem1542594 h x y)). Qed.
Lemma lem1542627 (h : real) (x : real) (y : real) : (term47 h x y) = (term87 h x y).
Proof. exact (TRANS (@lem1542565 x y h) (@lem1542626 h x y)). Qed.
Lemma lem1542629 (a : real) (x : real) (b : real) (r : real) : (term88 a x b r) = (term89 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem1542630 (h : real) (x : real) (y : real) : (term84 h x y) = (term90 h x y).
Proof. exact (@lem1542629 (term80 h) x (real_abs y) term46). Qed.
Lemma lem1542631 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1542638 (x : real) : (term69 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1542639 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1542640 (x : real) : (term91 x) = (real_add x).
Proof. exact (MK_COMB (@lem1542639) (@lem1542638 x)). Qed.
Lemma lem1542643 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1542640 x) (@lem1542631 y)). Qed.
Lemma lem1542652 (h : real) : (term94 h) = (term94 h).
Proof. exact (eq_refl (term94 h)). Qed.
Lemma lem1542655 (h : real) (x : real) (y : real) : (term95 h x y) = (term96 h x y).
Proof. exact (MK_COMB (@lem1542652 h) (@lem1542643 x y)). Qed.
Lemma lem1542656 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542657 (h : real) (x : real) (y : real) : (term97 h x y) = (term98 h x y).
Proof. exact (MK_COMB (@lem1542656) (@lem1542655 h x y)). Qed.
Lemma lem1542658 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542659 (h : real) (x : real) (y : real) : (term99 h x y) = (term100 h x y).
Proof. exact (MK_COMB (@lem1542657 h x y) (@lem1542658)). Qed.
Lemma lem1542690 (h : real) (x : real) (y : real) : (term101 h x y) = (term101 h x y).
Proof. exact (eq_refl (term101 h x y)). Qed.
Lemma lem1542691 (h : real) (x : real) (y : real) : (term90 h x y) = (term102 h x y).
Proof. exact (MK_COMB (@lem1542690 h x y) (@lem1542659 h x y)). Qed.
Lemma lem1542692 (h : real) (x : real) (y : real) : (term84 h x y) = (term102 h x y).
Proof. exact (TRANS (@lem1542630 h x y) (@lem1542691 h x y)). Qed.
Lemma lem1542693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542694 (h : real) (x : real) (y : real) : (term86 h x y) = (term103 h x y).
Proof. exact (MK_COMB (@lem1542693) (@lem1542692 h x y)). Qed.
Lemma lem1542696 (a : real) (x : real) (b : real) (r : real) : (term88 a x b r) = (term89 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem1542697 (h : real) (x : real) (y : real) : (term77 h x y) = (term104 h x y).
Proof. exact (@lem1542696 h x (real_abs y) term46). Qed.
Lemma lem1542698 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1542705 (x : real) : (term69 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1542706 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1542707 (x : real) : (term91 x) = (real_add x).
Proof. exact (MK_COMB (@lem1542706) (@lem1542705 x)). Qed.
Lemma lem1542710 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1542707 x) (@lem1542698 y)). Qed.
Lemma lem1542713 (h : real) : (real_add h) = (real_add h).
Proof. exact (eq_refl (real_add h)). Qed.
Lemma lem1542716 (h : real) (x : real) (y : real) : (term105 h x y) = (term106 h x y).
Proof. exact (MK_COMB (@lem1542713 h) (@lem1542710 x y)). Qed.
Lemma lem1542717 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542718 (h : real) (x : real) (y : real) : (term107 h x y) = (term108 h x y).
Proof. exact (MK_COMB (@lem1542717) (@lem1542716 h x y)). Qed.
Lemma lem1542719 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542720 (h : real) (x : real) (y : real) : (term109 h x y) = (term110 h x y).
Proof. exact (MK_COMB (@lem1542718 h x y) (@lem1542719)). Qed.
Lemma lem1542745 (h : real) (x : real) (y : real) : (term111 h x y) = (term111 h x y).
Proof. exact (eq_refl (term111 h x y)). Qed.
Lemma lem1542746 (h : real) (x : real) (y : real) : (term104 h x y) = (term112 h x y).
Proof. exact (MK_COMB (@lem1542745 h x y) (@lem1542720 h x y)). Qed.
Lemma lem1542747 (h : real) (x : real) (y : real) : (term77 h x y) = (term112 h x y).
Proof. exact (TRANS (@lem1542697 h x y) (@lem1542746 h x y)). Qed.
Lemma lem1542748 (h : real) (x : real) (y : real) : (term87 h x y) = (term113 h x y).
Proof. exact (MK_COMB (@lem1542694 h x y) (@lem1542747 h x y)). Qed.
Lemma lem1542749 (h : real) (x : real) (y : real) : (term47 h x y) = (term113 h x y).
Proof. exact (TRANS (@lem1542627 h x y) (@lem1542748 h x y)). Qed.
Lemma lem1542750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542751 (h : real) (x : real) (y : real) : (term58 h x y) = (term114 h x y).
Proof. exact (MK_COMB (@lem1542750) (@lem1542749 h x y)). Qed.
Lemma lem1542753 (a : real) (x : real) (r : real) : (term115 x a r) = (term116 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1542754 (x : real) (h : real) (y : real) : (term56 y x h) = (term117 x h y).
Proof. exact (@lem1542753 (term50 x h) y term46). Qed.
Lemma lem1542761 (y : real) : (term69 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1542764 (x : real) (h : real) : (term118 x h) = (term118 x h).
Proof. exact (eq_refl (term118 x h)). Qed.
Lemma lem1542765 (x : real) (h : real) (y : real) : (term119 x h y) = (term120 x h y).
Proof. exact (MK_COMB (@lem1542764 x h) (@lem1542761 y)). Qed.
Lemma lem1542766 (y : real) (x : real) (h : real) : (term120 x h y) = (term121 y x h).
Proof. exact (@lem1483488 y (term50 x h)). Qed.
Lemma lem1542767 (y : real) (x : real) (h : real) : (term119 x h y) = (term121 y x h).
Proof. exact (TRANS (@lem1542765 x h y) (@lem1542766 y x h)). Qed.
Lemma lem1542768 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1542769 (y : real) (x : real) (h : real) : (term122 x h y) = (term123 y x h).
Proof. exact (MK_COMB (@lem1542768) (@lem1542767 y x h)). Qed.
Lemma lem1542770 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542771 (y : real) (x : real) (h : real) : (term124 x h y) = (term125 y x h).
Proof. exact (MK_COMB (@lem1542769 y x h) (@lem1542770)). Qed.
Lemma lem1542784 (y : real) (x : real) (h : real) : (term126 x h y) = (term127 y x h).
Proof. exact (@lem1483488 (term80 y) (term50 x h)). Qed.
Lemma lem1542785 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1542786 (y : real) (x : real) (h : real) : (term128 x h y) = (term129 y x h).
Proof. exact (MK_COMB (@lem1542785) (@lem1542784 y x h)). Qed.
Lemma lem1542787 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542788 (y : real) (x : real) (h : real) : (term130 x h y) = (term131 y x h).
Proof. exact (MK_COMB (@lem1542786 y x h) (@lem1542787)). Qed.
Lemma lem1542789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542790 (y : real) (x : real) (h : real) : (term132 x h y) = (term133 y x h).
Proof. exact (MK_COMB (@lem1542789) (@lem1542788 y x h)). Qed.
Lemma lem1542791 (y : real) (x : real) (h : real) : (term117 x h y) = (term134 y x h).
Proof. exact (MK_COMB (@lem1542790 y x h) (@lem1542771 y x h)). Qed.
Lemma lem1542792 (y : real) (x : real) (h : real) : (term56 y x h) = (term134 y x h).
Proof. exact (TRANS (@lem1542754 x h y) (@lem1542791 y x h)). Qed.
Lemma lem1542793 (y : real) (x : real) (h : real) : (term59 y x h) = (term135 y x h).
Proof. exact (MK_COMB (@lem1542751 h x y) (@lem1542792 y x h)). Qed.
Lemma lem1542794 (y : real) (x : real) (h : real) : (term136 x h y) = (term135 y x h).
Proof. exact (eq_refl (term136 x h y)). Qed.
Lemma lem1542795 (x : real) (h : real) (y : real) : (term135 y x h) = (term136 x h y).
Proof. exact (SYM (@lem1542794 y x h)). Qed.
Lemma lem1542796 (x : real) (h : real) (y : real) : (term136 x h y) = (term137 x h y).
Proof. exact (@lem1482981 (term138 y x h) y). Qed.
Lemma lem1542797 (x : real) (h : real) (y : real) : (term135 y x h) = (term137 x h y).
Proof. exact (TRANS (@lem1542795 x h y) (@lem1542796 x h y)). Qed.
Lemma lem1542798 (y : real) (x : real) (h : real) : (term139 x h y) = (term140 y x h).
Proof. exact (eq_refl (term139 x h y)). Qed.
Lemma lem1542799 (y : real) : (term141 y) = (term141 y).
Proof. exact (eq_refl (term141 y)). Qed.
Lemma lem1542800 (y : real) (x : real) (h : real) : (term142 x h y) = (term143 y x h).
Proof. exact (MK_COMB (@lem1542799 y) (@lem1542798 y x h)). Qed.
Lemma lem1542801 (y : real) (x : real) (h : real) : (term144 x h y) = (term145 y x h).
Proof. exact (eq_refl (term144 x h y)). Qed.
Lemma lem1542802 (y : real) : (term146 y) = (term146 y).
Proof. exact (eq_refl (term146 y)). Qed.
Lemma lem1542803 (y : real) (x : real) (h : real) : (term147 x h y) = (term148 y x h).
Proof. exact (MK_COMB (@lem1542802 y) (@lem1542801 y x h)). Qed.
Lemma lem1542804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1542805 (y : real) (x : real) (h : real) : (term149 x h y) = (term150 y x h).
Proof. exact (MK_COMB (@lem1542804) (@lem1542803 y x h)). Qed.
Lemma lem1542806 (y : real) (x : real) (h : real) : (term137 x h y) = (term151 y x h).
Proof. exact (MK_COMB (@lem1542805 y x h) (@lem1542800 y x h)). Qed.
Lemma lem1542807 (y : real) (x : real) (h : real) : (term152 y x h) = (term152 y x h).
Proof. exact (eq_refl (term152 y x h)). Qed.
Lemma lem1542808 (y : real) (x : real) (h : real) : ((term135 y x h) = (term137 x h y)) = ((term135 y x h) = (term151 y x h)).
Proof. exact (MK_COMB (@lem1542807 y x h) (@lem1542806 y x h)). Qed.
Lemma lem1542809 (y : real) (x : real) (h : real) : (term135 y x h) = (term151 y x h).
Proof. exact (EQ_MP (@lem1542808 y x h) (@lem1542797 x h y)). Qed.
Lemma lem1542810 (y : real) : (term153 y) = (term154 y).
Proof. exact (@lem1483527 y term46). Qed.
Lemma lem1542816 (y : real) : (term155 y) = (term156 y).
Proof. exact (@lem1483519 y term46). Qed.
Lemma lem1542818 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1542819 : term158 = term46.
Proof. exact (@lem1542818 term159). Qed.
Lemma lem1542820 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1542821 (y : real) : (term156 y) = (term160 y).
Proof. exact (MK_COMB (@lem1542820 y) (@lem1542819)). Qed.
Lemma lem1542822 (y : real) : (term160 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1542823 (y : real) : (term156 y) = y.
Proof. exact (TRANS (@lem1542821 y) (@lem1542822 y)). Qed.
Lemma lem1542825 (y : real) : (term155 y) = y.
Proof. exact (TRANS (@lem1542816 y) (@lem1542823 y)). Qed.
Lemma lem1542826 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1542827 (y : real) : (term161 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1542826) (@lem1542825 y)). Qed.
Lemma lem1542828 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542829 (y : real) : (term154 y) = (term153 y).
Proof. exact (MK_COMB (@lem1542827 y) (@lem1542828)). Qed.
Lemma lem1542830 (y : real) : (term153 y) = (term153 y).
Proof. exact (TRANS (@lem1542810 y) (@lem1542829 y)). Qed.
Lemma lem1542831 (h : real) (x : real) (y : real) : (term162 h x y) = (term163 h x y).
Proof. exact (@lem1483525 (term164 h x y) term46). Qed.
Lemma lem1542861 (h : real) (x : real) (y : real) : (term165 h x y) = (term166 h x y).
Proof. exact (@lem1483519 (term164 h x y) term46). Qed.
Lemma lem1542863 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1542864 : term158 = term46.
Proof. exact (@lem1542863 term159). Qed.
Lemma lem1542865 (h : real) (x : real) (y : real) : (term167 h x y) = (term167 h x y).
Proof. exact (eq_refl (term167 h x y)). Qed.
Lemma lem1542866 (h : real) (x : real) (y : real) : (term166 h x y) = (term168 h x y).
Proof. exact (MK_COMB (@lem1542865 h x y) (@lem1542864)). Qed.
Lemma lem1542867 (h : real) (x : real) (y : real) : (term168 h x y) = (term164 h x y).
Proof. exact (@lem1483450 (term164 h x y)). Qed.
Lemma lem1542868 (h : real) (x : real) (y : real) : (term166 h x y) = (term164 h x y).
Proof. exact (TRANS (@lem1542866 h x y) (@lem1542867 h x y)). Qed.
Lemma lem1542870 (h : real) (x : real) (y : real) : (term165 h x y) = (term164 h x y).
Proof. exact (TRANS (@lem1542861 h x y) (@lem1542868 h x y)). Qed.
Lemma lem1542871 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542872 (h : real) (x : real) (y : real) : (term169 h x y) = (term170 h x y).
Proof. exact (MK_COMB (@lem1542871) (@lem1542870 h x y)). Qed.
Lemma lem1542873 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542874 (h : real) (x : real) (y : real) : (term163 h x y) = (term162 h x y).
Proof. exact (MK_COMB (@lem1542872 h x y) (@lem1542873)). Qed.
Lemma lem1542875 (h : real) (x : real) (y : real) : (term162 h x y) = (term162 h x y).
Proof. exact (TRANS (@lem1542831 h x y) (@lem1542874 h x y)). Qed.
Lemma lem1542876 (h : real) (x : real) (y : real) : (term171 h x y) = (term172 h x y).
Proof. exact (@lem1483525 (term173 h x y) term46). Qed.
Lemma lem1542900 (h : real) (x : real) (y : real) : (term174 h x y) = (term175 h x y).
Proof. exact (@lem1483519 (term173 h x y) term46). Qed.
Lemma lem1542902 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1542903 : term158 = term46.
Proof. exact (@lem1542902 term159). Qed.
Lemma lem1542904 (h : real) (x : real) (y : real) : (term176 h x y) = (term176 h x y).
Proof. exact (eq_refl (term176 h x y)). Qed.
Lemma lem1542905 (h : real) (x : real) (y : real) : (term175 h x y) = (term177 h x y).
Proof. exact (MK_COMB (@lem1542904 h x y) (@lem1542903)). Qed.
Lemma lem1542906 (h : real) (x : real) (y : real) : (term177 h x y) = (term173 h x y).
Proof. exact (@lem1483450 (term173 h x y)). Qed.
Lemma lem1542907 (h : real) (x : real) (y : real) : (term175 h x y) = (term173 h x y).
Proof. exact (TRANS (@lem1542905 h x y) (@lem1542906 h x y)). Qed.
Lemma lem1542909 (h : real) (x : real) (y : real) : (term174 h x y) = (term173 h x y).
Proof. exact (TRANS (@lem1542900 h x y) (@lem1542907 h x y)). Qed.
Lemma lem1542910 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542911 (h : real) (x : real) (y : real) : (term178 h x y) = (term179 h x y).
Proof. exact (MK_COMB (@lem1542910) (@lem1542909 h x y)). Qed.
Lemma lem1542912 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542913 (h : real) (x : real) (y : real) : (term172 h x y) = (term171 h x y).
Proof. exact (MK_COMB (@lem1542911 h x y) (@lem1542912)). Qed.
Lemma lem1542914 (h : real) (x : real) (y : real) : (term171 h x y) = (term171 h x y).
Proof. exact (TRANS (@lem1542876 h x y) (@lem1542913 h x y)). Qed.
Lemma lem1542915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542916 (h : real) (x : real) (y : real) : (term180 h x y) = (term180 h x y).
Proof. exact (MK_COMB (@lem1542915) (@lem1542875 h x y)). Qed.
Lemma lem1542917 (h : real) (x : real) (y : real) : (term181 h x y) = (term181 h x y).
Proof. exact (MK_COMB (@lem1542916 h x y) (@lem1542914 h x y)). Qed.
Lemma lem1542918 (h : real) (x : real) (y : real) : (term182 h x y) = (term183 h x y).
Proof. exact (@lem1483525 (term184 h x y) term46). Qed.
Lemma lem1542942 (h : real) (x : real) (y : real) : (term185 h x y) = (term186 h x y).
Proof. exact (@lem1483519 (term184 h x y) term46). Qed.
Lemma lem1542944 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1542945 : term158 = term46.
Proof. exact (@lem1542944 term159). Qed.
Lemma lem1542946 (h : real) (x : real) (y : real) : (term187 h x y) = (term187 h x y).
Proof. exact (eq_refl (term187 h x y)). Qed.
Lemma lem1542947 (h : real) (x : real) (y : real) : (term186 h x y) = (term188 h x y).
Proof. exact (MK_COMB (@lem1542946 h x y) (@lem1542945)). Qed.
Lemma lem1542948 (h : real) (x : real) (y : real) : (term188 h x y) = (term184 h x y).
Proof. exact (@lem1483450 (term184 h x y)). Qed.
Lemma lem1542949 (h : real) (x : real) (y : real) : (term186 h x y) = (term184 h x y).
Proof. exact (TRANS (@lem1542947 h x y) (@lem1542948 h x y)). Qed.
Lemma lem1542951 (h : real) (x : real) (y : real) : (term185 h x y) = (term184 h x y).
Proof. exact (TRANS (@lem1542942 h x y) (@lem1542949 h x y)). Qed.
Lemma lem1542952 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542953 (h : real) (x : real) (y : real) : (term189 h x y) = (term190 h x y).
Proof. exact (MK_COMB (@lem1542952) (@lem1542951 h x y)). Qed.
Lemma lem1542954 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542955 (h : real) (x : real) (y : real) : (term183 h x y) = (term182 h x y).
Proof. exact (MK_COMB (@lem1542953 h x y) (@lem1542954)). Qed.
Lemma lem1542956 (h : real) (x : real) (y : real) : (term182 h x y) = (term182 h x y).
Proof. exact (TRANS (@lem1542918 h x y) (@lem1542955 h x y)). Qed.
Lemma lem1542957 (h : real) (x : real) (y : real) : (term191 h x y) = (term192 h x y).
Proof. exact (@lem1483525 (term193 h x y) term46). Qed.
Lemma lem1542975 (h : real) (x : real) (y : real) : (term194 h x y) = (term195 h x y).
Proof. exact (@lem1483519 (term193 h x y) term46). Qed.
Lemma lem1542977 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1542978 : term158 = term46.
Proof. exact (@lem1542977 term159). Qed.
Lemma lem1542979 (h : real) (x : real) (y : real) : (term196 h x y) = (term196 h x y).
Proof. exact (eq_refl (term196 h x y)). Qed.
Lemma lem1542980 (h : real) (x : real) (y : real) : (term195 h x y) = (term197 h x y).
Proof. exact (MK_COMB (@lem1542979 h x y) (@lem1542978)). Qed.
Lemma lem1542981 (h : real) (x : real) (y : real) : (term197 h x y) = (term193 h x y).
Proof. exact (@lem1483450 (term193 h x y)). Qed.
Lemma lem1542982 (h : real) (x : real) (y : real) : (term195 h x y) = (term193 h x y).
Proof. exact (TRANS (@lem1542980 h x y) (@lem1542981 h x y)). Qed.
Lemma lem1542984 (h : real) (x : real) (y : real) : (term194 h x y) = (term193 h x y).
Proof. exact (TRANS (@lem1542975 h x y) (@lem1542982 h x y)). Qed.
Lemma lem1542985 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1542986 (h : real) (x : real) (y : real) : (term198 h x y) = (term199 h x y).
Proof. exact (MK_COMB (@lem1542985) (@lem1542984 h x y)). Qed.
Lemma lem1542987 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1542988 (h : real) (x : real) (y : real) : (term192 h x y) = (term191 h x y).
Proof. exact (MK_COMB (@lem1542986 h x y) (@lem1542987)). Qed.
Lemma lem1542989 (h : real) (x : real) (y : real) : (term191 h x y) = (term191 h x y).
Proof. exact (TRANS (@lem1542957 h x y) (@lem1542988 h x y)). Qed.
Lemma lem1542990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542991 (h : real) (x : real) (y : real) : (term200 h x y) = (term200 h x y).
Proof. exact (MK_COMB (@lem1542990) (@lem1542956 h x y)). Qed.
Lemma lem1542992 (h : real) (x : real) (y : real) : (term201 h x y) = (term201 h x y).
Proof. exact (MK_COMB (@lem1542991 h x y) (@lem1542989 h x y)). Qed.
Lemma lem1542993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1542994 (h : real) (x : real) (y : real) : (term202 h x y) = (term202 h x y).
Proof. exact (MK_COMB (@lem1542993) (@lem1542917 h x y)). Qed.
Lemma lem1542995 (h : real) (x : real) (y : real) : (term203 h x y) = (term203 h x y).
Proof. exact (MK_COMB (@lem1542994 h x y) (@lem1542992 h x y)). Qed.
Lemma lem1542996 (y : real) (x : real) (h : real) : (term131 y x h) = (term204 y x h).
Proof. exact (@lem1483527 (term127 y x h) term46). Qed.
Lemma lem1543014 (y : real) (x : real) (h : real) : (term205 y x h) = (term206 y x h).
Proof. exact (@lem1483519 (term127 y x h) term46). Qed.
Lemma lem1543016 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543017 : term158 = term46.
Proof. exact (@lem1543016 term159). Qed.
Lemma lem1543018 (y : real) (x : real) (h : real) : (term207 y x h) = (term207 y x h).
Proof. exact (eq_refl (term207 y x h)). Qed.
Lemma lem1543019 (y : real) (x : real) (h : real) : (term206 y x h) = (term208 y x h).
Proof. exact (MK_COMB (@lem1543018 y x h) (@lem1543017)). Qed.
Lemma lem1543020 (y : real) (x : real) (h : real) : (term208 y x h) = (term127 y x h).
Proof. exact (@lem1483450 (term127 y x h)). Qed.
Lemma lem1543021 (y : real) (x : real) (h : real) : (term206 y x h) = (term127 y x h).
Proof. exact (TRANS (@lem1543019 y x h) (@lem1543020 y x h)). Qed.
Lemma lem1543023 (y : real) (x : real) (h : real) : (term205 y x h) = (term127 y x h).
Proof. exact (TRANS (@lem1543014 y x h) (@lem1543021 y x h)). Qed.
Lemma lem1543024 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543025 (y : real) (x : real) (h : real) : (term209 y x h) = (term129 y x h).
Proof. exact (MK_COMB (@lem1543024) (@lem1543023 y x h)). Qed.
Lemma lem1543026 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543027 (y : real) (x : real) (h : real) : (term204 y x h) = (term131 y x h).
Proof. exact (MK_COMB (@lem1543025 y x h) (@lem1543026)). Qed.
Lemma lem1543028 (y : real) (x : real) (h : real) : (term131 y x h) = (term131 y x h).
Proof. exact (TRANS (@lem1542996 y x h) (@lem1543027 y x h)). Qed.
Lemma lem1543029 (y : real) (x : real) (h : real) : (term125 y x h) = (term210 y x h).
Proof. exact (@lem1483527 (term121 y x h) term46). Qed.
Lemma lem1543041 (y : real) (x : real) (h : real) : (term211 y x h) = (term212 y x h).
Proof. exact (@lem1483519 (term121 y x h) term46). Qed.
Lemma lem1543043 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543044 : term158 = term46.
Proof. exact (@lem1543043 term159). Qed.
Lemma lem1543045 (y : real) (x : real) (h : real) : (term213 y x h) = (term213 y x h).
Proof. exact (eq_refl (term213 y x h)). Qed.
Lemma lem1543046 (y : real) (x : real) (h : real) : (term212 y x h) = (term214 y x h).
Proof. exact (MK_COMB (@lem1543045 y x h) (@lem1543044)). Qed.
Lemma lem1543047 (y : real) (x : real) (h : real) : (term214 y x h) = (term121 y x h).
Proof. exact (@lem1483450 (term121 y x h)). Qed.
Lemma lem1543048 (y : real) (x : real) (h : real) : (term212 y x h) = (term121 y x h).
Proof. exact (TRANS (@lem1543046 y x h) (@lem1543047 y x h)). Qed.
Lemma lem1543050 (y : real) (x : real) (h : real) : (term211 y x h) = (term121 y x h).
Proof. exact (TRANS (@lem1543041 y x h) (@lem1543048 y x h)). Qed.
Lemma lem1543051 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543052 (y : real) (x : real) (h : real) : (term215 y x h) = (term123 y x h).
Proof. exact (MK_COMB (@lem1543051) (@lem1543050 y x h)). Qed.
Lemma lem1543053 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543054 (y : real) (x : real) (h : real) : (term210 y x h) = (term125 y x h).
Proof. exact (MK_COMB (@lem1543052 y x h) (@lem1543053)). Qed.
Lemma lem1543055 (y : real) (x : real) (h : real) : (term125 y x h) = (term125 y x h).
Proof. exact (TRANS (@lem1543029 y x h) (@lem1543054 y x h)). Qed.
Lemma lem1543056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543057 (y : real) (x : real) (h : real) : (term133 y x h) = (term133 y x h).
Proof. exact (MK_COMB (@lem1543056) (@lem1543028 y x h)). Qed.
Lemma lem1543058 (y : real) (x : real) (h : real) : (term134 y x h) = (term134 y x h).
Proof. exact (MK_COMB (@lem1543057 y x h) (@lem1543055 y x h)). Qed.
Lemma lem1543059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543060 (h : real) (x : real) (y : real) : (term216 h x y) = (term216 h x y).
Proof. exact (MK_COMB (@lem1543059) (@lem1542995 h x y)). Qed.
Lemma lem1543061 (y : real) (x : real) (h : real) : (term145 y x h) = (term145 y x h).
Proof. exact (MK_COMB (@lem1543060 h x y) (@lem1543058 y x h)). Qed.
Lemma lem1543062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543063 (y : real) : (term146 y) = (term146 y).
Proof. exact (MK_COMB (@lem1543062) (@lem1542830 y)). Qed.
Lemma lem1543064 (y : real) (x : real) (h : real) : (term148 y x h) = (term148 y x h).
Proof. exact (MK_COMB (@lem1543063 y) (@lem1543061 y x h)). Qed.
Lemma lem1543065 (y : real) : (term217 y) = (term218 y).
Proof. exact (@lem1483525 term46 y). Qed.
Lemma lem1543071 (y : real) : (term219 y) = (term220 y).
Proof. exact (@lem1483519 term46 y). Qed.
Lemma lem1543076 (y : real) : (term220 y) = (term80 y).
Proof. exact (@lem1483448 (term80 y)). Qed.
Lemma lem1543078 (y : real) : (term219 y) = (term80 y).
Proof. exact (TRANS (@lem1543071 y) (@lem1543076 y)). Qed.
Lemma lem1543079 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543080 (y : real) : (term221 y) = (term222 y).
Proof. exact (MK_COMB (@lem1543079) (@lem1543078 y)). Qed.
Lemma lem1543081 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543082 (y : real) : (term218 y) = (term223 y).
Proof. exact (MK_COMB (@lem1543080 y) (@lem1543081)). Qed.
Lemma lem1543083 (y : real) : (term217 y) = (term223 y).
Proof. exact (TRANS (@lem1543065 y) (@lem1543082 y)). Qed.
Lemma lem1543084 (h : real) (x : real) (y : real) : (term224 h x y) = (term225 h x y).
Proof. exact (@lem1483525 (term226 h x y) term46). Qed.
Lemma lem1543085 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543092 (y : real) : (real_neg y) = (term80 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1543101 (x : real) : (term94 x) = (term94 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem1543104 (x : real) (y : real) : (term227 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1543101 x) (@lem1543092 y)). Qed.
Lemma lem1543113 (h : real) : (term94 h) = (term94 h).
Proof. exact (eq_refl (term94 h)). Qed.
Lemma lem1543116 (h : real) (x : real) (y : real) : (term226 h x y) = (term229 h x y).
Proof. exact (MK_COMB (@lem1543113 h) (@lem1543104 x y)). Qed.
Lemma lem1543117 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543118 (h : real) (x : real) (y : real) : (term230 h x y) = (term231 h x y).
Proof. exact (MK_COMB (@lem1543117) (@lem1543116 h x y)). Qed.
Lemma lem1543119 (h : real) (x : real) (y : real) : (term232 h x y) = (term233 h x y).
Proof. exact (MK_COMB (@lem1543118 h x y) (@lem1543085)). Qed.
Lemma lem1543120 (h : real) (x : real) (y : real) : (term233 h x y) = (term234 h x y).
Proof. exact (@lem1483519 (term229 h x y) term46). Qed.
Lemma lem1543122 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543123 : term158 = term46.
Proof. exact (@lem1543122 term159). Qed.
Lemma lem1543124 (h : real) (x : real) (y : real) : (term235 h x y) = (term235 h x y).
Proof. exact (eq_refl (term235 h x y)). Qed.
Lemma lem1543125 (h : real) (x : real) (y : real) : (term234 h x y) = (term236 h x y).
Proof. exact (MK_COMB (@lem1543124 h x y) (@lem1543123)). Qed.
Lemma lem1543126 (h : real) (x : real) (y : real) : (term236 h x y) = (term229 h x y).
Proof. exact (@lem1483450 (term229 h x y)). Qed.
Lemma lem1543127 (h : real) (x : real) (y : real) : (term234 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543125 h x y) (@lem1543126 h x y)). Qed.
Lemma lem1543128 (h : real) (x : real) (y : real) : (term233 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543120 h x y) (@lem1543127 h x y)). Qed.
Lemma lem1543129 (h : real) (x : real) (y : real) : (term232 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543119 h x y) (@lem1543128 h x y)). Qed.
Lemma lem1543130 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543131 (h : real) (x : real) (y : real) : (term237 h x y) = (term238 h x y).
Proof. exact (MK_COMB (@lem1543130) (@lem1543129 h x y)). Qed.
Lemma lem1543132 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543133 (h : real) (x : real) (y : real) : (term225 h x y) = (term239 h x y).
Proof. exact (MK_COMB (@lem1543131 h x y) (@lem1543132)). Qed.
Lemma lem1543134 (h : real) (x : real) (y : real) : (term224 h x y) = (term239 h x y).
Proof. exact (TRANS (@lem1543084 h x y) (@lem1543133 h x y)). Qed.
Lemma lem1543135 (h : real) (x : real) (y : real) : (term240 h x y) = (term241 h x y).
Proof. exact (@lem1483525 (term242 h x y) term46). Qed.
Lemma lem1543136 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543143 (y : real) : (real_neg y) = (term80 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1543146 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1543149 (x : real) (y : real) : (term243 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1543146 x) (@lem1543143 y)). Qed.
Lemma lem1543158 (h : real) : (term94 h) = (term94 h).
Proof. exact (eq_refl (term94 h)). Qed.
Lemma lem1543161 (h : real) (x : real) (y : real) : (term242 h x y) = (term245 h x y).
Proof. exact (MK_COMB (@lem1543158 h) (@lem1543149 x y)). Qed.
Lemma lem1543162 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543163 (h : real) (x : real) (y : real) : (term246 h x y) = (term247 h x y).
Proof. exact (MK_COMB (@lem1543162) (@lem1543161 h x y)). Qed.
Lemma lem1543164 (h : real) (x : real) (y : real) : (term248 h x y) = (term249 h x y).
Proof. exact (MK_COMB (@lem1543163 h x y) (@lem1543136)). Qed.
Lemma lem1543165 (h : real) (x : real) (y : real) : (term249 h x y) = (term250 h x y).
Proof. exact (@lem1483519 (term245 h x y) term46). Qed.
Lemma lem1543167 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543168 : term158 = term46.
Proof. exact (@lem1543167 term159). Qed.
Lemma lem1543169 (h : real) (x : real) (y : real) : (term251 h x y) = (term251 h x y).
Proof. exact (eq_refl (term251 h x y)). Qed.
Lemma lem1543170 (h : real) (x : real) (y : real) : (term250 h x y) = (term252 h x y).
Proof. exact (MK_COMB (@lem1543169 h x y) (@lem1543168)). Qed.
Lemma lem1543171 (h : real) (x : real) (y : real) : (term252 h x y) = (term245 h x y).
Proof. exact (@lem1483450 (term245 h x y)). Qed.
Lemma lem1543172 (h : real) (x : real) (y : real) : (term250 h x y) = (term245 h x y).
Proof. exact (TRANS (@lem1543170 h x y) (@lem1543171 h x y)). Qed.
Lemma lem1543173 (h : real) (x : real) (y : real) : (term249 h x y) = (term245 h x y).
Proof. exact (TRANS (@lem1543165 h x y) (@lem1543172 h x y)). Qed.
Lemma lem1543174 (h : real) (x : real) (y : real) : (term248 h x y) = (term245 h x y).
Proof. exact (TRANS (@lem1543164 h x y) (@lem1543173 h x y)). Qed.
Lemma lem1543175 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543176 (h : real) (x : real) (y : real) : (term253 h x y) = (term254 h x y).
Proof. exact (MK_COMB (@lem1543175) (@lem1543174 h x y)). Qed.
Lemma lem1543177 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543178 (h : real) (x : real) (y : real) : (term241 h x y) = (term255 h x y).
Proof. exact (MK_COMB (@lem1543176 h x y) (@lem1543177)). Qed.
Lemma lem1543179 (h : real) (x : real) (y : real) : (term240 h x y) = (term255 h x y).
Proof. exact (TRANS (@lem1543135 h x y) (@lem1543178 h x y)). Qed.
Lemma lem1543180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543181 (h : real) (x : real) (y : real) : (term256 h x y) = (term257 h x y).
Proof. exact (MK_COMB (@lem1543180) (@lem1543134 h x y)). Qed.
Lemma lem1543182 (h : real) (x : real) (y : real) : (term258 h x y) = (term259 h x y).
Proof. exact (MK_COMB (@lem1543181 h x y) (@lem1543179 h x y)). Qed.
Lemma lem1543183 (h : real) (x : real) (y : real) : (term260 h x y) = (term261 h x y).
Proof. exact (@lem1483525 (term262 h x y) term46). Qed.
Lemma lem1543184 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543191 (y : real) : (real_neg y) = (term80 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1543200 (x : real) : (term94 x) = (term94 x).
Proof. exact (eq_refl (term94 x)). Qed.
Lemma lem1543203 (x : real) (y : real) : (term227 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1543200 x) (@lem1543191 y)). Qed.
Lemma lem1543206 (h : real) : (real_add h) = (real_add h).
Proof. exact (eq_refl (real_add h)). Qed.
Lemma lem1543209 (h : real) (x : real) (y : real) : (term262 h x y) = (term263 h x y).
Proof. exact (MK_COMB (@lem1543206 h) (@lem1543203 x y)). Qed.
Lemma lem1543210 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543211 (h : real) (x : real) (y : real) : (term264 h x y) = (term265 h x y).
Proof. exact (MK_COMB (@lem1543210) (@lem1543209 h x y)). Qed.
Lemma lem1543212 (h : real) (x : real) (y : real) : (term266 h x y) = (term267 h x y).
Proof. exact (MK_COMB (@lem1543211 h x y) (@lem1543184)). Qed.
Lemma lem1543213 (h : real) (x : real) (y : real) : (term267 h x y) = (term268 h x y).
Proof. exact (@lem1483519 (term263 h x y) term46). Qed.
Lemma lem1543215 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543216 : term158 = term46.
Proof. exact (@lem1543215 term159). Qed.
Lemma lem1543217 (h : real) (x : real) (y : real) : (term269 h x y) = (term269 h x y).
Proof. exact (eq_refl (term269 h x y)). Qed.
Lemma lem1543218 (h : real) (x : real) (y : real) : (term268 h x y) = (term270 h x y).
Proof. exact (MK_COMB (@lem1543217 h x y) (@lem1543216)). Qed.
Lemma lem1543219 (h : real) (x : real) (y : real) : (term270 h x y) = (term263 h x y).
Proof. exact (@lem1483450 (term263 h x y)). Qed.
Lemma lem1543220 (h : real) (x : real) (y : real) : (term268 h x y) = (term263 h x y).
Proof. exact (TRANS (@lem1543218 h x y) (@lem1543219 h x y)). Qed.
Lemma lem1543221 (h : real) (x : real) (y : real) : (term267 h x y) = (term263 h x y).
Proof. exact (TRANS (@lem1543213 h x y) (@lem1543220 h x y)). Qed.
Lemma lem1543222 (h : real) (x : real) (y : real) : (term266 h x y) = (term263 h x y).
Proof. exact (TRANS (@lem1543212 h x y) (@lem1543221 h x y)). Qed.
Lemma lem1543223 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543224 (h : real) (x : real) (y : real) : (term271 h x y) = (term272 h x y).
Proof. exact (MK_COMB (@lem1543223) (@lem1543222 h x y)). Qed.
Lemma lem1543225 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543226 (h : real) (x : real) (y : real) : (term261 h x y) = (term273 h x y).
Proof. exact (MK_COMB (@lem1543224 h x y) (@lem1543225)). Qed.
Lemma lem1543227 (h : real) (x : real) (y : real) : (term260 h x y) = (term273 h x y).
Proof. exact (TRANS (@lem1543183 h x y) (@lem1543226 h x y)). Qed.
Lemma lem1543228 (h : real) (x : real) (y : real) : (term274 h x y) = (term275 h x y).
Proof. exact (@lem1483525 (term276 h x y) term46). Qed.
Lemma lem1543229 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543236 (y : real) : (real_neg y) = (term80 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1543239 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1543242 (x : real) (y : real) : (term243 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1543239 x) (@lem1543236 y)). Qed.
Lemma lem1543245 (h : real) : (real_add h) = (real_add h).
Proof. exact (eq_refl (real_add h)). Qed.
Lemma lem1543248 (h : real) (x : real) (y : real) : (term276 h x y) = (term277 h x y).
Proof. exact (MK_COMB (@lem1543245 h) (@lem1543242 x y)). Qed.
Lemma lem1543249 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543250 (h : real) (x : real) (y : real) : (term278 h x y) = (term279 h x y).
Proof. exact (MK_COMB (@lem1543249) (@lem1543248 h x y)). Qed.
Lemma lem1543251 (h : real) (x : real) (y : real) : (term280 h x y) = (term281 h x y).
Proof. exact (MK_COMB (@lem1543250 h x y) (@lem1543229)). Qed.
Lemma lem1543252 (h : real) (x : real) (y : real) : (term281 h x y) = (term282 h x y).
Proof. exact (@lem1483519 (term277 h x y) term46). Qed.
Lemma lem1543254 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543255 : term158 = term46.
Proof. exact (@lem1543254 term159). Qed.
Lemma lem1543256 (h : real) (x : real) (y : real) : (term283 h x y) = (term283 h x y).
Proof. exact (eq_refl (term283 h x y)). Qed.
Lemma lem1543257 (h : real) (x : real) (y : real) : (term282 h x y) = (term284 h x y).
Proof. exact (MK_COMB (@lem1543256 h x y) (@lem1543255)). Qed.
Lemma lem1543258 (h : real) (x : real) (y : real) : (term284 h x y) = (term277 h x y).
Proof. exact (@lem1483450 (term277 h x y)). Qed.
Lemma lem1543259 (h : real) (x : real) (y : real) : (term282 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543257 h x y) (@lem1543258 h x y)). Qed.
Lemma lem1543260 (h : real) (x : real) (y : real) : (term281 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543252 h x y) (@lem1543259 h x y)). Qed.
Lemma lem1543261 (h : real) (x : real) (y : real) : (term280 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543251 h x y) (@lem1543260 h x y)). Qed.
Lemma lem1543262 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543263 (h : real) (x : real) (y : real) : (term285 h x y) = (term286 h x y).
Proof. exact (MK_COMB (@lem1543262) (@lem1543261 h x y)). Qed.
Lemma lem1543264 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543265 (h : real) (x : real) (y : real) : (term275 h x y) = (term287 h x y).
Proof. exact (MK_COMB (@lem1543263 h x y) (@lem1543264)). Qed.
Lemma lem1543266 (h : real) (x : real) (y : real) : (term274 h x y) = (term287 h x y).
Proof. exact (TRANS (@lem1543228 h x y) (@lem1543265 h x y)). Qed.
Lemma lem1543267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543268 (h : real) (x : real) (y : real) : (term288 h x y) = (term289 h x y).
Proof. exact (MK_COMB (@lem1543267) (@lem1543227 h x y)). Qed.
Lemma lem1543269 (h : real) (x : real) (y : real) : (term290 h x y) = (term291 h x y).
Proof. exact (MK_COMB (@lem1543268 h x y) (@lem1543266 h x y)). Qed.
Lemma lem1543270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543271 (h : real) (x : real) (y : real) : (term292 h x y) = (term293 h x y).
Proof. exact (MK_COMB (@lem1543270) (@lem1543182 h x y)). Qed.
Lemma lem1543272 (h : real) (x : real) (y : real) : (term294 h x y) = (term295 h x y).
Proof. exact (MK_COMB (@lem1543271 h x y) (@lem1543269 h x y)). Qed.
Lemma lem1543273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543274 (y : real) (x : real) (h : real) : (term133 y x h) = (term133 y x h).
Proof. exact (MK_COMB (@lem1543273) (@lem1543028 y x h)). Qed.
Lemma lem1543275 (y : real) (x : real) (h : real) : (term134 y x h) = (term134 y x h).
Proof. exact (MK_COMB (@lem1543274 y x h) (@lem1543055 y x h)). Qed.
Lemma lem1543276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543277 (h : real) (x : real) (y : real) : (term296 h x y) = (term297 h x y).
Proof. exact (MK_COMB (@lem1543276) (@lem1543272 h x y)). Qed.
Lemma lem1543278 (y : real) (x : real) (h : real) : (term140 y x h) = (term298 y x h).
Proof. exact (MK_COMB (@lem1543277 h x y) (@lem1543275 y x h)). Qed.
Lemma lem1543279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543280 (y : real) : (term141 y) = (term299 y).
Proof. exact (MK_COMB (@lem1543279) (@lem1543083 y)). Qed.
Lemma lem1543281 (y : real) (x : real) (h : real) : (term143 y x h) = (term300 y x h).
Proof. exact (MK_COMB (@lem1543280 y) (@lem1543278 y x h)). Qed.
Lemma lem1543282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1543283 (y : real) (x : real) (h : real) : (term150 y x h) = (term150 y x h).
Proof. exact (MK_COMB (@lem1543282) (@lem1543064 y x h)). Qed.
Lemma lem1543284 (y : real) (x : real) (h : real) : (term151 y x h) = (term301 y x h).
Proof. exact (MK_COMB (@lem1543283 y x h) (@lem1543281 y x h)). Qed.
Lemma lem1543285 (y : real) (x : real) (h : real) : (term135 y x h) = (term301 y x h).
Proof. exact (TRANS (@lem1542809 y x h) (@lem1543284 y x h)). Qed.
Lemma lem1543287 (y : real) (x : real) (h : real) : (term302 y x h) = (term300 y x h).
Proof. exact (eq_refl (term302 y x h)). Qed.
Lemma lem1543288 (y : real) (x : real) (h : real) : (term300 y x h) = (term302 y x h).
Proof. exact (SYM (@lem1543287 y x h)). Qed.
Lemma lem1543289 (y : real) (x : real) (h : real) : (term302 y x h) = (term303 y x h).
Proof. exact (@lem1482981 (term304 h x y) (real_add x h)). Qed.
Lemma lem1543290 (y : real) (x : real) (h : real) : (term300 y x h) = (term303 y x h).
Proof. exact (TRANS (@lem1543288 y x h) (@lem1543289 y x h)). Qed.
Lemma lem1543291 (y : real) (x : real) (h : real) : (term305 y x h) = (term306 y x h).
Proof. exact (eq_refl (term305 y x h)). Qed.
Lemma lem1543292 (x : real) (h : real) : (term307 x h) = (term307 x h).
Proof. exact (eq_refl (term307 x h)). Qed.
Lemma lem1543293 (y : real) (x : real) (h : real) : (term308 y x h) = (term309 y x h).
Proof. exact (MK_COMB (@lem1543292 x h) (@lem1543291 y x h)). Qed.
Lemma lem1543294 (y : real) (x : real) (h : real) : (term310 y x h) = (term311 y x h).
Proof. exact (eq_refl (term310 y x h)). Qed.
Lemma lem1543295 (x : real) (h : real) : (term312 x h) = (term312 x h).
Proof. exact (eq_refl (term312 x h)). Qed.
Lemma lem1543296 (y : real) (x : real) (h : real) : (term313 y x h) = (term314 y x h).
Proof. exact (MK_COMB (@lem1543295 x h) (@lem1543294 y x h)). Qed.
Lemma lem1543297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1543298 (y : real) (x : real) (h : real) : (term315 y x h) = (term316 y x h).
Proof. exact (MK_COMB (@lem1543297) (@lem1543296 y x h)). Qed.
Lemma lem1543299 (y : real) (x : real) (h : real) : (term303 y x h) = (term317 y x h).
Proof. exact (MK_COMB (@lem1543298 y x h) (@lem1543293 y x h)). Qed.
Lemma lem1543300 (y : real) (x : real) (h : real) : (term318 y x h) = (term318 y x h).
Proof. exact (eq_refl (term318 y x h)). Qed.
Lemma lem1543301 (y : real) (x : real) (h : real) : ((term300 y x h) = (term303 y x h)) = ((term300 y x h) = (term317 y x h)).
Proof. exact (MK_COMB (@lem1543300 y x h) (@lem1543299 y x h)). Qed.
Lemma lem1543302 (y : real) (x : real) (h : real) : (term300 y x h) = (term317 y x h).
Proof. exact (EQ_MP (@lem1543301 y x h) (@lem1543290 y x h)). Qed.
Lemma lem1543303 (x : real) (h : real) : (term319 x h) = (term320 x h).
Proof. exact (@lem1483527 (real_add x h) term46). Qed.
Lemma lem1543304 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543311 (h : real) (x : real) : (real_add x h) = (real_add h x).
Proof. exact (@lem1483488 h x). Qed.
Lemma lem1543312 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543313 (h : real) (x : real) : (term321 x h) = (term321 h x).
Proof. exact (MK_COMB (@lem1543312) (@lem1543311 h x)). Qed.
Lemma lem1543314 (h : real) (x : real) : (term322 x h) = (term322 h x).
Proof. exact (MK_COMB (@lem1543313 h x) (@lem1543304)). Qed.
Lemma lem1543315 (h : real) (x : real) : (term322 h x) = (term323 h x).
Proof. exact (@lem1483519 (real_add h x) term46). Qed.
Lemma lem1543317 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543318 : term158 = term46.
Proof. exact (@lem1543317 term159). Qed.
Lemma lem1543319 (h : real) (x : real) : (term324 h x) = (term324 h x).
Proof. exact (eq_refl (term324 h x)). Qed.
Lemma lem1543320 (h : real) (x : real) : (term323 h x) = (term325 h x).
Proof. exact (MK_COMB (@lem1543319 h x) (@lem1543318)). Qed.
Lemma lem1543321 (h : real) (x : real) : (term325 h x) = (real_add h x).
Proof. exact (@lem1483450 (real_add h x)). Qed.
Lemma lem1543322 (h : real) (x : real) : (term323 h x) = (real_add h x).
Proof. exact (TRANS (@lem1543320 h x) (@lem1543321 h x)). Qed.
Lemma lem1543323 (h : real) (x : real) : (term322 h x) = (real_add h x).
Proof. exact (TRANS (@lem1543315 h x) (@lem1543322 h x)). Qed.
Lemma lem1543324 (h : real) (x : real) : (term322 x h) = (real_add h x).
Proof. exact (TRANS (@lem1543314 h x) (@lem1543323 h x)). Qed.
Lemma lem1543325 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543326 (h : real) (x : real) : (term326 x h) = (term327 h x).
Proof. exact (MK_COMB (@lem1543325) (@lem1543324 h x)). Qed.
Lemma lem1543327 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543328 (h : real) (x : real) : (term320 x h) = (term319 h x).
Proof. exact (MK_COMB (@lem1543326 h x) (@lem1543327)). Qed.
Lemma lem1543329 (h : real) (x : real) : (term319 x h) = (term319 h x).
Proof. exact (TRANS (@lem1543303 x h) (@lem1543328 h x)). Qed.
Lemma lem1543330 (y : real) : (term223 y) = (term328 y).
Proof. exact (@lem1483525 (term80 y) term46). Qed.
Lemma lem1543342 (y : real) : (term329 y) = (term330 y).
Proof. exact (@lem1483519 (term80 y) term46). Qed.
Lemma lem1543344 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543345 : term158 = term46.
Proof. exact (@lem1543344 term159). Qed.
Lemma lem1543346 (y : real) : (term94 y) = (term94 y).
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1543347 (y : real) : (term330 y) = (term331 y).
Proof. exact (MK_COMB (@lem1543346 y) (@lem1543345)). Qed.
Lemma lem1543348 (y : real) : (term331 y) = (term80 y).
Proof. exact (@lem1483450 (term80 y)). Qed.
Lemma lem1543349 (y : real) : (term330 y) = (term80 y).
Proof. exact (TRANS (@lem1543347 y) (@lem1543348 y)). Qed.
Lemma lem1543351 (y : real) : (term329 y) = (term80 y).
Proof. exact (TRANS (@lem1543342 y) (@lem1543349 y)). Qed.
Lemma lem1543352 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543353 (y : real) : (term332 y) = (term222 y).
Proof. exact (MK_COMB (@lem1543352) (@lem1543351 y)). Qed.
Lemma lem1543354 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543355 (y : real) : (term328 y) = (term223 y).
Proof. exact (MK_COMB (@lem1543353 y) (@lem1543354)). Qed.
Lemma lem1543356 (y : real) : (term223 y) = (term223 y).
Proof. exact (TRANS (@lem1543330 y) (@lem1543355 y)). Qed.
Lemma lem1543357 (h : real) (x : real) (y : real) : (term239 h x y) = (term333 h x y).
Proof. exact (@lem1483525 (term229 h x y) term46). Qed.
Lemma lem1543393 (h : real) (x : real) (y : real) : (term233 h x y) = (term234 h x y).
Proof. exact (@lem1483519 (term229 h x y) term46). Qed.
Lemma lem1543395 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543396 : term158 = term46.
Proof. exact (@lem1543395 term159). Qed.
Lemma lem1543397 (h : real) (x : real) (y : real) : (term235 h x y) = (term235 h x y).
Proof. exact (eq_refl (term235 h x y)). Qed.
Lemma lem1543398 (h : real) (x : real) (y : real) : (term234 h x y) = (term236 h x y).
Proof. exact (MK_COMB (@lem1543397 h x y) (@lem1543396)). Qed.
Lemma lem1543399 (h : real) (x : real) (y : real) : (term236 h x y) = (term229 h x y).
Proof. exact (@lem1483450 (term229 h x y)). Qed.
Lemma lem1543400 (h : real) (x : real) (y : real) : (term234 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543398 h x y) (@lem1543399 h x y)). Qed.
Lemma lem1543402 (h : real) (x : real) (y : real) : (term233 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543393 h x y) (@lem1543400 h x y)). Qed.
Lemma lem1543403 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543404 (h : real) (x : real) (y : real) : (term334 h x y) = (term238 h x y).
Proof. exact (MK_COMB (@lem1543403) (@lem1543402 h x y)). Qed.
Lemma lem1543405 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543406 (h : real) (x : real) (y : real) : (term333 h x y) = (term239 h x y).
Proof. exact (MK_COMB (@lem1543404 h x y) (@lem1543405)). Qed.
Lemma lem1543407 (h : real) (x : real) (y : real) : (term239 h x y) = (term239 h x y).
Proof. exact (TRANS (@lem1543357 h x y) (@lem1543406 h x y)). Qed.
Lemma lem1543408 (h : real) (x : real) (y : real) : (term255 h x y) = (term335 h x y).
Proof. exact (@lem1483525 (term245 h x y) term46). Qed.
Lemma lem1543438 (h : real) (x : real) (y : real) : (term249 h x y) = (term250 h x y).
Proof. exact (@lem1483519 (term245 h x y) term46). Qed.
Lemma lem1543440 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543441 : term158 = term46.
Proof. exact (@lem1543440 term159). Qed.
Lemma lem1543442 (h : real) (x : real) (y : real) : (term251 h x y) = (term251 h x y).
Proof. exact (eq_refl (term251 h x y)). Qed.
Lemma lem1543443 (h : real) (x : real) (y : real) : (term250 h x y) = (term252 h x y).
Proof. exact (MK_COMB (@lem1543442 h x y) (@lem1543441)). Qed.
Lemma lem1543444 (h : real) (x : real) (y : real) : (term252 h x y) = (term245 h x y).
Proof. exact (@lem1483450 (term245 h x y)). Qed.
Lemma lem1543445 (h : real) (x : real) (y : real) : (term250 h x y) = (term245 h x y).
Proof. exact (TRANS (@lem1543443 h x y) (@lem1543444 h x y)). Qed.
Lemma lem1543447 (h : real) (x : real) (y : real) : (term249 h x y) = (term245 h x y).
Proof. exact (TRANS (@lem1543438 h x y) (@lem1543445 h x y)). Qed.
Lemma lem1543448 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543449 (h : real) (x : real) (y : real) : (term336 h x y) = (term254 h x y).
Proof. exact (MK_COMB (@lem1543448) (@lem1543447 h x y)). Qed.
Lemma lem1543450 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543451 (h : real) (x : real) (y : real) : (term335 h x y) = (term255 h x y).
Proof. exact (MK_COMB (@lem1543449 h x y) (@lem1543450)). Qed.
Lemma lem1543452 (h : real) (x : real) (y : real) : (term255 h x y) = (term255 h x y).
Proof. exact (TRANS (@lem1543408 h x y) (@lem1543451 h x y)). Qed.
Lemma lem1543453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543454 (h : real) (x : real) (y : real) : (term257 h x y) = (term257 h x y).
Proof. exact (MK_COMB (@lem1543453) (@lem1543407 h x y)). Qed.
Lemma lem1543455 (h : real) (x : real) (y : real) : (term259 h x y) = (term259 h x y).
Proof. exact (MK_COMB (@lem1543454 h x y) (@lem1543452 h x y)). Qed.
Lemma lem1543456 (h : real) (x : real) (y : real) : (term273 h x y) = (term337 h x y).
Proof. exact (@lem1483525 (term263 h x y) term46). Qed.
Lemma lem1543486 (h : real) (x : real) (y : real) : (term267 h x y) = (term268 h x y).
Proof. exact (@lem1483519 (term263 h x y) term46). Qed.
Lemma lem1543488 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543489 : term158 = term46.
Proof. exact (@lem1543488 term159). Qed.
Lemma lem1543490 (h : real) (x : real) (y : real) : (term269 h x y) = (term269 h x y).
Proof. exact (eq_refl (term269 h x y)). Qed.
Lemma lem1543491 (h : real) (x : real) (y : real) : (term268 h x y) = (term270 h x y).
Proof. exact (MK_COMB (@lem1543490 h x y) (@lem1543489)). Qed.
Lemma lem1543492 (h : real) (x : real) (y : real) : (term270 h x y) = (term263 h x y).
Proof. exact (@lem1483450 (term263 h x y)). Qed.
Lemma lem1543493 (h : real) (x : real) (y : real) : (term268 h x y) = (term263 h x y).
Proof. exact (TRANS (@lem1543491 h x y) (@lem1543492 h x y)). Qed.
Lemma lem1543495 (h : real) (x : real) (y : real) : (term267 h x y) = (term263 h x y).
Proof. exact (TRANS (@lem1543486 h x y) (@lem1543493 h x y)). Qed.
Lemma lem1543496 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543497 (h : real) (x : real) (y : real) : (term338 h x y) = (term272 h x y).
Proof. exact (MK_COMB (@lem1543496) (@lem1543495 h x y)). Qed.
Lemma lem1543498 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543499 (h : real) (x : real) (y : real) : (term337 h x y) = (term273 h x y).
Proof. exact (MK_COMB (@lem1543497 h x y) (@lem1543498)). Qed.
Lemma lem1543500 (h : real) (x : real) (y : real) : (term273 h x y) = (term273 h x y).
Proof. exact (TRANS (@lem1543456 h x y) (@lem1543499 h x y)). Qed.
Lemma lem1543501 (h : real) (x : real) (y : real) : (term287 h x y) = (term339 h x y).
Proof. exact (@lem1483525 (term277 h x y) term46). Qed.
Lemma lem1543525 (h : real) (x : real) (y : real) : (term281 h x y) = (term282 h x y).
Proof. exact (@lem1483519 (term277 h x y) term46). Qed.
Lemma lem1543527 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543528 : term158 = term46.
Proof. exact (@lem1543527 term159). Qed.
Lemma lem1543529 (h : real) (x : real) (y : real) : (term283 h x y) = (term283 h x y).
Proof. exact (eq_refl (term283 h x y)). Qed.
Lemma lem1543530 (h : real) (x : real) (y : real) : (term282 h x y) = (term284 h x y).
Proof. exact (MK_COMB (@lem1543529 h x y) (@lem1543528)). Qed.
Lemma lem1543531 (h : real) (x : real) (y : real) : (term284 h x y) = (term277 h x y).
Proof. exact (@lem1483450 (term277 h x y)). Qed.
Lemma lem1543532 (h : real) (x : real) (y : real) : (term282 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543530 h x y) (@lem1543531 h x y)). Qed.
Lemma lem1543534 (h : real) (x : real) (y : real) : (term281 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543525 h x y) (@lem1543532 h x y)). Qed.
Lemma lem1543535 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543536 (h : real) (x : real) (y : real) : (term340 h x y) = (term286 h x y).
Proof. exact (MK_COMB (@lem1543535) (@lem1543534 h x y)). Qed.
Lemma lem1543537 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543538 (h : real) (x : real) (y : real) : (term339 h x y) = (term287 h x y).
Proof. exact (MK_COMB (@lem1543536 h x y) (@lem1543537)). Qed.
Lemma lem1543539 (h : real) (x : real) (y : real) : (term287 h x y) = (term287 h x y).
Proof. exact (TRANS (@lem1543501 h x y) (@lem1543538 h x y)). Qed.
Lemma lem1543540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543541 (h : real) (x : real) (y : real) : (term289 h x y) = (term289 h x y).
Proof. exact (MK_COMB (@lem1543540) (@lem1543500 h x y)). Qed.
Lemma lem1543542 (h : real) (x : real) (y : real) : (term291 h x y) = (term291 h x y).
Proof. exact (MK_COMB (@lem1543541 h x y) (@lem1543539 h x y)). Qed.
Lemma lem1543543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543544 (h : real) (x : real) (y : real) : (term293 h x y) = (term293 h x y).
Proof. exact (MK_COMB (@lem1543543) (@lem1543455 h x y)). Qed.
Lemma lem1543545 (h : real) (x : real) (y : real) : (term295 h x y) = (term295 h x y).
Proof. exact (MK_COMB (@lem1543544 h x y) (@lem1543542 h x y)). Qed.
Lemma lem1543546 (y : real) (x : real) (h : real) : (term341 y x h) = (term342 y x h).
Proof. exact (@lem1483527 (term173 y x h) term46). Qed.
Lemma lem1543547 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543554 (h : real) (x : real) : (real_add x h) = (real_add h x).
Proof. exact (@lem1483488 h x). Qed.
Lemma lem1543563 (y : real) : (term94 y) = (term94 y).
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1543564 (y : real) (h : real) (x : real) : (term173 y x h) = (term173 y h x).
Proof. exact (MK_COMB (@lem1543563 y) (@lem1543554 h x)). Qed.
Lemma lem1543565 (h : real) (y : real) (x : real) : (term173 y h x) = (term184 h y x).
Proof. exact (@lem1483484 h (term80 y) x). Qed.
Lemma lem1543566 (x : real) (y : real) : (term343 y x) = (term244 x y).
Proof. exact (@lem1483488 x (term80 y)). Qed.
Lemma lem1543567 (h : real) : (real_add h) = (real_add h).
Proof. exact (eq_refl (real_add h)). Qed.
Lemma lem1543568 (h : real) (x : real) (y : real) : (term184 h y x) = (term277 h x y).
Proof. exact (MK_COMB (@lem1543567 h) (@lem1543566 x y)). Qed.
Lemma lem1543569 (h : real) (x : real) (y : real) : (term173 y h x) = (term277 h x y).
Proof. exact (TRANS (@lem1543565 h y x) (@lem1543568 h x y)). Qed.
Lemma lem1543570 (h : real) (x : real) (y : real) : (term173 y x h) = (term277 h x y).
Proof. exact (TRANS (@lem1543564 y h x) (@lem1543569 h x y)). Qed.
Lemma lem1543571 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543572 (h : real) (x : real) (y : real) : (term344 y x h) = (term279 h x y).
Proof. exact (MK_COMB (@lem1543571) (@lem1543570 h x y)). Qed.
Lemma lem1543573 (h : real) (x : real) (y : real) : (term174 y x h) = (term281 h x y).
Proof. exact (MK_COMB (@lem1543572 h x y) (@lem1543547)). Qed.
Lemma lem1543574 (h : real) (x : real) (y : real) : (term281 h x y) = (term282 h x y).
Proof. exact (@lem1483519 (term277 h x y) term46). Qed.
Lemma lem1543576 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543577 : term158 = term46.
Proof. exact (@lem1543576 term159). Qed.
Lemma lem1543578 (h : real) (x : real) (y : real) : (term283 h x y) = (term283 h x y).
Proof. exact (eq_refl (term283 h x y)). Qed.
Lemma lem1543579 (h : real) (x : real) (y : real) : (term282 h x y) = (term284 h x y).
Proof. exact (MK_COMB (@lem1543578 h x y) (@lem1543577)). Qed.
Lemma lem1543580 (h : real) (x : real) (y : real) : (term284 h x y) = (term277 h x y).
Proof. exact (@lem1483450 (term277 h x y)). Qed.
Lemma lem1543581 (h : real) (x : real) (y : real) : (term282 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543579 h x y) (@lem1543580 h x y)). Qed.
Lemma lem1543582 (h : real) (x : real) (y : real) : (term281 h x y) = (term277 h x y).
Proof. exact (TRANS (@lem1543574 h x y) (@lem1543581 h x y)). Qed.
Lemma lem1543583 (h : real) (x : real) (y : real) : (term174 y x h) = (term277 h x y).
Proof. exact (TRANS (@lem1543573 h x y) (@lem1543582 h x y)). Qed.
Lemma lem1543584 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543585 (h : real) (x : real) (y : real) : (term345 y x h) = (term346 h x y).
Proof. exact (MK_COMB (@lem1543584) (@lem1543583 h x y)). Qed.
Lemma lem1543586 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543587 (h : real) (x : real) (y : real) : (term342 y x h) = (term347 h x y).
Proof. exact (MK_COMB (@lem1543585 h x y) (@lem1543586)). Qed.
Lemma lem1543588 (h : real) (x : real) (y : real) : (term341 y x h) = (term347 h x y).
Proof. exact (TRANS (@lem1543546 y x h) (@lem1543587 h x y)). Qed.
Lemma lem1543589 (y : real) (x : real) (h : real) : (term348 y x h) = (term349 y x h).
Proof. exact (@lem1483527 (term193 y x h) term46). Qed.
Lemma lem1543590 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543597 (h : real) (x : real) : (real_add x h) = (real_add h x).
Proof. exact (@lem1483488 h x). Qed.
Lemma lem1543600 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1543601 (y : real) (h : real) (x : real) : (term193 y x h) = (term193 y h x).
Proof. exact (MK_COMB (@lem1543600 y) (@lem1543597 h x)). Qed.
Lemma lem1543602 (h : real) (y : real) (x : real) : (term193 y h x) = (term193 h y x).
Proof. exact (@lem1483484 h y x). Qed.
Lemma lem1543603 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1483488 x y). Qed.
Lemma lem1543604 (h : real) : (real_add h) = (real_add h).
Proof. exact (eq_refl (real_add h)). Qed.
Lemma lem1543605 (h : real) (x : real) (y : real) : (term193 h y x) = (term193 h x y).
Proof. exact (MK_COMB (@lem1543604 h) (@lem1543603 x y)). Qed.
Lemma lem1543606 (h : real) (x : real) (y : real) : (term193 y h x) = (term193 h x y).
Proof. exact (TRANS (@lem1543602 h y x) (@lem1543605 h x y)). Qed.
Lemma lem1543607 (h : real) (x : real) (y : real) : (term193 y x h) = (term193 h x y).
Proof. exact (TRANS (@lem1543601 y h x) (@lem1543606 h x y)). Qed.
Lemma lem1543608 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543609 (h : real) (x : real) (y : real) : (term350 y x h) = (term350 h x y).
Proof. exact (MK_COMB (@lem1543608) (@lem1543607 h x y)). Qed.
Lemma lem1543610 (h : real) (x : real) (y : real) : (term194 y x h) = (term194 h x y).
Proof. exact (MK_COMB (@lem1543609 h x y) (@lem1543590)). Qed.
Lemma lem1543611 (h : real) (x : real) (y : real) : (term194 h x y) = (term195 h x y).
Proof. exact (@lem1483519 (term193 h x y) term46). Qed.
Lemma lem1543613 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543614 : term158 = term46.
Proof. exact (@lem1543613 term159). Qed.
Lemma lem1543615 (h : real) (x : real) (y : real) : (term196 h x y) = (term196 h x y).
Proof. exact (eq_refl (term196 h x y)). Qed.
Lemma lem1543616 (h : real) (x : real) (y : real) : (term195 h x y) = (term197 h x y).
Proof. exact (MK_COMB (@lem1543615 h x y) (@lem1543614)). Qed.
Lemma lem1543617 (h : real) (x : real) (y : real) : (term197 h x y) = (term193 h x y).
Proof. exact (@lem1483450 (term193 h x y)). Qed.
Lemma lem1543618 (h : real) (x : real) (y : real) : (term195 h x y) = (term193 h x y).
Proof. exact (TRANS (@lem1543616 h x y) (@lem1543617 h x y)). Qed.
Lemma lem1543619 (h : real) (x : real) (y : real) : (term194 h x y) = (term193 h x y).
Proof. exact (TRANS (@lem1543611 h x y) (@lem1543618 h x y)). Qed.
Lemma lem1543620 (h : real) (x : real) (y : real) : (term194 y x h) = (term193 h x y).
Proof. exact (TRANS (@lem1543610 h x y) (@lem1543619 h x y)). Qed.
Lemma lem1543621 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543622 (h : real) (x : real) (y : real) : (term351 y x h) = (term352 h x y).
Proof. exact (MK_COMB (@lem1543621) (@lem1543620 h x y)). Qed.
Lemma lem1543623 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543624 (h : real) (x : real) (y : real) : (term349 y x h) = (term348 h x y).
Proof. exact (MK_COMB (@lem1543622 h x y) (@lem1543623)). Qed.
Lemma lem1543625 (h : real) (x : real) (y : real) : (term348 y x h) = (term348 h x y).
Proof. exact (TRANS (@lem1543589 y x h) (@lem1543624 h x y)). Qed.
Lemma lem1543626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543627 (h : real) (x : real) (y : real) : (term353 y x h) = (term354 h x y).
Proof. exact (MK_COMB (@lem1543626) (@lem1543588 h x y)). Qed.
Lemma lem1543628 (h : real) (x : real) (y : real) : (term355 y x h) = (term356 h x y).
Proof. exact (MK_COMB (@lem1543627 h x y) (@lem1543625 h x y)). Qed.
Lemma lem1543629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543630 (h : real) (x : real) (y : real) : (term297 h x y) = (term297 h x y).
Proof. exact (MK_COMB (@lem1543629) (@lem1543545 h x y)). Qed.
Lemma lem1543631 (h : real) (x : real) (y : real) : (term357 y x h) = (term358 h x y).
Proof. exact (MK_COMB (@lem1543630 h x y) (@lem1543628 h x y)). Qed.
Lemma lem1543632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543633 (y : real) : (term299 y) = (term299 y).
Proof. exact (MK_COMB (@lem1543632) (@lem1543356 y)). Qed.
Lemma lem1543634 (h : real) (x : real) (y : real) : (term311 y x h) = (term359 h x y).
Proof. exact (MK_COMB (@lem1543633 y) (@lem1543631 h x y)). Qed.
Lemma lem1543635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543636 (h : real) (x : real) : (term312 x h) = (term312 h x).
Proof. exact (MK_COMB (@lem1543635) (@lem1543329 h x)). Qed.
Lemma lem1543637 (h : real) (x : real) (y : real) : (term314 y x h) = (term360 h x y).
Proof. exact (MK_COMB (@lem1543636 h x) (@lem1543634 h x y)). Qed.
Lemma lem1543638 (x : real) (h : real) : (term361 x h) = (term362 x h).
Proof. exact (@lem1483525 term46 (real_add x h)). Qed.
Lemma lem1543645 (h : real) (x : real) : (real_add x h) = (real_add h x).
Proof. exact (@lem1483488 h x). Qed.
Lemma lem1543648 : term363 = term363.
Proof. exact (eq_refl term363). Qed.
Lemma lem1543649 (h : real) (x : real) : (term364 x h) = (term364 h x).
Proof. exact (MK_COMB (@lem1543648) (@lem1543645 h x)). Qed.
Lemma lem1543650 (h : real) (x : real) : (term364 h x) = (term365 h x).
Proof. exact (@lem1483519 term46 (real_add h x)). Qed.
Lemma lem1543657 (h : real) (x : real) : (term366 h x) = (term228 h x).
Proof. exact (@lem1483508 h term367 x). Qed.
Lemma lem1543658 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem1543659 (h : real) (x : real) : (term365 h x) = (term369 h x).
Proof. exact (MK_COMB (@lem1543658) (@lem1543657 h x)). Qed.
Lemma lem1543660 (h : real) (x : real) : (term369 h x) = (term228 h x).
Proof. exact (@lem1483448 (term228 h x)). Qed.
Lemma lem1543661 (h : real) (x : real) : (term365 h x) = (term228 h x).
Proof. exact (TRANS (@lem1543659 h x) (@lem1543660 h x)). Qed.
Lemma lem1543662 (h : real) (x : real) : (term364 h x) = (term228 h x).
Proof. exact (TRANS (@lem1543650 h x) (@lem1543661 h x)). Qed.
Lemma lem1543663 (h : real) (x : real) : (term364 x h) = (term228 h x).
Proof. exact (TRANS (@lem1543649 h x) (@lem1543662 h x)). Qed.
Lemma lem1543664 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543665 (h : real) (x : real) : (term370 x h) = (term371 h x).
Proof. exact (MK_COMB (@lem1543664) (@lem1543663 h x)). Qed.
Lemma lem1543666 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543667 (h : real) (x : real) : (term362 x h) = (term372 h x).
Proof. exact (MK_COMB (@lem1543665 h x) (@lem1543666)). Qed.
Lemma lem1543668 (h : real) (x : real) : (term361 x h) = (term372 h x).
Proof. exact (TRANS (@lem1543638 x h) (@lem1543667 h x)). Qed.
Lemma lem1543669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543670 (h : real) (x : real) (y : real) : (term257 h x y) = (term257 h x y).
Proof. exact (MK_COMB (@lem1543669) (@lem1543407 h x y)). Qed.
Lemma lem1543671 (h : real) (x : real) (y : real) : (term259 h x y) = (term259 h x y).
Proof. exact (MK_COMB (@lem1543670 h x y) (@lem1543452 h x y)). Qed.
Lemma lem1543672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543673 (h : real) (x : real) (y : real) : (term289 h x y) = (term289 h x y).
Proof. exact (MK_COMB (@lem1543672) (@lem1543500 h x y)). Qed.
Lemma lem1543674 (h : real) (x : real) (y : real) : (term291 h x y) = (term291 h x y).
Proof. exact (MK_COMB (@lem1543673 h x y) (@lem1543539 h x y)). Qed.
Lemma lem1543675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543676 (h : real) (x : real) (y : real) : (term293 h x y) = (term293 h x y).
Proof. exact (MK_COMB (@lem1543675) (@lem1543671 h x y)). Qed.
Lemma lem1543677 (h : real) (x : real) (y : real) : (term295 h x y) = (term295 h x y).
Proof. exact (MK_COMB (@lem1543676 h x y) (@lem1543674 h x y)). Qed.
Lemma lem1543678 (y : real) (x : real) (h : real) : (term373 y x h) = (term374 y x h).
Proof. exact (@lem1483527 (term375 y x h) term46). Qed.
Lemma lem1543679 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543686 (h : real) (x : real) : (real_add x h) = (real_add h x).
Proof. exact (@lem1483488 h x). Qed.
Lemma lem1543687 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1543688 (h : real) (x : real) : (term376 x h) = (term376 h x).
Proof. exact (MK_COMB (@lem1543687) (@lem1543686 h x)). Qed.
Lemma lem1543689 (h : real) (x : real) : (term376 h x) = (term366 h x).
Proof. exact (@lem1483512 (real_add h x)). Qed.
Lemma lem1543696 (h : real) (x : real) : (term366 h x) = (term228 h x).
Proof. exact (@lem1483508 h term367 x). Qed.
Lemma lem1543697 (h : real) (x : real) : (term376 h x) = (term228 h x).
Proof. exact (TRANS (@lem1543689 h x) (@lem1543696 h x)). Qed.
Lemma lem1543698 (h : real) (x : real) : (term376 x h) = (term228 h x).
Proof. exact (TRANS (@lem1543688 h x) (@lem1543697 h x)). Qed.
Lemma lem1543707 (y : real) : (term94 y) = (term94 y).
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1543708 (y : real) (h : real) (x : real) : (term375 y x h) = (term229 y h x).
Proof. exact (MK_COMB (@lem1543707 y) (@lem1543698 h x)). Qed.
Lemma lem1543709 (h : real) (y : real) (x : real) : (term229 y h x) = (term229 h y x).
Proof. exact (@lem1483484 (term80 h) (term80 y) (term80 x)). Qed.
Lemma lem1543710 (x : real) (y : real) : (term228 y x) = (term228 x y).
Proof. exact (@lem1483488 (term80 x) (term80 y)). Qed.
Lemma lem1543711 (h : real) : (term94 h) = (term94 h).
Proof. exact (eq_refl (term94 h)). Qed.
Lemma lem1543712 (h : real) (x : real) (y : real) : (term229 h y x) = (term229 h x y).
Proof. exact (MK_COMB (@lem1543711 h) (@lem1543710 x y)). Qed.
Lemma lem1543713 (h : real) (x : real) (y : real) : (term229 y h x) = (term229 h x y).
Proof. exact (TRANS (@lem1543709 h y x) (@lem1543712 h x y)). Qed.
Lemma lem1543714 (h : real) (x : real) (y : real) : (term375 y x h) = (term229 h x y).
Proof. exact (TRANS (@lem1543708 y h x) (@lem1543713 h x y)). Qed.
Lemma lem1543715 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543716 (h : real) (x : real) (y : real) : (term377 y x h) = (term231 h x y).
Proof. exact (MK_COMB (@lem1543715) (@lem1543714 h x y)). Qed.
Lemma lem1543717 (h : real) (x : real) (y : real) : (term378 y x h) = (term233 h x y).
Proof. exact (MK_COMB (@lem1543716 h x y) (@lem1543679)). Qed.
Lemma lem1543718 (h : real) (x : real) (y : real) : (term233 h x y) = (term234 h x y).
Proof. exact (@lem1483519 (term229 h x y) term46). Qed.
Lemma lem1543720 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543721 : term158 = term46.
Proof. exact (@lem1543720 term159). Qed.
Lemma lem1543722 (h : real) (x : real) (y : real) : (term235 h x y) = (term235 h x y).
Proof. exact (eq_refl (term235 h x y)). Qed.
Lemma lem1543723 (h : real) (x : real) (y : real) : (term234 h x y) = (term236 h x y).
Proof. exact (MK_COMB (@lem1543722 h x y) (@lem1543721)). Qed.
Lemma lem1543724 (h : real) (x : real) (y : real) : (term236 h x y) = (term229 h x y).
Proof. exact (@lem1483450 (term229 h x y)). Qed.
Lemma lem1543725 (h : real) (x : real) (y : real) : (term234 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543723 h x y) (@lem1543724 h x y)). Qed.
Lemma lem1543726 (h : real) (x : real) (y : real) : (term233 h x y) = (term229 h x y).
Proof. exact (TRANS (@lem1543718 h x y) (@lem1543725 h x y)). Qed.
Lemma lem1543727 (h : real) (x : real) (y : real) : (term378 y x h) = (term229 h x y).
Proof. exact (TRANS (@lem1543717 h x y) (@lem1543726 h x y)). Qed.
Lemma lem1543728 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543729 (h : real) (x : real) (y : real) : (term379 y x h) = (term380 h x y).
Proof. exact (MK_COMB (@lem1543728) (@lem1543727 h x y)). Qed.
Lemma lem1543730 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543731 (h : real) (x : real) (y : real) : (term374 y x h) = (term381 h x y).
Proof. exact (MK_COMB (@lem1543729 h x y) (@lem1543730)). Qed.
Lemma lem1543732 (h : real) (x : real) (y : real) : (term373 y x h) = (term381 h x y).
Proof. exact (TRANS (@lem1543678 y x h) (@lem1543731 h x y)). Qed.
Lemma lem1543733 (y : real) (x : real) (h : real) : (term382 y x h) = (term383 y x h).
Proof. exact (@lem1483527 (term384 y x h) term46). Qed.
Lemma lem1543734 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543741 (h : real) (x : real) : (real_add x h) = (real_add h x).
Proof. exact (@lem1483488 h x). Qed.
Lemma lem1543742 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1543743 (h : real) (x : real) : (term376 x h) = (term376 h x).
Proof. exact (MK_COMB (@lem1543742) (@lem1543741 h x)). Qed.
Lemma lem1543744 (h : real) (x : real) : (term376 h x) = (term366 h x).
Proof. exact (@lem1483512 (real_add h x)). Qed.
Lemma lem1543751 (h : real) (x : real) : (term366 h x) = (term228 h x).
Proof. exact (@lem1483508 h term367 x). Qed.
Lemma lem1543752 (h : real) (x : real) : (term376 h x) = (term228 h x).
Proof. exact (TRANS (@lem1543744 h x) (@lem1543751 h x)). Qed.
Lemma lem1543753 (h : real) (x : real) : (term376 x h) = (term228 h x).
Proof. exact (TRANS (@lem1543743 h x) (@lem1543752 h x)). Qed.
Lemma lem1543756 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1543757 (y : real) (h : real) (x : real) : (term384 y x h) = (term263 y h x).
Proof. exact (MK_COMB (@lem1543756 y) (@lem1543753 h x)). Qed.
Lemma lem1543758 (h : real) (y : real) (x : real) : (term263 y h x) = (term245 h y x).
Proof. exact (@lem1483484 (term80 h) y (term80 x)). Qed.
Lemma lem1543759 (x : real) (y : real) : (term244 y x) = (term343 x y).
Proof. exact (@lem1483488 (term80 x) y). Qed.
Lemma lem1543760 (h : real) : (term94 h) = (term94 h).
Proof. exact (eq_refl (term94 h)). Qed.
Lemma lem1543761 (h : real) (x : real) (y : real) : (term245 h y x) = (term164 h x y).
Proof. exact (MK_COMB (@lem1543760 h) (@lem1543759 x y)). Qed.
Lemma lem1543762 (h : real) (x : real) (y : real) : (term263 y h x) = (term164 h x y).
Proof. exact (TRANS (@lem1543758 h y x) (@lem1543761 h x y)). Qed.
Lemma lem1543763 (h : real) (x : real) (y : real) : (term384 y x h) = (term164 h x y).
Proof. exact (TRANS (@lem1543757 y h x) (@lem1543762 h x y)). Qed.
Lemma lem1543764 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1543765 (h : real) (x : real) (y : real) : (term385 y x h) = (term386 h x y).
Proof. exact (MK_COMB (@lem1543764) (@lem1543763 h x y)). Qed.
Lemma lem1543766 (h : real) (x : real) (y : real) : (term387 y x h) = (term165 h x y).
Proof. exact (MK_COMB (@lem1543765 h x y) (@lem1543734)). Qed.
Lemma lem1543767 (h : real) (x : real) (y : real) : (term165 h x y) = (term166 h x y).
Proof. exact (@lem1483519 (term164 h x y) term46). Qed.
Lemma lem1543769 (x : nat) : (term157 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1543770 : term158 = term46.
Proof. exact (@lem1543769 term159). Qed.
Lemma lem1543771 (h : real) (x : real) (y : real) : (term167 h x y) = (term167 h x y).
Proof. exact (eq_refl (term167 h x y)). Qed.
Lemma lem1543772 (h : real) (x : real) (y : real) : (term166 h x y) = (term168 h x y).
Proof. exact (MK_COMB (@lem1543771 h x y) (@lem1543770)). Qed.
Lemma lem1543773 (h : real) (x : real) (y : real) : (term168 h x y) = (term164 h x y).
Proof. exact (@lem1483450 (term164 h x y)). Qed.
Lemma lem1543774 (h : real) (x : real) (y : real) : (term166 h x y) = (term164 h x y).
Proof. exact (TRANS (@lem1543772 h x y) (@lem1543773 h x y)). Qed.
Lemma lem1543775 (h : real) (x : real) (y : real) : (term165 h x y) = (term164 h x y).
Proof. exact (TRANS (@lem1543767 h x y) (@lem1543774 h x y)). Qed.
Lemma lem1543776 (h : real) (x : real) (y : real) : (term387 y x h) = (term164 h x y).
Proof. exact (TRANS (@lem1543766 h x y) (@lem1543775 h x y)). Qed.
Lemma lem1543777 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543778 (h : real) (x : real) (y : real) : (term388 y x h) = (term389 h x y).
Proof. exact (MK_COMB (@lem1543777) (@lem1543776 h x y)). Qed.
Lemma lem1543779 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543780 (h : real) (x : real) (y : real) : (term383 y x h) = (term390 h x y).
Proof. exact (MK_COMB (@lem1543778 h x y) (@lem1543779)). Qed.
Lemma lem1543781 (h : real) (x : real) (y : real) : (term382 y x h) = (term390 h x y).
Proof. exact (TRANS (@lem1543733 y x h) (@lem1543780 h x y)). Qed.
Lemma lem1543782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543783 (h : real) (x : real) (y : real) : (term391 y x h) = (term392 h x y).
Proof. exact (MK_COMB (@lem1543782) (@lem1543732 h x y)). Qed.
Lemma lem1543784 (h : real) (x : real) (y : real) : (term393 y x h) = (term394 h x y).
Proof. exact (MK_COMB (@lem1543783 h x y) (@lem1543781 h x y)). Qed.
Lemma lem1543785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543786 (h : real) (x : real) (y : real) : (term297 h x y) = (term297 h x y).
Proof. exact (MK_COMB (@lem1543785) (@lem1543677 h x y)). Qed.
Lemma lem1543787 (h : real) (x : real) (y : real) : (term395 y x h) = (term396 h x y).
Proof. exact (MK_COMB (@lem1543786 h x y) (@lem1543784 h x y)). Qed.
Lemma lem1543788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543789 (y : real) : (term299 y) = (term299 y).
Proof. exact (MK_COMB (@lem1543788) (@lem1543356 y)). Qed.
Lemma lem1543790 (h : real) (x : real) (y : real) : (term306 y x h) = (term397 h x y).
Proof. exact (MK_COMB (@lem1543789 y) (@lem1543787 h x y)). Qed.
Lemma lem1543791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543792 (h : real) (x : real) : (term307 x h) = (term398 h x).
Proof. exact (MK_COMB (@lem1543791) (@lem1543668 h x)). Qed.
Lemma lem1543793 (h : real) (x : real) (y : real) : (term309 y x h) = (term399 h x y).
Proof. exact (MK_COMB (@lem1543792 h x) (@lem1543790 h x y)). Qed.
Lemma lem1543794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1543795 (h : real) (x : real) (y : real) : (term316 y x h) = (term400 h x y).
Proof. exact (MK_COMB (@lem1543794) (@lem1543637 h x y)). Qed.
Lemma lem1543796 (h : real) (x : real) (y : real) : (term317 y x h) = (term401 h x y).
Proof. exact (MK_COMB (@lem1543795 h x y) (@lem1543793 h x y)). Qed.
Lemma lem1543808 (h : real) (x : real) (y : real) : (term300 y x h) = (term401 h x y).
Proof. exact (TRANS (@lem1543302 y x h) (@lem1543796 h x y)). Qed.
Lemma lem1543810 (y : real) (x : real) (h : real) : (term402 y x h) = (term148 y x h).
Proof. exact (eq_refl (term402 y x h)). Qed.
Lemma lem1543811 (y : real) (x : real) (h : real) : (term148 y x h) = (term402 y x h).
Proof. exact (SYM (@lem1543810 y x h)). Qed.
Lemma lem1543812 (y : real) (x : real) (h : real) : (term402 y x h) = (term403 y x h).
Proof. exact (@lem1482981 (term404 h x y) (real_add x h)). Qed.
Lemma lem1543813 (y : real) (x : real) (h : real) : (term148 y x h) = (term403 y x h).
Proof. exact (TRANS (@lem1543811 y x h) (@lem1543812 y x h)). Qed.
Lemma lem1543814 (y : real) (x : real) (h : real) : (term405 y x h) = (term406 y x h).
Proof. exact (eq_refl (term405 y x h)). Qed.
Lemma lem1543815 (x : real) (h : real) : (term307 x h) = (term307 x h).
Proof. exact (eq_refl (term307 x h)). Qed.
Lemma lem1543816 (y : real) (x : real) (h : real) : (term407 y x h) = (term408 y x h).
Proof. exact (MK_COMB (@lem1543815 x h) (@lem1543814 y x h)). Qed.
Lemma lem1543817 (y : real) (x : real) (h : real) : (term409 y x h) = (term410 y x h).
Proof. exact (eq_refl (term409 y x h)). Qed.
Lemma lem1543818 (x : real) (h : real) : (term312 x h) = (term312 x h).
Proof. exact (eq_refl (term312 x h)). Qed.
Lemma lem1543819 (y : real) (x : real) (h : real) : (term411 y x h) = (term412 y x h).
Proof. exact (MK_COMB (@lem1543818 x h) (@lem1543817 y x h)). Qed.
Lemma lem1543820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1543821 (y : real) (x : real) (h : real) : (term413 y x h) = (term414 y x h).
Proof. exact (MK_COMB (@lem1543820) (@lem1543819 y x h)). Qed.
Lemma lem1543822 (y : real) (x : real) (h : real) : (term403 y x h) = (term415 y x h).
Proof. exact (MK_COMB (@lem1543821 y x h) (@lem1543816 y x h)). Qed.
Lemma lem1543823 (y : real) (x : real) (h : real) : (term416 y x h) = (term416 y x h).
Proof. exact (eq_refl (term416 y x h)). Qed.
Lemma lem1543824 (y : real) (x : real) (h : real) : ((term148 y x h) = (term403 y x h)) = ((term148 y x h) = (term415 y x h)).
Proof. exact (MK_COMB (@lem1543823 y x h) (@lem1543822 y x h)). Qed.
Lemma lem1543825 (y : real) (x : real) (h : real) : (term148 y x h) = (term415 y x h).
Proof. exact (EQ_MP (@lem1543824 y x h) (@lem1543813 y x h)). Qed.
Lemma lem1543826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543827 (h : real) (x : real) (y : real) : (term180 h x y) = (term180 h x y).
Proof. exact (MK_COMB (@lem1543826) (@lem1542875 h x y)). Qed.
Lemma lem1543828 (h : real) (x : real) (y : real) : (term181 h x y) = (term181 h x y).
Proof. exact (MK_COMB (@lem1543827 h x y) (@lem1542914 h x y)). Qed.
Lemma lem1543829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543830 (h : real) (x : real) (y : real) : (term200 h x y) = (term200 h x y).
Proof. exact (MK_COMB (@lem1543829) (@lem1542956 h x y)). Qed.
Lemma lem1543831 (h : real) (x : real) (y : real) : (term201 h x y) = (term201 h x y).
Proof. exact (MK_COMB (@lem1543830 h x y) (@lem1542989 h x y)). Qed.
Lemma lem1543832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543833 (h : real) (x : real) (y : real) : (term202 h x y) = (term202 h x y).
Proof. exact (MK_COMB (@lem1543832) (@lem1543828 h x y)). Qed.
Lemma lem1543834 (h : real) (x : real) (y : real) : (term203 h x y) = (term203 h x y).
Proof. exact (MK_COMB (@lem1543833 h x y) (@lem1543831 h x y)). Qed.
Lemma lem1543835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543836 (h : real) (x : real) (y : real) : (term353 y x h) = (term354 h x y).
Proof. exact (MK_COMB (@lem1543835) (@lem1543588 h x y)). Qed.
Lemma lem1543837 (h : real) (x : real) (y : real) : (term355 y x h) = (term356 h x y).
Proof. exact (MK_COMB (@lem1543836 h x y) (@lem1543625 h x y)). Qed.
Lemma lem1543838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543839 (h : real) (x : real) (y : real) : (term216 h x y) = (term216 h x y).
Proof. exact (MK_COMB (@lem1543838) (@lem1543834 h x y)). Qed.
Lemma lem1543840 (h : real) (x : real) (y : real) : (term417 y x h) = (term418 h x y).
Proof. exact (MK_COMB (@lem1543839 h x y) (@lem1543837 h x y)). Qed.
Lemma lem1543841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543842 (y : real) : (term146 y) = (term146 y).
Proof. exact (MK_COMB (@lem1543841) (@lem1542830 y)). Qed.
Lemma lem1543843 (h : real) (x : real) (y : real) : (term410 y x h) = (term419 h x y).
Proof. exact (MK_COMB (@lem1543842 y) (@lem1543840 h x y)). Qed.
Lemma lem1543844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543845 (h : real) (x : real) : (term312 x h) = (term312 h x).
Proof. exact (MK_COMB (@lem1543844) (@lem1543329 h x)). Qed.
Lemma lem1543846 (h : real) (x : real) (y : real) : (term412 y x h) = (term420 h x y).
Proof. exact (MK_COMB (@lem1543845 h x) (@lem1543843 h x y)). Qed.
Lemma lem1543847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543848 (h : real) (x : real) (y : real) : (term180 h x y) = (term180 h x y).
Proof. exact (MK_COMB (@lem1543847) (@lem1542875 h x y)). Qed.
Lemma lem1543849 (h : real) (x : real) (y : real) : (term181 h x y) = (term181 h x y).
Proof. exact (MK_COMB (@lem1543848 h x y) (@lem1542914 h x y)). Qed.
Lemma lem1543850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543851 (h : real) (x : real) (y : real) : (term200 h x y) = (term200 h x y).
Proof. exact (MK_COMB (@lem1543850) (@lem1542956 h x y)). Qed.
Lemma lem1543852 (h : real) (x : real) (y : real) : (term201 h x y) = (term201 h x y).
Proof. exact (MK_COMB (@lem1543851 h x y) (@lem1542989 h x y)). Qed.
Lemma lem1543853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543854 (h : real) (x : real) (y : real) : (term202 h x y) = (term202 h x y).
Proof. exact (MK_COMB (@lem1543853) (@lem1543849 h x y)). Qed.
Lemma lem1543855 (h : real) (x : real) (y : real) : (term203 h x y) = (term203 h x y).
Proof. exact (MK_COMB (@lem1543854 h x y) (@lem1543852 h x y)). Qed.
Lemma lem1543856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543857 (h : real) (x : real) (y : real) : (term391 y x h) = (term392 h x y).
Proof. exact (MK_COMB (@lem1543856) (@lem1543732 h x y)). Qed.
Lemma lem1543858 (h : real) (x : real) (y : real) : (term393 y x h) = (term394 h x y).
Proof. exact (MK_COMB (@lem1543857 h x y) (@lem1543781 h x y)). Qed.
Lemma lem1543859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543860 (h : real) (x : real) (y : real) : (term216 h x y) = (term216 h x y).
Proof. exact (MK_COMB (@lem1543859) (@lem1543855 h x y)). Qed.
Lemma lem1543861 (h : real) (x : real) (y : real) : (term421 y x h) = (term422 h x y).
Proof. exact (MK_COMB (@lem1543860 h x y) (@lem1543858 h x y)). Qed.
Lemma lem1543862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543863 (y : real) : (term146 y) = (term146 y).
Proof. exact (MK_COMB (@lem1543862) (@lem1542830 y)). Qed.
Lemma lem1543864 (h : real) (x : real) (y : real) : (term406 y x h) = (term423 h x y).
Proof. exact (MK_COMB (@lem1543863 y) (@lem1543861 h x y)). Qed.
Lemma lem1543865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1543866 (h : real) (x : real) : (term307 x h) = (term398 h x).
Proof. exact (MK_COMB (@lem1543865) (@lem1543668 h x)). Qed.
Lemma lem1543867 (h : real) (x : real) (y : real) : (term408 y x h) = (term424 h x y).
Proof. exact (MK_COMB (@lem1543866 h x) (@lem1543864 h x y)). Qed.
Lemma lem1543868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1543869 (h : real) (x : real) (y : real) : (term414 y x h) = (term425 h x y).
Proof. exact (MK_COMB (@lem1543868) (@lem1543846 h x y)). Qed.
Lemma lem1543870 (h : real) (x : real) (y : real) : (term415 y x h) = (term426 h x y).
Proof. exact (MK_COMB (@lem1543869 h x y) (@lem1543867 h x y)). Qed.
Lemma lem1543882 (h : real) (x : real) (y : real) : (term148 y x h) = (term426 h x y).
Proof. exact (TRANS (@lem1543825 y x h) (@lem1543870 h x y)). Qed.
Lemma lem1543883 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1543884 (h : real) (x : real) (y : real) : (term150 y x h) = (term427 h x y).
Proof. exact (MK_COMB (@lem1543883) (@lem1543882 h x y)). Qed.
Lemma lem1543885 (h : real) (x : real) (y : real) : (term301 y x h) = (term428 h x y).
Proof. exact (MK_COMB (@lem1543884 h x y) (@lem1543808 h x y)). Qed.
Lemma lem1543886 (h : real) (x : real) (y : real) : (term135 y x h) = (term428 h x y).
Proof. exact (TRANS (@lem1543285 y x h) (@lem1543885 h x y)). Qed.
Lemma lem1543887 (h : real) (x : real) (y : real) : (term59 y x h) = (term428 h x y).
Proof. exact (TRANS (@lem1542793 y x h) (@lem1543886 h x y)). Qed.
Lemma lem1543888 (h : real) (x : real) (y : real) (h1 : term428 h x y) : term428 h x y.
Proof. exact (h1). Qed.
Lemma lem1543889 (h : real) (x : real) (y : real) (h1 : term426 h x y) : term426 h x y.
Proof. exact (h1). Qed.
Lemma lem1543890 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term420 h x y.
Proof. exact (h1). Qed.
Lemma lem1543891 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term419 h x y.
Proof. exact (proj2 (@lem1543890 h x y h1)). Qed.
Lemma lem1543893 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term418 h x y.
Proof. exact (proj2 (@lem1543891 h x y h1)). Qed.
Lemma lem1543895 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term356 h x y.
Proof. exact (proj2 (@lem1543893 h x y h1)). Qed.
Lemma lem1543896 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term203 h x y.
Proof. exact (proj1 (@lem1543893 h x y h1)). Qed.
Lemma lem1543898 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term181 h x y.
Proof. exact (proj1 (@lem1543896 h x y h1)). Qed.
Lemma lem1543900 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term162 h x y.
Proof. exact (proj1 (@lem1543898 h x y h1)). Qed.
Lemma lem1543904 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term347 h x y.
Proof. exact (proj1 (@lem1543895 h x y h1)). Qed.
Lemma lem1543906 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1543907 : term430 = term431.
Proof. exact (@lem1543906 (NUMERAL 0) term159). Qed.
Lemma lem1543908 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1543909 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1543910 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1543909 h1) (fun h1 : term431 = True => @lem1543908)). Qed.
Lemma lem1543911 : term431 = True.
Proof. exact (EQ_MP (@lem1543910) (@lem1543908)). Qed.
Lemma lem1543912 : term430 = True.
Proof. exact (TRANS (@lem1543907) (@lem1543911)). Qed.
Lemma lem1543913 : True = term430.
Proof. exact (SYM (@lem1543912)). Qed.
Lemma lem1543914 : term430.
Proof. exact (EQ_MP (@lem1543913) (@lem0)). Qed.
Lemma lem1543915 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term433 h x y.
Proof. exact (conj (@lem1543914) (@lem1543904 h x y h1)). Qed.
Lemma lem1543917 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1543918 (h : real) (x : real) (y : real) : term435 h x y.
Proof. exact (@lem1543917 term436 (term277 h x y)). Qed.
Lemma lem1543919 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term437 h x y.
Proof. exact (@lem1543918 h x y (@lem1543915 h x y h1)). Qed.
Lemma lem1543920 (h : real) (x : real) (y : real) : (term438 h x y) = (term277 h x y).
Proof. exact (@lem1483460 (term277 h x y)). Qed.
Lemma lem1543921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1543922 (h : real) (x : real) (y : real) : (term439 h x y) = (term346 h x y).
Proof. exact (MK_COMB (@lem1543921) (@lem1543920 h x y)). Qed.
Lemma lem1543923 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543924 (h : real) (x : real) (y : real) : (term437 h x y) = (term347 h x y).
Proof. exact (MK_COMB (@lem1543922 h x y) (@lem1543923)). Qed.
Lemma lem1543925 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term347 h x y.
Proof. exact (EQ_MP (@lem1543924 h x y) (@lem1543919 h x y h1)). Qed.
Lemma lem1543927 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1543928 : term430 = term431.
Proof. exact (@lem1543927 (NUMERAL 0) term159). Qed.
Lemma lem1543929 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1543930 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1543931 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1543930 h1) (fun h1 : term431 = True => @lem1543929)). Qed.
Lemma lem1543932 : term431 = True.
Proof. exact (EQ_MP (@lem1543931) (@lem1543929)). Qed.
Lemma lem1543933 : term430 = True.
Proof. exact (TRANS (@lem1543928) (@lem1543932)). Qed.
Lemma lem1543934 : True = term430.
Proof. exact (SYM (@lem1543933)). Qed.
Lemma lem1543935 : term430.
Proof. exact (EQ_MP (@lem1543934) (@lem0)). Qed.
Lemma lem1543936 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term440 h x y.
Proof. exact (conj (@lem1543935) (@lem1543900 h x y h1)). Qed.
Lemma lem1543938 (x : real) (y : real) : term441 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1543939 (h : real) (x : real) (y : real) : term442 h x y.
Proof. exact (@lem1543938 term436 (term164 h x y)). Qed.
Lemma lem1543940 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term443 h x y.
Proof. exact (@lem1543939 h x y (@lem1543936 h x y h1)). Qed.
Lemma lem1543941 (h : real) (x : real) (y : real) : (term444 h x y) = (term164 h x y).
Proof. exact (@lem1483460 (term164 h x y)). Qed.
Lemma lem1543942 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1543943 (h : real) (x : real) (y : real) : (term445 h x y) = (term170 h x y).
Proof. exact (MK_COMB (@lem1543942) (@lem1543941 h x y)). Qed.
Lemma lem1543944 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1543945 (h : real) (x : real) (y : real) : (term443 h x y) = (term162 h x y).
Proof. exact (MK_COMB (@lem1543943 h x y) (@lem1543944)). Qed.
Lemma lem1543946 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term162 h x y.
Proof. exact (EQ_MP (@lem1543945 h x y) (@lem1543940 h x y h1)). Qed.
Lemma lem1543947 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term446 h x y.
Proof. exact (conj (@lem1543946 h x y h1) (@lem1543925 h x y h1)). Qed.
Lemma lem1543949 (x : real) (y : real) : term447 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1543950 (h : real) (x : real) (y : real) : term448 h x y.
Proof. exact (@lem1543949 (term164 h x y) (term277 h x y)). Qed.
Lemma lem1543951 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term449 h x y.
Proof. exact (@lem1543950 h x y (@lem1543947 h x y h1)). Qed.
Lemma lem1543952 (h : real) (x : real) (y : real) : (term450 h x y) = (term451 h x y).
Proof. exact (@lem1483480 (term80 h) h (term343 x y) (term244 x y)). Qed.
Lemma lem1543953 (h : real) : (term452 h) = (term453 h).
Proof. exact (@lem1483440 term367 h). Qed.
Lemma lem1543955 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1543956 : term455 = term46.
Proof. exact (@lem1543955 term159). Qed.
Lemma lem1543957 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1543958 : term456 = term457.
Proof. exact (MK_COMB (@lem1543957) (@lem1543956)). Qed.
Lemma lem1543959 (h : real) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1543960 (h : real) : (term453 h) = (term458 h).
Proof. exact (MK_COMB (@lem1543958) (@lem1543959 h)). Qed.
Lemma lem1543961 (h : real) : (term452 h) = (term458 h).
Proof. exact (TRANS (@lem1543953 h) (@lem1543960 h)). Qed.
Lemma lem1543962 (h : real) : (term458 h) = term46.
Proof. exact (@lem1483446 h). Qed.
Lemma lem1543963 (h : real) : (term452 h) = term46.
Proof. exact (TRANS (@lem1543961 h) (@lem1543962 h)). Qed.
Lemma lem1543964 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1543965 (h : real) : (term459 h) = term368.
Proof. exact (MK_COMB (@lem1543964) (@lem1543963 h)). Qed.
Lemma lem1543966 (x : real) (y : real) : (term460 x y) = (term461 x y).
Proof. exact (@lem1483480 (term80 x) x y (term80 y)). Qed.
Lemma lem1543967 (x : real) : (term452 x) = (term453 x).
Proof. exact (@lem1483440 term367 x). Qed.
Lemma lem1543969 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1543970 : term455 = term46.
Proof. exact (@lem1543969 term159). Qed.
Lemma lem1543971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1543972 : term456 = term457.
Proof. exact (MK_COMB (@lem1543971) (@lem1543970)). Qed.
Lemma lem1543973 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1543974 (x : real) : (term453 x) = (term458 x).
Proof. exact (MK_COMB (@lem1543972) (@lem1543973 x)). Qed.
Lemma lem1543975 (x : real) : (term452 x) = (term458 x).
Proof. exact (TRANS (@lem1543967 x) (@lem1543974 x)). Qed.
Lemma lem1543976 (x : real) : (term458 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1543977 (x : real) : (term452 x) = term46.
Proof. exact (TRANS (@lem1543975 x) (@lem1543976 x)). Qed.
Lemma lem1543978 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1543979 (x : real) : (term459 x) = term368.
Proof. exact (MK_COMB (@lem1543978) (@lem1543977 x)). Qed.
Lemma lem1543980 (y : real) : (term462 y) = (term453 y).
Proof. exact (@lem1483442 term367 y). Qed.
Lemma lem1543982 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1543983 : term455 = term46.
Proof. exact (@lem1543982 term159). Qed.
Lemma lem1543984 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1543985 : term456 = term457.
Proof. exact (MK_COMB (@lem1543984) (@lem1543983)). Qed.
Lemma lem1543986 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1543987 (y : real) : (term453 y) = (term458 y).
Proof. exact (MK_COMB (@lem1543985) (@lem1543986 y)). Qed.
Lemma lem1543988 (y : real) : (term462 y) = (term458 y).
Proof. exact (TRANS (@lem1543980 y) (@lem1543987 y)). Qed.
Lemma lem1543989 (y : real) : (term458 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1543990 (y : real) : (term462 y) = term46.
Proof. exact (TRANS (@lem1543988 y) (@lem1543989 y)). Qed.
Lemma lem1543991 (x : real) (y : real) : (term461 x y) = term463.
Proof. exact (MK_COMB (@lem1543979 x) (@lem1543990 y)). Qed.
Lemma lem1543992 (x : real) (y : real) : (term460 x y) = term463.
Proof. exact (TRANS (@lem1543966 x y) (@lem1543991 x y)). Qed.
Lemma lem1543993 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1543994 (x : real) (y : real) : (term460 x y) = term46.
Proof. exact (TRANS (@lem1543992 x y) (@lem1543993)). Qed.
Lemma lem1543995 (h : real) (x : real) (y : real) : (term451 h x y) = term463.
Proof. exact (MK_COMB (@lem1543965 h) (@lem1543994 x y)). Qed.
Lemma lem1543996 (h : real) (x : real) (y : real) : (term450 h x y) = term463.
Proof. exact (TRANS (@lem1543952 h x y) (@lem1543995 h x y)). Qed.
Lemma lem1543997 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1543998 (h : real) (x : real) (y : real) : (term450 h x y) = term46.
Proof. exact (TRANS (@lem1543996 h x y) (@lem1543997)). Qed.
Lemma lem1543999 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544000 (h : real) (x : real) (y : real) : (term464 h x y) = term465.
Proof. exact (MK_COMB (@lem1543999) (@lem1543998 h x y)). Qed.
Lemma lem1544001 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544002 (h : real) (x : real) (y : real) : (term449 h x y) = term466.
Proof. exact (MK_COMB (@lem1544000 h x y) (@lem1544001)). Qed.
Lemma lem1544003 (h : real) (x : real) (y : real) (h1 : term420 h x y) : term466.
Proof. exact (EQ_MP (@lem1544002 h x y) (@lem1543951 h x y h1)). Qed.
Lemma lem1544005 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544006 : term466 = term467.
Proof. exact (@lem1544005 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1544007 : term467 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1544008 : term466 = False.
Proof. exact (TRANS (@lem1544006) (@lem1544007)). Qed.
Lemma lem1544009 (h : real) (x : real) (y : real) (h1 : term420 h x y) : False.
Proof. exact (EQ_MP (@lem1544008) (@lem1544003 h x y h1)). Qed.
Lemma lem1544010 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term424 h x y.
Proof. exact (h1). Qed.
Lemma lem1544011 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term423 h x y.
Proof. exact (proj2 (@lem1544010 h x y h1)). Qed.
Lemma lem1544013 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term422 h x y.
Proof. exact (proj2 (@lem1544011 h x y h1)). Qed.
Lemma lem1544015 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term394 h x y.
Proof. exact (proj2 (@lem1544013 h x y h1)). Qed.
Lemma lem1544016 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term203 h x y.
Proof. exact (proj1 (@lem1544013 h x y h1)). Qed.
Lemma lem1544017 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term201 h x y.
Proof. exact (proj2 (@lem1544016 h x y h1)). Qed.
Lemma lem1544021 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term191 h x y.
Proof. exact (proj2 (@lem1544017 h x y h1)). Qed.
Lemma lem1544024 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term381 h x y.
Proof. exact (proj1 (@lem1544015 h x y h1)). Qed.
Lemma lem1544026 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544027 : term430 = term431.
Proof. exact (@lem1544026 (NUMERAL 0) term159). Qed.
Lemma lem1544028 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1544029 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1544030 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1544029 h1) (fun h1 : term431 = True => @lem1544028)). Qed.
Lemma lem1544031 : term431 = True.
Proof. exact (EQ_MP (@lem1544030) (@lem1544028)). Qed.
Lemma lem1544032 : term430 = True.
Proof. exact (TRANS (@lem1544027) (@lem1544031)). Qed.
Lemma lem1544033 : True = term430.
Proof. exact (SYM (@lem1544032)). Qed.
Lemma lem1544034 : term430.
Proof. exact (EQ_MP (@lem1544033) (@lem0)). Qed.
Lemma lem1544035 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term468 h x y.
Proof. exact (conj (@lem1544034) (@lem1544024 h x y h1)). Qed.
Lemma lem1544037 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1544038 (h : real) (x : real) (y : real) : term469 h x y.
Proof. exact (@lem1544037 term436 (term229 h x y)). Qed.
Lemma lem1544039 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term470 h x y.
Proof. exact (@lem1544038 h x y (@lem1544035 h x y h1)). Qed.
Lemma lem1544040 (h : real) (x : real) (y : real) : (term471 h x y) = (term229 h x y).
Proof. exact (@lem1483460 (term229 h x y)). Qed.
Lemma lem1544041 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1544042 (h : real) (x : real) (y : real) : (term472 h x y) = (term380 h x y).
Proof. exact (MK_COMB (@lem1544041) (@lem1544040 h x y)). Qed.
Lemma lem1544043 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544044 (h : real) (x : real) (y : real) : (term470 h x y) = (term381 h x y).
Proof. exact (MK_COMB (@lem1544042 h x y) (@lem1544043)). Qed.
Lemma lem1544045 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term381 h x y.
Proof. exact (EQ_MP (@lem1544044 h x y) (@lem1544039 h x y h1)). Qed.
Lemma lem1544047 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544048 : term430 = term431.
Proof. exact (@lem1544047 (NUMERAL 0) term159). Qed.
Lemma lem1544049 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1544050 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1544051 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1544050 h1) (fun h1 : term431 = True => @lem1544049)). Qed.
Lemma lem1544052 : term431 = True.
Proof. exact (EQ_MP (@lem1544051) (@lem1544049)). Qed.
Lemma lem1544053 : term430 = True.
Proof. exact (TRANS (@lem1544048) (@lem1544052)). Qed.
Lemma lem1544054 : True = term430.
Proof. exact (SYM (@lem1544053)). Qed.
Lemma lem1544055 : term430.
Proof. exact (EQ_MP (@lem1544054) (@lem0)). Qed.
Lemma lem1544056 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term473 h x y.
Proof. exact (conj (@lem1544055) (@lem1544021 h x y h1)). Qed.
Lemma lem1544058 (x : real) (y : real) : term441 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1544059 (h : real) (x : real) (y : real) : term474 h x y.
Proof. exact (@lem1544058 term436 (term193 h x y)). Qed.
Lemma lem1544060 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term475 h x y.
Proof. exact (@lem1544059 h x y (@lem1544056 h x y h1)). Qed.
Lemma lem1544061 (h : real) (x : real) (y : real) : (term476 h x y) = (term193 h x y).
Proof. exact (@lem1483460 (term193 h x y)). Qed.
Lemma lem1544062 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544063 (h : real) (x : real) (y : real) : (term477 h x y) = (term199 h x y).
Proof. exact (MK_COMB (@lem1544062) (@lem1544061 h x y)). Qed.
Lemma lem1544064 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544065 (h : real) (x : real) (y : real) : (term475 h x y) = (term191 h x y).
Proof. exact (MK_COMB (@lem1544063 h x y) (@lem1544064)). Qed.
Lemma lem1544066 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term191 h x y.
Proof. exact (EQ_MP (@lem1544065 h x y) (@lem1544060 h x y h1)). Qed.
Lemma lem1544067 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term478 h x y.
Proof. exact (conj (@lem1544066 h x y h1) (@lem1544045 h x y h1)). Qed.
Lemma lem1544069 (x : real) (y : real) : term447 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1544070 (h : real) (x : real) (y : real) : term479 h x y.
Proof. exact (@lem1544069 (term193 h x y) (term229 h x y)). Qed.
Lemma lem1544071 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term480 h x y.
Proof. exact (@lem1544070 h x y (@lem1544067 h x y h1)). Qed.
Lemma lem1544072 (h : real) (x : real) (y : real) : (term481 h x y) = (term482 h x y).
Proof. exact (@lem1483480 h (term80 h) (real_add x y) (term228 x y)). Qed.
Lemma lem1544073 (h : real) : (term462 h) = (term453 h).
Proof. exact (@lem1483442 term367 h). Qed.
Lemma lem1544075 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544076 : term455 = term46.
Proof. exact (@lem1544075 term159). Qed.
Lemma lem1544077 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544078 : term456 = term457.
Proof. exact (MK_COMB (@lem1544077) (@lem1544076)). Qed.
Lemma lem1544079 (h : real) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1544080 (h : real) : (term453 h) = (term458 h).
Proof. exact (MK_COMB (@lem1544078) (@lem1544079 h)). Qed.
Lemma lem1544081 (h : real) : (term462 h) = (term458 h).
Proof. exact (TRANS (@lem1544073 h) (@lem1544080 h)). Qed.
Lemma lem1544082 (h : real) : (term458 h) = term46.
Proof. exact (@lem1483446 h). Qed.
Lemma lem1544083 (h : real) : (term462 h) = term46.
Proof. exact (TRANS (@lem1544081 h) (@lem1544082 h)). Qed.
Lemma lem1544084 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544085 (h : real) : (term483 h) = term368.
Proof. exact (MK_COMB (@lem1544084) (@lem1544083 h)). Qed.
Lemma lem1544086 (x : real) (y : real) : (term484 x y) = (term485 x y).
Proof. exact (@lem1483480 x (term80 x) y (term80 y)). Qed.
Lemma lem1544087 (x : real) : (term462 x) = (term453 x).
Proof. exact (@lem1483442 term367 x). Qed.
Lemma lem1544089 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544090 : term455 = term46.
Proof. exact (@lem1544089 term159). Qed.
Lemma lem1544091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544092 : term456 = term457.
Proof. exact (MK_COMB (@lem1544091) (@lem1544090)). Qed.
Lemma lem1544093 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1544094 (x : real) : (term453 x) = (term458 x).
Proof. exact (MK_COMB (@lem1544092) (@lem1544093 x)). Qed.
Lemma lem1544095 (x : real) : (term462 x) = (term458 x).
Proof. exact (TRANS (@lem1544087 x) (@lem1544094 x)). Qed.
Lemma lem1544096 (x : real) : (term458 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1544097 (x : real) : (term462 x) = term46.
Proof. exact (TRANS (@lem1544095 x) (@lem1544096 x)). Qed.
Lemma lem1544098 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544099 (x : real) : (term483 x) = term368.
Proof. exact (MK_COMB (@lem1544098) (@lem1544097 x)). Qed.
Lemma lem1544100 (y : real) : (term462 y) = (term453 y).
Proof. exact (@lem1483442 term367 y). Qed.
Lemma lem1544102 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544103 : term455 = term46.
Proof. exact (@lem1544102 term159). Qed.
Lemma lem1544104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544105 : term456 = term457.
Proof. exact (MK_COMB (@lem1544104) (@lem1544103)). Qed.
Lemma lem1544106 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544107 (y : real) : (term453 y) = (term458 y).
Proof. exact (MK_COMB (@lem1544105) (@lem1544106 y)). Qed.
Lemma lem1544108 (y : real) : (term462 y) = (term458 y).
Proof. exact (TRANS (@lem1544100 y) (@lem1544107 y)). Qed.
Lemma lem1544109 (y : real) : (term458 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1544110 (y : real) : (term462 y) = term46.
Proof. exact (TRANS (@lem1544108 y) (@lem1544109 y)). Qed.
Lemma lem1544111 (x : real) (y : real) : (term485 x y) = term463.
Proof. exact (MK_COMB (@lem1544099 x) (@lem1544110 y)). Qed.
Lemma lem1544112 (x : real) (y : real) : (term484 x y) = term463.
Proof. exact (TRANS (@lem1544086 x y) (@lem1544111 x y)). Qed.
Lemma lem1544113 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1544114 (x : real) (y : real) : (term484 x y) = term46.
Proof. exact (TRANS (@lem1544112 x y) (@lem1544113)). Qed.
Lemma lem1544115 (h : real) (x : real) (y : real) : (term482 h x y) = term463.
Proof. exact (MK_COMB (@lem1544085 h) (@lem1544114 x y)). Qed.
Lemma lem1544116 (h : real) (x : real) (y : real) : (term481 h x y) = term463.
Proof. exact (TRANS (@lem1544072 h x y) (@lem1544115 h x y)). Qed.
Lemma lem1544117 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1544118 (h : real) (x : real) (y : real) : (term481 h x y) = term46.
Proof. exact (TRANS (@lem1544116 h x y) (@lem1544117)). Qed.
Lemma lem1544119 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544120 (h : real) (x : real) (y : real) : (term486 h x y) = term465.
Proof. exact (MK_COMB (@lem1544119) (@lem1544118 h x y)). Qed.
Lemma lem1544121 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544122 (h : real) (x : real) (y : real) : (term480 h x y) = term466.
Proof. exact (MK_COMB (@lem1544120 h x y) (@lem1544121)). Qed.
Lemma lem1544123 (h : real) (x : real) (y : real) (h1 : term424 h x y) : term466.
Proof. exact (EQ_MP (@lem1544122 h x y) (@lem1544071 h x y h1)). Qed.
Lemma lem1544125 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544126 : term466 = term467.
Proof. exact (@lem1544125 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1544127 : term467 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1544128 : term466 = False.
Proof. exact (TRANS (@lem1544126) (@lem1544127)). Qed.
Lemma lem1544129 (h : real) (x : real) (y : real) (h1 : term424 h x y) : False.
Proof. exact (EQ_MP (@lem1544128) (@lem1544123 h x y h1)). Qed.
Lemma lem1544130 (h : real) (x : real) (y : real) (h1 : term426 h x y) : False.
Proof. exact (or_elim (@lem1543889 h x y h1) (fun h0 : term420 h x y => @lem1544009 h x y h0) (fun h0 : term424 h x y => @lem1544129 h x y h0)). Qed.
Lemma lem1544131 (h : real) (x : real) (y : real) (h1 : term401 h x y) : term401 h x y.
Proof. exact (h1). Qed.
Lemma lem1544132 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term360 h x y.
Proof. exact (h1). Qed.
Lemma lem1544133 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term359 h x y.
Proof. exact (proj2 (@lem1544132 h x y h1)). Qed.
Lemma lem1544135 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term358 h x y.
Proof. exact (proj2 (@lem1544133 h x y h1)). Qed.
Lemma lem1544137 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term356 h x y.
Proof. exact (proj2 (@lem1544135 h x y h1)). Qed.
Lemma lem1544138 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term295 h x y.
Proof. exact (proj1 (@lem1544135 h x y h1)). Qed.
Lemma lem1544140 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term259 h x y.
Proof. exact (proj1 (@lem1544138 h x y h1)). Qed.
Lemma lem1544142 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term239 h x y.
Proof. exact (proj1 (@lem1544140 h x y h1)). Qed.
Lemma lem1544145 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term348 h x y.
Proof. exact (proj2 (@lem1544137 h x y h1)). Qed.
Lemma lem1544148 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544149 : term430 = term431.
Proof. exact (@lem1544148 (NUMERAL 0) term159). Qed.
Lemma lem1544150 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1544151 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1544152 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1544151 h1) (fun h1 : term431 = True => @lem1544150)). Qed.
Lemma lem1544153 : term431 = True.
Proof. exact (EQ_MP (@lem1544152) (@lem1544150)). Qed.
Lemma lem1544154 : term430 = True.
Proof. exact (TRANS (@lem1544149) (@lem1544153)). Qed.
Lemma lem1544155 : True = term430.
Proof. exact (SYM (@lem1544154)). Qed.
Lemma lem1544156 : term430.
Proof. exact (EQ_MP (@lem1544155) (@lem0)). Qed.
Lemma lem1544157 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term487 h x y.
Proof. exact (conj (@lem1544156) (@lem1544145 h x y h1)). Qed.
Lemma lem1544159 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1544160 (h : real) (x : real) (y : real) : term488 h x y.
Proof. exact (@lem1544159 term436 (term193 h x y)). Qed.
Lemma lem1544161 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term489 h x y.
Proof. exact (@lem1544160 h x y (@lem1544157 h x y h1)). Qed.
Lemma lem1544162 (h : real) (x : real) (y : real) : (term476 h x y) = (term193 h x y).
Proof. exact (@lem1483460 (term193 h x y)). Qed.
Lemma lem1544163 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1544164 (h : real) (x : real) (y : real) : (term490 h x y) = (term352 h x y).
Proof. exact (MK_COMB (@lem1544163) (@lem1544162 h x y)). Qed.
Lemma lem1544165 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544166 (h : real) (x : real) (y : real) : (term489 h x y) = (term348 h x y).
Proof. exact (MK_COMB (@lem1544164 h x y) (@lem1544165)). Qed.
Lemma lem1544167 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term348 h x y.
Proof. exact (EQ_MP (@lem1544166 h x y) (@lem1544161 h x y h1)). Qed.
Lemma lem1544169 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544170 : term430 = term431.
Proof. exact (@lem1544169 (NUMERAL 0) term159). Qed.
Lemma lem1544171 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1544172 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1544173 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1544172 h1) (fun h1 : term431 = True => @lem1544171)). Qed.
Lemma lem1544174 : term431 = True.
Proof. exact (EQ_MP (@lem1544173) (@lem1544171)). Qed.
Lemma lem1544175 : term430 = True.
Proof. exact (TRANS (@lem1544170) (@lem1544174)). Qed.
Lemma lem1544176 : True = term430.
Proof. exact (SYM (@lem1544175)). Qed.
Lemma lem1544177 : term430.
Proof. exact (EQ_MP (@lem1544176) (@lem0)). Qed.
Lemma lem1544178 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term491 h x y.
Proof. exact (conj (@lem1544177) (@lem1544142 h x y h1)). Qed.
Lemma lem1544180 (x : real) (y : real) : term441 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1544181 (h : real) (x : real) (y : real) : term492 h x y.
Proof. exact (@lem1544180 term436 (term229 h x y)). Qed.
Lemma lem1544182 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term493 h x y.
Proof. exact (@lem1544181 h x y (@lem1544178 h x y h1)). Qed.
Lemma lem1544183 (h : real) (x : real) (y : real) : (term471 h x y) = (term229 h x y).
Proof. exact (@lem1483460 (term229 h x y)). Qed.
Lemma lem1544184 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544185 (h : real) (x : real) (y : real) : (term494 h x y) = (term238 h x y).
Proof. exact (MK_COMB (@lem1544184) (@lem1544183 h x y)). Qed.
Lemma lem1544186 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544187 (h : real) (x : real) (y : real) : (term493 h x y) = (term239 h x y).
Proof. exact (MK_COMB (@lem1544185 h x y) (@lem1544186)). Qed.
Lemma lem1544188 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term239 h x y.
Proof. exact (EQ_MP (@lem1544187 h x y) (@lem1544182 h x y h1)). Qed.
Lemma lem1544189 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term495 h x y.
Proof. exact (conj (@lem1544188 h x y h1) (@lem1544167 h x y h1)). Qed.
Lemma lem1544191 (x : real) (y : real) : term447 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1544192 (h : real) (x : real) (y : real) : term496 h x y.
Proof. exact (@lem1544191 (term229 h x y) (term193 h x y)). Qed.
Lemma lem1544193 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term497 h x y.
Proof. exact (@lem1544192 h x y (@lem1544189 h x y h1)). Qed.
Lemma lem1544194 (h : real) (x : real) (y : real) : (term498 h x y) = (term499 h x y).
Proof. exact (@lem1483480 (term80 h) h (term228 x y) (real_add x y)). Qed.
Lemma lem1544195 (h : real) : (term452 h) = (term453 h).
Proof. exact (@lem1483440 term367 h). Qed.
Lemma lem1544197 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544198 : term455 = term46.
Proof. exact (@lem1544197 term159). Qed.
Lemma lem1544199 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544200 : term456 = term457.
Proof. exact (MK_COMB (@lem1544199) (@lem1544198)). Qed.
Lemma lem1544201 (h : real) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1544202 (h : real) : (term453 h) = (term458 h).
Proof. exact (MK_COMB (@lem1544200) (@lem1544201 h)). Qed.
Lemma lem1544203 (h : real) : (term452 h) = (term458 h).
Proof. exact (TRANS (@lem1544195 h) (@lem1544202 h)). Qed.
Lemma lem1544204 (h : real) : (term458 h) = term46.
Proof. exact (@lem1483446 h). Qed.
Lemma lem1544205 (h : real) : (term452 h) = term46.
Proof. exact (TRANS (@lem1544203 h) (@lem1544204 h)). Qed.
Lemma lem1544206 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544207 (h : real) : (term459 h) = term368.
Proof. exact (MK_COMB (@lem1544206) (@lem1544205 h)). Qed.
Lemma lem1544208 (x : real) (y : real) : (term500 x y) = (term501 x y).
Proof. exact (@lem1483480 (term80 x) x (term80 y) y). Qed.
Lemma lem1544209 (x : real) : (term452 x) = (term453 x).
Proof. exact (@lem1483440 term367 x). Qed.
Lemma lem1544211 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544212 : term455 = term46.
Proof. exact (@lem1544211 term159). Qed.
Lemma lem1544213 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544214 : term456 = term457.
Proof. exact (MK_COMB (@lem1544213) (@lem1544212)). Qed.
Lemma lem1544215 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1544216 (x : real) : (term453 x) = (term458 x).
Proof. exact (MK_COMB (@lem1544214) (@lem1544215 x)). Qed.
Lemma lem1544217 (x : real) : (term452 x) = (term458 x).
Proof. exact (TRANS (@lem1544209 x) (@lem1544216 x)). Qed.
Lemma lem1544218 (x : real) : (term458 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1544219 (x : real) : (term452 x) = term46.
Proof. exact (TRANS (@lem1544217 x) (@lem1544218 x)). Qed.
Lemma lem1544220 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544221 (x : real) : (term459 x) = term368.
Proof. exact (MK_COMB (@lem1544220) (@lem1544219 x)). Qed.
Lemma lem1544222 (y : real) : (term452 y) = (term453 y).
Proof. exact (@lem1483440 term367 y). Qed.
Lemma lem1544224 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544225 : term455 = term46.
Proof. exact (@lem1544224 term159). Qed.
Lemma lem1544226 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544227 : term456 = term457.
Proof. exact (MK_COMB (@lem1544226) (@lem1544225)). Qed.
Lemma lem1544228 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544229 (y : real) : (term453 y) = (term458 y).
Proof. exact (MK_COMB (@lem1544227) (@lem1544228 y)). Qed.
Lemma lem1544230 (y : real) : (term452 y) = (term458 y).
Proof. exact (TRANS (@lem1544222 y) (@lem1544229 y)). Qed.
Lemma lem1544231 (y : real) : (term458 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1544232 (y : real) : (term452 y) = term46.
Proof. exact (TRANS (@lem1544230 y) (@lem1544231 y)). Qed.
Lemma lem1544233 (x : real) (y : real) : (term501 x y) = term463.
Proof. exact (MK_COMB (@lem1544221 x) (@lem1544232 y)). Qed.
Lemma lem1544234 (x : real) (y : real) : (term500 x y) = term463.
Proof. exact (TRANS (@lem1544208 x y) (@lem1544233 x y)). Qed.
Lemma lem1544235 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1544236 (x : real) (y : real) : (term500 x y) = term46.
Proof. exact (TRANS (@lem1544234 x y) (@lem1544235)). Qed.
Lemma lem1544237 (h : real) (x : real) (y : real) : (term499 h x y) = term463.
Proof. exact (MK_COMB (@lem1544207 h) (@lem1544236 x y)). Qed.
Lemma lem1544238 (h : real) (x : real) (y : real) : (term498 h x y) = term463.
Proof. exact (TRANS (@lem1544194 h x y) (@lem1544237 h x y)). Qed.
Lemma lem1544239 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1544240 (h : real) (x : real) (y : real) : (term498 h x y) = term46.
Proof. exact (TRANS (@lem1544238 h x y) (@lem1544239)). Qed.
Lemma lem1544241 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544242 (h : real) (x : real) (y : real) : (term502 h x y) = term465.
Proof. exact (MK_COMB (@lem1544241) (@lem1544240 h x y)). Qed.
Lemma lem1544243 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544244 (h : real) (x : real) (y : real) : (term497 h x y) = term466.
Proof. exact (MK_COMB (@lem1544242 h x y) (@lem1544243)). Qed.
Lemma lem1544245 (h : real) (x : real) (y : real) (h1 : term360 h x y) : term466.
Proof. exact (EQ_MP (@lem1544244 h x y) (@lem1544193 h x y h1)). Qed.
Lemma lem1544247 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544248 : term466 = term467.
Proof. exact (@lem1544247 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1544249 : term467 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1544250 : term466 = False.
Proof. exact (TRANS (@lem1544248) (@lem1544249)). Qed.
Lemma lem1544251 (h : real) (x : real) (y : real) (h1 : term360 h x y) : False.
Proof. exact (EQ_MP (@lem1544250) (@lem1544245 h x y h1)). Qed.
Lemma lem1544252 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term399 h x y.
Proof. exact (h1). Qed.
Lemma lem1544253 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term397 h x y.
Proof. exact (proj2 (@lem1544252 h x y h1)). Qed.
Lemma lem1544255 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term396 h x y.
Proof. exact (proj2 (@lem1544253 h x y h1)). Qed.
Lemma lem1544257 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term394 h x y.
Proof. exact (proj2 (@lem1544255 h x y h1)). Qed.
Lemma lem1544258 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term295 h x y.
Proof. exact (proj1 (@lem1544255 h x y h1)). Qed.
Lemma lem1544259 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term291 h x y.
Proof. exact (proj2 (@lem1544258 h x y h1)). Qed.
Lemma lem1544263 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term287 h x y.
Proof. exact (proj2 (@lem1544259 h x y h1)). Qed.
Lemma lem1544265 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term390 h x y.
Proof. exact (proj2 (@lem1544257 h x y h1)). Qed.
Lemma lem1544268 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544269 : term430 = term431.
Proof. exact (@lem1544268 (NUMERAL 0) term159). Qed.
Lemma lem1544270 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1544271 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1544272 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1544271 h1) (fun h1 : term431 = True => @lem1544270)). Qed.
Lemma lem1544273 : term431 = True.
Proof. exact (EQ_MP (@lem1544272) (@lem1544270)). Qed.
Lemma lem1544274 : term430 = True.
Proof. exact (TRANS (@lem1544269) (@lem1544273)). Qed.
Lemma lem1544275 : True = term430.
Proof. exact (SYM (@lem1544274)). Qed.
Lemma lem1544276 : term430.
Proof. exact (EQ_MP (@lem1544275) (@lem0)). Qed.
Lemma lem1544277 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term503 h x y.
Proof. exact (conj (@lem1544276) (@lem1544265 h x y h1)). Qed.
Lemma lem1544279 (x : real) (y : real) : term434 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1544280 (h : real) (x : real) (y : real) : term504 h x y.
Proof. exact (@lem1544279 term436 (term164 h x y)). Qed.
Lemma lem1544281 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term505 h x y.
Proof. exact (@lem1544280 h x y (@lem1544277 h x y h1)). Qed.
Lemma lem1544282 (h : real) (x : real) (y : real) : (term444 h x y) = (term164 h x y).
Proof. exact (@lem1483460 (term164 h x y)). Qed.
Lemma lem1544283 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1544284 (h : real) (x : real) (y : real) : (term506 h x y) = (term389 h x y).
Proof. exact (MK_COMB (@lem1544283) (@lem1544282 h x y)). Qed.
Lemma lem1544285 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544286 (h : real) (x : real) (y : real) : (term505 h x y) = (term390 h x y).
Proof. exact (MK_COMB (@lem1544284 h x y) (@lem1544285)). Qed.
Lemma lem1544287 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term390 h x y.
Proof. exact (EQ_MP (@lem1544286 h x y) (@lem1544281 h x y h1)). Qed.
Lemma lem1544289 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544290 : term430 = term431.
Proof. exact (@lem1544289 (NUMERAL 0) term159). Qed.
Lemma lem1544291 : term432 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1544292 (h1 : term432 = (BIT1 0)) : term431 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1544293 : (term432 = (BIT1 0)) = (term431 = True).
Proof. exact (prop_ext (fun h1 : term432 = (BIT1 0) => @lem1544292 h1) (fun h1 : term431 = True => @lem1544291)). Qed.
Lemma lem1544294 : term431 = True.
Proof. exact (EQ_MP (@lem1544293) (@lem1544291)). Qed.
Lemma lem1544295 : term430 = True.
Proof. exact (TRANS (@lem1544290) (@lem1544294)). Qed.
Lemma lem1544296 : True = term430.
Proof. exact (SYM (@lem1544295)). Qed.
Lemma lem1544297 : term430.
Proof. exact (EQ_MP (@lem1544296) (@lem0)). Qed.
Lemma lem1544298 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term507 h x y.
Proof. exact (conj (@lem1544297) (@lem1544263 h x y h1)). Qed.
Lemma lem1544300 (x : real) (y : real) : term441 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1544301 (h : real) (x : real) (y : real) : term508 h x y.
Proof. exact (@lem1544300 term436 (term277 h x y)). Qed.
Lemma lem1544302 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term509 h x y.
Proof. exact (@lem1544301 h x y (@lem1544298 h x y h1)). Qed.
Lemma lem1544303 (h : real) (x : real) (y : real) : (term438 h x y) = (term277 h x y).
Proof. exact (@lem1483460 (term277 h x y)). Qed.
Lemma lem1544304 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544305 (h : real) (x : real) (y : real) : (term510 h x y) = (term286 h x y).
Proof. exact (MK_COMB (@lem1544304) (@lem1544303 h x y)). Qed.
Lemma lem1544306 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544307 (h : real) (x : real) (y : real) : (term509 h x y) = (term287 h x y).
Proof. exact (MK_COMB (@lem1544305 h x y) (@lem1544306)). Qed.
Lemma lem1544308 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term287 h x y.
Proof. exact (EQ_MP (@lem1544307 h x y) (@lem1544302 h x y h1)). Qed.
Lemma lem1544309 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term511 h x y.
Proof. exact (conj (@lem1544308 h x y h1) (@lem1544287 h x y h1)). Qed.
Lemma lem1544311 (x : real) (y : real) : term447 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1544312 (h : real) (x : real) (y : real) : term512 h x y.
Proof. exact (@lem1544311 (term277 h x y) (term164 h x y)). Qed.
Lemma lem1544313 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term513 h x y.
Proof. exact (@lem1544312 h x y (@lem1544309 h x y h1)). Qed.
Lemma lem1544314 (h : real) (x : real) (y : real) : (term514 h x y) = (term515 h x y).
Proof. exact (@lem1483480 h (term80 h) (term244 x y) (term343 x y)). Qed.
Lemma lem1544315 (h : real) : (term462 h) = (term453 h).
Proof. exact (@lem1483442 term367 h). Qed.
Lemma lem1544317 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544318 : term455 = term46.
Proof. exact (@lem1544317 term159). Qed.
Lemma lem1544319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544320 : term456 = term457.
Proof. exact (MK_COMB (@lem1544319) (@lem1544318)). Qed.
Lemma lem1544321 (h : real) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1544322 (h : real) : (term453 h) = (term458 h).
Proof. exact (MK_COMB (@lem1544320) (@lem1544321 h)). Qed.
Lemma lem1544323 (h : real) : (term462 h) = (term458 h).
Proof. exact (TRANS (@lem1544315 h) (@lem1544322 h)). Qed.
Lemma lem1544324 (h : real) : (term458 h) = term46.
Proof. exact (@lem1483446 h). Qed.
Lemma lem1544325 (h : real) : (term462 h) = term46.
Proof. exact (TRANS (@lem1544323 h) (@lem1544324 h)). Qed.
Lemma lem1544326 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544327 (h : real) : (term483 h) = term368.
Proof. exact (MK_COMB (@lem1544326) (@lem1544325 h)). Qed.
Lemma lem1544328 (x : real) (y : real) : (term516 x y) = (term517 x y).
Proof. exact (@lem1483480 x (term80 x) (term80 y) y). Qed.
Lemma lem1544329 (x : real) : (term462 x) = (term453 x).
Proof. exact (@lem1483442 term367 x). Qed.
Lemma lem1544331 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544332 : term455 = term46.
Proof. exact (@lem1544331 term159). Qed.
Lemma lem1544333 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544334 : term456 = term457.
Proof. exact (MK_COMB (@lem1544333) (@lem1544332)). Qed.
Lemma lem1544335 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1544336 (x : real) : (term453 x) = (term458 x).
Proof. exact (MK_COMB (@lem1544334) (@lem1544335 x)). Qed.
Lemma lem1544337 (x : real) : (term462 x) = (term458 x).
Proof. exact (TRANS (@lem1544329 x) (@lem1544336 x)). Qed.
Lemma lem1544338 (x : real) : (term458 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1544339 (x : real) : (term462 x) = term46.
Proof. exact (TRANS (@lem1544337 x) (@lem1544338 x)). Qed.
Lemma lem1544340 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544341 (x : real) : (term483 x) = term368.
Proof. exact (MK_COMB (@lem1544340) (@lem1544339 x)). Qed.
Lemma lem1544342 (y : real) : (term452 y) = (term453 y).
Proof. exact (@lem1483440 term367 y). Qed.
Lemma lem1544344 (m : nat) : (term454 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544345 : term455 = term46.
Proof. exact (@lem1544344 term159). Qed.
Lemma lem1544346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544347 : term456 = term457.
Proof. exact (MK_COMB (@lem1544346) (@lem1544345)). Qed.
Lemma lem1544348 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544349 (y : real) : (term453 y) = (term458 y).
Proof. exact (MK_COMB (@lem1544347) (@lem1544348 y)). Qed.
Lemma lem1544350 (y : real) : (term452 y) = (term458 y).
Proof. exact (TRANS (@lem1544342 y) (@lem1544349 y)). Qed.
Lemma lem1544351 (y : real) : (term458 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1544352 (y : real) : (term452 y) = term46.
Proof. exact (TRANS (@lem1544350 y) (@lem1544351 y)). Qed.
Lemma lem1544353 (x : real) (y : real) : (term517 x y) = term463.
Proof. exact (MK_COMB (@lem1544341 x) (@lem1544352 y)). Qed.
Lemma lem1544354 (x : real) (y : real) : (term516 x y) = term463.
Proof. exact (TRANS (@lem1544328 x y) (@lem1544353 x y)). Qed.
Lemma lem1544355 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1544356 (x : real) (y : real) : (term516 x y) = term46.
Proof. exact (TRANS (@lem1544354 x y) (@lem1544355)). Qed.
Lemma lem1544357 (h : real) (x : real) (y : real) : (term515 h x y) = term463.
Proof. exact (MK_COMB (@lem1544327 h) (@lem1544356 x y)). Qed.
Lemma lem1544358 (h : real) (x : real) (y : real) : (term514 h x y) = term463.
Proof. exact (TRANS (@lem1544314 h x y) (@lem1544357 h x y)). Qed.
Lemma lem1544359 : term463 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1544360 (h : real) (x : real) (y : real) : (term514 h x y) = term46.
Proof. exact (TRANS (@lem1544358 h x y) (@lem1544359)). Qed.
Lemma lem1544361 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544362 (h : real) (x : real) (y : real) : (term518 h x y) = term465.
Proof. exact (MK_COMB (@lem1544361) (@lem1544360 h x y)). Qed.
Lemma lem1544363 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1544364 (h : real) (x : real) (y : real) : (term513 h x y) = term466.
Proof. exact (MK_COMB (@lem1544362 h x y) (@lem1544363)). Qed.
Lemma lem1544365 (h : real) (x : real) (y : real) (h1 : term399 h x y) : term466.
Proof. exact (EQ_MP (@lem1544364 h x y) (@lem1544313 h x y h1)). Qed.
Lemma lem1544367 (n : nat) (m : nat) : (term429 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1544368 : term466 = term467.
Proof. exact (@lem1544367 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1544369 : term467 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1544370 : term466 = False.
Proof. exact (TRANS (@lem1544368) (@lem1544369)). Qed.
Lemma lem1544371 (h : real) (x : real) (y : real) (h1 : term399 h x y) : False.
Proof. exact (EQ_MP (@lem1544370) (@lem1544365 h x y h1)). Qed.
Lemma lem1544372 (h : real) (x : real) (y : real) (h1 : term401 h x y) : False.
Proof. exact (or_elim (@lem1544131 h x y h1) (fun h0 : term360 h x y => @lem1544251 h x y h0) (fun h0 : term399 h x y => @lem1544371 h x y h0)). Qed.
Lemma lem1544373 (h : real) (x : real) (y : real) (h1 : term428 h x y) : False.
Proof. exact (or_elim (@lem1543888 h x y h1) (fun h0 : term426 h x y => @lem1544130 h x y h0) (fun h0 : term401 h x y => @lem1544372 h x y h0)). Qed.
Lemma lem1544374 (y : real) (x : real) (h : real) (h1 : term59 y x h) : term59 y x h.
Proof. exact (h1). Qed.
Lemma lem1544375 (y : real) (x : real) (h : real) (h1 : term59 y x h) : term428 h x y.
Proof. exact (EQ_MP (@lem1543887 h x y) (@lem1544374 y x h h1)). Qed.
Lemma lem1544376 (y : real) (x : real) (h : real) (h1 : term59 y x h) : (term428 h x y) = False.
Proof. exact (prop_ext (fun h2 : term428 h x y => @lem1544373 h x y h2) (fun h2 : False => @lem1544375 y x h h1)). Qed.
Lemma lem1544377 (y : real) (x : real) (h : real) (h1 : term59 y x h) : False.
Proof. exact (EQ_MP (@lem1544376 y x h h1) (@lem1544375 y x h h1)). Qed.
Lemma lem1544378 (y : real) (x : real) (h1 : term61 y x) : term61 y x.
Proof. exact (h1). Qed.
Lemma lem1544379 (y : real) (x : real) (h1 : term61 y x) : False.
Proof. exact (ex_elim (@lem1544378 y x h1) (fun h : real => fun h0 : term60 y x h => @lem1544377 y x h h0)). Qed.
Lemma lem1544380 (x : real) (h1 : term63 x) : term63 x.
Proof. exact (h1). Qed.
Lemma lem1544381 (x : real) (h1 : term63 x) : False.
Proof. exact (ex_elim (@lem1544380 x h1) (fun y : real => fun h0 : term62 x y => @lem1544379 y x h0)). Qed.
Lemma lem1544382 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1544383 (h1 : term65) : False.
Proof. exact (ex_elim (@lem1544382 h1) (fun x : real => fun h0 : term64 x => @lem1544381 x h0)). Qed.
Lemma lem1544384 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1544385 (h1 : term24) : term65.
Proof. exact (EQ_MP (@lem1542562) (@lem1544384 h1)). Qed.
Lemma lem1544386 (h1 : term24) : term65 = False.
Proof. exact (prop_ext (fun h2 : term65 => @lem1544383 h2) (fun h2 : False => @lem1544385 h1)). Qed.
Lemma lem1544387 (h1 : term24) : False.
Proof. exact (EQ_MP (@lem1544386 h1) (@lem1544385 h1)). Qed.
Lemma lem1544388 : term519.
Proof. exact (fun h0 : term24 => @lem1544387 h0). Qed.
Lemma lem1544389 : term520.
Proof. exact (@lem1386578 term521). Qed.
Lemma lem1544390 : term521.
Proof. exact (@lem1544389 (@lem1544388)). Qed.
