Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_ABS_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482705_spec.
Require Import thm1482706_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Require Import thm940073_spec.
Lemma lem1544403 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1544404 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1544403 (term4 x)). Qed.
Lemma lem1544405 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1544406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1544408 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1544406) (@lem1544405 x y)). Qed.
Lemma lem1544409 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1544408 x y)). Qed.
Lemma lem1544410 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544411 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1544410) (@lem1544409 x)). Qed.
Lemma lem1544412 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1544404 x) (@lem1544411 x)). Qed.
Lemma lem1544413 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1544414 : term12 = term13.
Proof. exact (@lem1544413 term14). Qed.
Lemma lem1544415 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1544416 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1544417 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1544416) (@lem1544415 x)). Qed.
Lemma lem1544418 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1544417 x) (@lem1544412 x)). Qed.
Lemma lem1544419 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1544418 x)). Qed.
Lemma lem1544420 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544421 : term13 = term20.
Proof. exact (MK_COMB (@lem1544420) (@lem1544419)). Qed.
Lemma lem1544423 : term12 = term20.
Proof. exact (TRANS (@lem1544414) (@lem1544421)). Qed.
Lemma lem1544426 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1544427 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1544426 x y)). Qed.
Lemma lem1544428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544429 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1544428) (@lem1544427 x)). Qed.
Lemma lem1544430 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1544429 x)). Qed.
Lemma lem1544431 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544432 : term20 = term20.
Proof. exact (MK_COMB (@lem1544431) (@lem1544430)). Qed.
Lemma lem1544433 : term12 = term20.
Proof. exact (TRANS (@lem1544423) (@lem1544432)). Qed.
Lemma lem1544434 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483533 (term22 x y) (term23 x y)). Qed.
Lemma lem1544435 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1544448 (x : real) (y : real) : (term22 x y) = (term24 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1544449 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1544450 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1544449) (@lem1544448 x y)). Qed.
Lemma lem1544451 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1544450 x y) (@lem1544435 x y)). Qed.
Lemma lem1544452 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (@lem1483519 (term24 x y) (term23 x y)). Qed.
Lemma lem1544461 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (@lem1483482 (real_abs x) (term31 y) (term32 x y)). Qed.
Lemma lem1544462 (x : real) (y : real) : (term28 x y) = (term30 x y).
Proof. exact (TRANS (@lem1544452 x y) (@lem1544461 x y)). Qed.
Lemma lem1544463 (x : real) (y : real) : (term27 x y) = (term30 x y).
Proof. exact (TRANS (@lem1544451 x y) (@lem1544462 x y)). Qed.
Lemma lem1544464 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544465 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1544464) (@lem1544463 x y)). Qed.
Lemma lem1544466 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544467 (x : real) (y : real) : (term21 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1544465 x y) (@lem1544466)). Qed.
Lemma lem1544468 (x : real) (y : real) : (term8 x y) = (term36 x y).
Proof. exact (TRANS (@lem1544434 x y) (@lem1544467 x y)). Qed.
Lemma lem1544469 (x : real) : (term10 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1544468 x y)). Qed.
Lemma lem1544470 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544471 (x : real) : (term11 x) = (term38 x).
Proof. exact (MK_COMB (@lem1544470) (@lem1544469 x)). Qed.
Lemma lem1544472 : term19 = term39.
Proof. exact (fun_ext (fun x : real => @lem1544471 x)). Qed.
Lemma lem1544473 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544474 : term20 = term40.
Proof. exact (MK_COMB (@lem1544473) (@lem1544472)). Qed.
Lemma lem1544489 : term12 = term40.
Proof. exact (TRANS (@lem1544433) (@lem1544474)). Qed.
Lemma lem1544490 (x : real) (y : real) : (term36 x y) = (term36 x y).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1544491 (x : real) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1544490 x y)). Qed.
Lemma lem1544492 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544493 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1544492) (@lem1544491 x)). Qed.
Lemma lem1544494 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1544493 x)). Qed.
Lemma lem1544495 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1544496 : term40 = term40.
Proof. exact (MK_COMB (@lem1544495) (@lem1544494)). Qed.
Lemma lem1544497 : term12 = term40.
Proof. exact (TRANS (@lem1544489) (@lem1544496)). Qed.
Lemma lem1544499 (a : real) (x : real) (b : real) (r : real) : (term41 a x b r) = (term42 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem1544500 (x : real) (y : real) : (term36 x y) = (term43 x y).
Proof. exact (@lem1544499 (real_abs x) y (term32 x y) term35). Qed.
Lemma lem1544507 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1544514 (y : real) : (term44 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1544515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544516 (y : real) : (term45 y) = (real_add y).
Proof. exact (MK_COMB (@lem1544515) (@lem1544514 y)). Qed.
Lemma lem1544519 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1544516 y) (@lem1544507 x y)). Qed.
Lemma lem1544522 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1544523 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1544522 x) (@lem1544519 x y)). Qed.
Lemma lem1544528 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (@lem1483484 y (real_abs x) (term32 x y)). Qed.
Lemma lem1544529 (x : real) (y : real) : (term49 x y) = (term51 x y).
Proof. exact (TRANS (@lem1544523 x y) (@lem1544528 x y)). Qed.
Lemma lem1544530 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544531 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1544530) (@lem1544529 x y)). Qed.
Lemma lem1544532 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544533 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1544531 x y) (@lem1544532)). Qed.
Lemma lem1544562 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (@lem1483484 (term58 y) (real_abs x) (term32 x y)). Qed.
Lemma lem1544563 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544564 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1544563) (@lem1544562 x y)). Qed.
Lemma lem1544565 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544566 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1544564 x y) (@lem1544565)). Qed.
Lemma lem1544567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1544568 (x : real) (y : real) : (term63 x y) = (term64 x y).
Proof. exact (MK_COMB (@lem1544567) (@lem1544566 x y)). Qed.
Lemma lem1544569 (x : real) (y : real) : (term43 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1544568 x y) (@lem1544533 x y)). Qed.
Lemma lem1544570 (x : real) (y : real) : (term36 x y) = (term65 x y).
Proof. exact (TRANS (@lem1544500 x y) (@lem1544569 x y)). Qed.
Lemma lem1544572 (a : real) (b : real) (x : real) (r : real) : (term66 a b x r) = (term67 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1544573 (x : real) (y : real) : (term62 x y) = (term68 x y).
Proof. exact (@lem1544572 (term58 y) (real_abs x) (real_sub x y) term35). Qed.
Lemma lem1544586 (x : real) (y : real) : (real_sub x y) = (term69 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1544589 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem1544590 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1544589) (@lem1544586 x y)). Qed.
Lemma lem1544591 (x : real) (y : real) : (term72 x y) = (term69 x y).
Proof. exact (@lem1483460 (term69 x y)). Qed.
Lemma lem1544592 (x : real) (y : real) : (term71 x y) = (term69 x y).
Proof. exact (TRANS (@lem1544590 x y) (@lem1544591 x y)). Qed.
Lemma lem1544595 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1544596 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1544595 x) (@lem1544592 x y)). Qed.
Lemma lem1544597 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (@lem1483484 x (real_abs x) (term58 y)). Qed.
Lemma lem1544598 (y : real) (x : real) : (term76 x y) = (term77 y x).
Proof. exact (@lem1483488 (term58 y) (real_abs x)). Qed.
Lemma lem1544599 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1544600 (y : real) (x : real) : (term75 x y) = (term78 y x).
Proof. exact (MK_COMB (@lem1544599 x) (@lem1544598 y x)). Qed.
Lemma lem1544601 (y : real) (x : real) : (term74 x y) = (term78 y x).
Proof. exact (TRANS (@lem1544597 x y) (@lem1544600 y x)). Qed.
Lemma lem1544602 (y : real) (x : real) : (term73 x y) = (term78 y x).
Proof. exact (TRANS (@lem1544596 x y) (@lem1544601 y x)). Qed.
Lemma lem1544611 (y : real) : (term79 y) = (term79 y).
Proof. exact (eq_refl (term79 y)). Qed.
Lemma lem1544612 (y : real) (x : real) : (term80 x y) = (term81 y x).
Proof. exact (MK_COMB (@lem1544611 y) (@lem1544602 y x)). Qed.
Lemma lem1544613 (y : real) (x : real) : (term81 y x) = (term82 y x).
Proof. exact (@lem1483484 x (term58 y) (term77 y x)). Qed.
Lemma lem1544614 (y : real) (x : real) : (term83 y x) = (term84 y x).
Proof. exact (@lem1483490 (term58 y) (term58 y) (real_abs x)). Qed.
Lemma lem1544615 (y : real) : (term85 y) = (term86 y).
Proof. exact (@lem1483438 term87 term87 y). Qed.
Lemma lem1544616 : term88 = term89.
Proof. exact (@lem1367763 term90 term90). Qed.
Lemma lem1544617 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1544618 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1544619 : term93 = term94.
Proof. exact (EQ_MP (@lem1544618) (@lem1544617)). Qed.
Lemma lem1544620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1544621 : term95 = term96.
Proof. exact (MK_COMB (@lem1544620) (@lem1544619)). Qed.
Lemma lem1544622 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1544623 : term89 = term97.
Proof. exact (MK_COMB (@lem1544622) (@lem1544621)). Qed.
Lemma lem1544624 : term88 = term97.
Proof. exact (TRANS (@lem1544616) (@lem1544623)). Qed.
Lemma lem1544625 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544626 : term98 = term99.
Proof. exact (MK_COMB (@lem1544625) (@lem1544624)). Qed.
Lemma lem1544627 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544628 (y : real) : (term86 y) = (term100 y).
Proof. exact (MK_COMB (@lem1544626) (@lem1544627 y)). Qed.
Lemma lem1544629 (y : real) : (term85 y) = (term100 y).
Proof. exact (TRANS (@lem1544615 y) (@lem1544628 y)). Qed.
Lemma lem1544630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544631 (y : real) : (term101 y) = (term102 y).
Proof. exact (MK_COMB (@lem1544630) (@lem1544629 y)). Qed.
Lemma lem1544632 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1544633 (y : real) (x : real) : (term84 y x) = (term103 y x).
Proof. exact (MK_COMB (@lem1544631 y) (@lem1544632 x)). Qed.
Lemma lem1544634 (y : real) (x : real) : (term83 y x) = (term103 y x).
Proof. exact (TRANS (@lem1544614 y x) (@lem1544633 y x)). Qed.
Lemma lem1544635 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1544636 (y : real) (x : real) : (term82 y x) = (term104 y x).
Proof. exact (MK_COMB (@lem1544635 x) (@lem1544634 y x)). Qed.
Lemma lem1544637 (y : real) (x : real) : (term81 y x) = (term104 y x).
Proof. exact (TRANS (@lem1544613 y x) (@lem1544636 y x)). Qed.
Lemma lem1544638 (y : real) (x : real) : (term80 x y) = (term104 y x).
Proof. exact (TRANS (@lem1544612 y x) (@lem1544637 y x)). Qed.
Lemma lem1544639 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544640 (y : real) (x : real) : (term105 x y) = (term106 y x).
Proof. exact (MK_COMB (@lem1544639) (@lem1544638 y x)). Qed.
Lemma lem1544641 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544642 (y : real) (x : real) : (term107 x y) = (term108 y x).
Proof. exact (MK_COMB (@lem1544640 y x) (@lem1544641)). Qed.
Lemma lem1544655 (x : real) (y : real) : (real_sub x y) = (term69 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1544658 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1544659 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1544658) (@lem1544655 x y)). Qed.
Lemma lem1544660 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (@lem1483508 x term87 (term58 y)). Qed.
Lemma lem1544661 (y : real) : (term113 y) = (term114 y).
Proof. exact (@lem1483476 term87 term87 y). Qed.
Lemma lem1544663 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1544664 : term117 = term118.
Proof. exact (@lem1544663 term90 term90). Qed.
Lemma lem1544665 : (term119 = (BIT1 0)) = (term120 = term90).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1544666 : term120 = term90.
Proof. exact (EQ_MP (@lem1544665) (@lem940073)). Qed.
Lemma lem1544667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1544668 : term118 = term121.
Proof. exact (MK_COMB (@lem1544667) (@lem1544666)). Qed.
Lemma lem1544669 : term117 = term121.
Proof. exact (TRANS (@lem1544664) (@lem1544668)). Qed.
Lemma lem1544670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544671 : term122 = term70.
Proof. exact (MK_COMB (@lem1544670) (@lem1544669)). Qed.
Lemma lem1544672 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544673 (y : real) : (term114 y) = (term44 y).
Proof. exact (MK_COMB (@lem1544671) (@lem1544672 y)). Qed.
Lemma lem1544674 (y : real) : (term113 y) = (term44 y).
Proof. exact (TRANS (@lem1544661 y) (@lem1544673 y)). Qed.
Lemma lem1544675 (y : real) : (term44 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1544676 (y : real) : (term113 y) = y.
Proof. exact (TRANS (@lem1544674 y) (@lem1544675 y)). Qed.
Lemma lem1544679 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1544680 (x : real) (y : real) : (term112 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1544679 x) (@lem1544676 y)). Qed.
Lemma lem1544681 (x : real) (y : real) : (term111 x y) = (term123 x y).
Proof. exact (TRANS (@lem1544660 x y) (@lem1544680 x y)). Qed.
Lemma lem1544682 (x : real) (y : real) : (term110 x y) = (term123 x y).
Proof. exact (TRANS (@lem1544659 x y) (@lem1544681 x y)). Qed.
Lemma lem1544685 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1544686 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1544685 x) (@lem1544682 x y)). Qed.
Lemma lem1544687 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem1483484 (term58 x) (real_abs x) y). Qed.
Lemma lem1544688 (y : real) (x : real) : (term127 x y) = (term128 y x).
Proof. exact (@lem1483488 y (real_abs x)). Qed.
Lemma lem1544689 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1544690 (y : real) (x : real) : (term126 x y) = (term129 y x).
Proof. exact (MK_COMB (@lem1544689 x) (@lem1544688 y x)). Qed.
Lemma lem1544691 (y : real) (x : real) : (term125 x y) = (term129 y x).
Proof. exact (TRANS (@lem1544687 x y) (@lem1544690 y x)). Qed.
Lemma lem1544692 (y : real) (x : real) : (term124 x y) = (term129 y x).
Proof. exact (TRANS (@lem1544686 x y) (@lem1544691 y x)). Qed.
Lemma lem1544701 (y : real) : (term79 y) = (term79 y).
Proof. exact (eq_refl (term79 y)). Qed.
Lemma lem1544702 (y : real) (x : real) : (term130 x y) = (term131 y x).
Proof. exact (MK_COMB (@lem1544701 y) (@lem1544692 y x)). Qed.
Lemma lem1544703 (y : real) (x : real) : (term131 y x) = (term132 y x).
Proof. exact (@lem1483484 (term58 x) (term58 y) (term128 y x)). Qed.
Lemma lem1544704 (y : real) (x : real) : (term133 y x) = (term134 y x).
Proof. exact (@lem1483490 (term58 y) y (real_abs x)). Qed.
Lemma lem1544705 (y : real) : (term135 y) = (term136 y).
Proof. exact (@lem1483440 term87 y). Qed.
Lemma lem1544707 (m : nat) : (term137 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544708 : term138 = term35.
Proof. exact (@lem1544707 term90). Qed.
Lemma lem1544709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544710 : term139 = term140.
Proof. exact (MK_COMB (@lem1544709) (@lem1544708)). Qed.
Lemma lem1544711 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544712 (y : real) : (term136 y) = (term141 y).
Proof. exact (MK_COMB (@lem1544710) (@lem1544711 y)). Qed.
Lemma lem1544713 (y : real) : (term135 y) = (term141 y).
Proof. exact (TRANS (@lem1544705 y) (@lem1544712 y)). Qed.
Lemma lem1544714 (y : real) : (term141 y) = term35.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1544715 (y : real) : (term135 y) = term35.
Proof. exact (TRANS (@lem1544713 y) (@lem1544714 y)). Qed.
Lemma lem1544716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544717 (y : real) : (term142 y) = term143.
Proof. exact (MK_COMB (@lem1544716) (@lem1544715 y)). Qed.
Lemma lem1544718 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1544719 (y : real) (x : real) : (term134 y x) = (term144 x).
Proof. exact (MK_COMB (@lem1544717 y) (@lem1544718 x)). Qed.
Lemma lem1544720 (y : real) (x : real) : (term133 y x) = (term144 x).
Proof. exact (TRANS (@lem1544704 y x) (@lem1544719 y x)). Qed.
Lemma lem1544721 (x : real) : (term144 x) = (real_abs x).
Proof. exact (@lem1483448 (real_abs x)). Qed.
Lemma lem1544722 (y : real) (x : real) : (term133 y x) = (real_abs x).
Proof. exact (TRANS (@lem1544720 y x) (@lem1544721 x)). Qed.
Lemma lem1544723 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1544724 (y : real) (x : real) : (term132 y x) = (term145 x).
Proof. exact (MK_COMB (@lem1544723 x) (@lem1544722 y x)). Qed.
Lemma lem1544725 (y : real) (x : real) : (term131 y x) = (term145 x).
Proof. exact (TRANS (@lem1544703 y x) (@lem1544724 y x)). Qed.
Lemma lem1544726 (y : real) (x : real) : (term130 x y) = (term145 x).
Proof. exact (TRANS (@lem1544702 y x) (@lem1544725 y x)). Qed.
Lemma lem1544727 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544728 (y : real) (x : real) : (term146 x y) = (term147 x).
Proof. exact (MK_COMB (@lem1544727) (@lem1544726 y x)). Qed.
Lemma lem1544729 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544730 (y : real) (x : real) : (term148 x y) = (term149 x).
Proof. exact (MK_COMB (@lem1544728 y x) (@lem1544729)). Qed.
Lemma lem1544731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1544732 (y : real) (x : real) : (term150 x y) = (term151 x).
Proof. exact (MK_COMB (@lem1544731) (@lem1544730 y x)). Qed.
Lemma lem1544733 (y : real) (x : real) : (term68 x y) = (term152 y x).
Proof. exact (MK_COMB (@lem1544732 y x) (@lem1544642 y x)). Qed.
Lemma lem1544734 (y : real) (x : real) : (term62 x y) = (term152 y x).
Proof. exact (TRANS (@lem1544573 x y) (@lem1544733 y x)). Qed.
Lemma lem1544735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1544736 (y : real) (x : real) : (term64 x y) = (term153 y x).
Proof. exact (MK_COMB (@lem1544735) (@lem1544734 y x)). Qed.
Lemma lem1544738 (a : real) (b : real) (x : real) (r : real) : (term66 a b x r) = (term67 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1544739 (x : real) (y : real) : (term55 x y) = (term154 x y).
Proof. exact (@lem1544738 y (real_abs x) (real_sub x y) term35). Qed.
Lemma lem1544752 (x : real) (y : real) : (real_sub x y) = (term69 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1544755 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem1544756 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1544755) (@lem1544752 x y)). Qed.
Lemma lem1544757 (x : real) (y : real) : (term72 x y) = (term69 x y).
Proof. exact (@lem1483460 (term69 x y)). Qed.
Lemma lem1544758 (x : real) (y : real) : (term71 x y) = (term69 x y).
Proof. exact (TRANS (@lem1544756 x y) (@lem1544757 x y)). Qed.
Lemma lem1544761 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1544762 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1544761 x) (@lem1544758 x y)). Qed.
Lemma lem1544763 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (@lem1483484 x (real_abs x) (term58 y)). Qed.
Lemma lem1544764 (y : real) (x : real) : (term76 x y) = (term77 y x).
Proof. exact (@lem1483488 (term58 y) (real_abs x)). Qed.
Lemma lem1544765 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1544766 (y : real) (x : real) : (term75 x y) = (term78 y x).
Proof. exact (MK_COMB (@lem1544765 x) (@lem1544764 y x)). Qed.
Lemma lem1544767 (y : real) (x : real) : (term74 x y) = (term78 y x).
Proof. exact (TRANS (@lem1544763 x y) (@lem1544766 y x)). Qed.
Lemma lem1544768 (y : real) (x : real) : (term73 x y) = (term78 y x).
Proof. exact (TRANS (@lem1544762 x y) (@lem1544767 y x)). Qed.
Lemma lem1544771 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1544772 (y : real) (x : real) : (term155 x y) = (term156 y x).
Proof. exact (MK_COMB (@lem1544771 y) (@lem1544768 y x)). Qed.
Lemma lem1544773 (y : real) (x : real) : (term156 y x) = (term157 y x).
Proof. exact (@lem1483484 x y (term77 y x)). Qed.
Lemma lem1544774 (y : real) (x : real) : (term158 y x) = (term159 y x).
Proof. exact (@lem1483490 y (term58 y) (real_abs x)). Qed.
Lemma lem1544775 (y : real) : (term160 y) = (term136 y).
Proof. exact (@lem1483442 term87 y). Qed.
Lemma lem1544777 (m : nat) : (term137 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544778 : term138 = term35.
Proof. exact (@lem1544777 term90). Qed.
Lemma lem1544779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544780 : term139 = term140.
Proof. exact (MK_COMB (@lem1544779) (@lem1544778)). Qed.
Lemma lem1544781 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544782 (y : real) : (term136 y) = (term141 y).
Proof. exact (MK_COMB (@lem1544780) (@lem1544781 y)). Qed.
Lemma lem1544783 (y : real) : (term160 y) = (term141 y).
Proof. exact (TRANS (@lem1544775 y) (@lem1544782 y)). Qed.
Lemma lem1544784 (y : real) : (term141 y) = term35.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1544785 (y : real) : (term160 y) = term35.
Proof. exact (TRANS (@lem1544783 y) (@lem1544784 y)). Qed.
Lemma lem1544786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544787 (y : real) : (term161 y) = term143.
Proof. exact (MK_COMB (@lem1544786) (@lem1544785 y)). Qed.
Lemma lem1544788 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1544789 (y : real) (x : real) : (term159 y x) = (term144 x).
Proof. exact (MK_COMB (@lem1544787 y) (@lem1544788 x)). Qed.
Lemma lem1544790 (y : real) (x : real) : (term158 y x) = (term144 x).
Proof. exact (TRANS (@lem1544774 y x) (@lem1544789 y x)). Qed.
Lemma lem1544791 (x : real) : (term144 x) = (real_abs x).
Proof. exact (@lem1483448 (real_abs x)). Qed.
Lemma lem1544792 (y : real) (x : real) : (term158 y x) = (real_abs x).
Proof. exact (TRANS (@lem1544790 y x) (@lem1544791 x)). Qed.
Lemma lem1544793 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1544794 (y : real) (x : real) : (term157 y x) = (term162 x).
Proof. exact (MK_COMB (@lem1544793 x) (@lem1544792 y x)). Qed.
Lemma lem1544795 (y : real) (x : real) : (term156 y x) = (term162 x).
Proof. exact (TRANS (@lem1544773 y x) (@lem1544794 y x)). Qed.
Lemma lem1544796 (y : real) (x : real) : (term155 x y) = (term162 x).
Proof. exact (TRANS (@lem1544772 y x) (@lem1544795 y x)). Qed.
Lemma lem1544797 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544798 (y : real) (x : real) : (term163 x y) = (term164 x).
Proof. exact (MK_COMB (@lem1544797) (@lem1544796 y x)). Qed.
Lemma lem1544799 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544800 (y : real) (x : real) : (term165 x y) = (term166 x).
Proof. exact (MK_COMB (@lem1544798 y x) (@lem1544799)). Qed.
Lemma lem1544813 (x : real) (y : real) : (real_sub x y) = (term69 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1544816 : term109 = term109.
Proof. exact (eq_refl term109). Qed.
Lemma lem1544817 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1544816) (@lem1544813 x y)). Qed.
Lemma lem1544818 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (@lem1483508 x term87 (term58 y)). Qed.
Lemma lem1544819 (y : real) : (term113 y) = (term114 y).
Proof. exact (@lem1483476 term87 term87 y). Qed.
Lemma lem1544821 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1544822 : term117 = term118.
Proof. exact (@lem1544821 term90 term90). Qed.
Lemma lem1544823 : (term119 = (BIT1 0)) = (term120 = term90).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1544824 : term120 = term90.
Proof. exact (EQ_MP (@lem1544823) (@lem940073)). Qed.
Lemma lem1544825 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1544826 : term118 = term121.
Proof. exact (MK_COMB (@lem1544825) (@lem1544824)). Qed.
Lemma lem1544827 : term117 = term121.
Proof. exact (TRANS (@lem1544822) (@lem1544826)). Qed.
Lemma lem1544828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544829 : term122 = term70.
Proof. exact (MK_COMB (@lem1544828) (@lem1544827)). Qed.
Lemma lem1544830 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544831 (y : real) : (term114 y) = (term44 y).
Proof. exact (MK_COMB (@lem1544829) (@lem1544830 y)). Qed.
Lemma lem1544832 (y : real) : (term113 y) = (term44 y).
Proof. exact (TRANS (@lem1544819 y) (@lem1544831 y)). Qed.
Lemma lem1544833 (y : real) : (term44 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1544834 (y : real) : (term113 y) = y.
Proof. exact (TRANS (@lem1544832 y) (@lem1544833 y)). Qed.
Lemma lem1544837 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1544838 (x : real) (y : real) : (term112 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1544837 x) (@lem1544834 y)). Qed.
Lemma lem1544839 (x : real) (y : real) : (term111 x y) = (term123 x y).
Proof. exact (TRANS (@lem1544818 x y) (@lem1544838 x y)). Qed.
Lemma lem1544840 (x : real) (y : real) : (term110 x y) = (term123 x y).
Proof. exact (TRANS (@lem1544817 x y) (@lem1544839 x y)). Qed.
Lemma lem1544843 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1544844 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1544843 x) (@lem1544840 x y)). Qed.
Lemma lem1544845 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem1483484 (term58 x) (real_abs x) y). Qed.
Lemma lem1544846 (y : real) (x : real) : (term127 x y) = (term128 y x).
Proof. exact (@lem1483488 y (real_abs x)). Qed.
Lemma lem1544847 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1544848 (y : real) (x : real) : (term126 x y) = (term129 y x).
Proof. exact (MK_COMB (@lem1544847 x) (@lem1544846 y x)). Qed.
Lemma lem1544849 (y : real) (x : real) : (term125 x y) = (term129 y x).
Proof. exact (TRANS (@lem1544845 x y) (@lem1544848 y x)). Qed.
Lemma lem1544850 (y : real) (x : real) : (term124 x y) = (term129 y x).
Proof. exact (TRANS (@lem1544844 x y) (@lem1544849 y x)). Qed.
Lemma lem1544853 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1544854 (y : real) (x : real) : (term167 x y) = (term168 y x).
Proof. exact (MK_COMB (@lem1544853 y) (@lem1544850 y x)). Qed.
Lemma lem1544855 (y : real) (x : real) : (term168 y x) = (term169 y x).
Proof. exact (@lem1483484 (term58 x) y (term128 y x)). Qed.
Lemma lem1544856 (y : real) (x : real) : (term170 y x) = (term171 y x).
Proof. exact (@lem1483490 y y (real_abs x)). Qed.
Lemma lem1544857 (y : real) : (real_add y y) = (term172 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1544858 : term173 = term95.
Proof. exact (@lem1367770 term90 term90). Qed.
Lemma lem1544859 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1544860 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1544861 : term93 = term94.
Proof. exact (EQ_MP (@lem1544860) (@lem1544859)). Qed.
Lemma lem1544862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1544863 : term95 = term96.
Proof. exact (MK_COMB (@lem1544862) (@lem1544861)). Qed.
Lemma lem1544864 : term173 = term96.
Proof. exact (TRANS (@lem1544858) (@lem1544863)). Qed.
Lemma lem1544865 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544866 : term174 = term175.
Proof. exact (MK_COMB (@lem1544865) (@lem1544864)). Qed.
Lemma lem1544867 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1544868 (y : real) : (term172 y) = (term176 y).
Proof. exact (MK_COMB (@lem1544866) (@lem1544867 y)). Qed.
Lemma lem1544869 (y : real) : (real_add y y) = (term176 y).
Proof. exact (TRANS (@lem1544857 y) (@lem1544868 y)). Qed.
Lemma lem1544870 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1544871 (y : real) : (term177 y) = (term178 y).
Proof. exact (MK_COMB (@lem1544870) (@lem1544869 y)). Qed.
Lemma lem1544872 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1544873 (y : real) (x : real) : (term171 y x) = (term179 y x).
Proof. exact (MK_COMB (@lem1544871 y) (@lem1544872 x)). Qed.
Lemma lem1544874 (y : real) (x : real) : (term170 y x) = (term179 y x).
Proof. exact (TRANS (@lem1544856 y x) (@lem1544873 y x)). Qed.
Lemma lem1544875 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1544876 (y : real) (x : real) : (term169 y x) = (term180 y x).
Proof. exact (MK_COMB (@lem1544875 x) (@lem1544874 y x)). Qed.
Lemma lem1544877 (y : real) (x : real) : (term168 y x) = (term180 y x).
Proof. exact (TRANS (@lem1544855 y x) (@lem1544876 y x)). Qed.
Lemma lem1544878 (y : real) (x : real) : (term167 x y) = (term180 y x).
Proof. exact (TRANS (@lem1544854 y x) (@lem1544877 y x)). Qed.
Lemma lem1544879 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544880 (y : real) (x : real) : (term181 x y) = (term182 y x).
Proof. exact (MK_COMB (@lem1544879) (@lem1544878 y x)). Qed.
Lemma lem1544881 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544882 (y : real) (x : real) : (term183 x y) = (term184 y x).
Proof. exact (MK_COMB (@lem1544880 y x) (@lem1544881)). Qed.
Lemma lem1544883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1544884 (y : real) (x : real) : (term185 x y) = (term186 y x).
Proof. exact (MK_COMB (@lem1544883) (@lem1544882 y x)). Qed.
Lemma lem1544885 (y : real) (x : real) : (term154 x y) = (term187 y x).
Proof. exact (MK_COMB (@lem1544884 y x) (@lem1544800 y x)). Qed.
Lemma lem1544886 (y : real) (x : real) : (term55 x y) = (term187 y x).
Proof. exact (TRANS (@lem1544739 x y) (@lem1544885 y x)). Qed.
Lemma lem1544887 (y : real) (x : real) : (term65 x y) = (term188 y x).
Proof. exact (MK_COMB (@lem1544736 y x) (@lem1544886 y x)). Qed.
Lemma lem1544888 (y : real) (x : real) : (term36 x y) = (term188 y x).
Proof. exact (TRANS (@lem1544570 x y) (@lem1544887 y x)). Qed.
Lemma lem1544889 (y : real) (x : real) : (term189 y x) = (term188 y x).
Proof. exact (eq_refl (term189 y x)). Qed.
Lemma lem1544890 (y : real) (x : real) : (term188 y x) = (term189 y x).
Proof. exact (SYM (@lem1544889 y x)). Qed.
Lemma lem1544891 (y : real) (x : real) : (term189 y x) = (term190 y x).
Proof. exact (@lem1482981 (term191 y x) x). Qed.
Lemma lem1544892 (y : real) (x : real) : (term188 y x) = (term190 y x).
Proof. exact (TRANS (@lem1544890 y x) (@lem1544891 y x)). Qed.
Lemma lem1544893 (y : real) (x : real) : (term192 y x) = (term193 y x).
Proof. exact (eq_refl (term192 y x)). Qed.
Lemma lem1544894 (x : real) : (term194 x) = (term194 x).
Proof. exact (eq_refl (term194 x)). Qed.
Lemma lem1544895 (y : real) (x : real) : (term195 y x) = (term196 y x).
Proof. exact (MK_COMB (@lem1544894 x) (@lem1544893 y x)). Qed.
Lemma lem1544896 (y : real) (x : real) : (term197 y x) = (term198 y x).
Proof. exact (eq_refl (term197 y x)). Qed.
Lemma lem1544897 (x : real) : (term199 x) = (term199 x).
Proof. exact (eq_refl (term199 x)). Qed.
Lemma lem1544898 (y : real) (x : real) : (term200 y x) = (term201 y x).
Proof. exact (MK_COMB (@lem1544897 x) (@lem1544896 y x)). Qed.
Lemma lem1544899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1544900 (y : real) (x : real) : (term202 y x) = (term203 y x).
Proof. exact (MK_COMB (@lem1544899) (@lem1544898 y x)). Qed.
Lemma lem1544901 (y : real) (x : real) : (term190 y x) = (term204 y x).
Proof. exact (MK_COMB (@lem1544900 y x) (@lem1544895 y x)). Qed.
Lemma lem1544902 (y : real) (x : real) : (term205 y x) = (term205 y x).
Proof. exact (eq_refl (term205 y x)). Qed.
Lemma lem1544903 (y : real) (x : real) : ((term188 y x) = (term190 y x)) = ((term188 y x) = (term204 y x)).
Proof. exact (MK_COMB (@lem1544902 y x) (@lem1544901 y x)). Qed.
Lemma lem1544904 (y : real) (x : real) : (term188 y x) = (term204 y x).
Proof. exact (EQ_MP (@lem1544903 y x) (@lem1544892 y x)). Qed.
Lemma lem1544905 (x : real) : (term206 x) = (term207 x).
Proof. exact (@lem1483527 x term35). Qed.
Lemma lem1544911 (x : real) : (term208 x) = (term209 x).
Proof. exact (@lem1483519 x term35). Qed.
Lemma lem1544913 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1544914 : term211 = term35.
Proof. exact (@lem1544913 term90). Qed.
Lemma lem1544915 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1544916 (x : real) : (term209 x) = (term212 x).
Proof. exact (MK_COMB (@lem1544915 x) (@lem1544914)). Qed.
Lemma lem1544917 (x : real) : (term212 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1544918 (x : real) : (term209 x) = x.
Proof. exact (TRANS (@lem1544916 x) (@lem1544917 x)). Qed.
Lemma lem1544920 (x : real) : (term208 x) = x.
Proof. exact (TRANS (@lem1544911 x) (@lem1544918 x)). Qed.
Lemma lem1544921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1544922 (x : real) : (term213 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1544921) (@lem1544920 x)). Qed.
Lemma lem1544923 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544924 (x : real) : (term207 x) = (term206 x).
Proof. exact (MK_COMB (@lem1544922 x) (@lem1544923)). Qed.
Lemma lem1544925 (x : real) : (term206 x) = (term206 x).
Proof. exact (TRANS (@lem1544905 x) (@lem1544924 x)). Qed.
Lemma lem1544926 (x : real) : (term214 x) = (term215 x).
Proof. exact (@lem1483525 (term135 x) term35). Qed.
Lemma lem1544927 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544939 (x : real) : (term135 x) = (term136 x).
Proof. exact (@lem1483440 term87 x). Qed.
Lemma lem1544941 (m : nat) : (term137 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1544942 : term138 = term35.
Proof. exact (@lem1544941 term90). Qed.
Lemma lem1544943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544944 : term139 = term140.
Proof. exact (MK_COMB (@lem1544943) (@lem1544942)). Qed.
Lemma lem1544945 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1544946 (x : real) : (term136 x) = (term141 x).
Proof. exact (MK_COMB (@lem1544944) (@lem1544945 x)). Qed.
Lemma lem1544947 (x : real) : (term135 x) = (term141 x).
Proof. exact (TRANS (@lem1544939 x) (@lem1544946 x)). Qed.
Lemma lem1544948 (x : real) : (term141 x) = term35.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1544950 (x : real) : (term135 x) = term35.
Proof. exact (TRANS (@lem1544947 x) (@lem1544948 x)). Qed.
Lemma lem1544951 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1544952 (x : real) : (term216 x) = term217.
Proof. exact (MK_COMB (@lem1544951) (@lem1544950 x)). Qed.
Lemma lem1544953 (x : real) : (term218 x) = term219.
Proof. exact (MK_COMB (@lem1544952 x) (@lem1544927)). Qed.
Lemma lem1544954 : term219 = term220.
Proof. exact (@lem1483519 term35 term35). Qed.
Lemma lem1544956 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1544957 : term211 = term35.
Proof. exact (@lem1544956 term90). Qed.
Lemma lem1544958 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem1544959 : term220 = term221.
Proof. exact (MK_COMB (@lem1544958) (@lem1544957)). Qed.
Lemma lem1544960 : term221 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1544961 : term220 = term35.
Proof. exact (TRANS (@lem1544959) (@lem1544960)). Qed.
Lemma lem1544962 : term219 = term35.
Proof. exact (TRANS (@lem1544954) (@lem1544961)). Qed.
Lemma lem1544963 (x : real) : (term218 x) = term35.
Proof. exact (TRANS (@lem1544953 x) (@lem1544962)). Qed.
Lemma lem1544964 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1544965 (x : real) : (term222 x) = term223.
Proof. exact (MK_COMB (@lem1544964) (@lem1544963 x)). Qed.
Lemma lem1544966 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544967 (x : real) : (term215 x) = term224.
Proof. exact (MK_COMB (@lem1544965 x) (@lem1544966)). Qed.
Lemma lem1544968 (x : real) : (term214 x) = term224.
Proof. exact (TRANS (@lem1544926 x) (@lem1544967 x)). Qed.
Lemma lem1544969 (y : real) (x : real) : (term225 y x) = (term226 y x).
Proof. exact (@lem1483525 (term227 y x) term35). Qed.
Lemma lem1544970 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1544983 (x : real) (y : real) : (term228 y x) = (term229 x y).
Proof. exact (@lem1483488 x (term100 y)). Qed.
Lemma lem1544986 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1544987 (x : real) (y : real) : (term227 y x) = (term230 x y).
Proof. exact (MK_COMB (@lem1544986 x) (@lem1544983 x y)). Qed.
Lemma lem1544988 (x : real) (y : real) : (term230 x y) = (term231 x y).
Proof. exact (@lem1483490 x x (term100 y)). Qed.
Lemma lem1544989 (x : real) : (real_add x x) = (term172 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1544990 : term173 = term95.
Proof. exact (@lem1367770 term90 term90). Qed.
Lemma lem1544991 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1544992 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1544993 : term93 = term94.
Proof. exact (EQ_MP (@lem1544992) (@lem1544991)). Qed.
Lemma lem1544994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1544995 : term95 = term96.
Proof. exact (MK_COMB (@lem1544994) (@lem1544993)). Qed.
Lemma lem1544996 : term173 = term96.
Proof. exact (TRANS (@lem1544990) (@lem1544995)). Qed.
Lemma lem1544997 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1544998 : term174 = term175.
Proof. exact (MK_COMB (@lem1544997) (@lem1544996)). Qed.
Lemma lem1544999 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545000 (x : real) : (term172 x) = (term176 x).
Proof. exact (MK_COMB (@lem1544998) (@lem1544999 x)). Qed.
Lemma lem1545001 (x : real) : (real_add x x) = (term176 x).
Proof. exact (TRANS (@lem1544989 x) (@lem1545000 x)). Qed.
Lemma lem1545002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1545003 (x : real) : (term177 x) = (term178 x).
Proof. exact (MK_COMB (@lem1545002) (@lem1545001 x)). Qed.
Lemma lem1545004 (y : real) : (term100 y) = (term100 y).
Proof. exact (eq_refl (term100 y)). Qed.
Lemma lem1545005 (x : real) (y : real) : (term231 x y) = (term232 x y).
Proof. exact (MK_COMB (@lem1545003 x) (@lem1545004 y)). Qed.
Lemma lem1545006 (x : real) (y : real) : (term230 x y) = (term232 x y).
Proof. exact (TRANS (@lem1544988 x y) (@lem1545005 x y)). Qed.
Lemma lem1545007 (x : real) (y : real) : (term227 y x) = (term232 x y).
Proof. exact (TRANS (@lem1544987 x y) (@lem1545006 x y)). Qed.
Lemma lem1545008 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545009 (x : real) (y : real) : (term233 y x) = (term234 x y).
Proof. exact (MK_COMB (@lem1545008) (@lem1545007 x y)). Qed.
Lemma lem1545010 (x : real) (y : real) : (term235 y x) = (term236 x y).
Proof. exact (MK_COMB (@lem1545009 x y) (@lem1544970)). Qed.
Lemma lem1545011 (x : real) (y : real) : (term236 x y) = (term237 x y).
Proof. exact (@lem1483519 (term232 x y) term35). Qed.
Lemma lem1545013 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545014 : term211 = term35.
Proof. exact (@lem1545013 term90). Qed.
Lemma lem1545015 (x : real) (y : real) : (term238 x y) = (term238 x y).
Proof. exact (eq_refl (term238 x y)). Qed.
Lemma lem1545016 (x : real) (y : real) : (term237 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem1545015 x y) (@lem1545014)). Qed.
Lemma lem1545017 (x : real) (y : real) : (term239 x y) = (term232 x y).
Proof. exact (@lem1483450 (term232 x y)). Qed.
Lemma lem1545018 (x : real) (y : real) : (term237 x y) = (term232 x y).
Proof. exact (TRANS (@lem1545016 x y) (@lem1545017 x y)). Qed.
Lemma lem1545019 (x : real) (y : real) : (term236 x y) = (term232 x y).
Proof. exact (TRANS (@lem1545011 x y) (@lem1545018 x y)). Qed.
Lemma lem1545020 (x : real) (y : real) : (term235 y x) = (term232 x y).
Proof. exact (TRANS (@lem1545010 x y) (@lem1545019 x y)). Qed.
Lemma lem1545021 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545022 (x : real) (y : real) : (term240 y x) = (term241 x y).
Proof. exact (MK_COMB (@lem1545021) (@lem1545020 x y)). Qed.
Lemma lem1545023 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545024 (x : real) (y : real) : (term226 y x) = (term242 x y).
Proof. exact (MK_COMB (@lem1545022 x y) (@lem1545023)). Qed.
Lemma lem1545025 (x : real) (y : real) : (term225 y x) = (term242 x y).
Proof. exact (TRANS (@lem1544969 y x) (@lem1545024 x y)). Qed.
Lemma lem1545026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545027 (x : real) : (term243 x) = term244.
Proof. exact (MK_COMB (@lem1545026) (@lem1544968 x)). Qed.
Lemma lem1545028 (x : real) (y : real) : (term245 y x) = (term246 x y).
Proof. exact (MK_COMB (@lem1545027 x) (@lem1545025 x y)). Qed.
Lemma lem1545029 (y : real) (x : real) : (term247 y x) = (term248 y x).
Proof. exact (@lem1483525 (term249 y x) term35). Qed.
Lemma lem1545030 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545043 (x : real) (y : real) : (term250 y x) = (term251 x y).
Proof. exact (@lem1483488 x (term176 y)). Qed.
Lemma lem1545052 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1545053 (x : real) (y : real) : (term249 y x) = (term252 x y).
Proof. exact (MK_COMB (@lem1545052 x) (@lem1545043 x y)). Qed.
Lemma lem1545054 (x : real) (y : real) : (term252 x y) = (term253 x y).
Proof. exact (@lem1483490 (term58 x) x (term176 y)). Qed.
Lemma lem1545055 (x : real) : (term135 x) = (term136 x).
Proof. exact (@lem1483440 term87 x). Qed.
Lemma lem1545057 (m : nat) : (term137 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1545058 : term138 = term35.
Proof. exact (@lem1545057 term90). Qed.
Lemma lem1545059 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545060 : term139 = term140.
Proof. exact (MK_COMB (@lem1545059) (@lem1545058)). Qed.
Lemma lem1545061 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545062 (x : real) : (term136 x) = (term141 x).
Proof. exact (MK_COMB (@lem1545060) (@lem1545061 x)). Qed.
Lemma lem1545063 (x : real) : (term135 x) = (term141 x).
Proof. exact (TRANS (@lem1545055 x) (@lem1545062 x)). Qed.
Lemma lem1545064 (x : real) : (term141 x) = term35.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1545065 (x : real) : (term135 x) = term35.
Proof. exact (TRANS (@lem1545063 x) (@lem1545064 x)). Qed.
Lemma lem1545066 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1545067 (x : real) : (term142 x) = term143.
Proof. exact (MK_COMB (@lem1545066) (@lem1545065 x)). Qed.
Lemma lem1545068 (y : real) : (term176 y) = (term176 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem1545069 (x : real) (y : real) : (term253 x y) = (term254 y).
Proof. exact (MK_COMB (@lem1545067 x) (@lem1545068 y)). Qed.
Lemma lem1545070 (x : real) (y : real) : (term252 x y) = (term254 y).
Proof. exact (TRANS (@lem1545054 x y) (@lem1545069 x y)). Qed.
Lemma lem1545071 (y : real) : (term254 y) = (term176 y).
Proof. exact (@lem1483448 (term176 y)). Qed.
Lemma lem1545072 (x : real) (y : real) : (term252 x y) = (term176 y).
Proof. exact (TRANS (@lem1545070 x y) (@lem1545071 y)). Qed.
Lemma lem1545073 (x : real) (y : real) : (term249 y x) = (term176 y).
Proof. exact (TRANS (@lem1545053 x y) (@lem1545072 x y)). Qed.
Lemma lem1545074 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545075 (x : real) (y : real) : (term255 y x) = (term256 y).
Proof. exact (MK_COMB (@lem1545074) (@lem1545073 x y)). Qed.
Lemma lem1545076 (x : real) (y : real) : (term257 y x) = (term258 y).
Proof. exact (MK_COMB (@lem1545075 x y) (@lem1545030)). Qed.
Lemma lem1545077 (y : real) : (term258 y) = (term259 y).
Proof. exact (@lem1483519 (term176 y) term35). Qed.
Lemma lem1545079 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545080 : term211 = term35.
Proof. exact (@lem1545079 term90). Qed.
Lemma lem1545081 (y : real) : (term178 y) = (term178 y).
Proof. exact (eq_refl (term178 y)). Qed.
Lemma lem1545082 (y : real) : (term259 y) = (term260 y).
Proof. exact (MK_COMB (@lem1545081 y) (@lem1545080)). Qed.
Lemma lem1545083 (y : real) : (term260 y) = (term176 y).
Proof. exact (@lem1483450 (term176 y)). Qed.
Lemma lem1545084 (y : real) : (term259 y) = (term176 y).
Proof. exact (TRANS (@lem1545082 y) (@lem1545083 y)). Qed.
Lemma lem1545085 (y : real) : (term258 y) = (term176 y).
Proof. exact (TRANS (@lem1545077 y) (@lem1545084 y)). Qed.
Lemma lem1545086 (x : real) (y : real) : (term257 y x) = (term176 y).
Proof. exact (TRANS (@lem1545076 x y) (@lem1545085 y)). Qed.
Lemma lem1545087 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545088 (x : real) (y : real) : (term261 y x) = (term262 y).
Proof. exact (MK_COMB (@lem1545087) (@lem1545086 x y)). Qed.
Lemma lem1545089 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545090 (x : real) (y : real) : (term248 y x) = (term263 y).
Proof. exact (MK_COMB (@lem1545088 x y) (@lem1545089)). Qed.
Lemma lem1545091 (x : real) (y : real) : (term247 y x) = (term263 y).
Proof. exact (TRANS (@lem1545029 y x) (@lem1545090 x y)). Qed.
Lemma lem1545092 (x : real) : (term264 x) = (term265 x).
Proof. exact (@lem1483525 (real_add x x) term35). Qed.
Lemma lem1545093 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545099 (x : real) : (real_add x x) = (term172 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1545100 : term173 = term95.
Proof. exact (@lem1367770 term90 term90). Qed.
Lemma lem1545101 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1545102 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1545103 : term93 = term94.
Proof. exact (EQ_MP (@lem1545102) (@lem1545101)). Qed.
Lemma lem1545104 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545105 : term95 = term96.
Proof. exact (MK_COMB (@lem1545104) (@lem1545103)). Qed.
Lemma lem1545106 : term173 = term96.
Proof. exact (TRANS (@lem1545100) (@lem1545105)). Qed.
Lemma lem1545107 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545108 : term174 = term175.
Proof. exact (MK_COMB (@lem1545107) (@lem1545106)). Qed.
Lemma lem1545109 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545110 (x : real) : (term172 x) = (term176 x).
Proof. exact (MK_COMB (@lem1545108) (@lem1545109 x)). Qed.
Lemma lem1545112 (x : real) : (real_add x x) = (term176 x).
Proof. exact (TRANS (@lem1545099 x) (@lem1545110 x)). Qed.
Lemma lem1545113 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545114 (x : real) : (term266 x) = (term256 x).
Proof. exact (MK_COMB (@lem1545113) (@lem1545112 x)). Qed.
Lemma lem1545115 (x : real) : (term267 x) = (term258 x).
Proof. exact (MK_COMB (@lem1545114 x) (@lem1545093)). Qed.
Lemma lem1545116 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483519 (term176 x) term35). Qed.
Lemma lem1545118 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545119 : term211 = term35.
Proof. exact (@lem1545118 term90). Qed.
Lemma lem1545120 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1545121 (x : real) : (term259 x) = (term260 x).
Proof. exact (MK_COMB (@lem1545120 x) (@lem1545119)). Qed.
Lemma lem1545122 (x : real) : (term260 x) = (term176 x).
Proof. exact (@lem1483450 (term176 x)). Qed.
Lemma lem1545123 (x : real) : (term259 x) = (term176 x).
Proof. exact (TRANS (@lem1545121 x) (@lem1545122 x)). Qed.
Lemma lem1545124 (x : real) : (term258 x) = (term176 x).
Proof. exact (TRANS (@lem1545116 x) (@lem1545123 x)). Qed.
Lemma lem1545125 (x : real) : (term267 x) = (term176 x).
Proof. exact (TRANS (@lem1545115 x) (@lem1545124 x)). Qed.
Lemma lem1545126 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545127 (x : real) : (term268 x) = (term262 x).
Proof. exact (MK_COMB (@lem1545126) (@lem1545125 x)). Qed.
Lemma lem1545128 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545129 (x : real) : (term265 x) = (term263 x).
Proof. exact (MK_COMB (@lem1545127 x) (@lem1545128)). Qed.
Lemma lem1545130 (x : real) : (term264 x) = (term263 x).
Proof. exact (TRANS (@lem1545092 x) (@lem1545129 x)). Qed.
Lemma lem1545131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545132 (x : real) (y : real) : (term269 y x) = (term270 y).
Proof. exact (MK_COMB (@lem1545131) (@lem1545091 x y)). Qed.
Lemma lem1545133 (y : real) (x : real) : (term271 y x) = (term272 y x).
Proof. exact (MK_COMB (@lem1545132 x y) (@lem1545130 x)). Qed.
Lemma lem1545134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545135 (x : real) (y : real) : (term273 y x) = (term274 x y).
Proof. exact (MK_COMB (@lem1545134) (@lem1545028 x y)). Qed.
Lemma lem1545136 (y : real) (x : real) : (term198 y x) = (term275 y x).
Proof. exact (MK_COMB (@lem1545135 x y) (@lem1545133 y x)). Qed.
Lemma lem1545137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545138 (x : real) : (term199 x) = (term199 x).
Proof. exact (MK_COMB (@lem1545137) (@lem1544925 x)). Qed.
Lemma lem1545139 (y : real) (x : real) : (term201 y x) = (term276 y x).
Proof. exact (MK_COMB (@lem1545138 x) (@lem1545136 y x)). Qed.
Lemma lem1545140 (x : real) : (term277 x) = (term278 x).
Proof. exact (@lem1483525 term35 x). Qed.
Lemma lem1545146 (x : real) : (term279 x) = (term280 x).
Proof. exact (@lem1483519 term35 x). Qed.
Lemma lem1545151 (x : real) : (term280 x) = (term58 x).
Proof. exact (@lem1483448 (term58 x)). Qed.
Lemma lem1545153 (x : real) : (term279 x) = (term58 x).
Proof. exact (TRANS (@lem1545146 x) (@lem1545151 x)). Qed.
Lemma lem1545154 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545155 (x : real) : (term281 x) = (term282 x).
Proof. exact (MK_COMB (@lem1545154) (@lem1545153 x)). Qed.
Lemma lem1545156 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545157 (x : real) : (term278 x) = (term283 x).
Proof. exact (MK_COMB (@lem1545155 x) (@lem1545156)). Qed.
Lemma lem1545158 (x : real) : (term277 x) = (term283 x).
Proof. exact (TRANS (@lem1545140 x) (@lem1545157 x)). Qed.
Lemma lem1545159 (x : real) : (term284 x) = (term285 x).
Proof. exact (@lem1483525 (term286 x) term35). Qed.
Lemma lem1545160 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545167 (x : real) : (real_neg x) = (term58 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1545176 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1545177 (x : real) : (term286 x) = (term85 x).
Proof. exact (MK_COMB (@lem1545176 x) (@lem1545167 x)). Qed.
Lemma lem1545178 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483438 term87 term87 x). Qed.
Lemma lem1545179 : term88 = term89.
Proof. exact (@lem1367763 term90 term90). Qed.
Lemma lem1545180 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1545181 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1545182 : term93 = term94.
Proof. exact (EQ_MP (@lem1545181) (@lem1545180)). Qed.
Lemma lem1545183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545184 : term95 = term96.
Proof. exact (MK_COMB (@lem1545183) (@lem1545182)). Qed.
Lemma lem1545185 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1545186 : term89 = term97.
Proof. exact (MK_COMB (@lem1545185) (@lem1545184)). Qed.
Lemma lem1545187 : term88 = term97.
Proof. exact (TRANS (@lem1545179) (@lem1545186)). Qed.
Lemma lem1545188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545189 : term98 = term99.
Proof. exact (MK_COMB (@lem1545188) (@lem1545187)). Qed.
Lemma lem1545190 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545191 (x : real) : (term86 x) = (term100 x).
Proof. exact (MK_COMB (@lem1545189) (@lem1545190 x)). Qed.
Lemma lem1545192 (x : real) : (term85 x) = (term100 x).
Proof. exact (TRANS (@lem1545178 x) (@lem1545191 x)). Qed.
Lemma lem1545193 (x : real) : (term286 x) = (term100 x).
Proof. exact (TRANS (@lem1545177 x) (@lem1545192 x)). Qed.
Lemma lem1545194 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545195 (x : real) : (term287 x) = (term288 x).
Proof. exact (MK_COMB (@lem1545194) (@lem1545193 x)). Qed.
Lemma lem1545196 (x : real) : (term289 x) = (term290 x).
Proof. exact (MK_COMB (@lem1545195 x) (@lem1545160)). Qed.
Lemma lem1545197 (x : real) : (term290 x) = (term291 x).
Proof. exact (@lem1483519 (term100 x) term35). Qed.
Lemma lem1545199 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545200 : term211 = term35.
Proof. exact (@lem1545199 term90). Qed.
Lemma lem1545201 (x : real) : (term102 x) = (term102 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1545202 (x : real) : (term291 x) = (term292 x).
Proof. exact (MK_COMB (@lem1545201 x) (@lem1545200)). Qed.
Lemma lem1545203 (x : real) : (term292 x) = (term100 x).
Proof. exact (@lem1483450 (term100 x)). Qed.
Lemma lem1545204 (x : real) : (term291 x) = (term100 x).
Proof. exact (TRANS (@lem1545202 x) (@lem1545203 x)). Qed.
Lemma lem1545205 (x : real) : (term290 x) = (term100 x).
Proof. exact (TRANS (@lem1545197 x) (@lem1545204 x)). Qed.
Lemma lem1545206 (x : real) : (term289 x) = (term100 x).
Proof. exact (TRANS (@lem1545196 x) (@lem1545205 x)). Qed.
Lemma lem1545207 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545208 (x : real) : (term293 x) = (term294 x).
Proof. exact (MK_COMB (@lem1545207) (@lem1545206 x)). Qed.
Lemma lem1545209 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545210 (x : real) : (term285 x) = (term295 x).
Proof. exact (MK_COMB (@lem1545208 x) (@lem1545209)). Qed.
Lemma lem1545211 (x : real) : (term284 x) = (term295 x).
Proof. exact (TRANS (@lem1545159 x) (@lem1545210 x)). Qed.
Lemma lem1545212 (y : real) (x : real) : (term296 y x) = (term297 y x).
Proof. exact (@lem1483525 (term298 y x) term35). Qed.
Lemma lem1545213 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545220 (x : real) : (real_neg x) = (term58 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1545229 (y : real) : (term102 y) = (term102 y).
Proof. exact (eq_refl (term102 y)). Qed.
Lemma lem1545230 (y : real) (x : real) : (term299 y x) = (term300 y x).
Proof. exact (MK_COMB (@lem1545229 y) (@lem1545220 x)). Qed.
Lemma lem1545231 (x : real) (y : real) : (term300 y x) = (term301 x y).
Proof. exact (@lem1483488 (term58 x) (term100 y)). Qed.
Lemma lem1545232 (x : real) (y : real) : (term299 y x) = (term301 x y).
Proof. exact (TRANS (@lem1545230 y x) (@lem1545231 x y)). Qed.
Lemma lem1545235 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1545236 (x : real) (y : real) : (term298 y x) = (term302 x y).
Proof. exact (MK_COMB (@lem1545235 x) (@lem1545232 x y)). Qed.
Lemma lem1545237 (x : real) (y : real) : (term302 x y) = (term303 x y).
Proof. exact (@lem1483490 x (term58 x) (term100 y)). Qed.
Lemma lem1545238 (x : real) : (term160 x) = (term136 x).
Proof. exact (@lem1483442 term87 x). Qed.
Lemma lem1545240 (m : nat) : (term137 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1545241 : term138 = term35.
Proof. exact (@lem1545240 term90). Qed.
Lemma lem1545242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545243 : term139 = term140.
Proof. exact (MK_COMB (@lem1545242) (@lem1545241)). Qed.
Lemma lem1545244 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545245 (x : real) : (term136 x) = (term141 x).
Proof. exact (MK_COMB (@lem1545243) (@lem1545244 x)). Qed.
Lemma lem1545246 (x : real) : (term160 x) = (term141 x).
Proof. exact (TRANS (@lem1545238 x) (@lem1545245 x)). Qed.
Lemma lem1545247 (x : real) : (term141 x) = term35.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1545248 (x : real) : (term160 x) = term35.
Proof. exact (TRANS (@lem1545246 x) (@lem1545247 x)). Qed.
Lemma lem1545249 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1545250 (x : real) : (term161 x) = term143.
Proof. exact (MK_COMB (@lem1545249) (@lem1545248 x)). Qed.
Lemma lem1545251 (y : real) : (term100 y) = (term100 y).
Proof. exact (eq_refl (term100 y)). Qed.
Lemma lem1545252 (x : real) (y : real) : (term303 x y) = (term304 y).
Proof. exact (MK_COMB (@lem1545250 x) (@lem1545251 y)). Qed.
Lemma lem1545253 (x : real) (y : real) : (term302 x y) = (term304 y).
Proof. exact (TRANS (@lem1545237 x y) (@lem1545252 x y)). Qed.
Lemma lem1545254 (y : real) : (term304 y) = (term100 y).
Proof. exact (@lem1483448 (term100 y)). Qed.
Lemma lem1545255 (x : real) (y : real) : (term302 x y) = (term100 y).
Proof. exact (TRANS (@lem1545253 x y) (@lem1545254 y)). Qed.
Lemma lem1545256 (x : real) (y : real) : (term298 y x) = (term100 y).
Proof. exact (TRANS (@lem1545236 x y) (@lem1545255 x y)). Qed.
Lemma lem1545257 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545258 (x : real) (y : real) : (term305 y x) = (term288 y).
Proof. exact (MK_COMB (@lem1545257) (@lem1545256 x y)). Qed.
Lemma lem1545259 (x : real) (y : real) : (term306 y x) = (term290 y).
Proof. exact (MK_COMB (@lem1545258 x y) (@lem1545213)). Qed.
Lemma lem1545260 (y : real) : (term290 y) = (term291 y).
Proof. exact (@lem1483519 (term100 y) term35). Qed.
Lemma lem1545262 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545263 : term211 = term35.
Proof. exact (@lem1545262 term90). Qed.
Lemma lem1545264 (y : real) : (term102 y) = (term102 y).
Proof. exact (eq_refl (term102 y)). Qed.
Lemma lem1545265 (y : real) : (term291 y) = (term292 y).
Proof. exact (MK_COMB (@lem1545264 y) (@lem1545263)). Qed.
Lemma lem1545266 (y : real) : (term292 y) = (term100 y).
Proof. exact (@lem1483450 (term100 y)). Qed.
Lemma lem1545267 (y : real) : (term291 y) = (term100 y).
Proof. exact (TRANS (@lem1545265 y) (@lem1545266 y)). Qed.
Lemma lem1545268 (y : real) : (term290 y) = (term100 y).
Proof. exact (TRANS (@lem1545260 y) (@lem1545267 y)). Qed.
Lemma lem1545269 (x : real) (y : real) : (term306 y x) = (term100 y).
Proof. exact (TRANS (@lem1545259 x y) (@lem1545268 y)). Qed.
Lemma lem1545270 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545271 (x : real) (y : real) : (term307 y x) = (term294 y).
Proof. exact (MK_COMB (@lem1545270) (@lem1545269 x y)). Qed.
Lemma lem1545272 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545273 (x : real) (y : real) : (term297 y x) = (term295 y).
Proof. exact (MK_COMB (@lem1545271 x y) (@lem1545272)). Qed.
Lemma lem1545274 (x : real) (y : real) : (term296 y x) = (term295 y).
Proof. exact (TRANS (@lem1545212 y x) (@lem1545273 x y)). Qed.
Lemma lem1545275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545276 (x : real) : (term308 x) = (term309 x).
Proof. exact (MK_COMB (@lem1545275) (@lem1545211 x)). Qed.
Lemma lem1545277 (x : real) (y : real) : (term310 y x) = (term311 x y).
Proof. exact (MK_COMB (@lem1545276 x) (@lem1545274 x y)). Qed.
Lemma lem1545278 (y : real) (x : real) : (term312 y x) = (term313 y x).
Proof. exact (@lem1483525 (term314 y x) term35). Qed.
Lemma lem1545279 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545286 (x : real) : (real_neg x) = (term58 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1545295 (y : real) : (term178 y) = (term178 y).
Proof. exact (eq_refl (term178 y)). Qed.
Lemma lem1545296 (y : real) (x : real) : (term315 y x) = (term316 y x).
Proof. exact (MK_COMB (@lem1545295 y) (@lem1545286 x)). Qed.
Lemma lem1545297 (x : real) (y : real) : (term316 y x) = (term317 x y).
Proof. exact (@lem1483488 (term58 x) (term176 y)). Qed.
Lemma lem1545298 (x : real) (y : real) : (term315 y x) = (term317 x y).
Proof. exact (TRANS (@lem1545296 y x) (@lem1545297 x y)). Qed.
Lemma lem1545307 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1545308 (x : real) (y : real) : (term314 y x) = (term318 x y).
Proof. exact (MK_COMB (@lem1545307 x) (@lem1545298 x y)). Qed.
Lemma lem1545309 (x : real) (y : real) : (term318 x y) = (term319 x y).
Proof. exact (@lem1483490 (term58 x) (term58 x) (term176 y)). Qed.
Lemma lem1545310 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483438 term87 term87 x). Qed.
Lemma lem1545311 : term88 = term89.
Proof. exact (@lem1367763 term90 term90). Qed.
Lemma lem1545312 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1545313 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1545314 : term93 = term94.
Proof. exact (EQ_MP (@lem1545313) (@lem1545312)). Qed.
Lemma lem1545315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1545316 : term95 = term96.
Proof. exact (MK_COMB (@lem1545315) (@lem1545314)). Qed.
Lemma lem1545317 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1545318 : term89 = term97.
Proof. exact (MK_COMB (@lem1545317) (@lem1545316)). Qed.
Lemma lem1545319 : term88 = term97.
Proof. exact (TRANS (@lem1545311) (@lem1545318)). Qed.
Lemma lem1545320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545321 : term98 = term99.
Proof. exact (MK_COMB (@lem1545320) (@lem1545319)). Qed.
Lemma lem1545322 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545323 (x : real) : (term86 x) = (term100 x).
Proof. exact (MK_COMB (@lem1545321) (@lem1545322 x)). Qed.
Lemma lem1545324 (x : real) : (term85 x) = (term100 x).
Proof. exact (TRANS (@lem1545310 x) (@lem1545323 x)). Qed.
Lemma lem1545325 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1545326 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1545325) (@lem1545324 x)). Qed.
Lemma lem1545327 (y : real) : (term176 y) = (term176 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem1545328 (x : real) (y : real) : (term319 x y) = (term320 x y).
Proof. exact (MK_COMB (@lem1545326 x) (@lem1545327 y)). Qed.
Lemma lem1545329 (x : real) (y : real) : (term318 x y) = (term320 x y).
Proof. exact (TRANS (@lem1545309 x y) (@lem1545328 x y)). Qed.
Lemma lem1545330 (x : real) (y : real) : (term314 y x) = (term320 x y).
Proof. exact (TRANS (@lem1545308 x y) (@lem1545329 x y)). Qed.
Lemma lem1545331 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545332 (x : real) (y : real) : (term321 y x) = (term322 x y).
Proof. exact (MK_COMB (@lem1545331) (@lem1545330 x y)). Qed.
Lemma lem1545333 (x : real) (y : real) : (term323 y x) = (term324 x y).
Proof. exact (MK_COMB (@lem1545332 x y) (@lem1545279)). Qed.
Lemma lem1545334 (x : real) (y : real) : (term324 x y) = (term325 x y).
Proof. exact (@lem1483519 (term320 x y) term35). Qed.
Lemma lem1545336 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545337 : term211 = term35.
Proof. exact (@lem1545336 term90). Qed.
Lemma lem1545338 (x : real) (y : real) : (term326 x y) = (term326 x y).
Proof. exact (eq_refl (term326 x y)). Qed.
Lemma lem1545339 (x : real) (y : real) : (term325 x y) = (term327 x y).
Proof. exact (MK_COMB (@lem1545338 x y) (@lem1545337)). Qed.
Lemma lem1545340 (x : real) (y : real) : (term327 x y) = (term320 x y).
Proof. exact (@lem1483450 (term320 x y)). Qed.
Lemma lem1545341 (x : real) (y : real) : (term325 x y) = (term320 x y).
Proof. exact (TRANS (@lem1545339 x y) (@lem1545340 x y)). Qed.
Lemma lem1545342 (x : real) (y : real) : (term324 x y) = (term320 x y).
Proof. exact (TRANS (@lem1545334 x y) (@lem1545341 x y)). Qed.
Lemma lem1545343 (x : real) (y : real) : (term323 y x) = (term320 x y).
Proof. exact (TRANS (@lem1545333 x y) (@lem1545342 x y)). Qed.
Lemma lem1545344 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545345 (x : real) (y : real) : (term328 y x) = (term329 x y).
Proof. exact (MK_COMB (@lem1545344) (@lem1545343 x y)). Qed.
Lemma lem1545346 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545347 (x : real) (y : real) : (term313 y x) = (term330 x y).
Proof. exact (MK_COMB (@lem1545345 x y) (@lem1545346)). Qed.
Lemma lem1545348 (x : real) (y : real) : (term312 y x) = (term330 x y).
Proof. exact (TRANS (@lem1545278 y x) (@lem1545347 x y)). Qed.
Lemma lem1545349 (x : real) : (term331 x) = (term332 x).
Proof. exact (@lem1483525 (term333 x) term35). Qed.
Lemma lem1545350 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545357 (x : real) : (real_neg x) = (term58 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1545360 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1545361 (x : real) : (term333 x) = (term160 x).
Proof. exact (MK_COMB (@lem1545360 x) (@lem1545357 x)). Qed.
Lemma lem1545362 (x : real) : (term160 x) = (term136 x).
Proof. exact (@lem1483442 term87 x). Qed.
Lemma lem1545364 (m : nat) : (term137 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1545365 : term138 = term35.
Proof. exact (@lem1545364 term90). Qed.
Lemma lem1545366 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1545367 : term139 = term140.
Proof. exact (MK_COMB (@lem1545366) (@lem1545365)). Qed.
Lemma lem1545368 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1545369 (x : real) : (term136 x) = (term141 x).
Proof. exact (MK_COMB (@lem1545367) (@lem1545368 x)). Qed.
Lemma lem1545370 (x : real) : (term160 x) = (term141 x).
Proof. exact (TRANS (@lem1545362 x) (@lem1545369 x)). Qed.
Lemma lem1545371 (x : real) : (term141 x) = term35.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1545372 (x : real) : (term160 x) = term35.
Proof. exact (TRANS (@lem1545370 x) (@lem1545371 x)). Qed.
Lemma lem1545373 (x : real) : (term333 x) = term35.
Proof. exact (TRANS (@lem1545361 x) (@lem1545372 x)). Qed.
Lemma lem1545374 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1545375 (x : real) : (term334 x) = term217.
Proof. exact (MK_COMB (@lem1545374) (@lem1545373 x)). Qed.
Lemma lem1545376 (x : real) : (term335 x) = term219.
Proof. exact (MK_COMB (@lem1545375 x) (@lem1545350)). Qed.
Lemma lem1545377 : term219 = term220.
Proof. exact (@lem1483519 term35 term35). Qed.
Lemma lem1545379 (x : nat) : (term210 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1545380 : term211 = term35.
Proof. exact (@lem1545379 term90). Qed.
Lemma lem1545381 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem1545382 : term220 = term221.
Proof. exact (MK_COMB (@lem1545381) (@lem1545380)). Qed.
Lemma lem1545383 : term221 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1545384 : term220 = term35.
Proof. exact (TRANS (@lem1545382) (@lem1545383)). Qed.
Lemma lem1545385 : term219 = term35.
Proof. exact (TRANS (@lem1545377) (@lem1545384)). Qed.
Lemma lem1545386 (x : real) : (term335 x) = term35.
Proof. exact (TRANS (@lem1545376 x) (@lem1545385)). Qed.
Lemma lem1545387 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1545388 (x : real) : (term336 x) = term223.
Proof. exact (MK_COMB (@lem1545387) (@lem1545386 x)). Qed.
Lemma lem1545389 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1545390 (x : real) : (term332 x) = term224.
Proof. exact (MK_COMB (@lem1545388 x) (@lem1545389)). Qed.
Lemma lem1545391 (x : real) : (term331 x) = term224.
Proof. exact (TRANS (@lem1545349 x) (@lem1545390 x)). Qed.
Lemma lem1545392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545393 (x : real) (y : real) : (term337 y x) = (term338 x y).
Proof. exact (MK_COMB (@lem1545392) (@lem1545348 x y)). Qed.
Lemma lem1545394 (x : real) (y : real) : (term339 y x) = (term340 x y).
Proof. exact (MK_COMB (@lem1545393 x y) (@lem1545391 x)). Qed.
Lemma lem1545395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545396 (x : real) (y : real) : (term341 y x) = (term342 x y).
Proof. exact (MK_COMB (@lem1545395) (@lem1545277 x y)). Qed.
Lemma lem1545397 (x : real) (y : real) : (term193 y x) = (term343 x y).
Proof. exact (MK_COMB (@lem1545396 x y) (@lem1545394 x y)). Qed.
Lemma lem1545398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1545399 (x : real) : (term194 x) = (term344 x).
Proof. exact (MK_COMB (@lem1545398) (@lem1545158 x)). Qed.
Lemma lem1545400 (x : real) (y : real) : (term196 y x) = (term345 x y).
Proof. exact (MK_COMB (@lem1545399 x) (@lem1545397 x y)). Qed.
Lemma lem1545401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1545402 (y : real) (x : real) : (term203 y x) = (term346 y x).
Proof. exact (MK_COMB (@lem1545401) (@lem1545139 y x)). Qed.
Lemma lem1545403 (x : real) (y : real) : (term204 y x) = (term347 x y).
Proof. exact (MK_COMB (@lem1545402 y x) (@lem1545400 x y)). Qed.
Lemma lem1545414 (x : real) (y : real) : (term188 y x) = (term347 x y).
Proof. exact (TRANS (@lem1544904 y x) (@lem1545403 x y)). Qed.
Lemma lem1545415 (x : real) (y : real) : (term36 x y) = (term347 x y).
Proof. exact (TRANS (@lem1544888 y x) (@lem1545414 x y)). Qed.
Lemma lem1545416 (x : real) (y : real) (h1 : term347 x y) : term347 x y.
Proof. exact (h1). Qed.
Lemma lem1545417 (y : real) (x : real) (h1 : term276 y x) : term276 y x.
Proof. exact (h1). Qed.
Lemma lem1545418 (y : real) (x : real) (h1 : term276 y x) : term275 y x.
Proof. exact (proj2 (@lem1545417 y x h1)). Qed.
Lemma lem1545421 (y : real) (x : real) (h1 : term276 y x) : term246 x y.
Proof. exact (proj1 (@lem1545418 y x h1)). Qed.
Lemma lem1545423 (y : real) (x : real) (h1 : term276 y x) : term224.
Proof. exact (proj1 (@lem1545421 y x h1)). Qed.
Lemma lem1545427 (n : nat) (m : nat) : (term348 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1545428 : term224 = term349.
Proof. exact (@lem1545427 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1545429 : term349 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1545430 : term224 = False.
Proof. exact (TRANS (@lem1545428) (@lem1545429)). Qed.
Lemma lem1545431 (y : real) (x : real) (h1 : term276 y x) : False.
Proof. exact (EQ_MP (@lem1545430) (@lem1545423 y x h1)). Qed.
Lemma lem1545432 (x : real) (y : real) (h1 : term345 x y) : term345 x y.
Proof. exact (h1). Qed.
Lemma lem1545433 (x : real) (y : real) (h1 : term345 x y) : term343 x y.
Proof. exact (proj2 (@lem1545432 x y h1)). Qed.
Lemma lem1545435 (x : real) (y : real) (h1 : term345 x y) : term340 x y.
Proof. exact (proj2 (@lem1545433 x y h1)). Qed.
Lemma lem1545439 (x : real) (y : real) (h1 : term345 x y) : term224.
Proof. exact (proj2 (@lem1545435 x y h1)). Qed.
Lemma lem1545442 (n : nat) (m : nat) : (term348 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1545443 : term224 = term349.
Proof. exact (@lem1545442 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1545444 : term349 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1545445 : term224 = False.
Proof. exact (TRANS (@lem1545443) (@lem1545444)). Qed.
Lemma lem1545446 (x : real) (y : real) (h1 : term345 x y) : False.
Proof. exact (EQ_MP (@lem1545445) (@lem1545439 x y h1)). Qed.
Lemma lem1545447 (x : real) (y : real) (h1 : term347 x y) : False.
Proof. exact (or_elim (@lem1545416 x y h1) (fun h0 : term276 y x => @lem1545431 y x h0) (fun h0 : term345 x y => @lem1545446 x y h0)). Qed.
Lemma lem1545448 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1545449 (x : real) (y : real) (h1 : term36 x y) : term347 x y.
Proof. exact (EQ_MP (@lem1545415 x y) (@lem1545448 x y h1)). Qed.
Lemma lem1545450 (x : real) (y : real) (h1 : term36 x y) : (term347 x y) = False.
Proof. exact (prop_ext (fun h2 : term347 x y => @lem1545447 x y h2) (fun h2 : False => @lem1545449 x y h1)). Qed.
Lemma lem1545451 (x : real) (y : real) (h1 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1545450 x y h1) (@lem1545449 x y h1)). Qed.
Lemma lem1545452 (x : real) (h1 : term38 x) : term38 x.
Proof. exact (h1). Qed.
Lemma lem1545453 (x : real) (h1 : term38 x) : False.
Proof. exact (ex_elim (@lem1545452 x h1) (fun y : real => fun h0 : term37 x y => @lem1545451 x y h0)). Qed.
Lemma lem1545454 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1545455 (h1 : term40) : False.
Proof. exact (ex_elim (@lem1545454 h1) (fun x : real => fun h0 : term39 x => @lem1545453 x h0)). Qed.
Lemma lem1545456 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1545457 (h1 : term12) : term40.
Proof. exact (EQ_MP (@lem1544497) (@lem1545456 h1)). Qed.
Lemma lem1545458 (h1 : term12) : term40 = False.
Proof. exact (prop_ext (fun h2 : term40 => @lem1545455 h2) (fun h2 : False => @lem1545457 h1)). Qed.
Lemma lem1545459 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1545458 h1) (@lem1545457 h1)). Qed.
Lemma lem1545460 : term350.
Proof. exact (fun h0 : term12 => @lem1545459 h0). Qed.
Lemma lem1545461 : term351.
Proof. exact (@lem1386578 term352). Qed.
Lemma lem1545462 : term352.
Proof. exact (@lem1545461 (@lem1545460)). Qed.
