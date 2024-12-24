Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_ADDR_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483486_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1509429 (x : real) (y : real) : (term0 x y) = (term1 x y).
Proof. exact (@lem17646 (term2 x y) (term3 y)). Qed.
Lemma lem1509430 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1509431 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1509430 (term8 x)). Qed.
Lemma lem1509432 (x : real) (y : real) : (term9 x y) = ((term2 x y) = (term3 y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1509433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1509434 (x : real) (y : real) : (term10 x y) = (term0 x y).
Proof. exact (MK_COMB (@lem1509433) (@lem1509432 x y)). Qed.
Lemma lem1509435 (x : real) (y : real) : (term10 x y) = (term1 x y).
Proof. exact (TRANS (@lem1509434 x y) (@lem1509429 x y)). Qed.
Lemma lem1509436 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1509435 x y)). Qed.
Lemma lem1509437 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509438 (x : real) : (term7 x) = (term13 x).
Proof. exact (MK_COMB (@lem1509437) (@lem1509436 x)). Qed.
Lemma lem1509439 (x : real) : (term6 x) = (term13 x).
Proof. exact (TRANS (@lem1509431 x) (@lem1509438 x)). Qed.
Lemma lem1509440 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1509441 : term14 = term15.
Proof. exact (@lem1509440 term16). Qed.
Lemma lem1509442 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1509443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1509444 (x : real) : (term19 x) = (term6 x).
Proof. exact (MK_COMB (@lem1509443) (@lem1509442 x)). Qed.
Lemma lem1509445 (x : real) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem1509444 x) (@lem1509439 x)). Qed.
Lemma lem1509446 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1509445 x)). Qed.
Lemma lem1509447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509448 : term15 = term22.
Proof. exact (MK_COMB (@lem1509447) (@lem1509446)). Qed.
Lemma lem1509450 : term14 = term22.
Proof. exact (TRANS (@lem1509441) (@lem1509448)). Qed.
Lemma lem1509467 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1509468 (x : real) : (term12 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1509467 x y)). Qed.
Lemma lem1509469 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509470 (x : real) : (term13 x) = (term13 x).
Proof. exact (MK_COMB (@lem1509469) (@lem1509468 x)). Qed.
Lemma lem1509471 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1509470 x)). Qed.
Lemma lem1509472 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509473 : term22 = term22.
Proof. exact (MK_COMB (@lem1509472) (@lem1509471)). Qed.
Lemma lem1509474 : term14 = term22.
Proof. exact (TRANS (@lem1509450) (@lem1509473)). Qed.
Lemma lem1509475 (y : real) (x : real) : (term2 x y) = (term23 y x).
Proof. exact (@lem1483523 (real_add x y) x). Qed.
Lemma lem1509487 (y : real) (x : real) : (term24 y x) = (term25 y x).
Proof. exact (@lem1483519 (real_add x y) x). Qed.
Lemma lem1509491 (x : real) (y : real) : (term25 y x) = (term26 x y).
Proof. exact (@lem1483486 x (term27 x) y). Qed.
Lemma lem1509492 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1509494 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509495 : term33 = term32.
Proof. exact (@lem1509494 term34). Qed.
Lemma lem1509496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509497 : term35 = term36.
Proof. exact (MK_COMB (@lem1509496) (@lem1509495)). Qed.
Lemma lem1509498 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1509499 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1509497) (@lem1509498 x)). Qed.
Lemma lem1509500 (x : real) : (term28 x) = (term37 x).
Proof. exact (TRANS (@lem1509492 x) (@lem1509499 x)). Qed.
Lemma lem1509501 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1509502 (x : real) : (term28 x) = term32.
Proof. exact (TRANS (@lem1509500 x) (@lem1509501 x)). Qed.
Lemma lem1509503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1509504 (x : real) : (term38 x) = term39.
Proof. exact (MK_COMB (@lem1509503) (@lem1509502 x)). Qed.
Lemma lem1509505 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1509506 (x : real) (y : real) : (term26 x y) = (term40 y).
Proof. exact (MK_COMB (@lem1509504 x) (@lem1509505 y)). Qed.
Lemma lem1509507 (x : real) (y : real) : (term25 y x) = (term40 y).
Proof. exact (TRANS (@lem1509491 x y) (@lem1509506 x y)). Qed.
Lemma lem1509508 (y : real) : (term40 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1509510 (x : real) (y : real) : (term25 y x) = y.
Proof. exact (TRANS (@lem1509507 x y) (@lem1509508 y)). Qed.
Lemma lem1509512 (x : real) (y : real) : (term24 y x) = y.
Proof. exact (TRANS (@lem1509487 y x) (@lem1509510 x y)). Qed.
Lemma lem1509513 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1509514 (x : real) (y : real) : (term41 y x) = (real_ge y).
Proof. exact (MK_COMB (@lem1509513) (@lem1509512 x y)). Qed.
Lemma lem1509515 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509516 (x : real) (y : real) : (term23 y x) = (term42 y).
Proof. exact (MK_COMB (@lem1509514 x y) (@lem1509515)). Qed.
Lemma lem1509517 (x : real) (y : real) : (term2 x y) = (term42 y).
Proof. exact (TRANS (@lem1509475 y x) (@lem1509516 x y)). Qed.
Lemma lem1509518 (y : real) : (term43 y) = (term44 y).
Proof. exact (@lem1483533 term32 y). Qed.
Lemma lem1509524 (y : real) : (term45 y) = (term46 y).
Proof. exact (@lem1483519 term32 y). Qed.
Lemma lem1509529 (y : real) : (term46 y) = (term27 y).
Proof. exact (@lem1483448 (term27 y)). Qed.
Lemma lem1509531 (y : real) : (term45 y) = (term27 y).
Proof. exact (TRANS (@lem1509524 y) (@lem1509529 y)). Qed.
Lemma lem1509532 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509533 (y : real) : (term47 y) = (term48 y).
Proof. exact (MK_COMB (@lem1509532) (@lem1509531 y)). Qed.
Lemma lem1509534 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509535 (y : real) : (term44 y) = (term49 y).
Proof. exact (MK_COMB (@lem1509533 y) (@lem1509534)). Qed.
Lemma lem1509536 (y : real) : (term43 y) = (term49 y).
Proof. exact (TRANS (@lem1509518 y) (@lem1509535 y)). Qed.
Lemma lem1509537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1509538 (x : real) (y : real) : (term50 x y) = (term51 y).
Proof. exact (MK_COMB (@lem1509537) (@lem1509517 x y)). Qed.
Lemma lem1509539 (x : real) (y : real) : (term52 x y) = (term53 y).
Proof. exact (MK_COMB (@lem1509538 x y) (@lem1509536 y)). Qed.
Lemma lem1509540 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (@lem1483533 x (real_add x y)). Qed.
Lemma lem1509552 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (@lem1483519 x (real_add x y)). Qed.
Lemma lem1509559 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1483508 x term30 y). Qed.
Lemma lem1509560 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1509561 (x : real) (y : real) : (term57 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1509560 x) (@lem1509559 x y)). Qed.
Lemma lem1509562 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (@lem1483490 x (term27 x) (term27 y)). Qed.
Lemma lem1509563 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1509565 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509566 : term33 = term32.
Proof. exact (@lem1509565 term34). Qed.
Lemma lem1509567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509568 : term35 = term36.
Proof. exact (MK_COMB (@lem1509567) (@lem1509566)). Qed.
Lemma lem1509569 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1509570 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1509568) (@lem1509569 x)). Qed.
Lemma lem1509571 (x : real) : (term28 x) = (term37 x).
Proof. exact (TRANS (@lem1509563 x) (@lem1509570 x)). Qed.
Lemma lem1509572 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1509573 (x : real) : (term28 x) = term32.
Proof. exact (TRANS (@lem1509571 x) (@lem1509572 x)). Qed.
Lemma lem1509574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1509575 (x : real) : (term38 x) = term39.
Proof. exact (MK_COMB (@lem1509574) (@lem1509573 x)). Qed.
Lemma lem1509576 (y : real) : (term27 y) = (term27 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1509577 (x : real) (y : real) : (term61 x y) = (term46 y).
Proof. exact (MK_COMB (@lem1509575 x) (@lem1509576 y)). Qed.
Lemma lem1509578 (x : real) (y : real) : (term60 x y) = (term46 y).
Proof. exact (TRANS (@lem1509562 x y) (@lem1509577 x y)). Qed.
Lemma lem1509579 (y : real) : (term46 y) = (term27 y).
Proof. exact (@lem1483448 (term27 y)). Qed.
Lemma lem1509580 (x : real) (y : real) : (term60 x y) = (term27 y).
Proof. exact (TRANS (@lem1509578 x y) (@lem1509579 y)). Qed.
Lemma lem1509581 (x : real) (y : real) : (term57 x y) = (term27 y).
Proof. exact (TRANS (@lem1509561 x y) (@lem1509580 x y)). Qed.
Lemma lem1509583 (x : real) (y : real) : (term56 x y) = (term27 y).
Proof. exact (TRANS (@lem1509552 x y) (@lem1509581 x y)). Qed.
Lemma lem1509584 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509585 (x : real) (y : real) : (term62 x y) = (term48 y).
Proof. exact (MK_COMB (@lem1509584) (@lem1509583 x y)). Qed.
Lemma lem1509586 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509587 (x : real) (y : real) : (term55 x y) = (term49 y).
Proof. exact (MK_COMB (@lem1509585 x y) (@lem1509586)). Qed.
Lemma lem1509588 (x : real) (y : real) : (term54 x y) = (term49 y).
Proof. exact (TRANS (@lem1509540 x y) (@lem1509587 x y)). Qed.
Lemma lem1509589 (y : real) : (term3 y) = (term63 y).
Proof. exact (@lem1483523 y term32). Qed.
Lemma lem1509595 (y : real) : (term64 y) = (term65 y).
Proof. exact (@lem1483519 y term32). Qed.
Lemma lem1509597 (x : nat) : (term66 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1509598 : term67 = term32.
Proof. exact (@lem1509597 term34). Qed.
Lemma lem1509599 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1509600 (y : real) : (term65 y) = (term68 y).
Proof. exact (MK_COMB (@lem1509599 y) (@lem1509598)). Qed.
Lemma lem1509601 (y : real) : (term68 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1509602 (y : real) : (term65 y) = y.
Proof. exact (TRANS (@lem1509600 y) (@lem1509601 y)). Qed.
Lemma lem1509604 (y : real) : (term64 y) = y.
Proof. exact (TRANS (@lem1509595 y) (@lem1509602 y)). Qed.
Lemma lem1509605 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1509606 (y : real) : (term69 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1509605) (@lem1509604 y)). Qed.
Lemma lem1509607 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509608 (y : real) : (term63 y) = (term42 y).
Proof. exact (MK_COMB (@lem1509606 y) (@lem1509607)). Qed.
Lemma lem1509609 (y : real) : (term3 y) = (term42 y).
Proof. exact (TRANS (@lem1509589 y) (@lem1509608 y)). Qed.
Lemma lem1509610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1509611 (x : real) (y : real) : (term70 x y) = (term71 y).
Proof. exact (MK_COMB (@lem1509610) (@lem1509588 x y)). Qed.
Lemma lem1509612 (x : real) (y : real) : (term72 x y) = (term73 y).
Proof. exact (MK_COMB (@lem1509611 x y) (@lem1509609 y)). Qed.
Lemma lem1509613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509614 (x : real) (y : real) : (term74 x y) = (term75 y).
Proof. exact (MK_COMB (@lem1509613) (@lem1509539 x y)). Qed.
Lemma lem1509615 (x : real) (y : real) : (term1 x y) = (term76 y).
Proof. exact (MK_COMB (@lem1509614 x y) (@lem1509612 x y)). Qed.
Lemma lem1509616 (x : real) : (term12 x) = term77.
Proof. exact (fun_ext (fun y : real => @lem1509615 x y)). Qed.
Lemma lem1509617 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509618 (x : real) : (term13 x) = term78.
Proof. exact (MK_COMB (@lem1509617) (@lem1509616 x)). Qed.
Lemma lem1509619 : term21 = term79.
Proof. exact (fun_ext (fun x : real => @lem1509618 x)). Qed.
Lemma lem1509620 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509621 : term22 = term80.
Proof. exact (MK_COMB (@lem1509620) (@lem1509619)). Qed.
Lemma lem1509622 : term14 = term80.
Proof. exact (TRANS (@lem1509474) (@lem1509621)). Qed.
Lemma lem1509624 {A : Type'} (t : Prop) : (term81 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1509625 (t : Prop) : (term82 t) = t.
Proof. exact (@lem1509624 real t). Qed.
Lemma lem1509626 : term80 = term78.
Proof. exact (@lem1509625 term78). Qed.
Lemma lem1509628 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1509629 (P : real -> Prop) (Q : real -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem1509628 real P Q). Qed.
Lemma lem1509630 : term87 = term88.
Proof. exact (@lem1509629 term89 term90). Qed.
Lemma lem1509631 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1509632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509633 (y : real) : (term92 y) = (term75 y).
Proof. exact (MK_COMB (@lem1509632) (@lem1509631 y)). Qed.
Lemma lem1509634 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1509635 (y : real) : (term94 y) = (term76 y).
Proof. exact (MK_COMB (@lem1509633 y) (@lem1509634 y)). Qed.
Lemma lem1509636 : term95 = term77.
Proof. exact (fun_ext (fun y : real => @lem1509635 y)). Qed.
Lemma lem1509637 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509638 : term87 = term78.
Proof. exact (MK_COMB (@lem1509637) (@lem1509636)). Qed.
Lemma lem1509639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1509640 : term96 = term97.
Proof. exact (MK_COMB (@lem1509639) (@lem1509638)). Qed.
Lemma lem1509641 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1509642 : term98 = term89.
Proof. exact (fun_ext (fun y : real => @lem1509641 y)). Qed.
Lemma lem1509643 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509644 : term99 = term100.
Proof. exact (MK_COMB (@lem1509643) (@lem1509642)). Qed.
Lemma lem1509645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509646 : term101 = term102.
Proof. exact (MK_COMB (@lem1509645) (@lem1509644)). Qed.
Lemma lem1509647 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1509648 : term103 = term90.
Proof. exact (fun_ext (fun y : real => @lem1509647 y)). Qed.
Lemma lem1509649 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509650 : term104 = term105.
Proof. exact (MK_COMB (@lem1509649) (@lem1509648)). Qed.
Lemma lem1509651 : term88 = term106.
Proof. exact (MK_COMB (@lem1509646) (@lem1509650)). Qed.
Lemma lem1509652 : (term87 = term88) = (term78 = term106).
Proof. exact (MK_COMB (@lem1509640) (@lem1509651)). Qed.
Lemma lem1509653 : term78 = term106.
Proof. exact (EQ_MP (@lem1509652) (@lem1509630)). Qed.
Lemma lem1509654 : term80 = term106.
Proof. exact (TRANS (@lem1509626) (@lem1509653)). Qed.
Lemma lem1509752 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term84 A P Q) = (term83 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1509753 (P : real -> Prop) (Q : real -> Prop) : (term86 P Q) = (term85 P Q).
Proof. exact (@lem1509752 real P Q). Qed.
Lemma lem1509754 : term88 = term87.
Proof. exact (@lem1509753 term89 term90). Qed.
Lemma lem1509755 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1509756 : term98 = term89.
Proof. exact (fun_ext (fun y : real => @lem1509755 y)). Qed.
Lemma lem1509757 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509758 : term99 = term100.
Proof. exact (MK_COMB (@lem1509757) (@lem1509756)). Qed.
Lemma lem1509759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509760 : term101 = term102.
Proof. exact (MK_COMB (@lem1509759) (@lem1509758)). Qed.
Lemma lem1509761 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1509762 : term103 = term90.
Proof. exact (fun_ext (fun y : real => @lem1509761 y)). Qed.
Lemma lem1509763 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509764 : term104 = term105.
Proof. exact (MK_COMB (@lem1509763) (@lem1509762)). Qed.
Lemma lem1509765 : term88 = term106.
Proof. exact (MK_COMB (@lem1509760) (@lem1509764)). Qed.
Lemma lem1509766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1509767 : term107 = term108.
Proof. exact (MK_COMB (@lem1509766) (@lem1509765)). Qed.
Lemma lem1509768 (y : real) : (term91 y) = (term53 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1509769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1509770 (y : real) : (term92 y) = (term75 y).
Proof. exact (MK_COMB (@lem1509769) (@lem1509768 y)). Qed.
Lemma lem1509771 (y : real) : (term93 y) = (term73 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1509772 (y : real) : (term94 y) = (term76 y).
Proof. exact (MK_COMB (@lem1509770 y) (@lem1509771 y)). Qed.
Lemma lem1509773 : term95 = term77.
Proof. exact (fun_ext (fun y : real => @lem1509772 y)). Qed.
Lemma lem1509774 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509775 : term87 = term78.
Proof. exact (MK_COMB (@lem1509774) (@lem1509773)). Qed.
Lemma lem1509776 : (term88 = term87) = (term106 = term78).
Proof. exact (MK_COMB (@lem1509767) (@lem1509775)). Qed.
Lemma lem1509777 : term106 = term78.
Proof. exact (EQ_MP (@lem1509776) (@lem1509754)). Qed.
Lemma lem1509778 : term80 = term78.
Proof. exact (TRANS (@lem1509654) (@lem1509777)). Qed.
Lemma lem1509781 : term14 = term78.
Proof. exact (TRANS (@lem1509622) (@lem1509778)). Qed.
Lemma lem1509798 (y : real) : (term76 y) = (term76 y).
Proof. exact (eq_refl (term76 y)). Qed.
Lemma lem1509799 : term77 = term77.
Proof. exact (fun_ext (fun y : real => @lem1509798 y)). Qed.
Lemma lem1509800 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1509801 : term78 = term78.
Proof. exact (MK_COMB (@lem1509800) (@lem1509799)). Qed.
Lemma lem1509802 : term14 = term78.
Proof. exact (TRANS (@lem1509781) (@lem1509801)). Qed.
Lemma lem1509812 (y : real) (h1 : term76 y) : term76 y.
Proof. exact (h1). Qed.
Lemma lem1509813 (y : real) (h1 : term53 y) : term53 y.
Proof. exact (h1). Qed.
Lemma lem1509814 (y : real) (h1 : term53 y) : term49 y.
Proof. exact (proj2 (@lem1509813 y h1)). Qed.
Lemma lem1509815 (y : real) (h1 : term53 y) : term42 y.
Proof. exact (proj1 (@lem1509813 y h1)). Qed.
Lemma lem1509817 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509818 : term110 = term111.
Proof. exact (@lem1509817 (NUMERAL 0) term34). Qed.
Lemma lem1509819 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1509820 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1509821 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1509820 h1) (fun h1 : term111 = True => @lem1509819)). Qed.
Lemma lem1509822 : term111 = True.
Proof. exact (EQ_MP (@lem1509821) (@lem1509819)). Qed.
Lemma lem1509823 : term110 = True.
Proof. exact (TRANS (@lem1509818) (@lem1509822)). Qed.
Lemma lem1509824 : True = term110.
Proof. exact (SYM (@lem1509823)). Qed.
Lemma lem1509825 : term110.
Proof. exact (EQ_MP (@lem1509824) (@lem0)). Qed.
Lemma lem1509826 (y : real) (h1 : term53 y) : term113 y.
Proof. exact (conj (@lem1509825) (@lem1509815 y h1)). Qed.
Lemma lem1509828 (x : real) (y : real) : term114 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1509829 (y : real) : term115 y.
Proof. exact (@lem1509828 term116 y). Qed.
Lemma lem1509830 (y : real) (h1 : term53 y) : term117 y.
Proof. exact (@lem1509829 y (@lem1509826 y h1)). Qed.
Lemma lem1509831 (y : real) : (term118 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1509832 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1509833 (y : real) : (term119 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1509832) (@lem1509831 y)). Qed.
Lemma lem1509834 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509835 (y : real) : (term117 y) = (term42 y).
Proof. exact (MK_COMB (@lem1509833 y) (@lem1509834)). Qed.
Lemma lem1509836 (y : real) (h1 : term53 y) : term42 y.
Proof. exact (EQ_MP (@lem1509835 y) (@lem1509830 y h1)). Qed.
Lemma lem1509838 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509839 : term110 = term111.
Proof. exact (@lem1509838 (NUMERAL 0) term34). Qed.
Lemma lem1509840 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1509841 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1509842 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1509841 h1) (fun h1 : term111 = True => @lem1509840)). Qed.
Lemma lem1509843 : term111 = True.
Proof. exact (EQ_MP (@lem1509842) (@lem1509840)). Qed.
Lemma lem1509844 : term110 = True.
Proof. exact (TRANS (@lem1509839) (@lem1509843)). Qed.
Lemma lem1509845 : True = term110.
Proof. exact (SYM (@lem1509844)). Qed.
Lemma lem1509846 : term110.
Proof. exact (EQ_MP (@lem1509845) (@lem0)). Qed.
Lemma lem1509847 (y : real) (h1 : term53 y) : term120 y.
Proof. exact (conj (@lem1509846) (@lem1509814 y h1)). Qed.
Lemma lem1509849 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1509850 (y : real) : term122 y.
Proof. exact (@lem1509849 term116 (term27 y)). Qed.
Lemma lem1509851 (y : real) (h1 : term53 y) : term123 y.
Proof. exact (@lem1509850 y (@lem1509847 y h1)). Qed.
Lemma lem1509852 (y : real) : (term124 y) = (term27 y).
Proof. exact (@lem1483460 (term27 y)). Qed.
Lemma lem1509853 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509854 (y : real) : (term125 y) = (term48 y).
Proof. exact (MK_COMB (@lem1509853) (@lem1509852 y)). Qed.
Lemma lem1509855 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509856 (y : real) : (term123 y) = (term49 y).
Proof. exact (MK_COMB (@lem1509854 y) (@lem1509855)). Qed.
Lemma lem1509857 (y : real) (h1 : term53 y) : term49 y.
Proof. exact (EQ_MP (@lem1509856 y) (@lem1509851 y h1)). Qed.
Lemma lem1509858 (y : real) (h1 : term53 y) : term73 y.
Proof. exact (conj (@lem1509857 y h1) (@lem1509836 y h1)). Qed.
Lemma lem1509860 (x : real) (y : real) : term126 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1509861 (y : real) : term127 y.
Proof. exact (@lem1509860 (term27 y) y). Qed.
Lemma lem1509862 (y : real) (h1 : term53 y) : term128 y.
Proof. exact (@lem1509861 y (@lem1509858 y h1)). Qed.
Lemma lem1509863 (y : real) : (term129 y) = (term29 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1509865 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509866 : term33 = term32.
Proof. exact (@lem1509865 term34). Qed.
Lemma lem1509867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509868 : term35 = term36.
Proof. exact (MK_COMB (@lem1509867) (@lem1509866)). Qed.
Lemma lem1509869 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1509870 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1509868) (@lem1509869 y)). Qed.
Lemma lem1509871 (y : real) : (term129 y) = (term37 y).
Proof. exact (TRANS (@lem1509863 y) (@lem1509870 y)). Qed.
Lemma lem1509872 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1509873 (y : real) : (term129 y) = term32.
Proof. exact (TRANS (@lem1509871 y) (@lem1509872 y)). Qed.
Lemma lem1509874 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509875 (y : real) : (term130 y) = term131.
Proof. exact (MK_COMB (@lem1509874) (@lem1509873 y)). Qed.
Lemma lem1509876 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509877 (y : real) : (term128 y) = term132.
Proof. exact (MK_COMB (@lem1509875 y) (@lem1509876)). Qed.
Lemma lem1509878 (y : real) (h1 : term53 y) : term132.
Proof. exact (EQ_MP (@lem1509877 y) (@lem1509862 y h1)). Qed.
Lemma lem1509880 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509881 : term132 = term133.
Proof. exact (@lem1509880 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1509882 : term133 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1509883 : term132 = False.
Proof. exact (TRANS (@lem1509881) (@lem1509882)). Qed.
Lemma lem1509884 (y : real) (h1 : term53 y) : False.
Proof. exact (EQ_MP (@lem1509883) (@lem1509878 y h1)). Qed.
Lemma lem1509885 (y : real) (h1 : term73 y) : term73 y.
Proof. exact (h1). Qed.
Lemma lem1509886 (y : real) (h1 : term73 y) : term42 y.
Proof. exact (proj2 (@lem1509885 y h1)). Qed.
Lemma lem1509887 (y : real) (h1 : term73 y) : term49 y.
Proof. exact (proj1 (@lem1509885 y h1)). Qed.
Lemma lem1509889 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509890 : term110 = term111.
Proof. exact (@lem1509889 (NUMERAL 0) term34). Qed.
Lemma lem1509891 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1509892 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1509893 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1509892 h1) (fun h1 : term111 = True => @lem1509891)). Qed.
Lemma lem1509894 : term111 = True.
Proof. exact (EQ_MP (@lem1509893) (@lem1509891)). Qed.
Lemma lem1509895 : term110 = True.
Proof. exact (TRANS (@lem1509890) (@lem1509894)). Qed.
Lemma lem1509896 : True = term110.
Proof. exact (SYM (@lem1509895)). Qed.
Lemma lem1509897 : term110.
Proof. exact (EQ_MP (@lem1509896) (@lem0)). Qed.
Lemma lem1509898 (y : real) (h1 : term73 y) : term113 y.
Proof. exact (conj (@lem1509897) (@lem1509886 y h1)). Qed.
Lemma lem1509900 (x : real) (y : real) : term114 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1509901 (y : real) : term115 y.
Proof. exact (@lem1509900 term116 y). Qed.
Lemma lem1509902 (y : real) (h1 : term73 y) : term117 y.
Proof. exact (@lem1509901 y (@lem1509898 y h1)). Qed.
Lemma lem1509903 (y : real) : (term118 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1509904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1509905 (y : real) : (term119 y) = (real_ge y).
Proof. exact (MK_COMB (@lem1509904) (@lem1509903 y)). Qed.
Lemma lem1509906 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509907 (y : real) : (term117 y) = (term42 y).
Proof. exact (MK_COMB (@lem1509905 y) (@lem1509906)). Qed.
Lemma lem1509908 (y : real) (h1 : term73 y) : term42 y.
Proof. exact (EQ_MP (@lem1509907 y) (@lem1509902 y h1)). Qed.
Lemma lem1509910 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509911 : term110 = term111.
Proof. exact (@lem1509910 (NUMERAL 0) term34). Qed.
Lemma lem1509912 : term112 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1509913 (h1 : term112 = (BIT1 0)) : term111 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1509914 : (term112 = (BIT1 0)) = (term111 = True).
Proof. exact (prop_ext (fun h1 : term112 = (BIT1 0) => @lem1509913 h1) (fun h1 : term111 = True => @lem1509912)). Qed.
Lemma lem1509915 : term111 = True.
Proof. exact (EQ_MP (@lem1509914) (@lem1509912)). Qed.
Lemma lem1509916 : term110 = True.
Proof. exact (TRANS (@lem1509911) (@lem1509915)). Qed.
Lemma lem1509917 : True = term110.
Proof. exact (SYM (@lem1509916)). Qed.
Lemma lem1509918 : term110.
Proof. exact (EQ_MP (@lem1509917) (@lem0)). Qed.
Lemma lem1509919 (y : real) (h1 : term73 y) : term120 y.
Proof. exact (conj (@lem1509918) (@lem1509887 y h1)). Qed.
Lemma lem1509921 (x : real) (y : real) : term121 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1509922 (y : real) : term122 y.
Proof. exact (@lem1509921 term116 (term27 y)). Qed.
Lemma lem1509923 (y : real) (h1 : term73 y) : term123 y.
Proof. exact (@lem1509922 y (@lem1509919 y h1)). Qed.
Lemma lem1509924 (y : real) : (term124 y) = (term27 y).
Proof. exact (@lem1483460 (term27 y)). Qed.
Lemma lem1509925 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509926 (y : real) : (term125 y) = (term48 y).
Proof. exact (MK_COMB (@lem1509925) (@lem1509924 y)). Qed.
Lemma lem1509927 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509928 (y : real) : (term123 y) = (term49 y).
Proof. exact (MK_COMB (@lem1509926 y) (@lem1509927)). Qed.
Lemma lem1509929 (y : real) (h1 : term73 y) : term49 y.
Proof. exact (EQ_MP (@lem1509928 y) (@lem1509923 y h1)). Qed.
Lemma lem1509930 (y : real) (h1 : term73 y) : term73 y.
Proof. exact (conj (@lem1509929 y h1) (@lem1509908 y h1)). Qed.
Lemma lem1509932 (x : real) (y : real) : term126 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1509933 (y : real) : term127 y.
Proof. exact (@lem1509932 (term27 y) y). Qed.
Lemma lem1509934 (y : real) (h1 : term73 y) : term128 y.
Proof. exact (@lem1509933 y (@lem1509930 y h1)). Qed.
Lemma lem1509935 (y : real) : (term129 y) = (term29 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1509937 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1509938 : term33 = term32.
Proof. exact (@lem1509937 term34). Qed.
Lemma lem1509939 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1509940 : term35 = term36.
Proof. exact (MK_COMB (@lem1509939) (@lem1509938)). Qed.
Lemma lem1509941 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1509942 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1509940) (@lem1509941 y)). Qed.
Lemma lem1509943 (y : real) : (term129 y) = (term37 y).
Proof. exact (TRANS (@lem1509935 y) (@lem1509942 y)). Qed.
Lemma lem1509944 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1509945 (y : real) : (term129 y) = term32.
Proof. exact (TRANS (@lem1509943 y) (@lem1509944 y)). Qed.
Lemma lem1509946 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1509947 (y : real) : (term130 y) = term131.
Proof. exact (MK_COMB (@lem1509946) (@lem1509945 y)). Qed.
Lemma lem1509948 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1509949 (y : real) : (term128 y) = term132.
Proof. exact (MK_COMB (@lem1509947 y) (@lem1509948)). Qed.
Lemma lem1509950 (y : real) (h1 : term73 y) : term132.
Proof. exact (EQ_MP (@lem1509949 y) (@lem1509934 y h1)). Qed.
Lemma lem1509952 (n : nat) (m : nat) : (term109 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1509953 : term132 = term133.
Proof. exact (@lem1509952 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1509954 : term133 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1509955 : term132 = False.
Proof. exact (TRANS (@lem1509953) (@lem1509954)). Qed.
Lemma lem1509956 (y : real) (h1 : term73 y) : False.
Proof. exact (EQ_MP (@lem1509955) (@lem1509950 y h1)). Qed.
Lemma lem1509957 (y : real) (h1 : term76 y) : False.
Proof. exact (or_elim (@lem1509812 y h1) (fun h0 : term53 y => @lem1509884 y h0) (fun h0 : term73 y => @lem1509956 y h0)). Qed.
Lemma lem1509959 (y : real) (h1 : term76 y) : term76 y.
Proof. exact (h1). Qed.
Lemma lem1509960 (y : real) (h1 : term76 y) : (term76 y) = False.
Proof. exact (prop_ext (fun h2 : term76 y => @lem1509957 y h1) (fun h2 : False => @lem1509959 y h1)). Qed.
Lemma lem1509961 (y : real) (h1 : term76 y) : False.
Proof. exact (EQ_MP (@lem1509960 y h1) (@lem1509959 y h1)). Qed.
Lemma lem1509962 (h1 : term78) : term78.
Proof. exact (h1). Qed.
Lemma lem1509963 (h1 : term78) : False.
Proof. exact (ex_elim (@lem1509962 h1) (fun y : real => fun h0 : term77 y => @lem1509961 y h0)). Qed.
Lemma lem1509964 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1509965 (h1 : term14) : term78.
Proof. exact (EQ_MP (@lem1509802) (@lem1509964 h1)). Qed.
Lemma lem1509966 (h1 : term14) : term78 = False.
Proof. exact (prop_ext (fun h2 : term78 => @lem1509963 h2) (fun h2 : False => @lem1509965 h1)). Qed.
Lemma lem1509967 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1509966 h1) (@lem1509965 h1)). Qed.
Lemma lem1509968 : term134.
Proof. exact (fun h0 : term14 => @lem1509967 h0). Qed.
Lemma lem1509969 : term135.
Proof. exact (@lem1386578 term136). Qed.
Lemma lem1509970 : term136.
Proof. exact (@lem1509969 (@lem1509968)). Qed.
