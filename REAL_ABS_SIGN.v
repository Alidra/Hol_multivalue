Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SIGN_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483484_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1541418 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17362 (term2 x y) (term3 x)). Qed.
Lemma lem1541419 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1541420 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1541419 (term8 x)). Qed.
Lemma lem1541421 (y : real) (x : real) : (term9 x y) = (term10 y x).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1541422 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1541423 (y : real) (x : real) : (term11 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1541422) (@lem1541421 y x)). Qed.
Lemma lem1541424 (y : real) (x : real) : (term11 x y) = (term1 y x).
Proof. exact (TRANS (@lem1541423 y x) (@lem1541418 y x)). Qed.
Lemma lem1541425 (x : real) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1541424 y x)). Qed.
Lemma lem1541426 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541427 (x : real) : (term7 x) = (term14 x).
Proof. exact (MK_COMB (@lem1541426) (@lem1541425 x)). Qed.
Lemma lem1541428 (x : real) : (term6 x) = (term14 x).
Proof. exact (TRANS (@lem1541420 x) (@lem1541427 x)). Qed.
Lemma lem1541429 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1541430 : term15 = term16.
Proof. exact (@lem1541429 term17). Qed.
Lemma lem1541431 (x : real) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1541432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1541433 (x : real) : (term20 x) = (term6 x).
Proof. exact (MK_COMB (@lem1541432) (@lem1541431 x)). Qed.
Lemma lem1541434 (x : real) : (term20 x) = (term14 x).
Proof. exact (TRANS (@lem1541433 x) (@lem1541428 x)). Qed.
Lemma lem1541435 : term21 = term22.
Proof. exact (fun_ext (fun x : real => @lem1541434 x)). Qed.
Lemma lem1541436 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541437 : term16 = term23.
Proof. exact (MK_COMB (@lem1541436) (@lem1541435)). Qed.
Lemma lem1541439 : term15 = term23.
Proof. exact (TRANS (@lem1541430) (@lem1541437)). Qed.
Lemma lem1541446 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1541447 (x : real) : (term13 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1541446 y x)). Qed.
Lemma lem1541448 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541449 (x : real) : (term14 x) = (term14 x).
Proof. exact (MK_COMB (@lem1541448) (@lem1541447 x)). Qed.
Lemma lem1541450 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1541449 x)). Qed.
Lemma lem1541451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541452 : term23 = term23.
Proof. exact (MK_COMB (@lem1541451) (@lem1541450)). Qed.
Lemma lem1541453 : term15 = term23.
Proof. exact (TRANS (@lem1541439) (@lem1541452)). Qed.
Lemma lem1541454 (x : real) (y : real) : (term2 x y) = (term24 x y).
Proof. exact (@lem1483521 y (term25 x y)). Qed.
Lemma lem1541467 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 y (term25 x y)). Qed.
Lemma lem1541468 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541469 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1541468) (@lem1541467 x y)). Qed.
Lemma lem1541470 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541471 (x : real) (y : real) : (term24 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1541469 x y) (@lem1541470)). Qed.
Lemma lem1541472 (x : real) (y : real) : (term2 x y) = (term31 x y).
Proof. exact (TRANS (@lem1541454 x y) (@lem1541471 x y)). Qed.
Lemma lem1541473 (x : real) : (term32 x) = (term33 x).
Proof. exact (@lem1483531 term30 x). Qed.
Lemma lem1541479 (x : real) : (term34 x) = (term35 x).
Proof. exact (@lem1483519 term30 x). Qed.
Lemma lem1541484 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483448 (term36 x)). Qed.
Lemma lem1541486 (x : real) : (term34 x) = (term36 x).
Proof. exact (TRANS (@lem1541479 x) (@lem1541484 x)). Qed.
Lemma lem1541487 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1541488 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1541487) (@lem1541486 x)). Qed.
Lemma lem1541489 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541490 (x : real) : (term33 x) = (term39 x).
Proof. exact (MK_COMB (@lem1541488 x) (@lem1541489)). Qed.
Lemma lem1541491 (x : real) : (term32 x) = (term39 x).
Proof. exact (TRANS (@lem1541473 x) (@lem1541490 x)). Qed.
Lemma lem1541492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541493 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1541492) (@lem1541472 x y)). Qed.
Lemma lem1541494 (y : real) (x : real) : (term1 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1541493 x y) (@lem1541491 x)). Qed.
Lemma lem1541495 (x : real) : (term13 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1541494 y x)). Qed.
Lemma lem1541496 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541497 (x : real) : (term14 x) = (term44 x).
Proof. exact (MK_COMB (@lem1541496) (@lem1541495 x)). Qed.
Lemma lem1541498 : term22 = term45.
Proof. exact (fun_ext (fun x : real => @lem1541497 x)). Qed.
Lemma lem1541499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541500 : term23 = term46.
Proof. exact (MK_COMB (@lem1541499) (@lem1541498)). Qed.
Lemma lem1541501 : term15 = term46.
Proof. exact (TRANS (@lem1541453) (@lem1541500)). Qed.
Lemma lem1541527 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem1541528 (P : real -> Prop) (Q : Prop) : (term49 P Q) = (term50 P Q).
Proof. exact (@lem1541527 real P Q). Qed.
Lemma lem1541529 (x : real) : (term51 x) = (term52 x).
Proof. exact (@lem1541528 (term53 x) (term39 x)). Qed.
Lemma lem1541530 (x : real) (y : real) : (term54 x y) = (term31 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1541531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541532 (x : real) (y : real) : (term55 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1541531) (@lem1541530 x y)). Qed.
Lemma lem1541533 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1541534 (y : real) (x : real) : (term56 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1541532 x y) (@lem1541533 x)). Qed.
Lemma lem1541535 (x : real) : (term57 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1541534 y x)). Qed.
Lemma lem1541536 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541537 (x : real) : (term51 x) = (term44 x).
Proof. exact (MK_COMB (@lem1541536) (@lem1541535 x)). Qed.
Lemma lem1541538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1541539 (x : real) : (term58 x) = (term59 x).
Proof. exact (MK_COMB (@lem1541538) (@lem1541537 x)). Qed.
Lemma lem1541540 (x : real) (y : real) : (term54 x y) = (term31 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1541541 (x : real) : (term60 x) = (term53 x).
Proof. exact (fun_ext (fun y : real => @lem1541540 x y)). Qed.
Lemma lem1541542 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541543 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1541542) (@lem1541541 x)). Qed.
Lemma lem1541544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541545 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1541544) (@lem1541543 x)). Qed.
Lemma lem1541546 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1541547 (x : real) : (term52 x) = (term65 x).
Proof. exact (MK_COMB (@lem1541545 x) (@lem1541546 x)). Qed.
Lemma lem1541548 (x : real) : ((term51 x) = (term52 x)) = ((term44 x) = (term65 x)).
Proof. exact (MK_COMB (@lem1541539 x) (@lem1541547 x)). Qed.
Lemma lem1541549 (x : real) : (term44 x) = (term65 x).
Proof. exact (EQ_MP (@lem1541548 x) (@lem1541529 x)). Qed.
Lemma lem1541554 : term45 = term66.
Proof. exact (fun_ext (fun x : real => @lem1541549 x)). Qed.
Lemma lem1541555 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541556 : term46 = term67.
Proof. exact (MK_COMB (@lem1541555) (@lem1541554)). Qed.
Lemma lem1541606 {A : Type'} (P : A -> Prop) (Q : Prop) : (term48 A P Q) = (term47 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1541607 (P : real -> Prop) (Q : Prop) : (term50 P Q) = (term49 P Q).
Proof. exact (@lem1541606 real P Q). Qed.
Lemma lem1541608 (x : real) : (term52 x) = (term51 x).
Proof. exact (@lem1541607 (term53 x) (term39 x)). Qed.
Lemma lem1541609 (x : real) (y : real) : (term54 x y) = (term31 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1541610 (x : real) : (term60 x) = (term53 x).
Proof. exact (fun_ext (fun y : real => @lem1541609 x y)). Qed.
Lemma lem1541611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541612 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1541611) (@lem1541610 x)). Qed.
Lemma lem1541613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541614 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1541613) (@lem1541612 x)). Qed.
Lemma lem1541615 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1541616 (x : real) : (term52 x) = (term65 x).
Proof. exact (MK_COMB (@lem1541614 x) (@lem1541615 x)). Qed.
Lemma lem1541617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1541618 (x : real) : (term68 x) = (term69 x).
Proof. exact (MK_COMB (@lem1541617) (@lem1541616 x)). Qed.
Lemma lem1541619 (x : real) (y : real) : (term54 x y) = (term31 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1541620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541621 (x : real) (y : real) : (term55 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1541620) (@lem1541619 x y)). Qed.
Lemma lem1541622 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1541623 (y : real) (x : real) : (term56 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1541621 x y) (@lem1541622 x)). Qed.
Lemma lem1541624 (x : real) : (term57 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1541623 y x)). Qed.
Lemma lem1541625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541626 (x : real) : (term51 x) = (term44 x).
Proof. exact (MK_COMB (@lem1541625) (@lem1541624 x)). Qed.
Lemma lem1541627 (x : real) : ((term52 x) = (term51 x)) = ((term65 x) = (term44 x)).
Proof. exact (MK_COMB (@lem1541618 x) (@lem1541626 x)). Qed.
Lemma lem1541628 (x : real) : (term65 x) = (term44 x).
Proof. exact (EQ_MP (@lem1541627 x) (@lem1541608 x)). Qed.
Lemma lem1541629 : term66 = term45.
Proof. exact (fun_ext (fun x : real => @lem1541628 x)). Qed.
Lemma lem1541630 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541631 : term67 = term46.
Proof. exact (MK_COMB (@lem1541630) (@lem1541629)). Qed.
Lemma lem1541632 : term46 = term46.
Proof. exact (TRANS (@lem1541556) (@lem1541631)). Qed.
Lemma lem1541635 : term15 = term46.
Proof. exact (TRANS (@lem1541501) (@lem1541632)). Qed.
Lemma lem1541642 (y : real) (x : real) : (term42 y x) = (term42 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem1541643 (x : real) : (term43 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1541642 y x)). Qed.
Lemma lem1541644 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541645 (x : real) : (term44 x) = (term44 x).
Proof. exact (MK_COMB (@lem1541644) (@lem1541643 x)). Qed.
Lemma lem1541646 : term45 = term45.
Proof. exact (fun_ext (fun x : real => @lem1541645 x)). Qed.
Lemma lem1541647 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541648 : term46 = term46.
Proof. exact (MK_COMB (@lem1541647) (@lem1541646)). Qed.
Lemma lem1541649 : term15 = term46.
Proof. exact (TRANS (@lem1541635) (@lem1541648)). Qed.
Lemma lem1541651 (a : real) (x : real) (r : real) : (term70 a x r) = (term71 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1541652 (x : real) (y : real) : (term31 x y) = (term72 x y).
Proof. exact (@lem1541651 y (real_sub x y) term30). Qed.
Lemma lem1541665 (x : real) (y : real) : (real_sub x y) = (term73 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1541668 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1541669 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1541668) (@lem1541665 x y)). Qed.
Lemma lem1541670 (x : real) (y : real) : (term76 x y) = (term73 x y).
Proof. exact (@lem1483460 (term73 x y)). Qed.
Lemma lem1541671 (x : real) (y : real) : (term75 x y) = (term73 x y).
Proof. exact (TRANS (@lem1541669 x y) (@lem1541670 x y)). Qed.
Lemma lem1541674 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1541675 (x : real) (y : real) : (term77 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1541674 y) (@lem1541671 x y)). Qed.
Lemma lem1541676 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (@lem1483484 x y (term36 y)). Qed.
Lemma lem1541677 (y : real) : (term80 y) = (term81 y).
Proof. exact (@lem1483442 term82 y). Qed.
Lemma lem1541679 (m : nat) : (term83 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1541680 : term84 = term30.
Proof. exact (@lem1541679 term85). Qed.
Lemma lem1541681 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541682 : term86 = term87.
Proof. exact (MK_COMB (@lem1541681) (@lem1541680)). Qed.
Lemma lem1541683 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1541684 (y : real) : (term81 y) = (term88 y).
Proof. exact (MK_COMB (@lem1541682) (@lem1541683 y)). Qed.
Lemma lem1541685 (y : real) : (term80 y) = (term88 y).
Proof. exact (TRANS (@lem1541677 y) (@lem1541684 y)). Qed.
Lemma lem1541686 (y : real) : (term88 y) = term30.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1541687 (y : real) : (term80 y) = term30.
Proof. exact (TRANS (@lem1541685 y) (@lem1541686 y)). Qed.
Lemma lem1541688 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1541689 (y : real) (x : real) : (term79 x y) = (term89 x).
Proof. exact (MK_COMB (@lem1541688 x) (@lem1541687 y)). Qed.
Lemma lem1541690 (y : real) (x : real) : (term78 x y) = (term89 x).
Proof. exact (TRANS (@lem1541676 x y) (@lem1541689 y x)). Qed.
Lemma lem1541691 (x : real) : (term89 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1541692 (y : real) (x : real) : (term78 x y) = x.
Proof. exact (TRANS (@lem1541690 y x) (@lem1541691 x)). Qed.
Lemma lem1541693 (y : real) (x : real) : (term77 x y) = x.
Proof. exact (TRANS (@lem1541675 x y) (@lem1541692 y x)). Qed.
Lemma lem1541694 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541695 (y : real) (x : real) : (term90 x y) = (real_gt x).
Proof. exact (MK_COMB (@lem1541694) (@lem1541693 y x)). Qed.
Lemma lem1541696 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541697 (y : real) (x : real) : (term91 x y) = (term92 x).
Proof. exact (MK_COMB (@lem1541695 y x) (@lem1541696)). Qed.
Lemma lem1541710 (x : real) (y : real) : (real_sub x y) = (term73 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1541713 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem1541714 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1541713) (@lem1541710 x y)). Qed.
Lemma lem1541715 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (@lem1483508 x term82 (term36 y)). Qed.
Lemma lem1541716 (y : real) : (term97 y) = (term98 y).
Proof. exact (@lem1483476 term82 term82 y). Qed.
Lemma lem1541718 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1541719 : term101 = term102.
Proof. exact (@lem1541718 term85 term85). Qed.
Lemma lem1541720 : (term103 = (BIT1 0)) = (term104 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1541721 : term104 = term85.
Proof. exact (EQ_MP (@lem1541720) (@lem940073)). Qed.
Lemma lem1541722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1541723 : term102 = term105.
Proof. exact (MK_COMB (@lem1541722) (@lem1541721)). Qed.
Lemma lem1541724 : term101 = term105.
Proof. exact (TRANS (@lem1541719) (@lem1541723)). Qed.
Lemma lem1541725 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541726 : term106 = term74.
Proof. exact (MK_COMB (@lem1541725) (@lem1541724)). Qed.
Lemma lem1541727 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1541728 (y : real) : (term98 y) = (term107 y).
Proof. exact (MK_COMB (@lem1541726) (@lem1541727 y)). Qed.
Lemma lem1541729 (y : real) : (term97 y) = (term107 y).
Proof. exact (TRANS (@lem1541716 y) (@lem1541728 y)). Qed.
Lemma lem1541730 (y : real) : (term107 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1541731 (y : real) : (term97 y) = y.
Proof. exact (TRANS (@lem1541729 y) (@lem1541730 y)). Qed.
Lemma lem1541734 (x : real) : (term108 x) = (term108 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1541735 (x : real) (y : real) : (term96 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1541734 x) (@lem1541731 y)). Qed.
Lemma lem1541736 (x : real) (y : real) : (term95 x y) = (term109 x y).
Proof. exact (TRANS (@lem1541715 x y) (@lem1541735 x y)). Qed.
Lemma lem1541737 (x : real) (y : real) : (term94 x y) = (term109 x y).
Proof. exact (TRANS (@lem1541714 x y) (@lem1541736 x y)). Qed.
Lemma lem1541740 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1541741 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1541740 y) (@lem1541737 x y)). Qed.
Lemma lem1541742 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (@lem1483484 (term36 x) y y). Qed.
Lemma lem1541743 (y : real) : (real_add y y) = (term113 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1541744 : term114 = term115.
Proof. exact (@lem1367770 term85 term85). Qed.
Lemma lem1541745 : term116 = term117.
Proof. exact (@lem706885). Qed.
Lemma lem1541746 : (term116 = term117) = (term118 = term119).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term117). Qed.
Lemma lem1541747 : term118 = term119.
Proof. exact (EQ_MP (@lem1541746) (@lem1541745)). Qed.
Lemma lem1541748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1541749 : term115 = term120.
Proof. exact (MK_COMB (@lem1541748) (@lem1541747)). Qed.
Lemma lem1541750 : term114 = term120.
Proof. exact (TRANS (@lem1541744) (@lem1541749)). Qed.
Lemma lem1541751 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541752 : term121 = term122.
Proof. exact (MK_COMB (@lem1541751) (@lem1541750)). Qed.
Lemma lem1541753 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1541754 (y : real) : (term113 y) = (term123 y).
Proof. exact (MK_COMB (@lem1541752) (@lem1541753 y)). Qed.
Lemma lem1541755 (y : real) : (real_add y y) = (term123 y).
Proof. exact (TRANS (@lem1541743 y) (@lem1541754 y)). Qed.
Lemma lem1541756 (x : real) : (term108 x) = (term108 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1541757 (x : real) (y : real) : (term112 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1541756 x) (@lem1541755 y)). Qed.
Lemma lem1541758 (x : real) (y : real) : (term111 x y) = (term124 x y).
Proof. exact (TRANS (@lem1541742 x y) (@lem1541757 x y)). Qed.
Lemma lem1541759 (x : real) (y : real) : (term110 x y) = (term124 x y).
Proof. exact (TRANS (@lem1541741 x y) (@lem1541758 x y)). Qed.
Lemma lem1541760 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541761 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (MK_COMB (@lem1541760) (@lem1541759 x y)). Qed.
Lemma lem1541762 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541763 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1541761 x y) (@lem1541762)). Qed.
Lemma lem1541764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541765 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1541764) (@lem1541763 x y)). Qed.
Lemma lem1541766 (y : real) (x : real) : (term72 x y) = (term131 y x).
Proof. exact (MK_COMB (@lem1541765 x y) (@lem1541697 y x)). Qed.
Lemma lem1541767 (y : real) (x : real) : (term31 x y) = (term131 y x).
Proof. exact (TRANS (@lem1541652 x y) (@lem1541766 y x)). Qed.
Lemma lem1541768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541769 (y : real) (x : real) : (term41 x y) = (term132 y x).
Proof. exact (MK_COMB (@lem1541768) (@lem1541767 y x)). Qed.
Lemma lem1541770 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1541773 (y : real) (x : real) : (term42 y x) = (term133 y x).
Proof. exact (MK_COMB (@lem1541769 y x) (@lem1541770 x)). Qed.
Lemma lem1541774 (y : real) (x : real) (h1 : term133 y x) : term133 y x.
Proof. exact (h1). Qed.
Lemma lem1541775 (y : real) (x : real) (h1 : term133 y x) : term39 x.
Proof. exact (proj2 (@lem1541774 y x h1)). Qed.
Lemma lem1541776 (y : real) (x : real) (h1 : term133 y x) : term131 y x.
Proof. exact (proj1 (@lem1541774 y x h1)). Qed.
Lemma lem1541777 (y : real) (x : real) (h1 : term133 y x) : term92 x.
Proof. exact (proj2 (@lem1541776 y x h1)). Qed.
Lemma lem1541780 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1541781 : term135 = term136.
Proof. exact (@lem1541780 (NUMERAL 0) term85). Qed.
Lemma lem1541782 : term137 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1541783 (h1 : term137 = (BIT1 0)) : term136 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1541784 : (term137 = (BIT1 0)) = (term136 = True).
Proof. exact (prop_ext (fun h1 : term137 = (BIT1 0) => @lem1541783 h1) (fun h1 : term136 = True => @lem1541782)). Qed.
Lemma lem1541785 : term136 = True.
Proof. exact (EQ_MP (@lem1541784) (@lem1541782)). Qed.
Lemma lem1541786 : term135 = True.
Proof. exact (TRANS (@lem1541781) (@lem1541785)). Qed.
Lemma lem1541787 : True = term135.
Proof. exact (SYM (@lem1541786)). Qed.
Lemma lem1541788 : term135.
Proof. exact (EQ_MP (@lem1541787) (@lem0)). Qed.
Lemma lem1541789 (y : real) (x : real) (h1 : term133 y x) : term138 x.
Proof. exact (conj (@lem1541788) (@lem1541775 y x h1)). Qed.
Lemma lem1541791 (x : real) (y : real) : term139 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1541792 (x : real) : term140 x.
Proof. exact (@lem1541791 term105 (term36 x)). Qed.
Lemma lem1541793 (y : real) (x : real) (h1 : term133 y x) : term141 x.
Proof. exact (@lem1541792 x (@lem1541789 y x h1)). Qed.
Lemma lem1541794 (x : real) : (term142 x) = (term36 x).
Proof. exact (@lem1483460 (term36 x)). Qed.
Lemma lem1541795 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1541796 (x : real) : (term143 x) = (term38 x).
Proof. exact (MK_COMB (@lem1541795) (@lem1541794 x)). Qed.
Lemma lem1541797 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541798 (x : real) : (term141 x) = (term39 x).
Proof. exact (MK_COMB (@lem1541796 x) (@lem1541797)). Qed.
Lemma lem1541799 (y : real) (x : real) (h1 : term133 y x) : term39 x.
Proof. exact (EQ_MP (@lem1541798 x) (@lem1541793 y x h1)). Qed.
Lemma lem1541801 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1541802 : term135 = term136.
Proof. exact (@lem1541801 (NUMERAL 0) term85). Qed.
Lemma lem1541803 : term137 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1541804 (h1 : term137 = (BIT1 0)) : term136 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1541805 : (term137 = (BIT1 0)) = (term136 = True).
Proof. exact (prop_ext (fun h1 : term137 = (BIT1 0) => @lem1541804 h1) (fun h1 : term136 = True => @lem1541803)). Qed.
Lemma lem1541806 : term136 = True.
Proof. exact (EQ_MP (@lem1541805) (@lem1541803)). Qed.
Lemma lem1541807 : term135 = True.
Proof. exact (TRANS (@lem1541802) (@lem1541806)). Qed.
Lemma lem1541808 : True = term135.
Proof. exact (SYM (@lem1541807)). Qed.
Lemma lem1541809 : term135.
Proof. exact (EQ_MP (@lem1541808) (@lem0)). Qed.
Lemma lem1541810 (y : real) (x : real) (h1 : term133 y x) : term144 x.
Proof. exact (conj (@lem1541809) (@lem1541777 y x h1)). Qed.
Lemma lem1541812 (x : real) (y : real) : term145 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1541813 (x : real) : term146 x.
Proof. exact (@lem1541812 term105 x). Qed.
Lemma lem1541814 (y : real) (x : real) (h1 : term133 y x) : term147 x.
Proof. exact (@lem1541813 x (@lem1541810 y x h1)). Qed.
Lemma lem1541815 (x : real) : (term107 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1541816 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541817 (x : real) : (term148 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1541816) (@lem1541815 x)). Qed.
Lemma lem1541818 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541819 (x : real) : (term147 x) = (term92 x).
Proof. exact (MK_COMB (@lem1541817 x) (@lem1541818)). Qed.
Lemma lem1541820 (y : real) (x : real) (h1 : term133 y x) : term92 x.
Proof. exact (EQ_MP (@lem1541819 x) (@lem1541814 y x h1)). Qed.
Lemma lem1541821 (y : real) (x : real) (h1 : term133 y x) : term149 x.
Proof. exact (conj (@lem1541820 y x h1) (@lem1541799 y x h1)). Qed.
Lemma lem1541823 (x : real) (y : real) : term150 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1541824 (x : real) : term151 x.
Proof. exact (@lem1541823 x (term36 x)). Qed.
Lemma lem1541825 (y : real) (x : real) (h1 : term133 y x) : term152 x.
Proof. exact (@lem1541824 x (@lem1541821 y x h1)). Qed.
Lemma lem1541826 (x : real) : (term80 x) = (term81 x).
Proof. exact (@lem1483442 term82 x). Qed.
Lemma lem1541828 (m : nat) : (term83 m) = term30.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1541829 : term84 = term30.
Proof. exact (@lem1541828 term85). Qed.
Lemma lem1541830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541831 : term86 = term87.
Proof. exact (MK_COMB (@lem1541830) (@lem1541829)). Qed.
Lemma lem1541832 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1541833 (x : real) : (term81 x) = (term88 x).
Proof. exact (MK_COMB (@lem1541831) (@lem1541832 x)). Qed.
Lemma lem1541834 (x : real) : (term80 x) = (term88 x).
Proof. exact (TRANS (@lem1541826 x) (@lem1541833 x)). Qed.
Lemma lem1541835 (x : real) : (term88 x) = term30.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1541836 (x : real) : (term80 x) = term30.
Proof. exact (TRANS (@lem1541834 x) (@lem1541835 x)). Qed.
Lemma lem1541837 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541838 (x : real) : (term153 x) = term154.
Proof. exact (MK_COMB (@lem1541837) (@lem1541836 x)). Qed.
Lemma lem1541839 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1541840 (x : real) : (term152 x) = term155.
Proof. exact (MK_COMB (@lem1541838 x) (@lem1541839)). Qed.
Lemma lem1541841 (y : real) (x : real) (h1 : term133 y x) : term155.
Proof. exact (EQ_MP (@lem1541840 x) (@lem1541825 y x h1)). Qed.
Lemma lem1541843 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1541844 : term155 = term156.
Proof. exact (@lem1541843 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1541845 : term156 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1541846 : term155 = False.
Proof. exact (TRANS (@lem1541844) (@lem1541845)). Qed.
Lemma lem1541847 (y : real) (x : real) (h1 : term133 y x) : False.
Proof. exact (EQ_MP (@lem1541846) (@lem1541841 y x h1)). Qed.
Lemma lem1541848 (y : real) (x : real) (h1 : term42 y x) : term42 y x.
Proof. exact (h1). Qed.
Lemma lem1541849 (y : real) (x : real) (h1 : term42 y x) : term133 y x.
Proof. exact (EQ_MP (@lem1541773 y x) (@lem1541848 y x h1)). Qed.
Lemma lem1541850 (y : real) (x : real) (h1 : term42 y x) : (term133 y x) = False.
Proof. exact (prop_ext (fun h2 : term133 y x => @lem1541847 y x h2) (fun h2 : False => @lem1541849 y x h1)). Qed.
Lemma lem1541851 (y : real) (x : real) (h1 : term42 y x) : False.
Proof. exact (EQ_MP (@lem1541850 y x h1) (@lem1541849 y x h1)). Qed.
Lemma lem1541852 (x : real) (h1 : term44 x) : term44 x.
Proof. exact (h1). Qed.
Lemma lem1541853 (x : real) (h1 : term44 x) : False.
Proof. exact (ex_elim (@lem1541852 x h1) (fun y : real => fun h0 : term43 x y => @lem1541851 y x h0)). Qed.
Lemma lem1541854 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1541855 (h1 : term46) : False.
Proof. exact (ex_elim (@lem1541854 h1) (fun x : real => fun h0 : term45 x => @lem1541853 x h0)). Qed.
Lemma lem1541856 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1541857 (h1 : term15) : term46.
Proof. exact (EQ_MP (@lem1541649) (@lem1541856 h1)). Qed.
Lemma lem1541858 (h1 : term15) : term46 = False.
Proof. exact (prop_ext (fun h2 : term46 => @lem1541855 h2) (fun h2 : False => @lem1541857 h1)). Qed.
Lemma lem1541859 (h1 : term15) : False.
Proof. exact (EQ_MP (@lem1541858 h1) (@lem1541857 h1)). Qed.
Lemma lem1541860 : term157.
Proof. exact (fun h0 : term15 => @lem1541859 h0). Qed.
Lemma lem1541861 : term158.
Proof. exact (@lem1386578 term159). Qed.
Lemma lem1541862 : term159.
Proof. exact (@lem1541861 (@lem1541860)). Qed.
