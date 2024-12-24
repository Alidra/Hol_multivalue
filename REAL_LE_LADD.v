Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LADD_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
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
Lemma lem1499429 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17646 (term2 y x z) (real_le y z)). Qed.
Lemma lem1499430 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1499431 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (@lem1499430 (term7 x y)). Qed.
Lemma lem1499432 (x : real) (y : real) (z : real) : (term8 x y z) = ((term2 y x z) = (real_le y z)).
Proof. exact (eq_refl (term8 x y z)). Qed.
Lemma lem1499433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1499434 (x : real) (y : real) (z : real) : (term9 x y z) = (term0 x y z).
Proof. exact (MK_COMB (@lem1499433) (@lem1499432 x y z)). Qed.
Lemma lem1499435 (x : real) (y : real) (z : real) : (term9 x y z) = (term1 x y z).
Proof. exact (TRANS (@lem1499434 x y z) (@lem1499429 x y z)). Qed.
Lemma lem1499436 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1499435 x y z)). Qed.
Lemma lem1499437 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499438 (x : real) (y : real) : (term6 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1499437) (@lem1499436 x y)). Qed.
Lemma lem1499439 (x : real) (y : real) : (term5 x y) = (term12 x y).
Proof. exact (TRANS (@lem1499431 x y) (@lem1499438 x y)). Qed.
Lemma lem1499440 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1499441 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1499440 (term15 x)). Qed.
Lemma lem1499442 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1499443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1499444 (x : real) (y : real) : (term18 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1499443) (@lem1499442 x y)). Qed.
Lemma lem1499445 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1499444 x y) (@lem1499439 x y)). Qed.
Lemma lem1499446 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1499445 x y)). Qed.
Lemma lem1499447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499448 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1499447) (@lem1499446 x)). Qed.
Lemma lem1499449 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1499441 x) (@lem1499448 x)). Qed.
Lemma lem1499450 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1499451 : term22 = term23.
Proof. exact (@lem1499450 term24). Qed.
Lemma lem1499452 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1499453 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1499454 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1499453) (@lem1499452 x)). Qed.
Lemma lem1499455 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1499454 x) (@lem1499449 x)). Qed.
Lemma lem1499456 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1499455 x)). Qed.
Lemma lem1499457 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499458 : term23 = term30.
Proof. exact (MK_COMB (@lem1499457) (@lem1499456)). Qed.
Lemma lem1499460 : term22 = term30.
Proof. exact (TRANS (@lem1499451) (@lem1499458)). Qed.
Lemma lem1499477 (x : real) (y : real) (z : real) : (term1 x y z) = (term1 x y z).
Proof. exact (eq_refl (term1 x y z)). Qed.
Lemma lem1499478 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1499477 x y z)). Qed.
Lemma lem1499479 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499480 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1499479) (@lem1499478 x y)). Qed.
Lemma lem1499481 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1499480 x y)). Qed.
Lemma lem1499482 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499483 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1499482) (@lem1499481 x)). Qed.
Lemma lem1499484 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1499483 x)). Qed.
Lemma lem1499485 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499486 : term30 = term30.
Proof. exact (MK_COMB (@lem1499485) (@lem1499484)). Qed.
Lemma lem1499487 : term22 = term30.
Proof. exact (TRANS (@lem1499460) (@lem1499486)). Qed.
Lemma lem1499488 (z : real) (x : real) (y : real) : (term2 y x z) = (term31 z x y).
Proof. exact (@lem1483523 (real_add x z) (real_add x y)). Qed.
Lemma lem1499506 (z : real) (x : real) (y : real) : (term32 z x y) = (term33 z x y).
Proof. exact (@lem1483519 (real_add x z) (real_add x y)). Qed.
Lemma lem1499513 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1483508 x term36 y). Qed.
Lemma lem1499514 (x : real) (z : real) : (term37 x z) = (term37 x z).
Proof. exact (eq_refl (term37 x z)). Qed.
Lemma lem1499515 (z : real) (x : real) (y : real) : (term33 z x y) = (term38 z x y).
Proof. exact (MK_COMB (@lem1499514 x z) (@lem1499513 x y)). Qed.
Lemma lem1499516 (x : real) (z : real) (y : real) : (term38 z x y) = (term39 x z y).
Proof. exact (@lem1483480 x (term40 x) z (term40 y)). Qed.
Lemma lem1499517 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483442 term36 x). Qed.
Lemma lem1499519 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1499520 : term45 = term44.
Proof. exact (@lem1499519 term46). Qed.
Lemma lem1499521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1499522 : term47 = term48.
Proof. exact (MK_COMB (@lem1499521) (@lem1499520)). Qed.
Lemma lem1499523 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1499524 (x : real) : (term42 x) = (term49 x).
Proof. exact (MK_COMB (@lem1499522) (@lem1499523 x)). Qed.
Lemma lem1499525 (x : real) : (term41 x) = (term49 x).
Proof. exact (TRANS (@lem1499517 x) (@lem1499524 x)). Qed.
Lemma lem1499526 (x : real) : (term49 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1499527 (x : real) : (term41 x) = term44.
Proof. exact (TRANS (@lem1499525 x) (@lem1499526 x)). Qed.
Lemma lem1499528 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1499529 (x : real) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem1499528) (@lem1499527 x)). Qed.
Lemma lem1499530 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1499531 (x : real) (y : real) (z : real) : (term39 x z y) = (term54 y z).
Proof. exact (MK_COMB (@lem1499529 x) (@lem1499530 y z)). Qed.
Lemma lem1499532 (x : real) (y : real) (z : real) : (term38 z x y) = (term54 y z).
Proof. exact (TRANS (@lem1499516 x z y) (@lem1499531 x y z)). Qed.
Lemma lem1499533 (y : real) (z : real) : (term54 y z) = (term53 y z).
Proof. exact (@lem1483448 (term53 y z)). Qed.
Lemma lem1499534 (x : real) (y : real) (z : real) : (term38 z x y) = (term53 y z).
Proof. exact (TRANS (@lem1499532 x y z) (@lem1499533 y z)). Qed.
Lemma lem1499535 (x : real) (y : real) (z : real) : (term33 z x y) = (term53 y z).
Proof. exact (TRANS (@lem1499515 z x y) (@lem1499534 x y z)). Qed.
Lemma lem1499537 (x : real) (y : real) (z : real) : (term32 z x y) = (term53 y z).
Proof. exact (TRANS (@lem1499506 z x y) (@lem1499535 x y z)). Qed.
Lemma lem1499538 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1499539 (x : real) (y : real) (z : real) : (term55 z x y) = (term56 y z).
Proof. exact (MK_COMB (@lem1499538) (@lem1499537 x y z)). Qed.
Lemma lem1499540 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1499541 (x : real) (y : real) (z : real) : (term31 z x y) = (term57 y z).
Proof. exact (MK_COMB (@lem1499539 x y z) (@lem1499540)). Qed.
Lemma lem1499542 (x : real) (y : real) (z : real) : (term2 y x z) = (term57 y z).
Proof. exact (TRANS (@lem1499488 z x y) (@lem1499541 x y z)). Qed.
Lemma lem1499543 (y : real) (z : real) : (term58 y z) = (term59 y z).
Proof. exact (@lem1483533 y z). Qed.
Lemma lem1499556 (y : real) (z : real) : (real_sub y z) = (term52 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1499557 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499558 (y : real) (z : real) : (term60 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1499557) (@lem1499556 y z)). Qed.
Lemma lem1499559 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1499560 (y : real) (z : real) : (term59 y z) = (term62 y z).
Proof. exact (MK_COMB (@lem1499558 y z) (@lem1499559)). Qed.
Lemma lem1499561 (y : real) (z : real) : (term58 y z) = (term62 y z).
Proof. exact (TRANS (@lem1499543 y z) (@lem1499560 y z)). Qed.
Lemma lem1499562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1499563 (x : real) (y : real) (z : real) : (term63 y x z) = (term64 y z).
Proof. exact (MK_COMB (@lem1499562) (@lem1499542 x y z)). Qed.
Lemma lem1499564 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 y z).
Proof. exact (MK_COMB (@lem1499563 x y z) (@lem1499561 y z)). Qed.
Lemma lem1499565 (y : real) (x : real) (z : real) : (term67 y x z) = (term68 y x z).
Proof. exact (@lem1483533 (real_add x y) (real_add x z)). Qed.
Lemma lem1499583 (y : real) (x : real) (z : real) : (term32 y x z) = (term33 y x z).
Proof. exact (@lem1483519 (real_add x y) (real_add x z)). Qed.
Lemma lem1499590 (x : real) (z : real) : (term34 x z) = (term35 x z).
Proof. exact (@lem1483508 x term36 z). Qed.
Lemma lem1499591 (x : real) (y : real) : (term37 x y) = (term37 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1499592 (y : real) (x : real) (z : real) : (term33 y x z) = (term38 y x z).
Proof. exact (MK_COMB (@lem1499591 x y) (@lem1499590 x z)). Qed.
Lemma lem1499593 (x : real) (y : real) (z : real) : (term38 y x z) = (term39 x y z).
Proof. exact (@lem1483480 x (term40 x) y (term40 z)). Qed.
Lemma lem1499594 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483442 term36 x). Qed.
Lemma lem1499596 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1499597 : term45 = term44.
Proof. exact (@lem1499596 term46). Qed.
Lemma lem1499598 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1499599 : term47 = term48.
Proof. exact (MK_COMB (@lem1499598) (@lem1499597)). Qed.
Lemma lem1499600 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1499601 (x : real) : (term42 x) = (term49 x).
Proof. exact (MK_COMB (@lem1499599) (@lem1499600 x)). Qed.
Lemma lem1499602 (x : real) : (term41 x) = (term49 x).
Proof. exact (TRANS (@lem1499594 x) (@lem1499601 x)). Qed.
Lemma lem1499603 (x : real) : (term49 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1499604 (x : real) : (term41 x) = term44.
Proof. exact (TRANS (@lem1499602 x) (@lem1499603 x)). Qed.
Lemma lem1499605 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1499606 (x : real) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem1499605) (@lem1499604 x)). Qed.
Lemma lem1499607 (y : real) (z : real) : (term52 y z) = (term52 y z).
Proof. exact (eq_refl (term52 y z)). Qed.
Lemma lem1499608 (x : real) (y : real) (z : real) : (term39 x y z) = (term69 y z).
Proof. exact (MK_COMB (@lem1499606 x) (@lem1499607 y z)). Qed.
Lemma lem1499609 (x : real) (y : real) (z : real) : (term38 y x z) = (term69 y z).
Proof. exact (TRANS (@lem1499593 x y z) (@lem1499608 x y z)). Qed.
Lemma lem1499610 (y : real) (z : real) : (term69 y z) = (term52 y z).
Proof. exact (@lem1483448 (term52 y z)). Qed.
Lemma lem1499611 (x : real) (y : real) (z : real) : (term38 y x z) = (term52 y z).
Proof. exact (TRANS (@lem1499609 x y z) (@lem1499610 y z)). Qed.
Lemma lem1499612 (x : real) (y : real) (z : real) : (term33 y x z) = (term52 y z).
Proof. exact (TRANS (@lem1499592 y x z) (@lem1499611 x y z)). Qed.
Lemma lem1499614 (x : real) (y : real) (z : real) : (term32 y x z) = (term52 y z).
Proof. exact (TRANS (@lem1499583 y x z) (@lem1499612 x y z)). Qed.
Lemma lem1499615 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1499616 (x : real) (y : real) (z : real) : (term70 y x z) = (term61 y z).
Proof. exact (MK_COMB (@lem1499615) (@lem1499614 x y z)). Qed.
Lemma lem1499617 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1499618 (x : real) (y : real) (z : real) : (term68 y x z) = (term62 y z).
Proof. exact (MK_COMB (@lem1499616 x y z) (@lem1499617)). Qed.
Lemma lem1499619 (x : real) (y : real) (z : real) : (term67 y x z) = (term62 y z).
Proof. exact (TRANS (@lem1499565 y x z) (@lem1499618 x y z)). Qed.
Lemma lem1499620 (z : real) (y : real) : (real_le y z) = (term71 z y).
Proof. exact (@lem1483523 z y). Qed.
Lemma lem1499626 (z : real) (y : real) : (real_sub z y) = (term52 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1499631 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1499633 (y : real) (z : real) : (real_sub z y) = (term53 y z).
Proof. exact (TRANS (@lem1499626 z y) (@lem1499631 y z)). Qed.
Lemma lem1499634 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1499635 (y : real) (z : real) : (term72 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1499634) (@lem1499633 y z)). Qed.
Lemma lem1499636 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1499637 (y : real) (z : real) : (term71 z y) = (term57 y z).
Proof. exact (MK_COMB (@lem1499635 y z) (@lem1499636)). Qed.
Lemma lem1499638 (y : real) (z : real) : (real_le y z) = (term57 y z).
Proof. exact (TRANS (@lem1499620 z y) (@lem1499637 y z)). Qed.
Lemma lem1499639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1499640 (x : real) (y : real) (z : real) : (term73 y x z) = (term74 y z).
Proof. exact (MK_COMB (@lem1499639) (@lem1499619 x y z)). Qed.
Lemma lem1499641 (x : real) (y : real) (z : real) : (term75 x y z) = (term76 y z).
Proof. exact (MK_COMB (@lem1499640 x y z) (@lem1499638 y z)). Qed.
Lemma lem1499642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499643 (x : real) (y : real) (z : real) : (term77 x y z) = (term78 y z).
Proof. exact (MK_COMB (@lem1499642) (@lem1499564 x y z)). Qed.
Lemma lem1499644 (x : real) (y : real) (z : real) : (term1 x y z) = (term79 y z).
Proof. exact (MK_COMB (@lem1499643 x y z) (@lem1499641 x y z)). Qed.
Lemma lem1499645 (x : real) (y : real) : (term11 x y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1499644 x y z)). Qed.
Lemma lem1499646 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499647 (x : real) (y : real) : (term12 x y) = (term81 y).
Proof. exact (MK_COMB (@lem1499646) (@lem1499645 x y)). Qed.
Lemma lem1499648 (x : real) : (term20 x) = term82.
Proof. exact (fun_ext (fun y : real => @lem1499647 x y)). Qed.
Lemma lem1499649 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499650 (x : real) : (term21 x) = term83.
Proof. exact (MK_COMB (@lem1499649) (@lem1499648 x)). Qed.
Lemma lem1499651 : term29 = term84.
Proof. exact (fun_ext (fun x : real => @lem1499650 x)). Qed.
Lemma lem1499652 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499653 : term30 = term85.
Proof. exact (MK_COMB (@lem1499652) (@lem1499651)). Qed.
Lemma lem1499654 : term22 = term85.
Proof. exact (TRANS (@lem1499487) (@lem1499653)). Qed.
Lemma lem1499656 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1499657 (t : Prop) : (term87 t) = t.
Proof. exact (@lem1499656 real t). Qed.
Lemma lem1499658 : term85 = term83.
Proof. exact (@lem1499657 term83). Qed.
Lemma lem1499664 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1499665 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem1499664 real P Q). Qed.
Lemma lem1499666 (y : real) : (term92 y) = (term93 y).
Proof. exact (@lem1499665 (term94 y) (term95 y)). Qed.
Lemma lem1499667 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1499668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499669 (y : real) (z : real) : (term97 y z) = (term78 y z).
Proof. exact (MK_COMB (@lem1499668) (@lem1499667 y z)). Qed.
Lemma lem1499670 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1499671 (y : real) (z : real) : (term99 y z) = (term79 y z).
Proof. exact (MK_COMB (@lem1499669 y z) (@lem1499670 y z)). Qed.
Lemma lem1499672 (y : real) : (term100 y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1499671 y z)). Qed.
Lemma lem1499673 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499674 (y : real) : (term92 y) = (term81 y).
Proof. exact (MK_COMB (@lem1499673) (@lem1499672 y)). Qed.
Lemma lem1499675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1499676 (y : real) : (term101 y) = (term102 y).
Proof. exact (MK_COMB (@lem1499675) (@lem1499674 y)). Qed.
Lemma lem1499677 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1499678 (y : real) : (term103 y) = (term94 y).
Proof. exact (fun_ext (fun z : real => @lem1499677 y z)). Qed.
Lemma lem1499679 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499680 (y : real) : (term104 y) = (term105 y).
Proof. exact (MK_COMB (@lem1499679) (@lem1499678 y)). Qed.
Lemma lem1499681 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499682 (y : real) : (term106 y) = (term107 y).
Proof. exact (MK_COMB (@lem1499681) (@lem1499680 y)). Qed.
Lemma lem1499683 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1499684 (y : real) : (term108 y) = (term95 y).
Proof. exact (fun_ext (fun z : real => @lem1499683 y z)). Qed.
Lemma lem1499685 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499686 (y : real) : (term109 y) = (term110 y).
Proof. exact (MK_COMB (@lem1499685) (@lem1499684 y)). Qed.
Lemma lem1499687 (y : real) : (term93 y) = (term111 y).
Proof. exact (MK_COMB (@lem1499682 y) (@lem1499686 y)). Qed.
Lemma lem1499688 (y : real) : ((term92 y) = (term93 y)) = ((term81 y) = (term111 y)).
Proof. exact (MK_COMB (@lem1499676 y) (@lem1499687 y)). Qed.
Lemma lem1499689 (y : real) : (term81 y) = (term111 y).
Proof. exact (EQ_MP (@lem1499688 y) (@lem1499666 y)). Qed.
Lemma lem1499786 : term82 = term112.
Proof. exact (fun_ext (fun y : real => @lem1499689 y)). Qed.
Lemma lem1499787 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499788 : term83 = term113.
Proof. exact (MK_COMB (@lem1499787) (@lem1499786)). Qed.
Lemma lem1499790 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1499791 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem1499790 real P Q). Qed.
Lemma lem1499792 : term114 = term115.
Proof. exact (@lem1499791 term116 term117). Qed.
Lemma lem1499793 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1499794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499795 (y : real) : (term119 y) = (term107 y).
Proof. exact (MK_COMB (@lem1499794) (@lem1499793 y)). Qed.
Lemma lem1499796 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1499797 (y : real) : (term121 y) = (term111 y).
Proof. exact (MK_COMB (@lem1499795 y) (@lem1499796 y)). Qed.
Lemma lem1499798 : term122 = term112.
Proof. exact (fun_ext (fun y : real => @lem1499797 y)). Qed.
Lemma lem1499799 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499800 : term114 = term113.
Proof. exact (MK_COMB (@lem1499799) (@lem1499798)). Qed.
Lemma lem1499801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1499802 : term123 = term124.
Proof. exact (MK_COMB (@lem1499801) (@lem1499800)). Qed.
Lemma lem1499803 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1499804 : term125 = term116.
Proof. exact (fun_ext (fun y : real => @lem1499803 y)). Qed.
Lemma lem1499805 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499806 : term126 = term127.
Proof. exact (MK_COMB (@lem1499805) (@lem1499804)). Qed.
Lemma lem1499807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499808 : term128 = term129.
Proof. exact (MK_COMB (@lem1499807) (@lem1499806)). Qed.
Lemma lem1499809 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1499810 : term130 = term117.
Proof. exact (fun_ext (fun y : real => @lem1499809 y)). Qed.
Lemma lem1499811 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499812 : term131 = term132.
Proof. exact (MK_COMB (@lem1499811) (@lem1499810)). Qed.
Lemma lem1499813 : term115 = term133.
Proof. exact (MK_COMB (@lem1499808) (@lem1499812)). Qed.
Lemma lem1499814 : (term114 = term115) = (term113 = term133).
Proof. exact (MK_COMB (@lem1499802) (@lem1499813)). Qed.
Lemma lem1499815 : term113 = term133.
Proof. exact (EQ_MP (@lem1499814) (@lem1499792)). Qed.
Lemma lem1499920 : term83 = term133.
Proof. exact (TRANS (@lem1499788) (@lem1499815)). Qed.
Lemma lem1499921 : term85 = term133.
Proof. exact (TRANS (@lem1499658) (@lem1499920)). Qed.
Lemma lem1499923 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1499924 (P : real -> Prop) (Q : real -> Prop) : (term91 P Q) = (term90 P Q).
Proof. exact (@lem1499923 real P Q). Qed.
Lemma lem1499925 : term115 = term114.
Proof. exact (@lem1499924 term116 term117). Qed.
Lemma lem1499926 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1499927 : term125 = term116.
Proof. exact (fun_ext (fun y : real => @lem1499926 y)). Qed.
Lemma lem1499928 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499929 : term126 = term127.
Proof. exact (MK_COMB (@lem1499928) (@lem1499927)). Qed.
Lemma lem1499930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499931 : term128 = term129.
Proof. exact (MK_COMB (@lem1499930) (@lem1499929)). Qed.
Lemma lem1499932 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1499933 : term130 = term117.
Proof. exact (fun_ext (fun y : real => @lem1499932 y)). Qed.
Lemma lem1499934 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499935 : term131 = term132.
Proof. exact (MK_COMB (@lem1499934) (@lem1499933)). Qed.
Lemma lem1499936 : term115 = term133.
Proof. exact (MK_COMB (@lem1499931) (@lem1499935)). Qed.
Lemma lem1499937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1499938 : term134 = term135.
Proof. exact (MK_COMB (@lem1499937) (@lem1499936)). Qed.
Lemma lem1499939 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1499940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499941 (y : real) : (term119 y) = (term107 y).
Proof. exact (MK_COMB (@lem1499940) (@lem1499939 y)). Qed.
Lemma lem1499942 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1499943 (y : real) : (term121 y) = (term111 y).
Proof. exact (MK_COMB (@lem1499941 y) (@lem1499942 y)). Qed.
Lemma lem1499944 : term122 = term112.
Proof. exact (fun_ext (fun y : real => @lem1499943 y)). Qed.
Lemma lem1499945 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499946 : term114 = term113.
Proof. exact (MK_COMB (@lem1499945) (@lem1499944)). Qed.
Lemma lem1499947 : (term115 = term114) = (term133 = term113).
Proof. exact (MK_COMB (@lem1499938) (@lem1499946)). Qed.
Lemma lem1499948 : term133 = term113.
Proof. exact (EQ_MP (@lem1499947) (@lem1499925)). Qed.
Lemma lem1499950 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1499951 (P : real -> Prop) (Q : real -> Prop) : (term91 P Q) = (term90 P Q).
Proof. exact (@lem1499950 real P Q). Qed.
Lemma lem1499952 (y : real) : (term93 y) = (term92 y).
Proof. exact (@lem1499951 (term94 y) (term95 y)). Qed.
Lemma lem1499953 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1499954 (y : real) : (term103 y) = (term94 y).
Proof. exact (fun_ext (fun z : real => @lem1499953 y z)). Qed.
Lemma lem1499955 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499956 (y : real) : (term104 y) = (term105 y).
Proof. exact (MK_COMB (@lem1499955) (@lem1499954 y)). Qed.
Lemma lem1499957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499958 (y : real) : (term106 y) = (term107 y).
Proof. exact (MK_COMB (@lem1499957) (@lem1499956 y)). Qed.
Lemma lem1499959 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1499960 (y : real) : (term108 y) = (term95 y).
Proof. exact (fun_ext (fun z : real => @lem1499959 y z)). Qed.
Lemma lem1499961 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499962 (y : real) : (term109 y) = (term110 y).
Proof. exact (MK_COMB (@lem1499961) (@lem1499960 y)). Qed.
Lemma lem1499963 (y : real) : (term93 y) = (term111 y).
Proof. exact (MK_COMB (@lem1499958 y) (@lem1499962 y)). Qed.
Lemma lem1499964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1499965 (y : real) : (term136 y) = (term137 y).
Proof. exact (MK_COMB (@lem1499964) (@lem1499963 y)). Qed.
Lemma lem1499966 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1499967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1499968 (y : real) (z : real) : (term97 y z) = (term78 y z).
Proof. exact (MK_COMB (@lem1499967) (@lem1499966 y z)). Qed.
Lemma lem1499969 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1499970 (y : real) (z : real) : (term99 y z) = (term79 y z).
Proof. exact (MK_COMB (@lem1499968 y z) (@lem1499969 y z)). Qed.
Lemma lem1499971 (y : real) : (term100 y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1499970 y z)). Qed.
Lemma lem1499972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499973 (y : real) : (term92 y) = (term81 y).
Proof. exact (MK_COMB (@lem1499972) (@lem1499971 y)). Qed.
Lemma lem1499974 (y : real) : ((term93 y) = (term92 y)) = ((term111 y) = (term81 y)).
Proof. exact (MK_COMB (@lem1499965 y) (@lem1499973 y)). Qed.
Lemma lem1499975 (y : real) : (term111 y) = (term81 y).
Proof. exact (EQ_MP (@lem1499974 y) (@lem1499952 y)). Qed.
Lemma lem1499976 : term112 = term82.
Proof. exact (fun_ext (fun y : real => @lem1499975 y)). Qed.
Lemma lem1499977 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1499978 : term113 = term83.
Proof. exact (MK_COMB (@lem1499977) (@lem1499976)). Qed.
Lemma lem1499979 : term133 = term83.
Proof. exact (TRANS (@lem1499948) (@lem1499978)). Qed.
Lemma lem1499980 : term85 = term83.
Proof. exact (TRANS (@lem1499921) (@lem1499979)). Qed.
Lemma lem1499983 : term22 = term83.
Proof. exact (TRANS (@lem1499654) (@lem1499980)). Qed.
Lemma lem1500000 (y : real) (z : real) : (term79 y z) = (term79 y z).
Proof. exact (eq_refl (term79 y z)). Qed.
Lemma lem1500001 (y : real) : (term80 y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1500000 y z)). Qed.
Lemma lem1500002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500003 (y : real) : (term81 y) = (term81 y).
Proof. exact (MK_COMB (@lem1500002) (@lem1500001 y)). Qed.
Lemma lem1500004 : term82 = term82.
Proof. exact (fun_ext (fun y : real => @lem1500003 y)). Qed.
Lemma lem1500005 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500006 : term83 = term83.
Proof. exact (MK_COMB (@lem1500005) (@lem1500004)). Qed.
Lemma lem1500007 : term22 = term83.
Proof. exact (TRANS (@lem1499983) (@lem1500006)). Qed.
Lemma lem1500017 (y : real) (z : real) (h1 : term79 y z) : term79 y z.
Proof. exact (h1). Qed.
Lemma lem1500018 (y : real) (z : real) (h1 : term66 y z) : term66 y z.
Proof. exact (h1). Qed.
Lemma lem1500019 (y : real) (z : real) (h1 : term66 y z) : term62 y z.
Proof. exact (proj2 (@lem1500018 y z h1)). Qed.
Lemma lem1500020 (y : real) (z : real) (h1 : term66 y z) : term57 y z.
Proof. exact (proj1 (@lem1500018 y z h1)). Qed.
Lemma lem1500022 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500023 : term139 = term140.
Proof. exact (@lem1500022 (NUMERAL 0) term46). Qed.
Lemma lem1500024 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1500025 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1500026 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1500025 h1) (fun h1 : term140 = True => @lem1500024)). Qed.
Lemma lem1500027 : term140 = True.
Proof. exact (EQ_MP (@lem1500026) (@lem1500024)). Qed.
Lemma lem1500028 : term139 = True.
Proof. exact (TRANS (@lem1500023) (@lem1500027)). Qed.
Lemma lem1500029 : True = term139.
Proof. exact (SYM (@lem1500028)). Qed.
Lemma lem1500030 : term139.
Proof. exact (EQ_MP (@lem1500029) (@lem0)). Qed.
Lemma lem1500031 (y : real) (z : real) (h1 : term66 y z) : term142 y z.
Proof. exact (conj (@lem1500030) (@lem1500020 y z h1)). Qed.
Lemma lem1500033 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1500034 (y : real) (z : real) : term144 y z.
Proof. exact (@lem1500033 term145 (term53 y z)). Qed.
Lemma lem1500035 (y : real) (z : real) (h1 : term66 y z) : term146 y z.
Proof. exact (@lem1500034 y z (@lem1500031 y z h1)). Qed.
Lemma lem1500036 (y : real) (z : real) : (term147 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1500037 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1500038 (y : real) (z : real) : (term148 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1500037) (@lem1500036 y z)). Qed.
Lemma lem1500039 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1500040 (y : real) (z : real) : (term146 y z) = (term57 y z).
Proof. exact (MK_COMB (@lem1500038 y z) (@lem1500039)). Qed.
Lemma lem1500041 (y : real) (z : real) (h1 : term66 y z) : term57 y z.
Proof. exact (EQ_MP (@lem1500040 y z) (@lem1500035 y z h1)). Qed.
Lemma lem1500043 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500044 : term139 = term140.
Proof. exact (@lem1500043 (NUMERAL 0) term46). Qed.
Lemma lem1500045 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1500046 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1500047 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1500046 h1) (fun h1 : term140 = True => @lem1500045)). Qed.
Lemma lem1500048 : term140 = True.
Proof. exact (EQ_MP (@lem1500047) (@lem1500045)). Qed.
Lemma lem1500049 : term139 = True.
Proof. exact (TRANS (@lem1500044) (@lem1500048)). Qed.
Lemma lem1500050 : True = term139.
Proof. exact (SYM (@lem1500049)). Qed.
Lemma lem1500051 : term139.
Proof. exact (EQ_MP (@lem1500050) (@lem0)). Qed.
Lemma lem1500052 (y : real) (z : real) (h1 : term66 y z) : term149 y z.
Proof. exact (conj (@lem1500051) (@lem1500019 y z h1)). Qed.
Lemma lem1500054 (x : real) (y : real) : term150 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1500055 (y : real) (z : real) : term151 y z.
Proof. exact (@lem1500054 term145 (term52 y z)). Qed.
Lemma lem1500056 (y : real) (z : real) (h1 : term66 y z) : term152 y z.
Proof. exact (@lem1500055 y z (@lem1500052 y z h1)). Qed.
Lemma lem1500057 (y : real) (z : real) : (term153 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1500058 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500059 (y : real) (z : real) : (term154 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1500058) (@lem1500057 y z)). Qed.
Lemma lem1500060 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1500061 (y : real) (z : real) : (term152 y z) = (term62 y z).
Proof. exact (MK_COMB (@lem1500059 y z) (@lem1500060)). Qed.
Lemma lem1500062 (y : real) (z : real) (h1 : term66 y z) : term62 y z.
Proof. exact (EQ_MP (@lem1500061 y z) (@lem1500056 y z h1)). Qed.
Lemma lem1500063 (y : real) (z : real) (h1 : term66 y z) : term76 y z.
Proof. exact (conj (@lem1500062 y z h1) (@lem1500041 y z h1)). Qed.
Lemma lem1500065 (x : real) (y : real) : term155 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1500066 (y : real) (z : real) : term156 y z.
Proof. exact (@lem1500065 (term52 y z) (term53 y z)). Qed.
Lemma lem1500067 (y : real) (z : real) (h1 : term66 y z) : term157 y z.
Proof. exact (@lem1500066 y z (@lem1500063 y z h1)). Qed.
Lemma lem1500068 (y : real) (z : real) : (term158 y z) = (term159 y z).
Proof. exact (@lem1483480 y (term40 y) (term40 z) z). Qed.
Lemma lem1500069 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1483442 term36 y). Qed.
Lemma lem1500071 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500072 : term45 = term44.
Proof. exact (@lem1500071 term46). Qed.
Lemma lem1500073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500074 : term47 = term48.
Proof. exact (MK_COMB (@lem1500073) (@lem1500072)). Qed.
Lemma lem1500075 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1500076 (y : real) : (term42 y) = (term49 y).
Proof. exact (MK_COMB (@lem1500074) (@lem1500075 y)). Qed.
Lemma lem1500077 (y : real) : (term41 y) = (term49 y).
Proof. exact (TRANS (@lem1500069 y) (@lem1500076 y)). Qed.
Lemma lem1500078 (y : real) : (term49 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1500079 (y : real) : (term41 y) = term44.
Proof. exact (TRANS (@lem1500077 y) (@lem1500078 y)). Qed.
Lemma lem1500080 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1500081 (y : real) : (term50 y) = term51.
Proof. exact (MK_COMB (@lem1500080) (@lem1500079 y)). Qed.
Lemma lem1500082 (z : real) : (term160 z) = (term42 z).
Proof. exact (@lem1483440 term36 z). Qed.
Lemma lem1500084 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500085 : term45 = term44.
Proof. exact (@lem1500084 term46). Qed.
Lemma lem1500086 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500087 : term47 = term48.
Proof. exact (MK_COMB (@lem1500086) (@lem1500085)). Qed.
Lemma lem1500088 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1500089 (z : real) : (term42 z) = (term49 z).
Proof. exact (MK_COMB (@lem1500087) (@lem1500088 z)). Qed.
Lemma lem1500090 (z : real) : (term160 z) = (term49 z).
Proof. exact (TRANS (@lem1500082 z) (@lem1500089 z)). Qed.
Lemma lem1500091 (z : real) : (term49 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1500092 (z : real) : (term160 z) = term44.
Proof. exact (TRANS (@lem1500090 z) (@lem1500091 z)). Qed.
Lemma lem1500093 (y : real) (z : real) : (term159 y z) = term161.
Proof. exact (MK_COMB (@lem1500081 y) (@lem1500092 z)). Qed.
Lemma lem1500094 (y : real) (z : real) : (term158 y z) = term161.
Proof. exact (TRANS (@lem1500068 y z) (@lem1500093 y z)). Qed.
Lemma lem1500095 : term161 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1500096 (y : real) (z : real) : (term158 y z) = term44.
Proof. exact (TRANS (@lem1500094 y z) (@lem1500095)). Qed.
Lemma lem1500097 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500098 (y : real) (z : real) : (term162 y z) = term163.
Proof. exact (MK_COMB (@lem1500097) (@lem1500096 y z)). Qed.
Lemma lem1500099 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1500100 (y : real) (z : real) : (term157 y z) = term164.
Proof. exact (MK_COMB (@lem1500098 y z) (@lem1500099)). Qed.
Lemma lem1500101 (y : real) (z : real) (h1 : term66 y z) : term164.
Proof. exact (EQ_MP (@lem1500100 y z) (@lem1500067 y z h1)). Qed.
Lemma lem1500103 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500104 : term164 = term165.
Proof. exact (@lem1500103 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1500105 : term165 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1500106 : term164 = False.
Proof. exact (TRANS (@lem1500104) (@lem1500105)). Qed.
Lemma lem1500107 (y : real) (z : real) (h1 : term66 y z) : False.
Proof. exact (EQ_MP (@lem1500106) (@lem1500101 y z h1)). Qed.
Lemma lem1500108 (y : real) (z : real) (h1 : term76 y z) : term76 y z.
Proof. exact (h1). Qed.
Lemma lem1500109 (y : real) (z : real) (h1 : term76 y z) : term57 y z.
Proof. exact (proj2 (@lem1500108 y z h1)). Qed.
Lemma lem1500110 (y : real) (z : real) (h1 : term76 y z) : term62 y z.
Proof. exact (proj1 (@lem1500108 y z h1)). Qed.
Lemma lem1500112 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500113 : term139 = term140.
Proof. exact (@lem1500112 (NUMERAL 0) term46). Qed.
Lemma lem1500114 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1500115 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1500116 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1500115 h1) (fun h1 : term140 = True => @lem1500114)). Qed.
Lemma lem1500117 : term140 = True.
Proof. exact (EQ_MP (@lem1500116) (@lem1500114)). Qed.
Lemma lem1500118 : term139 = True.
Proof. exact (TRANS (@lem1500113) (@lem1500117)). Qed.
Lemma lem1500119 : True = term139.
Proof. exact (SYM (@lem1500118)). Qed.
Lemma lem1500120 : term139.
Proof. exact (EQ_MP (@lem1500119) (@lem0)). Qed.
Lemma lem1500121 (y : real) (z : real) (h1 : term76 y z) : term142 y z.
Proof. exact (conj (@lem1500120) (@lem1500109 y z h1)). Qed.
Lemma lem1500123 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1500124 (y : real) (z : real) : term144 y z.
Proof. exact (@lem1500123 term145 (term53 y z)). Qed.
Lemma lem1500125 (y : real) (z : real) (h1 : term76 y z) : term146 y z.
Proof. exact (@lem1500124 y z (@lem1500121 y z h1)). Qed.
Lemma lem1500126 (y : real) (z : real) : (term147 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1500127 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1500128 (y : real) (z : real) : (term148 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1500127) (@lem1500126 y z)). Qed.
Lemma lem1500129 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1500130 (y : real) (z : real) : (term146 y z) = (term57 y z).
Proof. exact (MK_COMB (@lem1500128 y z) (@lem1500129)). Qed.
Lemma lem1500131 (y : real) (z : real) (h1 : term76 y z) : term57 y z.
Proof. exact (EQ_MP (@lem1500130 y z) (@lem1500125 y z h1)). Qed.
Lemma lem1500133 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500134 : term139 = term140.
Proof. exact (@lem1500133 (NUMERAL 0) term46). Qed.
Lemma lem1500135 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1500136 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1500137 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1500136 h1) (fun h1 : term140 = True => @lem1500135)). Qed.
Lemma lem1500138 : term140 = True.
Proof. exact (EQ_MP (@lem1500137) (@lem1500135)). Qed.
Lemma lem1500139 : term139 = True.
Proof. exact (TRANS (@lem1500134) (@lem1500138)). Qed.
Lemma lem1500140 : True = term139.
Proof. exact (SYM (@lem1500139)). Qed.
Lemma lem1500141 : term139.
Proof. exact (EQ_MP (@lem1500140) (@lem0)). Qed.
Lemma lem1500142 (y : real) (z : real) (h1 : term76 y z) : term149 y z.
Proof. exact (conj (@lem1500141) (@lem1500110 y z h1)). Qed.
Lemma lem1500144 (x : real) (y : real) : term150 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1500145 (y : real) (z : real) : term151 y z.
Proof. exact (@lem1500144 term145 (term52 y z)). Qed.
Lemma lem1500146 (y : real) (z : real) (h1 : term76 y z) : term152 y z.
Proof. exact (@lem1500145 y z (@lem1500142 y z h1)). Qed.
Lemma lem1500147 (y : real) (z : real) : (term153 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1500148 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500149 (y : real) (z : real) : (term154 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1500148) (@lem1500147 y z)). Qed.
Lemma lem1500150 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1500151 (y : real) (z : real) : (term152 y z) = (term62 y z).
Proof. exact (MK_COMB (@lem1500149 y z) (@lem1500150)). Qed.
Lemma lem1500152 (y : real) (z : real) (h1 : term76 y z) : term62 y z.
Proof. exact (EQ_MP (@lem1500151 y z) (@lem1500146 y z h1)). Qed.
Lemma lem1500153 (y : real) (z : real) (h1 : term76 y z) : term76 y z.
Proof. exact (conj (@lem1500152 y z h1) (@lem1500131 y z h1)). Qed.
Lemma lem1500155 (x : real) (y : real) : term155 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1500156 (y : real) (z : real) : term156 y z.
Proof. exact (@lem1500155 (term52 y z) (term53 y z)). Qed.
Lemma lem1500157 (y : real) (z : real) (h1 : term76 y z) : term157 y z.
Proof. exact (@lem1500156 y z (@lem1500153 y z h1)). Qed.
Lemma lem1500158 (y : real) (z : real) : (term158 y z) = (term159 y z).
Proof. exact (@lem1483480 y (term40 y) (term40 z) z). Qed.
Lemma lem1500159 (y : real) : (term41 y) = (term42 y).
Proof. exact (@lem1483442 term36 y). Qed.
Lemma lem1500161 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500162 : term45 = term44.
Proof. exact (@lem1500161 term46). Qed.
Lemma lem1500163 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500164 : term47 = term48.
Proof. exact (MK_COMB (@lem1500163) (@lem1500162)). Qed.
Lemma lem1500165 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1500166 (y : real) : (term42 y) = (term49 y).
Proof. exact (MK_COMB (@lem1500164) (@lem1500165 y)). Qed.
Lemma lem1500167 (y : real) : (term41 y) = (term49 y).
Proof. exact (TRANS (@lem1500159 y) (@lem1500166 y)). Qed.
Lemma lem1500168 (y : real) : (term49 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1500169 (y : real) : (term41 y) = term44.
Proof. exact (TRANS (@lem1500167 y) (@lem1500168 y)). Qed.
Lemma lem1500170 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1500171 (y : real) : (term50 y) = term51.
Proof. exact (MK_COMB (@lem1500170) (@lem1500169 y)). Qed.
Lemma lem1500172 (z : real) : (term160 z) = (term42 z).
Proof. exact (@lem1483440 term36 z). Qed.
Lemma lem1500174 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500175 : term45 = term44.
Proof. exact (@lem1500174 term46). Qed.
Lemma lem1500176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500177 : term47 = term48.
Proof. exact (MK_COMB (@lem1500176) (@lem1500175)). Qed.
Lemma lem1500178 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1500179 (z : real) : (term42 z) = (term49 z).
Proof. exact (MK_COMB (@lem1500177) (@lem1500178 z)). Qed.
Lemma lem1500180 (z : real) : (term160 z) = (term49 z).
Proof. exact (TRANS (@lem1500172 z) (@lem1500179 z)). Qed.
Lemma lem1500181 (z : real) : (term49 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1500182 (z : real) : (term160 z) = term44.
Proof. exact (TRANS (@lem1500180 z) (@lem1500181 z)). Qed.
Lemma lem1500183 (y : real) (z : real) : (term159 y z) = term161.
Proof. exact (MK_COMB (@lem1500171 y) (@lem1500182 z)). Qed.
Lemma lem1500184 (y : real) (z : real) : (term158 y z) = term161.
Proof. exact (TRANS (@lem1500158 y z) (@lem1500183 y z)). Qed.
Lemma lem1500185 : term161 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1500186 (y : real) (z : real) : (term158 y z) = term44.
Proof. exact (TRANS (@lem1500184 y z) (@lem1500185)). Qed.
Lemma lem1500187 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500188 (y : real) (z : real) : (term162 y z) = term163.
Proof. exact (MK_COMB (@lem1500187) (@lem1500186 y z)). Qed.
Lemma lem1500189 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1500190 (y : real) (z : real) : (term157 y z) = term164.
Proof. exact (MK_COMB (@lem1500188 y z) (@lem1500189)). Qed.
Lemma lem1500191 (y : real) (z : real) (h1 : term76 y z) : term164.
Proof. exact (EQ_MP (@lem1500190 y z) (@lem1500157 y z h1)). Qed.
Lemma lem1500193 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500194 : term164 = term165.
Proof. exact (@lem1500193 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1500195 : term165 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1500196 : term164 = False.
Proof. exact (TRANS (@lem1500194) (@lem1500195)). Qed.
Lemma lem1500197 (y : real) (z : real) (h1 : term76 y z) : False.
Proof. exact (EQ_MP (@lem1500196) (@lem1500191 y z h1)). Qed.
Lemma lem1500198 (y : real) (z : real) (h1 : term79 y z) : False.
Proof. exact (or_elim (@lem1500017 y z h1) (fun h0 : term66 y z => @lem1500107 y z h0) (fun h0 : term76 y z => @lem1500197 y z h0)). Qed.
Lemma lem1500200 (y : real) (z : real) (h1 : term79 y z) : term79 y z.
Proof. exact (h1). Qed.
Lemma lem1500201 (y : real) (z : real) (h1 : term79 y z) : (term79 y z) = False.
Proof. exact (prop_ext (fun h2 : term79 y z => @lem1500198 y z h1) (fun h2 : False => @lem1500200 y z h1)). Qed.
Lemma lem1500202 (y : real) (z : real) (h1 : term79 y z) : False.
Proof. exact (EQ_MP (@lem1500201 y z h1) (@lem1500200 y z h1)). Qed.
Lemma lem1500203 (y : real) (h1 : term81 y) : term81 y.
Proof. exact (h1). Qed.
Lemma lem1500204 (y : real) (h1 : term81 y) : False.
Proof. exact (ex_elim (@lem1500203 y h1) (fun z : real => fun h0 : term80 y z => @lem1500202 y z h0)). Qed.
Lemma lem1500205 (h1 : term83) : term83.
Proof. exact (h1). Qed.
Lemma lem1500206 (h1 : term83) : False.
Proof. exact (ex_elim (@lem1500205 h1) (fun y : real => fun h0 : term82 y => @lem1500204 y h0)). Qed.
Lemma lem1500207 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1500208 (h1 : term22) : term83.
Proof. exact (EQ_MP (@lem1500007) (@lem1500207 h1)). Qed.
Lemma lem1500209 (h1 : term22) : term83 = False.
Proof. exact (prop_ext (fun h2 : term83 => @lem1500206 h2) (fun h2 : False => @lem1500208 h1)). Qed.
Lemma lem1500210 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1500209 h1) (@lem1500208 h1)). Qed.
Lemma lem1500211 : term166.
Proof. exact (fun h0 : term22 => @lem1500210 h0). Qed.
Lemma lem1500212 : term167.
Proof. exact (@lem1386578 term168). Qed.
Lemma lem1500213 : term168.
Proof. exact (@lem1500212 (@lem1500211)). Qed.
