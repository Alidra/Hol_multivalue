Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_ABS_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482702_spec.
Require Import thm1482703_spec.
Require Import thm1482704_spec.
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
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm706885_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem1534501 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1534502 : term2 = term3.
Proof. exact (@lem1534501 term4). Qed.
Lemma lem1534503 (x : real) : (term5 x) = ((term6 x) = (real_abs x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1534504 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1534506 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1534504) (@lem1534503 x)). Qed.
Lemma lem1534507 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1534506 x)). Qed.
Lemma lem1534508 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534509 : term3 = term11.
Proof. exact (MK_COMB (@lem1534508) (@lem1534507)). Qed.
Lemma lem1534511 : term2 = term11.
Proof. exact (TRANS (@lem1534502) (@lem1534509)). Qed.
Lemma lem1534514 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1534515 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1534514 x)). Qed.
Lemma lem1534516 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534517 : term11 = term11.
Proof. exact (MK_COMB (@lem1534516) (@lem1534515)). Qed.
Lemma lem1534518 : term2 = term11.
Proof. exact (TRANS (@lem1534511) (@lem1534517)). Qed.
Lemma lem1534519 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483554 (term6 x) (real_abs x)). Qed.
Lemma lem1534525 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1483519 (term6 x) (real_abs x)). Qed.
Lemma lem1534530 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1483488 (term16 x) (term6 x)). Qed.
Lemma lem1534532 (x : real) : (term13 x) = (term15 x).
Proof. exact (TRANS (@lem1534525 x) (@lem1534530 x)). Qed.
Lemma lem1534533 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1534534 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1534533) (@lem1534532 x)). Qed.
Lemma lem1534535 (x : real) : (term18 x) = (term19 x).
Proof. exact (@lem1483512 (term15 x)). Qed.
Lemma lem1534536 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483508 (term16 x) term21 (term6 x)). Qed.
Lemma lem1534537 (x : real) : (term22 x) = (term22 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1534538 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1483476 term21 term21 (real_abs x)). Qed.
Lemma lem1534540 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1534541 : term27 = term28.
Proof. exact (@lem1534540 term29 term29). Qed.
Lemma lem1534542 : (term30 = (BIT1 0)) = (term31 = term29).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1534543 : term31 = term29.
Proof. exact (EQ_MP (@lem1534542) (@lem940073)). Qed.
Lemma lem1534544 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1534545 : term28 = term32.
Proof. exact (MK_COMB (@lem1534544) (@lem1534543)). Qed.
Lemma lem1534546 : term27 = term32.
Proof. exact (TRANS (@lem1534541) (@lem1534545)). Qed.
Lemma lem1534547 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534548 : term33 = term34.
Proof. exact (MK_COMB (@lem1534547) (@lem1534546)). Qed.
Lemma lem1534549 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1534550 (x : real) : (term24 x) = (term35 x).
Proof. exact (MK_COMB (@lem1534548) (@lem1534549 x)). Qed.
Lemma lem1534551 (x : real) : (term23 x) = (term35 x).
Proof. exact (TRANS (@lem1534538 x) (@lem1534550 x)). Qed.
Lemma lem1534552 (x : real) : (term35 x) = (real_abs x).
Proof. exact (@lem1483436 (real_abs x)). Qed.
Lemma lem1534553 (x : real) : (term23 x) = (real_abs x).
Proof. exact (TRANS (@lem1534551 x) (@lem1534552 x)). Qed.
Lemma lem1534554 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1534555 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1534554) (@lem1534553 x)). Qed.
Lemma lem1534556 (x : real) : (term20 x) = (term38 x).
Proof. exact (MK_COMB (@lem1534555 x) (@lem1534537 x)). Qed.
Lemma lem1534557 (x : real) : (term19 x) = (term38 x).
Proof. exact (TRANS (@lem1534536 x) (@lem1534556 x)). Qed.
Lemma lem1534558 (x : real) : (term18 x) = (term38 x).
Proof. exact (TRANS (@lem1534535 x) (@lem1534557 x)). Qed.
Lemma lem1534559 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1534560 (x : real) : ((term17 x) = (term18 x)) = ((term17 x) = (term38 x)).
Proof. exact (MK_COMB (@lem1534559 x) (@lem1534558 x)). Qed.
Lemma lem1534561 (x : real) : (term17 x) = (term38 x).
Proof. exact (EQ_MP (@lem1534560 x) (@lem1534534 x)). Qed.
Lemma lem1534562 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534563 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1534562) (@lem1534561 x)). Qed.
Lemma lem1534564 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534565 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem1534563 x) (@lem1534564)). Qed.
Lemma lem1534566 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534567 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1534566) (@lem1534532 x)). Qed.
Lemma lem1534568 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534569 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem1534567 x) (@lem1534568)). Qed.
Lemma lem1534570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534571 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1534570) (@lem1534569 x)). Qed.
Lemma lem1534572 (x : real) : (term12 x) = (term51 x).
Proof. exact (MK_COMB (@lem1534571 x) (@lem1534565 x)). Qed.
Lemma lem1534573 (x : real) : (term8 x) = (term51 x).
Proof. exact (TRANS (@lem1534519 x) (@lem1534572 x)). Qed.
Lemma lem1534574 : term10 = term52.
Proof. exact (fun_ext (fun x : real => @lem1534573 x)). Qed.
Lemma lem1534575 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534576 : term11 = term53.
Proof. exact (MK_COMB (@lem1534575) (@lem1534574)). Qed.
Lemma lem1534577 : term2 = term53.
Proof. exact (TRANS (@lem1534518) (@lem1534576)). Qed.
Lemma lem1534579 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1534580 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1534579 real P Q). Qed.
Lemma lem1534581 : term58 = term59.
Proof. exact (@lem1534580 term60 term61). Qed.
Lemma lem1534582 (x : real) : (term62 x) = (term48 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1534583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534584 (x : real) : (term63 x) = (term50 x).
Proof. exact (MK_COMB (@lem1534583) (@lem1534582 x)). Qed.
Lemma lem1534585 (x : real) : (term64 x) = (term44 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1534586 (x : real) : (term65 x) = (term51 x).
Proof. exact (MK_COMB (@lem1534584 x) (@lem1534585 x)). Qed.
Lemma lem1534587 : term66 = term52.
Proof. exact (fun_ext (fun x : real => @lem1534586 x)). Qed.
Lemma lem1534588 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534589 : term58 = term53.
Proof. exact (MK_COMB (@lem1534588) (@lem1534587)). Qed.
Lemma lem1534590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1534591 : term67 = term68.
Proof. exact (MK_COMB (@lem1534590) (@lem1534589)). Qed.
Lemma lem1534592 (x : real) : (term62 x) = (term48 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1534593 : term69 = term60.
Proof. exact (fun_ext (fun x : real => @lem1534592 x)). Qed.
Lemma lem1534594 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534595 : term70 = term71.
Proof. exact (MK_COMB (@lem1534594) (@lem1534593)). Qed.
Lemma lem1534596 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534597 : term72 = term73.
Proof. exact (MK_COMB (@lem1534596) (@lem1534595)). Qed.
Lemma lem1534598 (x : real) : (term64 x) = (term44 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1534599 : term74 = term61.
Proof. exact (fun_ext (fun x : real => @lem1534598 x)). Qed.
Lemma lem1534600 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534601 : term75 = term76.
Proof. exact (MK_COMB (@lem1534600) (@lem1534599)). Qed.
Lemma lem1534602 : term59 = term77.
Proof. exact (MK_COMB (@lem1534597) (@lem1534601)). Qed.
Lemma lem1534603 : (term58 = term59) = (term53 = term77).
Proof. exact (MK_COMB (@lem1534591) (@lem1534602)). Qed.
Lemma lem1534604 : term53 = term77.
Proof. exact (EQ_MP (@lem1534603) (@lem1534581)). Qed.
Lemma lem1534614 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1534615 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1534614 real P Q). Qed.
Lemma lem1534616 : term59 = term58.
Proof. exact (@lem1534615 term60 term61). Qed.
Lemma lem1534617 (x : real) : (term62 x) = (term48 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1534618 : term69 = term60.
Proof. exact (fun_ext (fun x : real => @lem1534617 x)). Qed.
Lemma lem1534619 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534620 : term70 = term71.
Proof. exact (MK_COMB (@lem1534619) (@lem1534618)). Qed.
Lemma lem1534621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534622 : term72 = term73.
Proof. exact (MK_COMB (@lem1534621) (@lem1534620)). Qed.
Lemma lem1534623 (x : real) : (term64 x) = (term44 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1534624 : term74 = term61.
Proof. exact (fun_ext (fun x : real => @lem1534623 x)). Qed.
Lemma lem1534625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534626 : term75 = term76.
Proof. exact (MK_COMB (@lem1534625) (@lem1534624)). Qed.
Lemma lem1534627 : term59 = term77.
Proof. exact (MK_COMB (@lem1534622) (@lem1534626)). Qed.
Lemma lem1534628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1534629 : term78 = term79.
Proof. exact (MK_COMB (@lem1534628) (@lem1534627)). Qed.
Lemma lem1534630 (x : real) : (term62 x) = (term48 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1534631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534632 (x : real) : (term63 x) = (term50 x).
Proof. exact (MK_COMB (@lem1534631) (@lem1534630 x)). Qed.
Lemma lem1534633 (x : real) : (term64 x) = (term44 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1534634 (x : real) : (term65 x) = (term51 x).
Proof. exact (MK_COMB (@lem1534632 x) (@lem1534633 x)). Qed.
Lemma lem1534635 : term66 = term52.
Proof. exact (fun_ext (fun x : real => @lem1534634 x)). Qed.
Lemma lem1534636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534637 : term58 = term53.
Proof. exact (MK_COMB (@lem1534636) (@lem1534635)). Qed.
Lemma lem1534638 : (term59 = term58) = (term77 = term53).
Proof. exact (MK_COMB (@lem1534629) (@lem1534637)). Qed.
Lemma lem1534639 : term77 = term53.
Proof. exact (EQ_MP (@lem1534638) (@lem1534616)). Qed.
Lemma lem1534640 : term53 = term53.
Proof. exact (TRANS (@lem1534604) (@lem1534639)). Qed.
Lemma lem1534643 : term2 = term53.
Proof. exact (TRANS (@lem1534577) (@lem1534640)). Qed.
Lemma lem1534648 (x : real) : (term51 x) = (term51 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1534649 : term52 = term52.
Proof. exact (fun_ext (fun x : real => @lem1534648 x)). Qed.
Lemma lem1534650 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1534651 : term53 = term53.
Proof. exact (MK_COMB (@lem1534650) (@lem1534649)). Qed.
Lemma lem1534652 : term2 = term53.
Proof. exact (TRANS (@lem1534643) (@lem1534651)). Qed.
Lemma lem1534654 (a : real) (x : real) (r : real) : (term80 x a r) = (term81 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1534655 (x : real) : (term48 x) = (term82 x).
Proof. exact (@lem1534654 (term6 x) x term42). Qed.
Lemma lem1534662 (x : real) : (term83 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534665 (x : real) : (term84 x) = (term84 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1534666 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem1534665 x) (@lem1534662 x)). Qed.
Lemma lem1534667 (x : real) : (term86 x) = (term87 x).
Proof. exact (@lem1483488 x (term6 x)). Qed.
Lemma lem1534668 (x : real) : (term85 x) = (term87 x).
Proof. exact (TRANS (@lem1534666 x) (@lem1534667 x)). Qed.
Lemma lem1534669 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534670 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1534669) (@lem1534668 x)). Qed.
Lemma lem1534671 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534672 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem1534670 x) (@lem1534671)). Qed.
Lemma lem1534685 (x : real) : (term92 x) = (term93 x).
Proof. exact (@lem1483488 (term94 x) (term6 x)). Qed.
Lemma lem1534686 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534687 (x : real) : (term95 x) = (term96 x).
Proof. exact (MK_COMB (@lem1534686) (@lem1534685 x)). Qed.
Lemma lem1534688 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534689 (x : real) : (term97 x) = (term98 x).
Proof. exact (MK_COMB (@lem1534687 x) (@lem1534688)). Qed.
Lemma lem1534690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534691 (x : real) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem1534690) (@lem1534689 x)). Qed.
Lemma lem1534692 (x : real) : (term82 x) = (term101 x).
Proof. exact (MK_COMB (@lem1534691 x) (@lem1534672 x)). Qed.
Lemma lem1534693 (x : real) : (term48 x) = (term101 x).
Proof. exact (TRANS (@lem1534655 x) (@lem1534692 x)). Qed.
Lemma lem1534694 (x : real) : (term102 x) = (term101 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1534695 (x : real) : (term101 x) = (term102 x).
Proof. exact (SYM (@lem1534694 x)). Qed.
Lemma lem1534696 (x : real) : (term102 x) = (term103 x).
Proof. exact (@lem1482981 (term104 x) (real_abs x)). Qed.
Lemma lem1534697 (x : real) : (term101 x) = (term103 x).
Proof. exact (TRANS (@lem1534695 x) (@lem1534696 x)). Qed.
Lemma lem1534698 (x : real) : (term105 x) = (term106 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1534699 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1534700 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1534699 x) (@lem1534698 x)). Qed.
Lemma lem1534701 (x : real) : (term110 x) = (term111 x).
Proof. exact (eq_refl (term110 x)). Qed.
Lemma lem1534702 (x : real) : (term112 x) = (term112 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1534703 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1534702 x) (@lem1534701 x)). Qed.
Lemma lem1534704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534705 (x : real) : (term115 x) = (term116 x).
Proof. exact (MK_COMB (@lem1534704) (@lem1534703 x)). Qed.
Lemma lem1534706 (x : real) : (term103 x) = (term117 x).
Proof. exact (MK_COMB (@lem1534705 x) (@lem1534700 x)). Qed.
Lemma lem1534707 (x : real) : (term118 x) = (term118 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem1534708 (x : real) : ((term101 x) = (term103 x)) = ((term101 x) = (term117 x)).
Proof. exact (MK_COMB (@lem1534707 x) (@lem1534706 x)). Qed.
Lemma lem1534709 (x : real) : (term101 x) = (term117 x).
Proof. exact (EQ_MP (@lem1534708 x) (@lem1534697 x)). Qed.
Lemma lem1534710 (x : real) : (term119 x) = (term120 x).
Proof. exact (@lem1483527 (real_abs x) term42). Qed.
Lemma lem1534716 (x : real) : (term121 x) = (term122 x).
Proof. exact (@lem1483519 (real_abs x) term42). Qed.
Lemma lem1534718 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534719 : term124 = term42.
Proof. exact (@lem1534718 term29). Qed.
Lemma lem1534720 (x : real) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1534721 (x : real) : (term122 x) = (term125 x).
Proof. exact (MK_COMB (@lem1534720 x) (@lem1534719)). Qed.
Lemma lem1534722 (x : real) : (term125 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1534723 (x : real) : (term122 x) = (real_abs x).
Proof. exact (TRANS (@lem1534721 x) (@lem1534722 x)). Qed.
Lemma lem1534725 (x : real) : (term121 x) = (real_abs x).
Proof. exact (TRANS (@lem1534716 x) (@lem1534723 x)). Qed.
Lemma lem1534726 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1534727 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1534726) (@lem1534725 x)). Qed.
Lemma lem1534728 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534729 (x : real) : (term120 x) = (term119 x).
Proof. exact (MK_COMB (@lem1534727 x) (@lem1534728)). Qed.
Lemma lem1534730 (x : real) : (term119 x) = (term119 x).
Proof. exact (TRANS (@lem1534710 x) (@lem1534729 x)). Qed.
Lemma lem1534731 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1483525 (term130 x) term42). Qed.
Lemma lem1534749 (x : real) : (term131 x) = (term132 x).
Proof. exact (@lem1483519 (term130 x) term42). Qed.
Lemma lem1534751 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534752 : term124 = term42.
Proof. exact (@lem1534751 term29). Qed.
Lemma lem1534753 (x : real) : (term133 x) = (term133 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1534754 (x : real) : (term132 x) = (term134 x).
Proof. exact (MK_COMB (@lem1534753 x) (@lem1534752)). Qed.
Lemma lem1534755 (x : real) : (term134 x) = (term130 x).
Proof. exact (@lem1483450 (term130 x)). Qed.
Lemma lem1534756 (x : real) : (term132 x) = (term130 x).
Proof. exact (TRANS (@lem1534754 x) (@lem1534755 x)). Qed.
Lemma lem1534758 (x : real) : (term131 x) = (term130 x).
Proof. exact (TRANS (@lem1534749 x) (@lem1534756 x)). Qed.
Lemma lem1534759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534760 (x : real) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1534759) (@lem1534758 x)). Qed.
Lemma lem1534761 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534762 (x : real) : (term129 x) = (term128 x).
Proof. exact (MK_COMB (@lem1534760 x) (@lem1534761)). Qed.
Lemma lem1534763 (x : real) : (term128 x) = (term128 x).
Proof. exact (TRANS (@lem1534731 x) (@lem1534762 x)). Qed.
Lemma lem1534764 (x : real) : (term137 x) = (term138 x).
Proof. exact (@lem1483525 (term139 x) term42). Qed.
Lemma lem1534776 (x : real) : (term140 x) = (term141 x).
Proof. exact (@lem1483519 (term139 x) term42). Qed.
Lemma lem1534778 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534779 : term124 = term42.
Proof. exact (@lem1534778 term29). Qed.
Lemma lem1534780 (x : real) : (term142 x) = (term142 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1534781 (x : real) : (term141 x) = (term143 x).
Proof. exact (MK_COMB (@lem1534780 x) (@lem1534779)). Qed.
Lemma lem1534782 (x : real) : (term143 x) = (term139 x).
Proof. exact (@lem1483450 (term139 x)). Qed.
Lemma lem1534783 (x : real) : (term141 x) = (term139 x).
Proof. exact (TRANS (@lem1534781 x) (@lem1534782 x)). Qed.
Lemma lem1534785 (x : real) : (term140 x) = (term139 x).
Proof. exact (TRANS (@lem1534776 x) (@lem1534783 x)). Qed.
Lemma lem1534786 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534787 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1534786) (@lem1534785 x)). Qed.
Lemma lem1534788 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534789 (x : real) : (term138 x) = (term137 x).
Proof. exact (MK_COMB (@lem1534787 x) (@lem1534788)). Qed.
Lemma lem1534790 (x : real) : (term137 x) = (term137 x).
Proof. exact (TRANS (@lem1534764 x) (@lem1534789 x)). Qed.
Lemma lem1534791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534792 (x : real) : (term146 x) = (term146 x).
Proof. exact (MK_COMB (@lem1534791) (@lem1534763 x)). Qed.
Lemma lem1534793 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem1534792 x) (@lem1534790 x)). Qed.
Lemma lem1534794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534795 (x : real) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem1534794) (@lem1534730 x)). Qed.
Lemma lem1534796 (x : real) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1534795 x) (@lem1534793 x)). Qed.
Lemma lem1534797 (x : real) : (term147 x) = (term148 x).
Proof. exact (@lem1483525 term42 (real_abs x)). Qed.
Lemma lem1534803 (x : real) : (term149 x) = (term150 x).
Proof. exact (@lem1483519 term42 (real_abs x)). Qed.
Lemma lem1534808 (x : real) : (term150 x) = (term16 x).
Proof. exact (@lem1483448 (term16 x)). Qed.
Lemma lem1534810 (x : real) : (term149 x) = (term16 x).
Proof. exact (TRANS (@lem1534803 x) (@lem1534808 x)). Qed.
Lemma lem1534811 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534812 (x : real) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem1534811) (@lem1534810 x)). Qed.
Lemma lem1534813 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534814 (x : real) : (term148 x) = (term153 x).
Proof. exact (MK_COMB (@lem1534812 x) (@lem1534813)). Qed.
Lemma lem1534815 (x : real) : (term147 x) = (term153 x).
Proof. exact (TRANS (@lem1534797 x) (@lem1534814 x)). Qed.
Lemma lem1534816 (x : real) : (term154 x) = (term155 x).
Proof. exact (@lem1483525 (term156 x) term42). Qed.
Lemma lem1534817 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534824 (x : real) : (term157 x) = (term16 x).
Proof. exact (@lem1483512 (real_abs x)). Qed.
Lemma lem1534833 (x : real) : (term158 x) = (term158 x).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1534836 (x : real) : (term156 x) = (term159 x).
Proof. exact (MK_COMB (@lem1534833 x) (@lem1534824 x)). Qed.
Lemma lem1534837 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1534838 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1534837) (@lem1534836 x)). Qed.
Lemma lem1534839 (x : real) : (term162 x) = (term163 x).
Proof. exact (MK_COMB (@lem1534838 x) (@lem1534817)). Qed.
Lemma lem1534840 (x : real) : (term163 x) = (term164 x).
Proof. exact (@lem1483519 (term159 x) term42). Qed.
Lemma lem1534842 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534843 : term124 = term42.
Proof. exact (@lem1534842 term29). Qed.
Lemma lem1534844 (x : real) : (term165 x) = (term165 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1534845 (x : real) : (term164 x) = (term166 x).
Proof. exact (MK_COMB (@lem1534844 x) (@lem1534843)). Qed.
Lemma lem1534846 (x : real) : (term166 x) = (term159 x).
Proof. exact (@lem1483450 (term159 x)). Qed.
Lemma lem1534847 (x : real) : (term164 x) = (term159 x).
Proof. exact (TRANS (@lem1534845 x) (@lem1534846 x)). Qed.
Lemma lem1534848 (x : real) : (term163 x) = (term159 x).
Proof. exact (TRANS (@lem1534840 x) (@lem1534847 x)). Qed.
Lemma lem1534849 (x : real) : (term162 x) = (term159 x).
Proof. exact (TRANS (@lem1534839 x) (@lem1534848 x)). Qed.
Lemma lem1534850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534851 (x : real) : (term167 x) = (term168 x).
Proof. exact (MK_COMB (@lem1534850) (@lem1534849 x)). Qed.
Lemma lem1534852 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534853 (x : real) : (term155 x) = (term169 x).
Proof. exact (MK_COMB (@lem1534851 x) (@lem1534852)). Qed.
Lemma lem1534854 (x : real) : (term154 x) = (term169 x).
Proof. exact (TRANS (@lem1534816 x) (@lem1534853 x)). Qed.
Lemma lem1534855 (x : real) : (term170 x) = (term171 x).
Proof. exact (@lem1483525 (term172 x) term42). Qed.
Lemma lem1534856 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534863 (x : real) : (term157 x) = (term16 x).
Proof. exact (@lem1483512 (real_abs x)). Qed.
Lemma lem1534866 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1534869 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1534866 x) (@lem1534863 x)). Qed.
Lemma lem1534870 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1534871 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1534870) (@lem1534869 x)). Qed.
Lemma lem1534872 (x : real) : (term176 x) = (term177 x).
Proof. exact (MK_COMB (@lem1534871 x) (@lem1534856)). Qed.
Lemma lem1534873 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483519 (term173 x) term42). Qed.
Lemma lem1534875 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1534876 : term124 = term42.
Proof. exact (@lem1534875 term29). Qed.
Lemma lem1534877 (x : real) : (term179 x) = (term179 x).
Proof. exact (eq_refl (term179 x)). Qed.
Lemma lem1534878 (x : real) : (term178 x) = (term180 x).
Proof. exact (MK_COMB (@lem1534877 x) (@lem1534876)). Qed.
Lemma lem1534879 (x : real) : (term180 x) = (term173 x).
Proof. exact (@lem1483450 (term173 x)). Qed.
Lemma lem1534880 (x : real) : (term178 x) = (term173 x).
Proof. exact (TRANS (@lem1534878 x) (@lem1534879 x)). Qed.
Lemma lem1534881 (x : real) : (term177 x) = (term173 x).
Proof. exact (TRANS (@lem1534873 x) (@lem1534880 x)). Qed.
Lemma lem1534882 (x : real) : (term176 x) = (term173 x).
Proof. exact (TRANS (@lem1534872 x) (@lem1534881 x)). Qed.
Lemma lem1534883 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534884 (x : real) : (term181 x) = (term182 x).
Proof. exact (MK_COMB (@lem1534883) (@lem1534882 x)). Qed.
Lemma lem1534885 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534886 (x : real) : (term171 x) = (term183 x).
Proof. exact (MK_COMB (@lem1534884 x) (@lem1534885)). Qed.
Lemma lem1534887 (x : real) : (term170 x) = (term183 x).
Proof. exact (TRANS (@lem1534855 x) (@lem1534886 x)). Qed.
Lemma lem1534888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534889 (x : real) : (term184 x) = (term185 x).
Proof. exact (MK_COMB (@lem1534888) (@lem1534854 x)). Qed.
Lemma lem1534890 (x : real) : (term106 x) = (term186 x).
Proof. exact (MK_COMB (@lem1534889 x) (@lem1534887 x)). Qed.
Lemma lem1534891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534892 (x : real) : (term107 x) = (term187 x).
Proof. exact (MK_COMB (@lem1534891) (@lem1534815 x)). Qed.
Lemma lem1534893 (x : real) : (term109 x) = (term188 x).
Proof. exact (MK_COMB (@lem1534892 x) (@lem1534890 x)). Qed.
Lemma lem1534894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1534895 (x : real) : (term116 x) = (term116 x).
Proof. exact (MK_COMB (@lem1534894) (@lem1534796 x)). Qed.
Lemma lem1534896 (x : real) : (term117 x) = (term189 x).
Proof. exact (MK_COMB (@lem1534895 x) (@lem1534893 x)). Qed.
Lemma lem1534897 (x : real) : (term101 x) = (term189 x).
Proof. exact (TRANS (@lem1534709 x) (@lem1534896 x)). Qed.
Lemma lem1534899 (x : real) (r : real) : (term190 x r) = (term191 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1534900 (x : real) : (term153 x) = (term192 x).
Proof. exact (@lem1534899 x term42). Qed.
Lemma lem1534907 (x : real) : (term83 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534908 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534909 (x : real) : (term193 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1534908) (@lem1534907 x)). Qed.
Lemma lem1534910 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534911 (x : real) : (term194 x) = (term195 x).
Proof. exact (MK_COMB (@lem1534909 x) (@lem1534910)). Qed.
Lemma lem1534924 (x : real) : (term196 x) = (term196 x).
Proof. exact (eq_refl (term196 x)). Qed.
Lemma lem1534925 (x : real) : (term192 x) = (term197 x).
Proof. exact (MK_COMB (@lem1534924 x) (@lem1534911 x)). Qed.
Lemma lem1534926 (x : real) : (term153 x) = (term197 x).
Proof. exact (TRANS (@lem1534900 x) (@lem1534925 x)). Qed.
Lemma lem1534927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1534928 (x : real) : (term187 x) = (term198 x).
Proof. exact (MK_COMB (@lem1534927) (@lem1534926 x)). Qed.
Lemma lem1534930 (a : real) (x : real) (r : real) : (term199 a x r) = (term81 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1534931 (x : real) : (term169 x) = (term200 x).
Proof. exact (@lem1534930 (term94 x) x term42). Qed.
Lemma lem1534938 (x : real) : (term83 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1534947 (x : real) : (term158 x) = (term158 x).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1534948 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1534947 x) (@lem1534938 x)). Qed.
Lemma lem1534949 (x : real) : (term202 x) = (term203 x).
Proof. exact (@lem1483440 term21 x). Qed.
Lemma lem1534951 (m : nat) : (term204 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1534952 : term205 = term42.
Proof. exact (@lem1534951 term29). Qed.
Lemma lem1534953 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534954 : term206 = term207.
Proof. exact (MK_COMB (@lem1534953) (@lem1534952)). Qed.
Lemma lem1534955 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1534956 (x : real) : (term203 x) = (term208 x).
Proof. exact (MK_COMB (@lem1534954) (@lem1534955 x)). Qed.
Lemma lem1534957 (x : real) : (term202 x) = (term208 x).
Proof. exact (TRANS (@lem1534949 x) (@lem1534956 x)). Qed.
Lemma lem1534958 (x : real) : (term208 x) = term42.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1534959 (x : real) : (term202 x) = term42.
Proof. exact (TRANS (@lem1534957 x) (@lem1534958 x)). Qed.
Lemma lem1534960 (x : real) : (term201 x) = term42.
Proof. exact (TRANS (@lem1534948 x) (@lem1534959 x)). Qed.
Lemma lem1534961 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534962 (x : real) : (term209 x) = term210.
Proof. exact (MK_COMB (@lem1534961) (@lem1534960 x)). Qed.
Lemma lem1534963 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1534964 (x : real) : (term211 x) = term212.
Proof. exact (MK_COMB (@lem1534962 x) (@lem1534963)). Qed.
Lemma lem1534982 (x : real) : (term213 x) = (term214 x).
Proof. exact (@lem1483438 term21 term21 x). Qed.
Lemma lem1534983 : term215 = term216.
Proof. exact (@lem1367763 term29 term29). Qed.
Lemma lem1534984 : term217 = term218.
Proof. exact (@lem706885). Qed.
Lemma lem1534985 : (term217 = term218) = (term219 = term220).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term218). Qed.
Lemma lem1534986 : term219 = term220.
Proof. exact (EQ_MP (@lem1534985) (@lem1534984)). Qed.
Lemma lem1534987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1534988 : term221 = term222.
Proof. exact (MK_COMB (@lem1534987) (@lem1534986)). Qed.
Lemma lem1534989 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1534990 : term216 = term223.
Proof. exact (MK_COMB (@lem1534989) (@lem1534988)). Qed.
Lemma lem1534991 : term215 = term223.
Proof. exact (TRANS (@lem1534983) (@lem1534990)). Qed.
Lemma lem1534992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1534993 : term224 = term225.
Proof. exact (MK_COMB (@lem1534992) (@lem1534991)). Qed.
Lemma lem1534994 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1534995 (x : real) : (term214 x) = (term226 x).
Proof. exact (MK_COMB (@lem1534993) (@lem1534994 x)). Qed.
Lemma lem1534997 (x : real) : (term213 x) = (term226 x).
Proof. exact (TRANS (@lem1534982 x) (@lem1534995 x)). Qed.
Lemma lem1534998 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1534999 (x : real) : (term227 x) = (term228 x).
Proof. exact (MK_COMB (@lem1534998) (@lem1534997 x)). Qed.
Lemma lem1535000 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535001 (x : real) : (term229 x) = (term230 x).
Proof. exact (MK_COMB (@lem1534999 x) (@lem1535000)). Qed.
Lemma lem1535002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535003 (x : real) : (term231 x) = (term232 x).
Proof. exact (MK_COMB (@lem1535002) (@lem1535001 x)). Qed.
Lemma lem1535004 (x : real) : (term200 x) = (term233 x).
Proof. exact (MK_COMB (@lem1535003 x) (@lem1534964 x)). Qed.
Lemma lem1535005 (x : real) : (term169 x) = (term233 x).
Proof. exact (TRANS (@lem1534931 x) (@lem1535004 x)). Qed.
Lemma lem1535006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535007 (x : real) : (term185 x) = (term234 x).
Proof. exact (MK_COMB (@lem1535006) (@lem1535005 x)). Qed.
Lemma lem1535009 (a : real) (x : real) (r : real) : (term199 a x r) = (term81 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1535010 (x : real) : (term183 x) = (term235 x).
Proof. exact (@lem1535009 x x term42). Qed.
Lemma lem1535017 (x : real) : (term83 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1535020 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1535021 (x : real) : (term236 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1535020 x) (@lem1535017 x)). Qed.
Lemma lem1535022 (x : real) : (real_add x x) = (term237 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1535023 : term238 = term221.
Proof. exact (@lem1367770 term29 term29). Qed.
Lemma lem1535024 : term217 = term218.
Proof. exact (@lem706885). Qed.
Lemma lem1535025 : (term217 = term218) = (term219 = term220).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term218). Qed.
Lemma lem1535026 : term219 = term220.
Proof. exact (EQ_MP (@lem1535025) (@lem1535024)). Qed.
Lemma lem1535027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535028 : term221 = term222.
Proof. exact (MK_COMB (@lem1535027) (@lem1535026)). Qed.
Lemma lem1535029 : term238 = term222.
Proof. exact (TRANS (@lem1535023) (@lem1535028)). Qed.
Lemma lem1535030 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535031 : term239 = term240.
Proof. exact (MK_COMB (@lem1535030) (@lem1535029)). Qed.
Lemma lem1535032 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535033 (x : real) : (term237 x) = (term241 x).
Proof. exact (MK_COMB (@lem1535031) (@lem1535032 x)). Qed.
Lemma lem1535034 (x : real) : (real_add x x) = (term241 x).
Proof. exact (TRANS (@lem1535022 x) (@lem1535033 x)). Qed.
Lemma lem1535035 (x : real) : (term236 x) = (term241 x).
Proof. exact (TRANS (@lem1535021 x) (@lem1535034 x)). Qed.
Lemma lem1535036 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535037 (x : real) : (term242 x) = (term243 x).
Proof. exact (MK_COMB (@lem1535036) (@lem1535035 x)). Qed.
Lemma lem1535038 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535039 (x : real) : (term244 x) = (term245 x).
Proof. exact (MK_COMB (@lem1535037 x) (@lem1535038)). Qed.
Lemma lem1535051 (x : real) : (term246 x) = (term203 x).
Proof. exact (@lem1483442 term21 x). Qed.
Lemma lem1535053 (m : nat) : (term204 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1535054 : term205 = term42.
Proof. exact (@lem1535053 term29). Qed.
Lemma lem1535055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535056 : term206 = term207.
Proof. exact (MK_COMB (@lem1535055) (@lem1535054)). Qed.
Lemma lem1535057 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535058 (x : real) : (term203 x) = (term208 x).
Proof. exact (MK_COMB (@lem1535056) (@lem1535057 x)). Qed.
Lemma lem1535059 (x : real) : (term246 x) = (term208 x).
Proof. exact (TRANS (@lem1535051 x) (@lem1535058 x)). Qed.
Lemma lem1535060 (x : real) : (term208 x) = term42.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1535062 (x : real) : (term246 x) = term42.
Proof. exact (TRANS (@lem1535059 x) (@lem1535060 x)). Qed.
Lemma lem1535063 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535064 (x : real) : (term247 x) = term210.
Proof. exact (MK_COMB (@lem1535063) (@lem1535062 x)). Qed.
Lemma lem1535065 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535066 (x : real) : (term248 x) = term212.
Proof. exact (MK_COMB (@lem1535064 x) (@lem1535065)). Qed.
Lemma lem1535067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535068 (x : real) : (term249 x) = term250.
Proof. exact (MK_COMB (@lem1535067) (@lem1535066 x)). Qed.
Lemma lem1535069 (x : real) : (term235 x) = (term251 x).
Proof. exact (MK_COMB (@lem1535068 x) (@lem1535039 x)). Qed.
Lemma lem1535070 (x : real) : (term183 x) = (term251 x).
Proof. exact (TRANS (@lem1535010 x) (@lem1535069 x)). Qed.
Lemma lem1535071 (x : real) : (term186 x) = (term252 x).
Proof. exact (MK_COMB (@lem1535007 x) (@lem1535070 x)). Qed.
Lemma lem1535074 (x : real) : (term188 x) = (term253 x).
Proof. exact (MK_COMB (@lem1534928 x) (@lem1535071 x)). Qed.
Lemma lem1535076 (x : real) : (term254 x) = (term114 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem1535077 (x : real) : (term114 x) = (term254 x).
Proof. exact (SYM (@lem1535076 x)). Qed.
Lemma lem1535078 (x : real) : (term254 x) = (term255 x).
Proof. exact (@lem1482981 (term256 x) x). Qed.
Lemma lem1535079 (x : real) : (term114 x) = (term255 x).
Proof. exact (TRANS (@lem1535077 x) (@lem1535078 x)). Qed.
Lemma lem1535080 (x : real) : (term257 x) = (term258 x).
Proof. exact (eq_refl (term257 x)). Qed.
Lemma lem1535081 (x : real) : (term259 x) = (term259 x).
Proof. exact (eq_refl (term259 x)). Qed.
Lemma lem1535082 (x : real) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem1535081 x) (@lem1535080 x)). Qed.
Lemma lem1535083 (x : real) : (term262 x) = (term263 x).
Proof. exact (eq_refl (term262 x)). Qed.
Lemma lem1535084 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1535085 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1535084 x) (@lem1535083 x)). Qed.
Lemma lem1535086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535087 (x : real) : (term267 x) = (term268 x).
Proof. exact (MK_COMB (@lem1535086) (@lem1535085 x)). Qed.
Lemma lem1535088 (x : real) : (term255 x) = (term269 x).
Proof. exact (MK_COMB (@lem1535087 x) (@lem1535082 x)). Qed.
Lemma lem1535089 (x : real) : (term270 x) = (term270 x).
Proof. exact (eq_refl (term270 x)). Qed.
Lemma lem1535090 (x : real) : ((term114 x) = (term255 x)) = ((term114 x) = (term269 x)).
Proof. exact (MK_COMB (@lem1535089 x) (@lem1535088 x)). Qed.
Lemma lem1535091 (x : real) : (term114 x) = (term269 x).
Proof. exact (EQ_MP (@lem1535090 x) (@lem1535079 x)). Qed.
Lemma lem1535092 (x : real) : (term271 x) = (term272 x).
Proof. exact (@lem1483527 x term42). Qed.
Lemma lem1535098 (x : real) : (term273 x) = (term274 x).
Proof. exact (@lem1483519 x term42). Qed.
Lemma lem1535100 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535101 : term124 = term42.
Proof. exact (@lem1535100 term29). Qed.
Lemma lem1535102 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1535103 (x : real) : (term274 x) = (term275 x).
Proof. exact (MK_COMB (@lem1535102 x) (@lem1535101)). Qed.
Lemma lem1535104 (x : real) : (term275 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1535105 (x : real) : (term274 x) = x.
Proof. exact (TRANS (@lem1535103 x) (@lem1535104 x)). Qed.
Lemma lem1535107 (x : real) : (term273 x) = x.
Proof. exact (TRANS (@lem1535098 x) (@lem1535105 x)). Qed.
Lemma lem1535108 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1535109 (x : real) : (term276 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1535108) (@lem1535107 x)). Qed.
Lemma lem1535110 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535111 (x : real) : (term272 x) = (term271 x).
Proof. exact (MK_COMB (@lem1535109 x) (@lem1535110)). Qed.
Lemma lem1535112 (x : real) : (term271 x) = (term271 x).
Proof. exact (TRANS (@lem1535092 x) (@lem1535111 x)). Qed.
Lemma lem1535113 (x : real) : (term277 x) = (term278 x).
Proof. exact (@lem1483525 (term202 x) term42). Qed.
Lemma lem1535114 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535126 (x : real) : (term202 x) = (term203 x).
Proof. exact (@lem1483440 term21 x). Qed.
Lemma lem1535128 (m : nat) : (term204 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1535129 : term205 = term42.
Proof. exact (@lem1535128 term29). Qed.
Lemma lem1535130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535131 : term206 = term207.
Proof. exact (MK_COMB (@lem1535130) (@lem1535129)). Qed.
Lemma lem1535132 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535133 (x : real) : (term203 x) = (term208 x).
Proof. exact (MK_COMB (@lem1535131) (@lem1535132 x)). Qed.
Lemma lem1535134 (x : real) : (term202 x) = (term208 x).
Proof. exact (TRANS (@lem1535126 x) (@lem1535133 x)). Qed.
Lemma lem1535135 (x : real) : (term208 x) = term42.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1535137 (x : real) : (term202 x) = term42.
Proof. exact (TRANS (@lem1535134 x) (@lem1535135 x)). Qed.
Lemma lem1535138 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1535139 (x : real) : (term279 x) = term280.
Proof. exact (MK_COMB (@lem1535138) (@lem1535137 x)). Qed.
Lemma lem1535140 (x : real) : (term281 x) = term282.
Proof. exact (MK_COMB (@lem1535139 x) (@lem1535114)). Qed.
Lemma lem1535141 : term282 = term283.
Proof. exact (@lem1483519 term42 term42). Qed.
Lemma lem1535143 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535144 : term124 = term42.
Proof. exact (@lem1535143 term29). Qed.
Lemma lem1535145 : term284 = term284.
Proof. exact (eq_refl term284). Qed.
Lemma lem1535146 : term283 = term285.
Proof. exact (MK_COMB (@lem1535145) (@lem1535144)). Qed.
Lemma lem1535147 : term285 = term42.
Proof. exact (@lem1483448 term42). Qed.
Lemma lem1535148 : term283 = term42.
Proof. exact (TRANS (@lem1535146) (@lem1535147)). Qed.
Lemma lem1535149 : term282 = term42.
Proof. exact (TRANS (@lem1535141) (@lem1535148)). Qed.
Lemma lem1535150 (x : real) : (term281 x) = term42.
Proof. exact (TRANS (@lem1535140 x) (@lem1535149)). Qed.
Lemma lem1535151 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535152 (x : real) : (term286 x) = term210.
Proof. exact (MK_COMB (@lem1535151) (@lem1535150 x)). Qed.
Lemma lem1535153 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535154 (x : real) : (term278 x) = term212.
Proof. exact (MK_COMB (@lem1535152 x) (@lem1535153)). Qed.
Lemma lem1535155 (x : real) : (term277 x) = term212.
Proof. exact (TRANS (@lem1535113 x) (@lem1535154 x)). Qed.
Lemma lem1535156 (x : real) : (term287 x) = (term288 x).
Proof. exact (@lem1483525 (real_add x x) term42). Qed.
Lemma lem1535157 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535163 (x : real) : (real_add x x) = (term237 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1535164 : term238 = term221.
Proof. exact (@lem1367770 term29 term29). Qed.
Lemma lem1535165 : term217 = term218.
Proof. exact (@lem706885). Qed.
Lemma lem1535166 : (term217 = term218) = (term219 = term220).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term218). Qed.
Lemma lem1535167 : term219 = term220.
Proof. exact (EQ_MP (@lem1535166) (@lem1535165)). Qed.
Lemma lem1535168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535169 : term221 = term222.
Proof. exact (MK_COMB (@lem1535168) (@lem1535167)). Qed.
Lemma lem1535170 : term238 = term222.
Proof. exact (TRANS (@lem1535164) (@lem1535169)). Qed.
Lemma lem1535171 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535172 : term239 = term240.
Proof. exact (MK_COMB (@lem1535171) (@lem1535170)). Qed.
Lemma lem1535173 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535174 (x : real) : (term237 x) = (term241 x).
Proof. exact (MK_COMB (@lem1535172) (@lem1535173 x)). Qed.
Lemma lem1535176 (x : real) : (real_add x x) = (term241 x).
Proof. exact (TRANS (@lem1535163 x) (@lem1535174 x)). Qed.
Lemma lem1535177 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1535178 (x : real) : (term289 x) = (term290 x).
Proof. exact (MK_COMB (@lem1535177) (@lem1535176 x)). Qed.
Lemma lem1535179 (x : real) : (term291 x) = (term292 x).
Proof. exact (MK_COMB (@lem1535178 x) (@lem1535157)). Qed.
Lemma lem1535180 (x : real) : (term292 x) = (term293 x).
Proof. exact (@lem1483519 (term241 x) term42). Qed.
Lemma lem1535182 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535183 : term124 = term42.
Proof. exact (@lem1535182 term29). Qed.
Lemma lem1535184 (x : real) : (term294 x) = (term294 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem1535185 (x : real) : (term293 x) = (term295 x).
Proof. exact (MK_COMB (@lem1535184 x) (@lem1535183)). Qed.
Lemma lem1535186 (x : real) : (term295 x) = (term241 x).
Proof. exact (@lem1483450 (term241 x)). Qed.
Lemma lem1535187 (x : real) : (term293 x) = (term241 x).
Proof. exact (TRANS (@lem1535185 x) (@lem1535186 x)). Qed.
Lemma lem1535188 (x : real) : (term292 x) = (term241 x).
Proof. exact (TRANS (@lem1535180 x) (@lem1535187 x)). Qed.
Lemma lem1535189 (x : real) : (term291 x) = (term241 x).
Proof. exact (TRANS (@lem1535179 x) (@lem1535188 x)). Qed.
Lemma lem1535190 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535191 (x : real) : (term296 x) = (term243 x).
Proof. exact (MK_COMB (@lem1535190) (@lem1535189 x)). Qed.
Lemma lem1535192 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535193 (x : real) : (term288 x) = (term245 x).
Proof. exact (MK_COMB (@lem1535191 x) (@lem1535192)). Qed.
Lemma lem1535194 (x : real) : (term287 x) = (term245 x).
Proof. exact (TRANS (@lem1535156 x) (@lem1535193 x)). Qed.
Lemma lem1535195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535196 (x : real) : (term297 x) = term250.
Proof. exact (MK_COMB (@lem1535195) (@lem1535155 x)). Qed.
Lemma lem1535197 (x : real) : (term298 x) = (term251 x).
Proof. exact (MK_COMB (@lem1535196 x) (@lem1535194 x)). Qed.
Lemma lem1535198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535199 (x : real) : (term264 x) = (term264 x).
Proof. exact (MK_COMB (@lem1535198) (@lem1535112 x)). Qed.
Lemma lem1535200 (x : real) : (term263 x) = (term299 x).
Proof. exact (MK_COMB (@lem1535199 x) (@lem1535197 x)). Qed.
Lemma lem1535201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535202 (x : real) : (term264 x) = (term264 x).
Proof. exact (MK_COMB (@lem1535201) (@lem1535112 x)). Qed.
Lemma lem1535203 (x : real) : (term266 x) = (term300 x).
Proof. exact (MK_COMB (@lem1535202 x) (@lem1535200 x)). Qed.
Lemma lem1535204 (x : real) : (term301 x) = (term302 x).
Proof. exact (@lem1483525 term42 x). Qed.
Lemma lem1535210 (x : real) : (term303 x) = (term304 x).
Proof. exact (@lem1483519 term42 x). Qed.
Lemma lem1535215 (x : real) : (term304 x) = (term94 x).
Proof. exact (@lem1483448 (term94 x)). Qed.
Lemma lem1535217 (x : real) : (term303 x) = (term94 x).
Proof. exact (TRANS (@lem1535210 x) (@lem1535215 x)). Qed.
Lemma lem1535218 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535219 (x : real) : (term305 x) = (term306 x).
Proof. exact (MK_COMB (@lem1535218) (@lem1535217 x)). Qed.
Lemma lem1535220 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535221 (x : real) : (term302 x) = (term307 x).
Proof. exact (MK_COMB (@lem1535219 x) (@lem1535220)). Qed.
Lemma lem1535222 (x : real) : (term301 x) = (term307 x).
Proof. exact (TRANS (@lem1535204 x) (@lem1535221 x)). Qed.
Lemma lem1535223 (x : real) : (term308 x) = (term309 x).
Proof. exact (@lem1483527 (real_neg x) term42). Qed.
Lemma lem1535224 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535231 (x : real) : (real_neg x) = (term94 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1535232 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1535233 (x : real) : (term310 x) = (term311 x).
Proof. exact (MK_COMB (@lem1535232) (@lem1535231 x)). Qed.
Lemma lem1535234 (x : real) : (term312 x) = (term313 x).
Proof. exact (MK_COMB (@lem1535233 x) (@lem1535224)). Qed.
Lemma lem1535235 (x : real) : (term313 x) = (term314 x).
Proof. exact (@lem1483519 (term94 x) term42). Qed.
Lemma lem1535237 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535238 : term124 = term42.
Proof. exact (@lem1535237 term29). Qed.
Lemma lem1535239 (x : real) : (term158 x) = (term158 x).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1535240 (x : real) : (term314 x) = (term315 x).
Proof. exact (MK_COMB (@lem1535239 x) (@lem1535238)). Qed.
Lemma lem1535241 (x : real) : (term315 x) = (term94 x).
Proof. exact (@lem1483450 (term94 x)). Qed.
Lemma lem1535242 (x : real) : (term314 x) = (term94 x).
Proof. exact (TRANS (@lem1535240 x) (@lem1535241 x)). Qed.
Lemma lem1535243 (x : real) : (term313 x) = (term94 x).
Proof. exact (TRANS (@lem1535235 x) (@lem1535242 x)). Qed.
Lemma lem1535244 (x : real) : (term312 x) = (term94 x).
Proof. exact (TRANS (@lem1535234 x) (@lem1535243 x)). Qed.
Lemma lem1535245 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1535246 (x : real) : (term316 x) = (term317 x).
Proof. exact (MK_COMB (@lem1535245) (@lem1535244 x)). Qed.
Lemma lem1535247 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535248 (x : real) : (term309 x) = (term318 x).
Proof. exact (MK_COMB (@lem1535246 x) (@lem1535247)). Qed.
Lemma lem1535249 (x : real) : (term308 x) = (term318 x).
Proof. exact (TRANS (@lem1535223 x) (@lem1535248 x)). Qed.
Lemma lem1535250 (x : real) : (term319 x) = (term320 x).
Proof. exact (@lem1483525 (term321 x) term42). Qed.
Lemma lem1535251 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535258 (x : real) : (real_neg x) = (term94 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1535267 (x : real) : (term158 x) = (term158 x).
Proof. exact (eq_refl (term158 x)). Qed.
Lemma lem1535268 (x : real) : (term321 x) = (term213 x).
Proof. exact (MK_COMB (@lem1535267 x) (@lem1535258 x)). Qed.
Lemma lem1535269 (x : real) : (term213 x) = (term214 x).
Proof. exact (@lem1483438 term21 term21 x). Qed.
Lemma lem1535270 : term215 = term216.
Proof. exact (@lem1367763 term29 term29). Qed.
Lemma lem1535271 : term217 = term218.
Proof. exact (@lem706885). Qed.
Lemma lem1535272 : (term217 = term218) = (term219 = term220).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term218). Qed.
Lemma lem1535273 : term219 = term220.
Proof. exact (EQ_MP (@lem1535272) (@lem1535271)). Qed.
Lemma lem1535274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535275 : term221 = term222.
Proof. exact (MK_COMB (@lem1535274) (@lem1535273)). Qed.
Lemma lem1535276 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1535277 : term216 = term223.
Proof. exact (MK_COMB (@lem1535276) (@lem1535275)). Qed.
Lemma lem1535278 : term215 = term223.
Proof. exact (TRANS (@lem1535270) (@lem1535277)). Qed.
Lemma lem1535279 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535280 : term224 = term225.
Proof. exact (MK_COMB (@lem1535279) (@lem1535278)). Qed.
Lemma lem1535281 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535282 (x : real) : (term214 x) = (term226 x).
Proof. exact (MK_COMB (@lem1535280) (@lem1535281 x)). Qed.
Lemma lem1535283 (x : real) : (term213 x) = (term226 x).
Proof. exact (TRANS (@lem1535269 x) (@lem1535282 x)). Qed.
Lemma lem1535284 (x : real) : (term321 x) = (term226 x).
Proof. exact (TRANS (@lem1535268 x) (@lem1535283 x)). Qed.
Lemma lem1535285 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1535286 (x : real) : (term322 x) = (term323 x).
Proof. exact (MK_COMB (@lem1535285) (@lem1535284 x)). Qed.
Lemma lem1535287 (x : real) : (term324 x) = (term325 x).
Proof. exact (MK_COMB (@lem1535286 x) (@lem1535251)). Qed.
Lemma lem1535288 (x : real) : (term325 x) = (term326 x).
Proof. exact (@lem1483519 (term226 x) term42). Qed.
Lemma lem1535290 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535291 : term124 = term42.
Proof. exact (@lem1535290 term29). Qed.
Lemma lem1535292 (x : real) : (term327 x) = (term327 x).
Proof. exact (eq_refl (term327 x)). Qed.
Lemma lem1535293 (x : real) : (term326 x) = (term328 x).
Proof. exact (MK_COMB (@lem1535292 x) (@lem1535291)). Qed.
Lemma lem1535294 (x : real) : (term328 x) = (term226 x).
Proof. exact (@lem1483450 (term226 x)). Qed.
Lemma lem1535295 (x : real) : (term326 x) = (term226 x).
Proof. exact (TRANS (@lem1535293 x) (@lem1535294 x)). Qed.
Lemma lem1535296 (x : real) : (term325 x) = (term226 x).
Proof. exact (TRANS (@lem1535288 x) (@lem1535295 x)). Qed.
Lemma lem1535297 (x : real) : (term324 x) = (term226 x).
Proof. exact (TRANS (@lem1535287 x) (@lem1535296 x)). Qed.
Lemma lem1535298 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535299 (x : real) : (term329 x) = (term228 x).
Proof. exact (MK_COMB (@lem1535298) (@lem1535297 x)). Qed.
Lemma lem1535300 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535301 (x : real) : (term320 x) = (term230 x).
Proof. exact (MK_COMB (@lem1535299 x) (@lem1535300)). Qed.
Lemma lem1535302 (x : real) : (term319 x) = (term230 x).
Proof. exact (TRANS (@lem1535250 x) (@lem1535301 x)). Qed.
Lemma lem1535303 (x : real) : (term330 x) = (term331 x).
Proof. exact (@lem1483525 (term332 x) term42). Qed.
Lemma lem1535304 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535311 (x : real) : (real_neg x) = (term94 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1535314 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1535315 (x : real) : (term332 x) = (term246 x).
Proof. exact (MK_COMB (@lem1535314 x) (@lem1535311 x)). Qed.
Lemma lem1535316 (x : real) : (term246 x) = (term203 x).
Proof. exact (@lem1483442 term21 x). Qed.
Lemma lem1535318 (m : nat) : (term204 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1535319 : term205 = term42.
Proof. exact (@lem1535318 term29). Qed.
Lemma lem1535320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535321 : term206 = term207.
Proof. exact (MK_COMB (@lem1535320) (@lem1535319)). Qed.
Lemma lem1535322 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535323 (x : real) : (term203 x) = (term208 x).
Proof. exact (MK_COMB (@lem1535321) (@lem1535322 x)). Qed.
Lemma lem1535324 (x : real) : (term246 x) = (term208 x).
Proof. exact (TRANS (@lem1535316 x) (@lem1535323 x)). Qed.
Lemma lem1535325 (x : real) : (term208 x) = term42.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1535326 (x : real) : (term246 x) = term42.
Proof. exact (TRANS (@lem1535324 x) (@lem1535325 x)). Qed.
Lemma lem1535327 (x : real) : (term332 x) = term42.
Proof. exact (TRANS (@lem1535315 x) (@lem1535326 x)). Qed.
Lemma lem1535328 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1535329 (x : real) : (term333 x) = term280.
Proof. exact (MK_COMB (@lem1535328) (@lem1535327 x)). Qed.
Lemma lem1535330 (x : real) : (term334 x) = term282.
Proof. exact (MK_COMB (@lem1535329 x) (@lem1535304)). Qed.
Lemma lem1535331 : term282 = term283.
Proof. exact (@lem1483519 term42 term42). Qed.
Lemma lem1535333 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535334 : term124 = term42.
Proof. exact (@lem1535333 term29). Qed.
Lemma lem1535335 : term284 = term284.
Proof. exact (eq_refl term284). Qed.
Lemma lem1535336 : term283 = term285.
Proof. exact (MK_COMB (@lem1535335) (@lem1535334)). Qed.
Lemma lem1535337 : term285 = term42.
Proof. exact (@lem1483448 term42). Qed.
Lemma lem1535338 : term283 = term42.
Proof. exact (TRANS (@lem1535336) (@lem1535337)). Qed.
Lemma lem1535339 : term282 = term42.
Proof. exact (TRANS (@lem1535331) (@lem1535338)). Qed.
Lemma lem1535340 (x : real) : (term334 x) = term42.
Proof. exact (TRANS (@lem1535330 x) (@lem1535339)). Qed.
Lemma lem1535341 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535342 (x : real) : (term335 x) = term210.
Proof. exact (MK_COMB (@lem1535341) (@lem1535340 x)). Qed.
Lemma lem1535343 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535344 (x : real) : (term331 x) = term212.
Proof. exact (MK_COMB (@lem1535342 x) (@lem1535343)). Qed.
Lemma lem1535345 (x : real) : (term330 x) = term212.
Proof. exact (TRANS (@lem1535303 x) (@lem1535344 x)). Qed.
Lemma lem1535346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535347 (x : real) : (term336 x) = (term232 x).
Proof. exact (MK_COMB (@lem1535346) (@lem1535302 x)). Qed.
Lemma lem1535348 (x : real) : (term337 x) = (term233 x).
Proof. exact (MK_COMB (@lem1535347 x) (@lem1535345 x)). Qed.
Lemma lem1535349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535350 (x : real) : (term338 x) = (term339 x).
Proof. exact (MK_COMB (@lem1535349) (@lem1535249 x)). Qed.
Lemma lem1535351 (x : real) : (term258 x) = (term340 x).
Proof. exact (MK_COMB (@lem1535350 x) (@lem1535348 x)). Qed.
Lemma lem1535352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535353 (x : real) : (term259 x) = (term196 x).
Proof. exact (MK_COMB (@lem1535352) (@lem1535222 x)). Qed.
Lemma lem1535354 (x : real) : (term261 x) = (term341 x).
Proof. exact (MK_COMB (@lem1535353 x) (@lem1535351 x)). Qed.
Lemma lem1535355 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535356 (x : real) : (term268 x) = (term342 x).
Proof. exact (MK_COMB (@lem1535355) (@lem1535203 x)). Qed.
Lemma lem1535357 (x : real) : (term269 x) = (term343 x).
Proof. exact (MK_COMB (@lem1535356 x) (@lem1535354 x)). Qed.
Lemma lem1535369 (x : real) : (term114 x) = (term343 x).
Proof. exact (TRANS (@lem1535091 x) (@lem1535357 x)). Qed.
Lemma lem1535370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535371 (x : real) : (term116 x) = (term344 x).
Proof. exact (MK_COMB (@lem1535370) (@lem1535369 x)). Qed.
Lemma lem1535372 (x : real) : (term189 x) = (term345 x).
Proof. exact (MK_COMB (@lem1535371 x) (@lem1535074 x)). Qed.
Lemma lem1535373 (x : real) : (term101 x) = (term345 x).
Proof. exact (TRANS (@lem1534897 x) (@lem1535372 x)). Qed.
Lemma lem1535374 (x : real) : (term48 x) = (term345 x).
Proof. exact (TRANS (@lem1534693 x) (@lem1535373 x)). Qed.
Lemma lem1535376 (a : real) (x : real) (r : real) : (term199 a x r) = (term81 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1535377 (x : real) : (term44 x) = (term346 x).
Proof. exact (@lem1535376 (real_abs x) (real_abs x) term42). Qed.
Lemma lem1535384 (x : real) : (term35 x) = (real_abs x).
Proof. exact (@lem1483460 (real_abs x)). Qed.
Lemma lem1535387 (x : real) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1535388 (x : real) : (term347 x) = (term348 x).
Proof. exact (MK_COMB (@lem1535387 x) (@lem1535384 x)). Qed.
Lemma lem1535389 (x : real) : (term348 x) = (term349 x).
Proof. exact (@lem1483444 (real_abs x)). Qed.
Lemma lem1535390 : term238 = term221.
Proof. exact (@lem1367770 term29 term29). Qed.
Lemma lem1535391 : term217 = term218.
Proof. exact (@lem706885). Qed.
Lemma lem1535392 : (term217 = term218) = (term219 = term220).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term218). Qed.
Lemma lem1535393 : term219 = term220.
Proof. exact (EQ_MP (@lem1535392) (@lem1535391)). Qed.
Lemma lem1535394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535395 : term221 = term222.
Proof. exact (MK_COMB (@lem1535394) (@lem1535393)). Qed.
Lemma lem1535396 : term238 = term222.
Proof. exact (TRANS (@lem1535390) (@lem1535395)). Qed.
Lemma lem1535397 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535398 : term239 = term240.
Proof. exact (MK_COMB (@lem1535397) (@lem1535396)). Qed.
Lemma lem1535399 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1535400 (x : real) : (term349 x) = (term350 x).
Proof. exact (MK_COMB (@lem1535398) (@lem1535399 x)). Qed.
Lemma lem1535401 (x : real) : (term348 x) = (term350 x).
Proof. exact (TRANS (@lem1535389 x) (@lem1535400 x)). Qed.
Lemma lem1535402 (x : real) : (term347 x) = (term350 x).
Proof. exact (TRANS (@lem1535388 x) (@lem1535401 x)). Qed.
Lemma lem1535403 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535404 (x : real) : (term351 x) = (term352 x).
Proof. exact (MK_COMB (@lem1535403) (@lem1535402 x)). Qed.
Lemma lem1535405 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535406 (x : real) : (term353 x) = (term354 x).
Proof. exact (MK_COMB (@lem1535404 x) (@lem1535405)). Qed.
Lemma lem1535418 (x : real) : (term355 x) = (term356 x).
Proof. exact (@lem1483442 term21 (real_abs x)). Qed.
Lemma lem1535420 (m : nat) : (term204 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1535421 : term205 = term42.
Proof. exact (@lem1535420 term29). Qed.
Lemma lem1535422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535423 : term206 = term207.
Proof. exact (MK_COMB (@lem1535422) (@lem1535421)). Qed.
Lemma lem1535424 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1535425 (x : real) : (term356 x) = (term357 x).
Proof. exact (MK_COMB (@lem1535423) (@lem1535424 x)). Qed.
Lemma lem1535426 (x : real) : (term355 x) = (term357 x).
Proof. exact (TRANS (@lem1535418 x) (@lem1535425 x)). Qed.
Lemma lem1535427 (x : real) : (term357 x) = term42.
Proof. exact (@lem1483446 (real_abs x)). Qed.
Lemma lem1535429 (x : real) : (term355 x) = term42.
Proof. exact (TRANS (@lem1535426 x) (@lem1535427 x)). Qed.
Lemma lem1535430 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535431 (x : real) : (term358 x) = term210.
Proof. exact (MK_COMB (@lem1535430) (@lem1535429 x)). Qed.
Lemma lem1535432 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535433 (x : real) : (term359 x) = term212.
Proof. exact (MK_COMB (@lem1535431 x) (@lem1535432)). Qed.
Lemma lem1535434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535435 (x : real) : (term360 x) = term250.
Proof. exact (MK_COMB (@lem1535434) (@lem1535433 x)). Qed.
Lemma lem1535436 (x : real) : (term346 x) = (term361 x).
Proof. exact (MK_COMB (@lem1535435 x) (@lem1535406 x)). Qed.
Lemma lem1535437 (x : real) : (term44 x) = (term361 x).
Proof. exact (TRANS (@lem1535377 x) (@lem1535436 x)). Qed.
Lemma lem1535438 (x : real) : (term362 x) = (term361 x).
Proof. exact (eq_refl (term362 x)). Qed.
Lemma lem1535439 (x : real) : (term361 x) = (term362 x).
Proof. exact (SYM (@lem1535438 x)). Qed.
Lemma lem1535440 (x : real) : (term362 x) = (term363 x).
Proof. exact (@lem1482981 term364 x). Qed.
Lemma lem1535441 (x : real) : (term361 x) = (term363 x).
Proof. exact (TRANS (@lem1535439 x) (@lem1535440 x)). Qed.
Lemma lem1535442 (x : real) : (term365 x) = (term366 x).
Proof. exact (eq_refl (term365 x)). Qed.
Lemma lem1535443 (x : real) : (term259 x) = (term259 x).
Proof. exact (eq_refl (term259 x)). Qed.
Lemma lem1535444 (x : real) : (term367 x) = (term368 x).
Proof. exact (MK_COMB (@lem1535443 x) (@lem1535442 x)). Qed.
Lemma lem1535445 (x : real) : (term369 x) = (term251 x).
Proof. exact (eq_refl (term369 x)). Qed.
Lemma lem1535446 (x : real) : (term264 x) = (term264 x).
Proof. exact (eq_refl (term264 x)). Qed.
Lemma lem1535447 (x : real) : (term370 x) = (term299 x).
Proof. exact (MK_COMB (@lem1535446 x) (@lem1535445 x)). Qed.
Lemma lem1535448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535449 (x : real) : (term371 x) = (term372 x).
Proof. exact (MK_COMB (@lem1535448) (@lem1535447 x)). Qed.
Lemma lem1535450 (x : real) : (term363 x) = (term373 x).
Proof. exact (MK_COMB (@lem1535449 x) (@lem1535444 x)). Qed.
Lemma lem1535451 (x : real) : (term374 x) = (term374 x).
Proof. exact (eq_refl (term374 x)). Qed.
Lemma lem1535452 (x : real) : ((term361 x) = (term363 x)) = ((term361 x) = (term373 x)).
Proof. exact (MK_COMB (@lem1535451 x) (@lem1535450 x)). Qed.
Lemma lem1535453 (x : real) : (term361 x) = (term373 x).
Proof. exact (EQ_MP (@lem1535452 x) (@lem1535441 x)). Qed.
Lemma lem1535454 : term212 = term375.
Proof. exact (@lem1483525 term42 term42). Qed.
Lemma lem1535460 : term282 = term283.
Proof. exact (@lem1483519 term42 term42). Qed.
Lemma lem1535462 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535463 : term124 = term42.
Proof. exact (@lem1535462 term29). Qed.
Lemma lem1535464 : term284 = term284.
Proof. exact (eq_refl term284). Qed.
Lemma lem1535465 : term283 = term285.
Proof. exact (MK_COMB (@lem1535464) (@lem1535463)). Qed.
Lemma lem1535466 : term285 = term42.
Proof. exact (@lem1483448 term42). Qed.
Lemma lem1535467 : term283 = term42.
Proof. exact (TRANS (@lem1535465) (@lem1535466)). Qed.
Lemma lem1535469 : term282 = term42.
Proof. exact (TRANS (@lem1535460) (@lem1535467)). Qed.
Lemma lem1535470 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535471 : term376 = term210.
Proof. exact (MK_COMB (@lem1535470) (@lem1535469)). Qed.
Lemma lem1535472 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535473 : term375 = term212.
Proof. exact (MK_COMB (@lem1535471) (@lem1535472)). Qed.
Lemma lem1535474 : term212 = term212.
Proof. exact (TRANS (@lem1535454) (@lem1535473)). Qed.
Lemma lem1535475 (x : real) : (term245 x) = (term377 x).
Proof. exact (@lem1483525 (term241 x) term42). Qed.
Lemma lem1535487 (x : real) : (term292 x) = (term293 x).
Proof. exact (@lem1483519 (term241 x) term42). Qed.
Lemma lem1535489 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535490 : term124 = term42.
Proof. exact (@lem1535489 term29). Qed.
Lemma lem1535491 (x : real) : (term294 x) = (term294 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem1535492 (x : real) : (term293 x) = (term295 x).
Proof. exact (MK_COMB (@lem1535491 x) (@lem1535490)). Qed.
Lemma lem1535493 (x : real) : (term295 x) = (term241 x).
Proof. exact (@lem1483450 (term241 x)). Qed.
Lemma lem1535494 (x : real) : (term293 x) = (term241 x).
Proof. exact (TRANS (@lem1535492 x) (@lem1535493 x)). Qed.
Lemma lem1535496 (x : real) : (term292 x) = (term241 x).
Proof. exact (TRANS (@lem1535487 x) (@lem1535494 x)). Qed.
Lemma lem1535497 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535498 (x : real) : (term378 x) = (term243 x).
Proof. exact (MK_COMB (@lem1535497) (@lem1535496 x)). Qed.
Lemma lem1535499 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535500 (x : real) : (term377 x) = (term245 x).
Proof. exact (MK_COMB (@lem1535498 x) (@lem1535499)). Qed.
Lemma lem1535501 (x : real) : (term245 x) = (term245 x).
Proof. exact (TRANS (@lem1535475 x) (@lem1535500 x)). Qed.
Lemma lem1535502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535503 : term250 = term250.
Proof. exact (MK_COMB (@lem1535502) (@lem1535474)). Qed.
Lemma lem1535504 (x : real) : (term251 x) = (term251 x).
Proof. exact (MK_COMB (@lem1535503) (@lem1535501 x)). Qed.
Lemma lem1535505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535506 (x : real) : (term264 x) = (term264 x).
Proof. exact (MK_COMB (@lem1535505) (@lem1535112 x)). Qed.
Lemma lem1535507 (x : real) : (term299 x) = (term299 x).
Proof. exact (MK_COMB (@lem1535506 x) (@lem1535504 x)). Qed.
Lemma lem1535508 (x : real) : (term379 x) = (term380 x).
Proof. exact (@lem1483525 (term381 x) term42). Qed.
Lemma lem1535509 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535516 (x : real) : (real_neg x) = (term94 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1535519 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem1535520 (x : real) : (term381 x) = (term382 x).
Proof. exact (MK_COMB (@lem1535519) (@lem1535516 x)). Qed.
Lemma lem1535521 (x : real) : (term382 x) = (term383 x).
Proof. exact (@lem1483476 term222 term21 x). Qed.
Lemma lem1535523 (m : nat) (n : nat) : (term384 m n) = (term385 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1535524 : term386 = term387.
Proof. exact (@lem1535523 term220 term29). Qed.
Lemma lem1535525 : term388 = term218.
Proof. exact (@lem996237 term218). Qed.
Lemma lem1535526 : (term388 = term218) = (term389 = term220).
Proof. exact (@lem1007663 term218 (BIT1 0) term218). Qed.
Lemma lem1535527 : term389 = term220.
Proof. exact (EQ_MP (@lem1535526) (@lem1535525)). Qed.
Lemma lem1535528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535529 : term390 = term222.
Proof. exact (MK_COMB (@lem1535528) (@lem1535527)). Qed.
Lemma lem1535530 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1535531 : term387 = term223.
Proof. exact (MK_COMB (@lem1535530) (@lem1535529)). Qed.
Lemma lem1535532 : term386 = term223.
Proof. exact (TRANS (@lem1535524) (@lem1535531)). Qed.
Lemma lem1535533 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535534 : term391 = term225.
Proof. exact (MK_COMB (@lem1535533) (@lem1535532)). Qed.
Lemma lem1535535 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535536 (x : real) : (term383 x) = (term226 x).
Proof. exact (MK_COMB (@lem1535534) (@lem1535535 x)). Qed.
Lemma lem1535537 (x : real) : (term382 x) = (term226 x).
Proof. exact (TRANS (@lem1535521 x) (@lem1535536 x)). Qed.
Lemma lem1535538 (x : real) : (term381 x) = (term226 x).
Proof. exact (TRANS (@lem1535520 x) (@lem1535537 x)). Qed.
Lemma lem1535539 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1535540 (x : real) : (term392 x) = (term323 x).
Proof. exact (MK_COMB (@lem1535539) (@lem1535538 x)). Qed.
Lemma lem1535541 (x : real) : (term393 x) = (term325 x).
Proof. exact (MK_COMB (@lem1535540 x) (@lem1535509)). Qed.
Lemma lem1535542 (x : real) : (term325 x) = (term326 x).
Proof. exact (@lem1483519 (term226 x) term42). Qed.
Lemma lem1535544 (x : nat) : (term123 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535545 : term124 = term42.
Proof. exact (@lem1535544 term29). Qed.
Lemma lem1535546 (x : real) : (term327 x) = (term327 x).
Proof. exact (eq_refl (term327 x)). Qed.
Lemma lem1535547 (x : real) : (term326 x) = (term328 x).
Proof. exact (MK_COMB (@lem1535546 x) (@lem1535545)). Qed.
Lemma lem1535548 (x : real) : (term328 x) = (term226 x).
Proof. exact (@lem1483450 (term226 x)). Qed.
Lemma lem1535549 (x : real) : (term326 x) = (term226 x).
Proof. exact (TRANS (@lem1535547 x) (@lem1535548 x)). Qed.
Lemma lem1535550 (x : real) : (term325 x) = (term226 x).
Proof. exact (TRANS (@lem1535542 x) (@lem1535549 x)). Qed.
Lemma lem1535551 (x : real) : (term393 x) = (term226 x).
Proof. exact (TRANS (@lem1535541 x) (@lem1535550 x)). Qed.
Lemma lem1535552 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535553 (x : real) : (term394 x) = (term228 x).
Proof. exact (MK_COMB (@lem1535552) (@lem1535551 x)). Qed.
Lemma lem1535554 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1535555 (x : real) : (term380 x) = (term230 x).
Proof. exact (MK_COMB (@lem1535553 x) (@lem1535554)). Qed.
Lemma lem1535556 (x : real) : (term379 x) = (term230 x).
Proof. exact (TRANS (@lem1535508 x) (@lem1535555 x)). Qed.
Lemma lem1535557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535558 : term250 = term250.
Proof. exact (MK_COMB (@lem1535557) (@lem1535474)). Qed.
Lemma lem1535559 (x : real) : (term366 x) = (term395 x).
Proof. exact (MK_COMB (@lem1535558) (@lem1535556 x)). Qed.
Lemma lem1535560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535561 (x : real) : (term259 x) = (term196 x).
Proof. exact (MK_COMB (@lem1535560) (@lem1535222 x)). Qed.
Lemma lem1535562 (x : real) : (term368 x) = (term396 x).
Proof. exact (MK_COMB (@lem1535561 x) (@lem1535559 x)). Qed.
Lemma lem1535563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535564 (x : real) : (term372 x) = (term372 x).
Proof. exact (MK_COMB (@lem1535563) (@lem1535507 x)). Qed.
Lemma lem1535565 (x : real) : (term373 x) = (term397 x).
Proof. exact (MK_COMB (@lem1535564 x) (@lem1535562 x)). Qed.
Lemma lem1535576 (x : real) : (term361 x) = (term397 x).
Proof. exact (TRANS (@lem1535453 x) (@lem1535565 x)). Qed.
Lemma lem1535577 (x : real) : (term44 x) = (term397 x).
Proof. exact (TRANS (@lem1535437 x) (@lem1535576 x)). Qed.
Lemma lem1535578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535579 (x : real) : (term50 x) = (term398 x).
Proof. exact (MK_COMB (@lem1535578) (@lem1535374 x)). Qed.
Lemma lem1535580 (x : real) : (term51 x) = (term399 x).
Proof. exact (MK_COMB (@lem1535579 x) (@lem1535577 x)). Qed.
Lemma lem1535581 (x : real) (h1 : term399 x) : term399 x.
Proof. exact (h1). Qed.
Lemma lem1535582 (x : real) (h1 : term345 x) : term345 x.
Proof. exact (h1). Qed.
Lemma lem1535583 (x : real) (h1 : term343 x) : term343 x.
Proof. exact (h1). Qed.
Lemma lem1535584 (x : real) (h1 : term300 x) : term300 x.
Proof. exact (h1). Qed.
Lemma lem1535585 (x : real) (h1 : term300 x) : term299 x.
Proof. exact (proj2 (@lem1535584 x h1)). Qed.
Lemma lem1535587 (x : real) (h1 : term300 x) : term251 x.
Proof. exact (proj2 (@lem1535585 x h1)). Qed.
Lemma lem1535590 (x : real) (h1 : term300 x) : term212.
Proof. exact (proj1 (@lem1535587 x h1)). Qed.
Lemma lem1535592 (n : nat) (m : nat) : (term400 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1535593 : term212 = term401.
Proof. exact (@lem1535592 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1535594 : term401 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1535595 : term212 = False.
Proof. exact (TRANS (@lem1535593) (@lem1535594)). Qed.
Lemma lem1535596 (x : real) (h1 : term300 x) : False.
Proof. exact (EQ_MP (@lem1535595) (@lem1535590 x h1)). Qed.
Lemma lem1535597 (x : real) (h1 : term341 x) : term341 x.
Proof. exact (h1). Qed.
Lemma lem1535598 (x : real) (h1 : term341 x) : term340 x.
Proof. exact (proj2 (@lem1535597 x h1)). Qed.
Lemma lem1535600 (x : real) (h1 : term341 x) : term233 x.
Proof. exact (proj2 (@lem1535598 x h1)). Qed.
Lemma lem1535602 (x : real) (h1 : term341 x) : term212.
Proof. exact (proj2 (@lem1535600 x h1)). Qed.
Lemma lem1535605 (n : nat) (m : nat) : (term400 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1535606 : term212 = term401.
Proof. exact (@lem1535605 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1535607 : term401 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1535608 : term212 = False.
Proof. exact (TRANS (@lem1535606) (@lem1535607)). Qed.
Lemma lem1535609 (x : real) (h1 : term341 x) : False.
Proof. exact (EQ_MP (@lem1535608) (@lem1535602 x h1)). Qed.
Lemma lem1535610 (x : real) (h1 : term343 x) : False.
Proof. exact (or_elim (@lem1535583 x h1) (fun h0 : term300 x => @lem1535596 x h0) (fun h0 : term341 x => @lem1535609 x h0)). Qed.
Lemma lem1535611 (x : real) (h1 : term253 x) : term253 x.
Proof. exact (h1). Qed.
Lemma lem1535612 (x : real) (h1 : term253 x) : term252 x.
Proof. exact (proj2 (@lem1535611 x h1)). Qed.
Lemma lem1535616 (x : real) (h1 : term253 x) : term251 x.
Proof. exact (proj2 (@lem1535612 x h1)). Qed.
Lemma lem1535621 (x : real) (h1 : term253 x) : term212.
Proof. exact (proj1 (@lem1535616 x h1)). Qed.
Lemma lem1535623 (n : nat) (m : nat) : (term400 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1535624 : term212 = term401.
Proof. exact (@lem1535623 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1535625 : term401 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1535626 : term212 = False.
Proof. exact (TRANS (@lem1535624) (@lem1535625)). Qed.
Lemma lem1535627 (x : real) (h1 : term253 x) : False.
Proof. exact (EQ_MP (@lem1535626) (@lem1535621 x h1)). Qed.
Lemma lem1535628 (x : real) (h1 : term345 x) : False.
Proof. exact (or_elim (@lem1535582 x h1) (fun h0 : term343 x => @lem1535610 x h0) (fun h0 : term253 x => @lem1535627 x h0)). Qed.
Lemma lem1535629 (x : real) (h1 : term397 x) : term397 x.
Proof. exact (h1). Qed.
Lemma lem1535630 (x : real) (h1 : term299 x) : term299 x.
Proof. exact (h1). Qed.
Lemma lem1535631 (x : real) (h1 : term299 x) : term251 x.
Proof. exact (proj2 (@lem1535630 x h1)). Qed.
Lemma lem1535634 (x : real) (h1 : term299 x) : term212.
Proof. exact (proj1 (@lem1535631 x h1)). Qed.
Lemma lem1535636 (n : nat) (m : nat) : (term400 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1535637 : term212 = term401.
Proof. exact (@lem1535636 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1535638 : term401 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1535639 : term212 = False.
Proof. exact (TRANS (@lem1535637) (@lem1535638)). Qed.
Lemma lem1535640 (x : real) (h1 : term299 x) : False.
Proof. exact (EQ_MP (@lem1535639) (@lem1535634 x h1)). Qed.
Lemma lem1535641 (x : real) (h1 : term396 x) : term396 x.
Proof. exact (h1). Qed.
Lemma lem1535642 (x : real) (h1 : term396 x) : term395 x.
Proof. exact (proj2 (@lem1535641 x h1)). Qed.
Lemma lem1535645 (x : real) (h1 : term396 x) : term212.
Proof. exact (proj1 (@lem1535642 x h1)). Qed.
Lemma lem1535647 (n : nat) (m : nat) : (term400 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1535648 : term212 = term401.
Proof. exact (@lem1535647 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1535649 : term401 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1535650 : term212 = False.
Proof. exact (TRANS (@lem1535648) (@lem1535649)). Qed.
Lemma lem1535651 (x : real) (h1 : term396 x) : False.
Proof. exact (EQ_MP (@lem1535650) (@lem1535645 x h1)). Qed.
Lemma lem1535652 (x : real) (h1 : term397 x) : False.
Proof. exact (or_elim (@lem1535629 x h1) (fun h0 : term299 x => @lem1535640 x h0) (fun h0 : term396 x => @lem1535651 x h0)). Qed.
Lemma lem1535653 (x : real) (h1 : term399 x) : False.
Proof. exact (or_elim (@lem1535581 x h1) (fun h0 : term345 x => @lem1535628 x h0) (fun h0 : term397 x => @lem1535652 x h0)). Qed.
Lemma lem1535654 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1535655 (x : real) (h1 : term51 x) : term399 x.
Proof. exact (EQ_MP (@lem1535580 x) (@lem1535654 x h1)). Qed.
Lemma lem1535656 (x : real) (h1 : term51 x) : (term399 x) = False.
Proof. exact (prop_ext (fun h2 : term399 x => @lem1535653 x h2) (fun h2 : False => @lem1535655 x h1)). Qed.
Lemma lem1535657 (x : real) (h1 : term51 x) : False.
Proof. exact (EQ_MP (@lem1535656 x h1) (@lem1535655 x h1)). Qed.
Lemma lem1535658 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1535659 (h1 : term53) : False.
Proof. exact (ex_elim (@lem1535658 h1) (fun x : real => fun h0 : term52 x => @lem1535657 x h0)). Qed.
Lemma lem1535660 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1535661 (h1 : term2) : term53.
Proof. exact (EQ_MP (@lem1534652) (@lem1535660 h1)). Qed.
Lemma lem1535662 (h1 : term2) : term53 = False.
Proof. exact (prop_ext (fun h2 : term53 => @lem1535659 h2) (fun h2 : False => @lem1535661 h1)). Qed.
Lemma lem1535663 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1535662 h1) (@lem1535661 h1)). Qed.
Lemma lem1535664 : term402.
Proof. exact (fun h0 : term2 => @lem1535663 h0). Qed.
Lemma lem1535665 : term403.
Proof. exact (@lem1386578 term404). Qed.
Lemma lem1535666 : term404.
Proof. exact (@lem1535665 (@lem1535664)). Qed.
