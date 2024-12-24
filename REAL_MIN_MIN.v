Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_MIN_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482716_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483533_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Lemma lem1557487 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term1 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1557488 (P : real -> Prop) (Q : real -> Prop) : (term2 P Q) = (term3 P Q).
Proof. exact (@lem1557487 real P Q). Qed.
Lemma lem1557489 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem1557488 (term6 x) (term7 x)). Qed.
Lemma lem1557490 (y : real) (x : real) : (term8 x y) = (term9 y x).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1557491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557492 (y : real) (x : real) : (term10 x y) = (term11 y x).
Proof. exact (MK_COMB (@lem1557491) (@lem1557490 y x)). Qed.
Lemma lem1557493 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1557494 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1557492 y x) (@lem1557493 x y)). Qed.
Lemma lem1557495 (x : real) : (term16 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1557494 x y)). Qed.
Lemma lem1557496 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557497 (x : real) : (term4 x) = (term18 x).
Proof. exact (MK_COMB (@lem1557496) (@lem1557495 x)). Qed.
Lemma lem1557498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557499 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1557498) (@lem1557497 x)). Qed.
Lemma lem1557500 (y : real) (x : real) : (term8 x y) = (term9 y x).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1557501 (x : real) : (term21 x) = (term6 x).
Proof. exact (fun_ext (fun y : real => @lem1557500 y x)). Qed.
Lemma lem1557502 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557503 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1557502) (@lem1557501 x)). Qed.
Lemma lem1557504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557505 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1557504) (@lem1557503 x)). Qed.
Lemma lem1557506 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1557507 (x : real) : (term26 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1557506 x y)). Qed.
Lemma lem1557508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557509 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1557508) (@lem1557507 x)). Qed.
Lemma lem1557510 (x : real) : (term5 x) = (term29 x).
Proof. exact (MK_COMB (@lem1557505 x) (@lem1557509 x)). Qed.
Lemma lem1557511 (x : real) : ((term4 x) = (term5 x)) = ((term18 x) = (term29 x)).
Proof. exact (MK_COMB (@lem1557499 x) (@lem1557510 x)). Qed.
Lemma lem1557512 (x : real) : (term18 x) = (term29 x).
Proof. exact (EQ_MP (@lem1557511 x) (@lem1557489 x)). Qed.
Lemma lem1557523 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1557512 x)). Qed.
Lemma lem1557524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557525 : term32 = term33.
Proof. exact (MK_COMB (@lem1557524) (@lem1557523)). Qed.
Lemma lem1557527 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term1 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1557528 (P : real -> Prop) (Q : real -> Prop) : (term2 P Q) = (term3 P Q).
Proof. exact (@lem1557527 real P Q). Qed.
Lemma lem1557529 : term34 = term35.
Proof. exact (@lem1557528 term36 term37). Qed.
Lemma lem1557530 (x : real) : (term38 x) = (term23 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1557531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557532 (x : real) : (term39 x) = (term25 x).
Proof. exact (MK_COMB (@lem1557531) (@lem1557530 x)). Qed.
Lemma lem1557533 (x : real) : (term40 x) = (term28 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1557534 (x : real) : (term41 x) = (term29 x).
Proof. exact (MK_COMB (@lem1557532 x) (@lem1557533 x)). Qed.
Lemma lem1557535 : term42 = term31.
Proof. exact (fun_ext (fun x : real => @lem1557534 x)). Qed.
Lemma lem1557536 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557537 : term34 = term33.
Proof. exact (MK_COMB (@lem1557536) (@lem1557535)). Qed.
Lemma lem1557538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557539 : term43 = term44.
Proof. exact (MK_COMB (@lem1557538) (@lem1557537)). Qed.
Lemma lem1557540 (x : real) : (term38 x) = (term23 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1557541 : term45 = term36.
Proof. exact (fun_ext (fun x : real => @lem1557540 x)). Qed.
Lemma lem1557542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557543 : term46 = term47.
Proof. exact (MK_COMB (@lem1557542) (@lem1557541)). Qed.
Lemma lem1557544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557545 : term48 = term49.
Proof. exact (MK_COMB (@lem1557544) (@lem1557543)). Qed.
Lemma lem1557546 (x : real) : (term40 x) = (term28 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1557547 : term50 = term37.
Proof. exact (fun_ext (fun x : real => @lem1557546 x)). Qed.
Lemma lem1557548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1557549 : term51 = term52.
Proof. exact (MK_COMB (@lem1557548) (@lem1557547)). Qed.
Lemma lem1557550 : term35 = term53.
Proof. exact (MK_COMB (@lem1557545) (@lem1557549)). Qed.
Lemma lem1557551 : (term34 = term35) = (term33 = term53).
Proof. exact (MK_COMB (@lem1557539) (@lem1557550)). Qed.
Lemma lem1557552 : term33 = term53.
Proof. exact (EQ_MP (@lem1557551) (@lem1557529)). Qed.
Lemma lem1557571 : term32 = term53.
Proof. exact (TRANS (@lem1557525) (@lem1557552)). Qed.
Lemma lem1557572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557574 : term54 = term55.
Proof. exact (MK_COMB (@lem1557572) (@lem1557571)). Qed.
Lemma lem1557576 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557577 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1557576 (term6 x)). Qed.
Lemma lem1557578 (y : real) (x : real) : (term8 x y) = (term9 y x).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1557579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557581 (y : real) (x : real) : (term60 x y) = (term61 y x).
Proof. exact (MK_COMB (@lem1557579) (@lem1557578 y x)). Qed.
Lemma lem1557582 (x : real) : (term62 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1557581 y x)). Qed.
Lemma lem1557583 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557584 (x : real) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1557583) (@lem1557582 x)). Qed.
Lemma lem1557585 (x : real) : (term58 x) = (term64 x).
Proof. exact (TRANS (@lem1557577 x) (@lem1557584 x)). Qed.
Lemma lem1557586 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557587 : term65 = term66.
Proof. exact (@lem1557586 term36). Qed.
Lemma lem1557588 (x : real) : (term38 x) = (term23 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1557589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557590 (x : real) : (term67 x) = (term58 x).
Proof. exact (MK_COMB (@lem1557589) (@lem1557588 x)). Qed.
Lemma lem1557591 (x : real) : (term67 x) = (term64 x).
Proof. exact (TRANS (@lem1557590 x) (@lem1557585 x)). Qed.
Lemma lem1557592 : term68 = term69.
Proof. exact (fun_ext (fun x : real => @lem1557591 x)). Qed.
Lemma lem1557593 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557594 : term66 = term70.
Proof. exact (MK_COMB (@lem1557593) (@lem1557592)). Qed.
Lemma lem1557595 : term65 = term70.
Proof. exact (TRANS (@lem1557587) (@lem1557594)). Qed.
Lemma lem1557597 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557598 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem1557597 (term7 x)). Qed.
Lemma lem1557599 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1557600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557602 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1557600) (@lem1557599 x y)). Qed.
Lemma lem1557603 (x : real) : (term75 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1557602 x y)). Qed.
Lemma lem1557604 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557605 (x : real) : (term72 x) = (term77 x).
Proof. exact (MK_COMB (@lem1557604) (@lem1557603 x)). Qed.
Lemma lem1557606 (x : real) : (term71 x) = (term77 x).
Proof. exact (TRANS (@lem1557598 x) (@lem1557605 x)). Qed.
Lemma lem1557607 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1557608 : term78 = term79.
Proof. exact (@lem1557607 term37). Qed.
Lemma lem1557609 (x : real) : (term40 x) = (term28 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1557610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1557611 (x : real) : (term80 x) = (term71 x).
Proof. exact (MK_COMB (@lem1557610) (@lem1557609 x)). Qed.
Lemma lem1557612 (x : real) : (term80 x) = (term77 x).
Proof. exact (TRANS (@lem1557611 x) (@lem1557606 x)). Qed.
Lemma lem1557613 : term81 = term82.
Proof. exact (fun_ext (fun x : real => @lem1557612 x)). Qed.
Lemma lem1557614 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557615 : term79 = term83.
Proof. exact (MK_COMB (@lem1557614) (@lem1557613)). Qed.
Lemma lem1557616 : term78 = term83.
Proof. exact (TRANS (@lem1557608) (@lem1557615)). Qed.
Lemma lem1557617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557618 : term84 = term85.
Proof. exact (MK_COMB (@lem1557617) (@lem1557595)). Qed.
Lemma lem1557619 : term86 = term87.
Proof. exact (MK_COMB (@lem1557618) (@lem1557616)). Qed.
Lemma lem1557620 : term55 = term86.
Proof. exact (@lem17045 term47 term52). Qed.
Lemma lem1557621 : term55 = term87.
Proof. exact (TRANS (@lem1557620) (@lem1557619)). Qed.
Lemma lem1557622 : term54 = term87.
Proof. exact (TRANS (@lem1557574) (@lem1557621)). Qed.
Lemma lem1557625 (y : real) (x : real) : (term61 y x) = (term61 y x).
Proof. exact (eq_refl (term61 y x)). Qed.
Lemma lem1557626 (x : real) : (term63 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1557625 y x)). Qed.
Lemma lem1557627 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557628 (x : real) : (term64 x) = (term64 x).
Proof. exact (MK_COMB (@lem1557627) (@lem1557626 x)). Qed.
Lemma lem1557629 : term69 = term69.
Proof. exact (fun_ext (fun x : real => @lem1557628 x)). Qed.
Lemma lem1557630 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557631 : term70 = term70.
Proof. exact (MK_COMB (@lem1557630) (@lem1557629)). Qed.
Lemma lem1557634 (x : real) (y : real) : (term74 x y) = (term74 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem1557635 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1557634 x y)). Qed.
Lemma lem1557636 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557637 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem1557636) (@lem1557635 x)). Qed.
Lemma lem1557638 : term82 = term82.
Proof. exact (fun_ext (fun x : real => @lem1557637 x)). Qed.
Lemma lem1557639 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557640 : term83 = term83.
Proof. exact (MK_COMB (@lem1557639) (@lem1557638)). Qed.
Lemma lem1557641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557642 : term85 = term85.
Proof. exact (MK_COMB (@lem1557641) (@lem1557631)). Qed.
Lemma lem1557643 : term87 = term87.
Proof. exact (MK_COMB (@lem1557642) (@lem1557640)). Qed.
Lemma lem1557644 : term54 = term87.
Proof. exact (TRANS (@lem1557622) (@lem1557643)). Qed.
Lemma lem1557645 (y : real) (x : real) : (term61 y x) = (term88 y x).
Proof. exact (@lem1483533 (real_min x y) x). Qed.
Lemma lem1557651 (y : real) (x : real) : (term89 y x) = (term90 y x).
Proof. exact (@lem1483519 (real_min x y) x). Qed.
Lemma lem1557656 (x : real) (y : real) : (term90 y x) = (term91 x y).
Proof. exact (@lem1483488 (term92 x) (real_min x y)). Qed.
Lemma lem1557658 (x : real) (y : real) : (term89 y x) = (term91 x y).
Proof. exact (TRANS (@lem1557651 y x) (@lem1557656 x y)). Qed.
Lemma lem1557659 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557660 (x : real) (y : real) : (term93 y x) = (term94 x y).
Proof. exact (MK_COMB (@lem1557659) (@lem1557658 x y)). Qed.
Lemma lem1557661 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1557662 (x : real) (y : real) : (term88 y x) = (term96 x y).
Proof. exact (MK_COMB (@lem1557660 x y) (@lem1557661)). Qed.
Lemma lem1557663 (x : real) (y : real) : (term61 y x) = (term96 x y).
Proof. exact (TRANS (@lem1557645 y x) (@lem1557662 x y)). Qed.
Lemma lem1557664 (x : real) : (term63 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1557663 x y)). Qed.
Lemma lem1557665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557666 (x : real) : (term64 x) = (term98 x).
Proof. exact (MK_COMB (@lem1557665) (@lem1557664 x)). Qed.
Lemma lem1557667 : term69 = term99.
Proof. exact (fun_ext (fun x : real => @lem1557666 x)). Qed.
Lemma lem1557668 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557669 : term70 = term100.
Proof. exact (MK_COMB (@lem1557668) (@lem1557667)). Qed.
Lemma lem1557670 (x : real) (y : real) : (term74 x y) = (term101 x y).
Proof. exact (@lem1483533 (real_min x y) y). Qed.
Lemma lem1557676 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (@lem1483519 (real_min x y) y). Qed.
Lemma lem1557681 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (@lem1483488 (term92 y) (real_min x y)). Qed.
Lemma lem1557683 (x : real) (y : real) : (term102 x y) = (term104 x y).
Proof. exact (TRANS (@lem1557676 x y) (@lem1557681 x y)). Qed.
Lemma lem1557684 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557685 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1557684) (@lem1557683 x y)). Qed.
Lemma lem1557686 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1557687 (x : real) (y : real) : (term101 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1557685 x y) (@lem1557686)). Qed.
Lemma lem1557688 (x : real) (y : real) : (term74 x y) = (term107 x y).
Proof. exact (TRANS (@lem1557670 x y) (@lem1557687 x y)). Qed.
Lemma lem1557689 (x : real) : (term76 x) = (term108 x).
Proof. exact (fun_ext (fun y : real => @lem1557688 x y)). Qed.
Lemma lem1557690 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557691 (x : real) : (term77 x) = (term109 x).
Proof. exact (MK_COMB (@lem1557690) (@lem1557689 x)). Qed.
Lemma lem1557692 : term82 = term110.
Proof. exact (fun_ext (fun x : real => @lem1557691 x)). Qed.
Lemma lem1557693 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557694 : term83 = term111.
Proof. exact (MK_COMB (@lem1557693) (@lem1557692)). Qed.
Lemma lem1557695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557696 : term85 = term112.
Proof. exact (MK_COMB (@lem1557695) (@lem1557669)). Qed.
Lemma lem1557697 : term87 = term113.
Proof. exact (MK_COMB (@lem1557696) (@lem1557694)). Qed.
Lemma lem1557698 : term54 = term113.
Proof. exact (TRANS (@lem1557644) (@lem1557697)). Qed.
Lemma lem1557717 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1557718 (P : real -> Prop) (Q : real -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem1557717 real P Q). Qed.
Lemma lem1557719 : term118 = term119.
Proof. exact (@lem1557718 term99 term110). Qed.
Lemma lem1557720 (x : real) : (term120 x) = (term98 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1557721 : term121 = term99.
Proof. exact (fun_ext (fun x : real => @lem1557720 x)). Qed.
Lemma lem1557722 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557723 : term122 = term100.
Proof. exact (MK_COMB (@lem1557722) (@lem1557721)). Qed.
Lemma lem1557724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557725 : term123 = term112.
Proof. exact (MK_COMB (@lem1557724) (@lem1557723)). Qed.
Lemma lem1557726 (x : real) : (term124 x) = (term109 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1557727 : term125 = term110.
Proof. exact (fun_ext (fun x : real => @lem1557726 x)). Qed.
Lemma lem1557728 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557729 : term126 = term111.
Proof. exact (MK_COMB (@lem1557728) (@lem1557727)). Qed.
Lemma lem1557730 : term118 = term113.
Proof. exact (MK_COMB (@lem1557725) (@lem1557729)). Qed.
Lemma lem1557731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557732 : term127 = term128.
Proof. exact (MK_COMB (@lem1557731) (@lem1557730)). Qed.
Lemma lem1557733 (x : real) : (term120 x) = (term98 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1557734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557735 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem1557734) (@lem1557733 x)). Qed.
Lemma lem1557736 (x : real) : (term124 x) = (term109 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem1557737 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem1557735 x) (@lem1557736 x)). Qed.
Lemma lem1557738 : term133 = term134.
Proof. exact (fun_ext (fun x : real => @lem1557737 x)). Qed.
Lemma lem1557739 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557740 : term119 = term135.
Proof. exact (MK_COMB (@lem1557739) (@lem1557738)). Qed.
Lemma lem1557741 : (term118 = term119) = (term113 = term135).
Proof. exact (MK_COMB (@lem1557732) (@lem1557740)). Qed.
Lemma lem1557742 : term113 = term135.
Proof. exact (EQ_MP (@lem1557741) (@lem1557719)). Qed.
Lemma lem1557744 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1557745 (P : real -> Prop) (Q : real -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem1557744 real P Q). Qed.
Lemma lem1557746 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1557745 (term97 x) (term108 x)). Qed.
Lemma lem1557747 (x : real) (y : real) : (term138 x y) = (term96 x y).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1557748 (x : real) : (term139 x) = (term97 x).
Proof. exact (fun_ext (fun y : real => @lem1557747 x y)). Qed.
Lemma lem1557749 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557750 (x : real) : (term140 x) = (term98 x).
Proof. exact (MK_COMB (@lem1557749) (@lem1557748 x)). Qed.
Lemma lem1557751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557752 (x : real) : (term141 x) = (term130 x).
Proof. exact (MK_COMB (@lem1557751) (@lem1557750 x)). Qed.
Lemma lem1557753 (x : real) (y : real) : (term142 x y) = (term107 x y).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem1557754 (x : real) : (term143 x) = (term108 x).
Proof. exact (fun_ext (fun y : real => @lem1557753 x y)). Qed.
Lemma lem1557755 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557756 (x : real) : (term144 x) = (term109 x).
Proof. exact (MK_COMB (@lem1557755) (@lem1557754 x)). Qed.
Lemma lem1557757 (x : real) : (term136 x) = (term132 x).
Proof. exact (MK_COMB (@lem1557752 x) (@lem1557756 x)). Qed.
Lemma lem1557758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1557759 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1557758) (@lem1557757 x)). Qed.
Lemma lem1557760 (x : real) (y : real) : (term138 x y) = (term96 x y).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1557761 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557762 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1557761) (@lem1557760 x y)). Qed.
Lemma lem1557763 (x : real) (y : real) : (term142 x y) = (term107 x y).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem1557764 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1557762 x y) (@lem1557763 x y)). Qed.
Lemma lem1557765 (x : real) : (term151 x) = (term152 x).
Proof. exact (fun_ext (fun y : real => @lem1557764 x y)). Qed.
Lemma lem1557766 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557767 (x : real) : (term137 x) = (term153 x).
Proof. exact (MK_COMB (@lem1557766) (@lem1557765 x)). Qed.
Lemma lem1557768 (x : real) : ((term136 x) = (term137 x)) = ((term132 x) = (term153 x)).
Proof. exact (MK_COMB (@lem1557759 x) (@lem1557767 x)). Qed.
Lemma lem1557769 (x : real) : (term132 x) = (term153 x).
Proof. exact (EQ_MP (@lem1557768 x) (@lem1557746 x)). Qed.
Lemma lem1557770 : term134 = term154.
Proof. exact (fun_ext (fun x : real => @lem1557769 x)). Qed.
Lemma lem1557771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557772 : term135 = term155.
Proof. exact (MK_COMB (@lem1557771) (@lem1557770)). Qed.
Lemma lem1557774 : term113 = term155.
Proof. exact (TRANS (@lem1557742) (@lem1557772)). Qed.
Lemma lem1557777 : term54 = term155.
Proof. exact (TRANS (@lem1557698) (@lem1557774)). Qed.
Lemma lem1557782 (x : real) (y : real) : (term150 x y) = (term150 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1557783 (x : real) : (term152 x) = (term152 x).
Proof. exact (fun_ext (fun y : real => @lem1557782 x y)). Qed.
Lemma lem1557784 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557785 (x : real) : (term153 x) = (term153 x).
Proof. exact (MK_COMB (@lem1557784) (@lem1557783 x)). Qed.
Lemma lem1557786 : term154 = term154.
Proof. exact (fun_ext (fun x : real => @lem1557785 x)). Qed.
Lemma lem1557787 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1557788 : term155 = term155.
Proof. exact (MK_COMB (@lem1557787) (@lem1557786)). Qed.
Lemma lem1557789 : term54 = term155.
Proof. exact (TRANS (@lem1557777) (@lem1557788)). Qed.
Lemma lem1557791 (x : real) (a : real) (y : real) (r : real) : (term156 a x y r) = (term157 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1557792 (x : real) (y : real) : (term96 x y) = (term158 x y).
Proof. exact (@lem1557791 x (term92 x) y term95). Qed.
Lemma lem1557809 (x : real) (y : real) : (term159 x y) = (term159 x y).
Proof. exact (eq_refl (term159 x y)). Qed.
Lemma lem1557821 (x : real) : (term160 x) = (term161 x).
Proof. exact (@lem1483440 term162 x). Qed.
Lemma lem1557823 (m : nat) : (term163 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1557824 : term164 = term95.
Proof. exact (@lem1557823 term165). Qed.
Lemma lem1557825 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1557826 : term166 = term167.
Proof. exact (MK_COMB (@lem1557825) (@lem1557824)). Qed.
Lemma lem1557827 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1557828 (x : real) : (term161 x) = (term168 x).
Proof. exact (MK_COMB (@lem1557826) (@lem1557827 x)). Qed.
Lemma lem1557829 (x : real) : (term160 x) = (term168 x).
Proof. exact (TRANS (@lem1557821 x) (@lem1557828 x)). Qed.
Lemma lem1557830 (x : real) : (term168 x) = term95.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1557832 (x : real) : (term160 x) = term95.
Proof. exact (TRANS (@lem1557829 x) (@lem1557830 x)). Qed.
Lemma lem1557833 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557834 (x : real) : (term169 x) = term170.
Proof. exact (MK_COMB (@lem1557833) (@lem1557832 x)). Qed.
Lemma lem1557835 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1557836 (x : real) : (term171 x) = term172.
Proof. exact (MK_COMB (@lem1557834 x) (@lem1557835)). Qed.
Lemma lem1557837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557838 (x : real) : (term173 x) = term174.
Proof. exact (MK_COMB (@lem1557837) (@lem1557836 x)). Qed.
Lemma lem1557839 (x : real) (y : real) : (term158 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1557838 x) (@lem1557809 x y)). Qed.
Lemma lem1557842 (x : real) (y : real) : (term96 x y) = (term175 x y).
Proof. exact (TRANS (@lem1557792 x y) (@lem1557839 x y)). Qed.
Lemma lem1557844 (x : real) (a : real) (y : real) (r : real) : (term156 a x y r) = (term157 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1557845 (x : real) (y : real) : (term107 x y) = (term176 x y).
Proof. exact (@lem1557844 x (term92 y) y term95). Qed.
Lemma lem1557857 (y : real) : (term160 y) = (term161 y).
Proof. exact (@lem1483440 term162 y). Qed.
Lemma lem1557859 (m : nat) : (term163 m) = term95.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1557860 : term164 = term95.
Proof. exact (@lem1557859 term165). Qed.
Lemma lem1557861 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1557862 : term166 = term167.
Proof. exact (MK_COMB (@lem1557861) (@lem1557860)). Qed.
Lemma lem1557863 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1557864 (y : real) : (term161 y) = (term168 y).
Proof. exact (MK_COMB (@lem1557862) (@lem1557863 y)). Qed.
Lemma lem1557865 (y : real) : (term160 y) = (term168 y).
Proof. exact (TRANS (@lem1557857 y) (@lem1557864 y)). Qed.
Lemma lem1557866 (y : real) : (term168 y) = term95.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1557868 (y : real) : (term160 y) = term95.
Proof. exact (TRANS (@lem1557865 y) (@lem1557866 y)). Qed.
Lemma lem1557869 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557870 (y : real) : (term169 y) = term170.
Proof. exact (MK_COMB (@lem1557869) (@lem1557868 y)). Qed.
Lemma lem1557871 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1557872 (y : real) : (term171 y) = term172.
Proof. exact (MK_COMB (@lem1557870 y) (@lem1557871)). Qed.
Lemma lem1557885 (x : real) (y : real) : (term177 y x) = (term178 x y).
Proof. exact (@lem1483488 x (term92 y)). Qed.
Lemma lem1557886 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1557887 (x : real) (y : real) : (term179 y x) = (term180 x y).
Proof. exact (MK_COMB (@lem1557886) (@lem1557885 x y)). Qed.
Lemma lem1557888 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem1557889 (x : real) (y : real) : (term159 y x) = (term181 x y).
Proof. exact (MK_COMB (@lem1557887 x y) (@lem1557888)). Qed.
Lemma lem1557890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1557891 (x : real) (y : real) : (term182 y x) = (term183 x y).
Proof. exact (MK_COMB (@lem1557890) (@lem1557889 x y)). Qed.
Lemma lem1557892 (x : real) (y : real) : (term176 x y) = (term184 x y).
Proof. exact (MK_COMB (@lem1557891 x y) (@lem1557872 y)). Qed.
Lemma lem1557895 (x : real) (y : real) : (term107 x y) = (term184 x y).
Proof. exact (TRANS (@lem1557845 x y) (@lem1557892 x y)). Qed.
Lemma lem1557896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1557897 (x : real) (y : real) : (term148 x y) = (term185 x y).
Proof. exact (MK_COMB (@lem1557896) (@lem1557842 x y)). Qed.
Lemma lem1557898 (x : real) (y : real) : (term150 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1557897 x y) (@lem1557895 x y)). Qed.
Lemma lem1557899 (x : real) (y : real) (h1 : term186 x y) : term186 x y.
Proof. exact (h1). Qed.
Lemma lem1557900 (x : real) (y : real) (h1 : term175 x y) : term175 x y.
Proof. exact (h1). Qed.
Lemma lem1557902 (x : real) (y : real) (h1 : term175 x y) : term172.
Proof. exact (proj1 (@lem1557900 x y h1)). Qed.
Lemma lem1557904 (n : nat) (m : nat) : (term187 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1557905 : term172 = term188.
Proof. exact (@lem1557904 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1557906 : term188 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1557907 : term172 = False.
Proof. exact (TRANS (@lem1557905) (@lem1557906)). Qed.
Lemma lem1557908 (x : real) (y : real) (h1 : term175 x y) : False.
Proof. exact (EQ_MP (@lem1557907) (@lem1557902 x y h1)). Qed.
Lemma lem1557909 (x : real) (y : real) (h1 : term184 x y) : term184 x y.
Proof. exact (h1). Qed.
Lemma lem1557910 (x : real) (y : real) (h1 : term184 x y) : term172.
Proof. exact (proj2 (@lem1557909 x y h1)). Qed.
Lemma lem1557913 (n : nat) (m : nat) : (term187 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1557914 : term172 = term188.
Proof. exact (@lem1557913 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1557915 : term188 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1557916 : term172 = False.
Proof. exact (TRANS (@lem1557914) (@lem1557915)). Qed.
Lemma lem1557917 (x : real) (y : real) (h1 : term184 x y) : False.
Proof. exact (EQ_MP (@lem1557916) (@lem1557910 x y h1)). Qed.
Lemma lem1557918 (x : real) (y : real) (h1 : term186 x y) : False.
Proof. exact (or_elim (@lem1557899 x y h1) (fun h0 : term175 x y => @lem1557908 x y h0) (fun h0 : term184 x y => @lem1557917 x y h0)). Qed.
Lemma lem1557919 (x : real) (y : real) (h1 : term150 x y) : term150 x y.
Proof. exact (h1). Qed.
Lemma lem1557920 (x : real) (y : real) (h1 : term150 x y) : term186 x y.
Proof. exact (EQ_MP (@lem1557898 x y) (@lem1557919 x y h1)). Qed.
Lemma lem1557921 (x : real) (y : real) (h1 : term150 x y) : (term186 x y) = False.
Proof. exact (prop_ext (fun h2 : term186 x y => @lem1557918 x y h2) (fun h2 : False => @lem1557920 x y h1)). Qed.
Lemma lem1557922 (x : real) (y : real) (h1 : term150 x y) : False.
Proof. exact (EQ_MP (@lem1557921 x y h1) (@lem1557920 x y h1)). Qed.
Lemma lem1557923 (x : real) (h1 : term153 x) : term153 x.
Proof. exact (h1). Qed.
Lemma lem1557924 (x : real) (h1 : term153 x) : False.
Proof. exact (ex_elim (@lem1557923 x h1) (fun y : real => fun h0 : term152 x y => @lem1557922 x y h0)). Qed.
Lemma lem1557925 (h1 : term155) : term155.
Proof. exact (h1). Qed.
Lemma lem1557926 (h1 : term155) : False.
Proof. exact (ex_elim (@lem1557925 h1) (fun x : real => fun h0 : term154 x => @lem1557924 x h0)). Qed.
Lemma lem1557927 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1557928 (h1 : term54) : term155.
Proof. exact (EQ_MP (@lem1557789) (@lem1557927 h1)). Qed.
Lemma lem1557929 (h1 : term54) : term155 = False.
Proof. exact (prop_ext (fun h2 : term155 => @lem1557926 h2) (fun h2 : False => @lem1557928 h1)). Qed.
Lemma lem1557930 (h1 : term54) : False.
Proof. exact (EQ_MP (@lem1557929 h1) (@lem1557928 h1)). Qed.
Lemma lem1557931 : term189.
Proof. exact (fun h0 : term54 => @lem1557930 h0). Qed.
Lemma lem1557932 : term190.
Proof. exact (@lem1386578 term32). Qed.
Lemma lem1557933 : term32.
Proof. exact (@lem1557932 (@lem1557931)). Qed.
