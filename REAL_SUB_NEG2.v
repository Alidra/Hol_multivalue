Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_NEG2_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
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
Lemma lem1519540 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519541 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1519540 (term4 x)). Qed.
Lemma lem1519542 (y : real) (x : real) : (term5 x y) = ((term6 x y) = (real_sub y x)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1519543 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519545 (y : real) (x : real) : (term7 x y) = (term8 y x).
Proof. exact (MK_COMB (@lem1519543) (@lem1519542 y x)). Qed.
Lemma lem1519546 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1519545 y x)). Qed.
Lemma lem1519547 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519548 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1519547) (@lem1519546 x)). Qed.
Lemma lem1519549 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1519541 x) (@lem1519548 x)). Qed.
Lemma lem1519550 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1519551 : term12 = term13.
Proof. exact (@lem1519550 term14). Qed.
Lemma lem1519552 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1519553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1519554 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1519553) (@lem1519552 x)). Qed.
Lemma lem1519555 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1519554 x) (@lem1519549 x)). Qed.
Lemma lem1519556 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1519555 x)). Qed.
Lemma lem1519557 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519558 : term13 = term20.
Proof. exact (MK_COMB (@lem1519557) (@lem1519556)). Qed.
Lemma lem1519560 : term12 = term20.
Proof. exact (TRANS (@lem1519551) (@lem1519558)). Qed.
Lemma lem1519563 (y : real) (x : real) : (term8 y x) = (term8 y x).
Proof. exact (eq_refl (term8 y x)). Qed.
Lemma lem1519564 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1519563 y x)). Qed.
Lemma lem1519565 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519566 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1519565) (@lem1519564 x)). Qed.
Lemma lem1519567 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1519566 x)). Qed.
Lemma lem1519568 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519569 : term20 = term20.
Proof. exact (MK_COMB (@lem1519568) (@lem1519567)). Qed.
Lemma lem1519570 : term12 = term20.
Proof. exact (TRANS (@lem1519560) (@lem1519569)). Qed.
Lemma lem1519571 (y : real) (x : real) : (term8 y x) = (term21 y x).
Proof. exact (@lem1483554 (term6 x y) (real_sub y x)). Qed.
Lemma lem1519577 (y : real) (x : real) : (real_sub y x) = (term22 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1519582 (x : real) (y : real) : (term22 y x) = (term23 x y).
Proof. exact (@lem1483488 (term24 x) y). Qed.
Lemma lem1519584 (x : real) (y : real) : (real_sub y x) = (term23 x y).
Proof. exact (TRANS (@lem1519577 y x) (@lem1519582 x y)). Qed.
Lemma lem1519591 (y : real) : (real_neg y) = (term24 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1519598 (x : real) : (real_neg x) = (term24 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1519599 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1519600 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1519599) (@lem1519598 x)). Qed.
Lemma lem1519601 (x : real) (y : real) : (term6 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1519600 x) (@lem1519591 y)). Qed.
Lemma lem1519602 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (@lem1483519 (term24 x) (term24 y)). Qed.
Lemma lem1519603 (y : real) : (term29 y) = (term30 y).
Proof. exact (@lem1483476 term31 term31 y). Qed.
Lemma lem1519605 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1519606 : term34 = term35.
Proof. exact (@lem1519605 term36 term36). Qed.
Lemma lem1519607 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1519608 : term38 = term36.
Proof. exact (EQ_MP (@lem1519607) (@lem940073)). Qed.
Lemma lem1519609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1519610 : term35 = term39.
Proof. exact (MK_COMB (@lem1519609) (@lem1519608)). Qed.
Lemma lem1519611 : term34 = term39.
Proof. exact (TRANS (@lem1519606) (@lem1519610)). Qed.
Lemma lem1519612 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519613 : term40 = term41.
Proof. exact (MK_COMB (@lem1519612) (@lem1519611)). Qed.
Lemma lem1519614 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519615 (y : real) : (term30 y) = (term42 y).
Proof. exact (MK_COMB (@lem1519613) (@lem1519614 y)). Qed.
Lemma lem1519616 (y : real) : (term29 y) = (term42 y).
Proof. exact (TRANS (@lem1519603 y) (@lem1519615 y)). Qed.
Lemma lem1519617 (y : real) : (term42 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1519618 (y : real) : (term29 y) = y.
Proof. exact (TRANS (@lem1519616 y) (@lem1519617 y)). Qed.
Lemma lem1519619 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1519622 (x : real) (y : real) : (term28 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1519619 x) (@lem1519618 y)). Qed.
Lemma lem1519623 (x : real) (y : real) : (term27 x y) = (term23 x y).
Proof. exact (TRANS (@lem1519602 x y) (@lem1519622 x y)). Qed.
Lemma lem1519624 (x : real) (y : real) : (term6 x y) = (term23 x y).
Proof. exact (TRANS (@lem1519601 x y) (@lem1519623 x y)). Qed.
Lemma lem1519625 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1519626 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1519625) (@lem1519624 x y)). Qed.
Lemma lem1519627 (x : real) (y : real) : (term46 y x) = (term47 x y).
Proof. exact (MK_COMB (@lem1519626 x y) (@lem1519584 x y)). Qed.
Lemma lem1519628 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (@lem1483519 (term23 x y) (term23 x y)). Qed.
Lemma lem1519629 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (@lem1483508 (term24 x) term31 y). Qed.
Lemma lem1519630 (y : real) : (term24 y) = (term24 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem1519631 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483476 term31 term31 x). Qed.
Lemma lem1519633 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1519634 : term34 = term35.
Proof. exact (@lem1519633 term36 term36). Qed.
Lemma lem1519635 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1519636 : term38 = term36.
Proof. exact (EQ_MP (@lem1519635) (@lem940073)). Qed.
Lemma lem1519637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1519638 : term35 = term39.
Proof. exact (MK_COMB (@lem1519637) (@lem1519636)). Qed.
Lemma lem1519639 : term34 = term39.
Proof. exact (TRANS (@lem1519634) (@lem1519638)). Qed.
Lemma lem1519640 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519641 : term40 = term41.
Proof. exact (MK_COMB (@lem1519640) (@lem1519639)). Qed.
Lemma lem1519642 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1519643 (x : real) : (term30 x) = (term42 x).
Proof. exact (MK_COMB (@lem1519641) (@lem1519642 x)). Qed.
Lemma lem1519644 (x : real) : (term29 x) = (term42 x).
Proof. exact (TRANS (@lem1519631 x) (@lem1519643 x)). Qed.
Lemma lem1519645 (x : real) : (term42 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1519646 (x : real) : (term29 x) = x.
Proof. exact (TRANS (@lem1519644 x) (@lem1519645 x)). Qed.
Lemma lem1519647 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519648 (x : real) : (term51 x) = (real_add x).
Proof. exact (MK_COMB (@lem1519647) (@lem1519646 x)). Qed.
Lemma lem1519649 (x : real) (y : real) : (term50 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1519648 x) (@lem1519630 y)). Qed.
Lemma lem1519650 (x : real) (y : real) : (term49 x y) = (term22 x y).
Proof. exact (TRANS (@lem1519629 x y) (@lem1519649 x y)). Qed.
Lemma lem1519651 (x : real) (y : real) : (term52 x y) = (term52 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1519652 (x : real) (y : real) : (term48 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1519651 x y) (@lem1519650 x y)). Qed.
Lemma lem1519653 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem1483480 (term24 x) x y (term24 y)). Qed.
Lemma lem1519654 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1483440 term31 x). Qed.
Lemma lem1519656 (m : nat) : (term57 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519657 : term59 = term58.
Proof. exact (@lem1519656 term36). Qed.
Lemma lem1519658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519659 : term60 = term61.
Proof. exact (MK_COMB (@lem1519658) (@lem1519657)). Qed.
Lemma lem1519660 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1519661 (x : real) : (term56 x) = (term62 x).
Proof. exact (MK_COMB (@lem1519659) (@lem1519660 x)). Qed.
Lemma lem1519662 (x : real) : (term55 x) = (term62 x).
Proof. exact (TRANS (@lem1519654 x) (@lem1519661 x)). Qed.
Lemma lem1519663 (x : real) : (term62 x) = term58.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1519664 (x : real) : (term55 x) = term58.
Proof. exact (TRANS (@lem1519662 x) (@lem1519663 x)). Qed.
Lemma lem1519665 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1519666 (x : real) : (term63 x) = term64.
Proof. exact (MK_COMB (@lem1519665) (@lem1519664 x)). Qed.
Lemma lem1519667 (y : real) : (term65 y) = (term56 y).
Proof. exact (@lem1483442 term31 y). Qed.
Lemma lem1519669 (m : nat) : (term57 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1519670 : term59 = term58.
Proof. exact (@lem1519669 term36). Qed.
Lemma lem1519671 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1519672 : term60 = term61.
Proof. exact (MK_COMB (@lem1519671) (@lem1519670)). Qed.
Lemma lem1519673 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1519674 (y : real) : (term56 y) = (term62 y).
Proof. exact (MK_COMB (@lem1519672) (@lem1519673 y)). Qed.
Lemma lem1519675 (y : real) : (term65 y) = (term62 y).
Proof. exact (TRANS (@lem1519667 y) (@lem1519674 y)). Qed.
Lemma lem1519676 (y : real) : (term62 y) = term58.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1519677 (y : real) : (term65 y) = term58.
Proof. exact (TRANS (@lem1519675 y) (@lem1519676 y)). Qed.
Lemma lem1519678 (x : real) (y : real) : (term54 x y) = term66.
Proof. exact (MK_COMB (@lem1519666 x) (@lem1519677 y)). Qed.
Lemma lem1519679 (x : real) (y : real) : (term53 x y) = term66.
Proof. exact (TRANS (@lem1519653 x y) (@lem1519678 x y)). Qed.
Lemma lem1519680 : term66 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1519681 (x : real) (y : real) : (term53 x y) = term58.
Proof. exact (TRANS (@lem1519679 x y) (@lem1519680)). Qed.
Lemma lem1519682 (x : real) (y : real) : (term48 x y) = term58.
Proof. exact (TRANS (@lem1519652 x y) (@lem1519681 x y)). Qed.
Lemma lem1519683 (x : real) (y : real) : (term47 x y) = term58.
Proof. exact (TRANS (@lem1519628 x y) (@lem1519682 x y)). Qed.
Lemma lem1519684 (y : real) (x : real) : (term46 y x) = term58.
Proof. exact (TRANS (@lem1519627 x y) (@lem1519683 x y)). Qed.
Lemma lem1519685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1519686 (y : real) (x : real) : (term67 y x) = term68.
Proof. exact (MK_COMB (@lem1519685) (@lem1519684 y x)). Qed.
Lemma lem1519687 : term68 = term69.
Proof. exact (@lem1483512 term58). Qed.
Lemma lem1519689 (x : nat) : (term70 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1519690 : term69 = term58.
Proof. exact (@lem1519689 term36). Qed.
Lemma lem1519691 : term68 = term58.
Proof. exact (TRANS (@lem1519687) (@lem1519690)). Qed.
Lemma lem1519692 (y : real) (x : real) : (term71 y x) = (term71 y x).
Proof. exact (eq_refl (term71 y x)). Qed.
Lemma lem1519693 (y : real) (x : real) : ((term67 y x) = term68) = ((term67 y x) = term58).
Proof. exact (MK_COMB (@lem1519692 y x) (@lem1519691)). Qed.
Lemma lem1519694 (y : real) (x : real) : (term67 y x) = term58.
Proof. exact (EQ_MP (@lem1519693 y x) (@lem1519686 y x)). Qed.
Lemma lem1519695 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1519696 (y : real) (x : real) : (term72 y x) = term73.
Proof. exact (MK_COMB (@lem1519695) (@lem1519694 y x)). Qed.
Lemma lem1519697 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1519698 (y : real) (x : real) : (term74 y x) = term75.
Proof. exact (MK_COMB (@lem1519696 y x) (@lem1519697)). Qed.
Lemma lem1519699 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1519700 (y : real) (x : real) : (term76 y x) = term73.
Proof. exact (MK_COMB (@lem1519699) (@lem1519684 y x)). Qed.
Lemma lem1519701 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1519702 (y : real) (x : real) : (term77 y x) = term75.
Proof. exact (MK_COMB (@lem1519700 y x) (@lem1519701)). Qed.
Lemma lem1519703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519704 (y : real) (x : real) : (term78 y x) = term79.
Proof. exact (MK_COMB (@lem1519703) (@lem1519702 y x)). Qed.
Lemma lem1519705 (y : real) (x : real) : (term21 y x) = term80.
Proof. exact (MK_COMB (@lem1519704 y x) (@lem1519698 y x)). Qed.
Lemma lem1519706 (y : real) (x : real) : (term8 y x) = term80.
Proof. exact (TRANS (@lem1519571 y x) (@lem1519705 y x)). Qed.
Lemma lem1519707 (x : real) : (term10 x) = term81.
Proof. exact (fun_ext (fun y : real => @lem1519706 y x)). Qed.
Lemma lem1519708 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519709 (x : real) : (term11 x) = term82.
Proof. exact (MK_COMB (@lem1519708) (@lem1519707 x)). Qed.
Lemma lem1519710 : term19 = term83.
Proof. exact (fun_ext (fun x : real => @lem1519709 x)). Qed.
Lemma lem1519711 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519712 : term20 = term84.
Proof. exact (MK_COMB (@lem1519711) (@lem1519710)). Qed.
Lemma lem1519713 : term12 = term84.
Proof. exact (TRANS (@lem1519570) (@lem1519712)). Qed.
Lemma lem1519715 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519716 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1519715 real t). Qed.
Lemma lem1519717 : term84 = term82.
Proof. exact (@lem1519716 term82). Qed.
Lemma lem1519719 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1519720 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1519719 real P Q). Qed.
Lemma lem1519721 : term91 = term92.
Proof. exact (@lem1519720 term93 term93). Qed.
Lemma lem1519722 (y : real) : (term94 y) = term75.
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1519723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519724 (y : real) : (term95 y) = term79.
Proof. exact (MK_COMB (@lem1519723) (@lem1519722 y)). Qed.
Lemma lem1519725 (y : real) : (term94 y) = term75.
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1519726 (y : real) : (term96 y) = term80.
Proof. exact (MK_COMB (@lem1519724 y) (@lem1519725 y)). Qed.
Lemma lem1519727 : term97 = term81.
Proof. exact (fun_ext (fun y : real => @lem1519726 y)). Qed.
Lemma lem1519728 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519729 : term91 = term82.
Proof. exact (MK_COMB (@lem1519728) (@lem1519727)). Qed.
Lemma lem1519730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1519731 : term98 = term99.
Proof. exact (MK_COMB (@lem1519730) (@lem1519729)). Qed.
Lemma lem1519732 (y : real) : (term94 y) = term75.
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1519733 : term100 = term93.
Proof. exact (fun_ext (fun y : real => @lem1519732 y)). Qed.
Lemma lem1519734 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519735 : term101 = term102.
Proof. exact (MK_COMB (@lem1519734) (@lem1519733)). Qed.
Lemma lem1519736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519737 : term103 = term104.
Proof. exact (MK_COMB (@lem1519736) (@lem1519735)). Qed.
Lemma lem1519738 (y : real) : (term94 y) = term75.
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1519739 : term100 = term93.
Proof. exact (fun_ext (fun y : real => @lem1519738 y)). Qed.
Lemma lem1519740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1519741 : term101 = term102.
Proof. exact (MK_COMB (@lem1519740) (@lem1519739)). Qed.
Lemma lem1519742 : term92 = term105.
Proof. exact (MK_COMB (@lem1519737) (@lem1519741)). Qed.
Lemma lem1519743 : (term91 = term92) = (term82 = term105).
Proof. exact (MK_COMB (@lem1519731) (@lem1519742)). Qed.
Lemma lem1519744 : term82 = term105.
Proof. exact (EQ_MP (@lem1519743) (@lem1519721)). Qed.
Lemma lem1519745 : term84 = term105.
Proof. exact (TRANS (@lem1519717) (@lem1519744)). Qed.
Lemma lem1519747 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519748 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1519747 real t). Qed.
Lemma lem1519749 : term102 = term75.
Proof. exact (@lem1519748 term75). Qed.
Lemma lem1519750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1519751 : term104 = term79.
Proof. exact (MK_COMB (@lem1519750) (@lem1519749)). Qed.
Lemma lem1519753 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1519754 (t : Prop) : (term86 t) = t.
Proof. exact (@lem1519753 real t). Qed.
Lemma lem1519755 : term102 = term75.
Proof. exact (@lem1519754 term75). Qed.
Lemma lem1519756 : term105 = term80.
Proof. exact (MK_COMB (@lem1519751) (@lem1519755)). Qed.
Lemma lem1519759 : term84 = term80.
Proof. exact (TRANS (@lem1519745) (@lem1519756)). Qed.
Lemma lem1519768 : term12 = term80.
Proof. exact (TRANS (@lem1519713) (@lem1519759)). Qed.
Lemma lem1519778 (h1 : term80) : term80.
Proof. exact (h1). Qed.
Lemma lem1519779 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem1519781 (n : nat) (m : nat) : (term106 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1519782 : term75 = term107.
Proof. exact (@lem1519781 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1519783 : term107 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1519784 : term75 = False.
Proof. exact (TRANS (@lem1519782) (@lem1519783)). Qed.
Lemma lem1519785 (h1 : term75) : False.
Proof. exact (EQ_MP (@lem1519784) (@lem1519779 h1)). Qed.
Lemma lem1519786 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem1519788 (n : nat) (m : nat) : (term106 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1519789 : term75 = term107.
Proof. exact (@lem1519788 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1519790 : term107 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1519791 : term75 = False.
Proof. exact (TRANS (@lem1519789) (@lem1519790)). Qed.
Lemma lem1519792 (h1 : term75) : False.
Proof. exact (EQ_MP (@lem1519791) (@lem1519786 h1)). Qed.
Lemma lem1519793 (h1 : term80) : False.
Proof. exact (or_elim (@lem1519778 h1) (fun h0 : term75 => @lem1519785 h0) (fun h0 : term75 => @lem1519792 h0)). Qed.
Lemma lem1519795 (h1 : term80) : term80.
Proof. exact (h1). Qed.
Lemma lem1519796 (h1 : term80) : term80 = False.
Proof. exact (prop_ext (fun h2 : term80 => @lem1519793 h1) (fun h2 : False => @lem1519795 h1)). Qed.
Lemma lem1519797 (h1 : term80) : False.
Proof. exact (EQ_MP (@lem1519796 h1) (@lem1519795 h1)). Qed.
Lemma lem1519798 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1519799 (h1 : term12) : term80.
Proof. exact (EQ_MP (@lem1519768) (@lem1519798 h1)). Qed.
Lemma lem1519800 (h1 : term12) : term80 = False.
Proof. exact (prop_ext (fun h2 : term80 => @lem1519797 h2) (fun h2 : False => @lem1519799 h1)). Qed.
Lemma lem1519801 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1519800 h1) (@lem1519799 h1)). Qed.
Lemma lem1519802 : term108.
Proof. exact (fun h0 : term12 => @lem1519801 h0). Qed.
Lemma lem1519803 : term109.
Proof. exact (@lem1386578 term110). Qed.
Lemma lem1519804 : term110.
Proof. exact (@lem1519803 (@lem1519802)). Qed.
