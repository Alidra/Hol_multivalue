Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_NEG_term_abbrevs.
Require Import COND_SWAP_spec.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_NEG_NEG_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_NEG_0_spec.
Require Import REAL_ZPOW_0_spec.
Require Import real_zpow_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm2306330_spec.
Require Import thm2841542_spec.
Require Import thm2841544_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841588_spec.
Require Import thm2841589_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2954598_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem3169501 (n : int) : (term0 n) = (term1 n).
Proof. exact (@lem2954598 (term1 n)). Qed.
Lemma lem3169515 (n : int) : (term2 n) = (term3 n).
Proof. exact (@lem16933 (term3 n)). Qed.
Lemma lem3169518 (n : int) : (term4 n) = (term4 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem3169520 (n : int) : (term5 n) = (term5 n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem3169521 (n : int) : (term6 n) = (term7 n).
Proof. exact (MK_COMB (@lem3169520 n) (@lem3169515 n)). Qed.
Lemma lem3169522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3169523 (n : int) : (term8 n) = (term9 n).
Proof. exact (MK_COMB (@lem3169522) (@lem3169521 n)). Qed.
Lemma lem3169524 (n : int) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem3169523 n) (@lem3169518 n)). Qed.
Lemma lem3169525 (n : int) : (term12 n) = (term10 n).
Proof. exact (@lem17646 (term13 n) (term14 n)). Qed.
Lemma lem3169526 (n : int) : (term12 n) = (term11 n).
Proof. exact (TRANS (@lem3169525 n) (@lem3169524 n)). Qed.
Lemma lem3169528 (n : int) : (term15 n) = (term15 n).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem3169529 (n : int) : (term16 n) = (term17 n).
Proof. exact (MK_COMB (@lem3169528 n) (@lem3169526 n)). Qed.
Lemma lem3169530 (n : int) : (term18 n) = (term16 n).
Proof. exact (@lem17362 (term19 n) ((term13 n) = (term14 n))). Qed.
Lemma lem3169570 (n : int) : (term18 n) = (term17 n).
Proof. exact (TRANS (@lem3169530 n) (@lem3169529 n)). Qed.
Lemma lem3169572 (y : int) (x : int) : (term20 x y) = (term21 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem3169573 (n : int) : (term19 n) = (term22 n).
Proof. exact (@lem3169572 term23 n). Qed.
Lemma lem3169575 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3169576 (n : int) : (term25 n) = (term26 n).
Proof. exact (@lem3169575 (term27 n) term23). Qed.
Lemma lem3169578 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3169579 (n : int) : (term30 n) = (term31 n).
Proof. exact (@lem3169578 n term32). Qed.
Lemma lem3169581 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169582 : term34 = term35.
Proof. exact (@lem3169581 term36). Qed.
Lemma lem3169583 (n : int) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3169584 (n : int) : (term31 n) = (term38 n).
Proof. exact (MK_COMB (@lem3169583 n) (@lem3169582)). Qed.
Lemma lem3169585 (n : int) : (term30 n) = (term38 n).
Proof. exact (TRANS (@lem3169579 n) (@lem3169584 n)). Qed.
Lemma lem3169586 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3169587 (n : int) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem3169586) (@lem3169585 n)). Qed.
Lemma lem3169589 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169590 : term41 = term42.
Proof. exact (@lem3169589 (NUMERAL 0)). Qed.
Lemma lem3169591 (n : int) : (term26 n) = (term43 n).
Proof. exact (MK_COMB (@lem3169587 n) (@lem3169590)). Qed.
Lemma lem3169592 (n : int) : (term25 n) = (term43 n).
Proof. exact (TRANS (@lem3169576 n) (@lem3169591 n)). Qed.
Lemma lem3169593 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3169594 (n : int) : (term44 n) = (term45 n).
Proof. exact (MK_COMB (@lem3169593) (@lem3169592 n)). Qed.
Lemma lem3169596 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3169597 (n : int) : (term46 n) = (term47 n).
Proof. exact (@lem3169596 term48 n). Qed.
Lemma lem3169599 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3169600 : term49 = term50.
Proof. exact (@lem3169599 term23 term32). Qed.
Lemma lem3169602 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169603 : term41 = term42.
Proof. exact (@lem3169602 (NUMERAL 0)). Qed.
Lemma lem3169604 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3169605 : term51 = term52.
Proof. exact (MK_COMB (@lem3169604) (@lem3169603)). Qed.
Lemma lem3169607 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169608 : term34 = term35.
Proof. exact (@lem3169607 term36). Qed.
Lemma lem3169609 : term50 = term53.
Proof. exact (MK_COMB (@lem3169605) (@lem3169608)). Qed.
Lemma lem3169610 : term49 = term53.
Proof. exact (TRANS (@lem3169600) (@lem3169609)). Qed.
Lemma lem3169611 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3169612 : term54 = term55.
Proof. exact (MK_COMB (@lem3169611) (@lem3169610)). Qed.
Lemma lem3169613 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3169614 (n : int) : (term47 n) = (term56 n).
Proof. exact (MK_COMB (@lem3169612) (@lem3169613 n)). Qed.
Lemma lem3169615 (n : int) : (term46 n) = (term56 n).
Proof. exact (TRANS (@lem3169597 n) (@lem3169614 n)). Qed.
Lemma lem3169616 (n : int) : (term22 n) = (term57 n).
Proof. exact (MK_COMB (@lem3169594 n) (@lem3169615 n)). Qed.
Lemma lem3169617 (n : int) : (term19 n) = (term57 n).
Proof. exact (TRANS (@lem3169573 n) (@lem3169616 n)). Qed.
Lemma lem3169620 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3169621 (n : int) : (term13 n) = (term58 n).
Proof. exact (@lem3169620 term23 (int_neg n)). Qed.
Lemma lem3169623 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169624 : term41 = term42.
Proof. exact (@lem3169623 (NUMERAL 0)). Qed.
Lemma lem3169625 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3169626 : term59 = term60.
Proof. exact (MK_COMB (@lem3169625) (@lem3169624)). Qed.
Lemma lem3169628 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3169629 (n : int) : (term61 n) = (term62 n).
Proof. exact (@lem3169628 n). Qed.
Lemma lem3169630 (n : int) : (term58 n) = (term63 n).
Proof. exact (MK_COMB (@lem3169626) (@lem3169629 n)). Qed.
Lemma lem3169632 (n : int) : (term13 n) = (term63 n).
Proof. exact (TRANS (@lem3169621 n) (@lem3169630 n)). Qed.
Lemma lem3169635 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3169636 (n : int) : (term3 n) = (term64 n).
Proof. exact (@lem3169635 term23 n). Qed.
Lemma lem3169638 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169639 : term41 = term42.
Proof. exact (@lem3169638 (NUMERAL 0)). Qed.
Lemma lem3169640 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3169641 : term59 = term60.
Proof. exact (MK_COMB (@lem3169640) (@lem3169639)). Qed.
Lemma lem3169642 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3169643 (n : int) : (term64 n) = (term65 n).
Proof. exact (MK_COMB (@lem3169641) (@lem3169642 n)). Qed.
Lemma lem3169645 (n : int) : (term3 n) = (term65 n).
Proof. exact (TRANS (@lem3169636 n) (@lem3169643 n)). Qed.
Lemma lem3169646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3169647 (n : int) : (term5 n) = (term66 n).
Proof. exact (MK_COMB (@lem3169646) (@lem3169632 n)). Qed.
Lemma lem3169648 (n : int) : (term7 n) = (term67 n).
Proof. exact (MK_COMB (@lem3169647 n) (@lem3169645 n)). Qed.
Lemma lem3169650 (y : int) (x : int) : (term68 x y) = (term69 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem3169651 (n : int) : (term70 n) = (term71 n).
Proof. exact (@lem3169650 (int_neg n) term23). Qed.
Lemma lem3169653 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3169654 (n : int) : (term71 n) = (term72 n).
Proof. exact (@lem3169653 (term73 n) term23). Qed.
Lemma lem3169656 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3169657 (n : int) : (term74 n) = (term75 n).
Proof. exact (@lem3169656 (int_neg n) term32). Qed.
Lemma lem3169659 (x : int) : (term61 x) = (term62 x).
Proof. exact (EQ_MP (@lem2841589 x) (@lem2841588 x)). Qed.
Lemma lem3169660 (n : int) : (term61 n) = (term62 n).
Proof. exact (@lem3169659 n). Qed.
Lemma lem3169661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3169662 (n : int) : (term76 n) = (term77 n).
Proof. exact (MK_COMB (@lem3169661) (@lem3169660 n)). Qed.
Lemma lem3169664 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169665 : term34 = term35.
Proof. exact (@lem3169664 term36). Qed.
Lemma lem3169666 (n : int) : (term75 n) = (term78 n).
Proof. exact (MK_COMB (@lem3169662 n) (@lem3169665)). Qed.
Lemma lem3169667 (n : int) : (term74 n) = (term78 n).
Proof. exact (TRANS (@lem3169657 n) (@lem3169666 n)). Qed.
Lemma lem3169668 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3169669 (n : int) : (term79 n) = (term80 n).
Proof. exact (MK_COMB (@lem3169668) (@lem3169667 n)). Qed.
Lemma lem3169671 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169672 : term41 = term42.
Proof. exact (@lem3169671 (NUMERAL 0)). Qed.
Lemma lem3169673 (n : int) : (term72 n) = (term81 n).
Proof. exact (MK_COMB (@lem3169669 n) (@lem3169672)). Qed.
Lemma lem3169674 (n : int) : (term71 n) = (term81 n).
Proof. exact (TRANS (@lem3169654 n) (@lem3169673 n)). Qed.
Lemma lem3169675 (n : int) : (term70 n) = (term81 n).
Proof. exact (TRANS (@lem3169651 n) (@lem3169674 n)). Qed.
Lemma lem3169677 (y : int) (x : int) : (term68 x y) = (term69 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem3169678 (n : int) : (term14 n) = (term25 n).
Proof. exact (@lem3169677 n term23). Qed.
Lemma lem3169680 (x : int) (y : int) : (int_le x y) = (term24 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3169681 (n : int) : (term25 n) = (term26 n).
Proof. exact (@lem3169680 (term27 n) term23). Qed.
Lemma lem3169683 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3169684 (n : int) : (term30 n) = (term31 n).
Proof. exact (@lem3169683 n term32). Qed.
Lemma lem3169686 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169687 : term34 = term35.
Proof. exact (@lem3169686 term36). Qed.
Lemma lem3169688 (n : int) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3169689 (n : int) : (term31 n) = (term38 n).
Proof. exact (MK_COMB (@lem3169688 n) (@lem3169687)). Qed.
Lemma lem3169690 (n : int) : (term30 n) = (term38 n).
Proof. exact (TRANS (@lem3169684 n) (@lem3169689 n)). Qed.
Lemma lem3169691 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3169692 (n : int) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem3169691) (@lem3169690 n)). Qed.
Lemma lem3169694 (n : nat) : (term33 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3169695 : term41 = term42.
Proof. exact (@lem3169694 (NUMERAL 0)). Qed.
Lemma lem3169696 (n : int) : (term26 n) = (term43 n).
Proof. exact (MK_COMB (@lem3169692 n) (@lem3169695)). Qed.
Lemma lem3169697 (n : int) : (term25 n) = (term43 n).
Proof. exact (TRANS (@lem3169681 n) (@lem3169696 n)). Qed.
Lemma lem3169698 (n : int) : (term14 n) = (term43 n).
Proof. exact (TRANS (@lem3169678 n) (@lem3169697 n)). Qed.
Lemma lem3169699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3169700 (n : int) : (term82 n) = (term83 n).
Proof. exact (MK_COMB (@lem3169699) (@lem3169675 n)). Qed.
Lemma lem3169701 (n : int) : (term4 n) = (term84 n).
Proof. exact (MK_COMB (@lem3169700 n) (@lem3169698 n)). Qed.
Lemma lem3169702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3169703 (n : int) : (term9 n) = (term85 n).
Proof. exact (MK_COMB (@lem3169702) (@lem3169648 n)). Qed.
Lemma lem3169704 (n : int) : (term11 n) = (term86 n).
Proof. exact (MK_COMB (@lem3169703 n) (@lem3169701 n)). Qed.
Lemma lem3169705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3169706 (n : int) : (term15 n) = (term87 n).
Proof. exact (MK_COMB (@lem3169705) (@lem3169617 n)). Qed.
Lemma lem3169707 (n : int) : (term17 n) = (term88 n).
Proof. exact (MK_COMB (@lem3169706 n) (@lem3169704 n)). Qed.
Lemma lem3169708 (n : int) : (term18 n) = (term88 n).
Proof. exact (TRANS (@lem3169570 n) (@lem3169707 n)). Qed.
Lemma lem3169712 (t : Prop) : (term89 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3169768 (n : int) : (term90 n) = (term88 n).
Proof. exact (@lem3169712 (term88 n)). Qed.
Lemma lem3169769 (n : int) : (term43 n) = (term91 n).
Proof. exact (@lem1988287 term42 (term38 n)). Qed.
Lemma lem3169781 (n : int) : (term92 n) = (term93 n).
Proof. exact (@lem1982792 term42 (term38 n)). Qed.
Lemma lem3169782 (n : int) : (term94 n) = (term95 n).
Proof. exact (@lem1982781 (real_of_int n) term96 term35). Qed.
Lemma lem3169784 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3169785 : term35 = term98.
Proof. exact (@lem3169784 term36). Qed.
Lemma lem3169787 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3169788 : term96 = term101.
Proof. exact (@lem3169787 term36). Qed.
Lemma lem3169789 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3169790 : term102 = term103.
Proof. exact (MK_COMB (@lem3169789) (@lem3169788)). Qed.
Lemma lem3169791 : term104 = term105.
Proof. exact (MK_COMB (@lem3169790) (@lem3169785)). Qed.
Lemma lem3169792 : term105 = term106.
Proof. exact (@lem1981613 term96 term35 term35 term35). Qed.
Lemma lem3169794 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3169795 : term109 = term110.
Proof. exact (@lem3169794 term36 term36). Qed.
Lemma lem3169796 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3169797 : term112 = term36.
Proof. exact (EQ_MP (@lem3169796) (@lem940073)). Qed.
Lemma lem3169798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3169799 : term110 = term35.
Proof. exact (MK_COMB (@lem3169798) (@lem3169797)). Qed.
Lemma lem3169800 : term109 = term35.
Proof. exact (TRANS (@lem3169795) (@lem3169799)). Qed.
Lemma lem3169802 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3169803 : term104 = term115.
Proof. exact (@lem3169802 term36 term36). Qed.
Lemma lem3169804 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3169805 : term112 = term36.
Proof. exact (EQ_MP (@lem3169804) (@lem940073)). Qed.
Lemma lem3169806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3169807 : term110 = term35.
Proof. exact (MK_COMB (@lem3169806) (@lem3169805)). Qed.
Lemma lem3169808 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3169809 : term115 = term96.
Proof. exact (MK_COMB (@lem3169808) (@lem3169807)). Qed.
Lemma lem3169810 : term104 = term96.
Proof. exact (TRANS (@lem3169803) (@lem3169809)). Qed.
Lemma lem3169811 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3169812 : term116 = term117.
Proof. exact (MK_COMB (@lem3169811) (@lem3169810)). Qed.
Lemma lem3169813 : term106 = term101.
Proof. exact (MK_COMB (@lem3169812) (@lem3169800)). Qed.
Lemma lem3169814 : term105 = term101.
Proof. exact (TRANS (@lem3169792) (@lem3169813)). Qed.
Lemma lem3169815 : term104 = term101.
Proof. exact (TRANS (@lem3169791) (@lem3169814)). Qed.
Lemma lem3169817 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3169818 : term101 = term96.
Proof. exact (@lem3169817 term96). Qed.
Lemma lem3169819 : term104 = term96.
Proof. exact (TRANS (@lem3169815) (@lem3169818)). Qed.
Lemma lem3169822 (n : int) : (term119 n) = (term119 n).
Proof. exact (eq_refl (term119 n)). Qed.
Lemma lem3169823 (n : int) : (term95 n) = (term120 n).
Proof. exact (MK_COMB (@lem3169822 n) (@lem3169819)). Qed.
Lemma lem3169824 (n : int) : (term94 n) = (term120 n).
Proof. exact (TRANS (@lem3169782 n) (@lem3169823 n)). Qed.
Lemma lem3169825 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3169826 (n : int) : (term93 n) = (term121 n).
Proof. exact (MK_COMB (@lem3169825) (@lem3169824 n)). Qed.
Lemma lem3169827 (n : int) : (term121 n) = (term120 n).
Proof. exact (@lem1982721 (term120 n)). Qed.
Lemma lem3169828 (n : int) : (term93 n) = (term120 n).
Proof. exact (TRANS (@lem3169826 n) (@lem3169827 n)). Qed.
Lemma lem3169830 (n : int) : (term92 n) = (term120 n).
Proof. exact (TRANS (@lem3169781 n) (@lem3169828 n)). Qed.
Lemma lem3169831 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3169832 (n : int) : (term122 n) = (term123 n).
Proof. exact (MK_COMB (@lem3169831) (@lem3169830 n)). Qed.
Lemma lem3169833 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3169834 (n : int) : (term91 n) = (term124 n).
Proof. exact (MK_COMB (@lem3169832 n) (@lem3169833)). Qed.
Lemma lem3169835 (n : int) : (term43 n) = (term124 n).
Proof. exact (TRANS (@lem3169769 n) (@lem3169834 n)). Qed.
Lemma lem3169836 (n : int) : (term56 n) = (term125 n).
Proof. exact (@lem1988287 (real_of_int n) term53). Qed.
Lemma lem3169843 : term53 = term35.
Proof. exact (@lem1982721 term35). Qed.
Lemma lem3169846 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem3169847 (n : int) : (term127 n) = (term128 n).
Proof. exact (MK_COMB (@lem3169846 n) (@lem3169843)). Qed.
Lemma lem3169848 (n : int) : (term128 n) = (term129 n).
Proof. exact (@lem1982792 (real_of_int n) term35). Qed.
Lemma lem3169850 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3169851 : term35 = term98.
Proof. exact (@lem3169850 term36). Qed.
Lemma lem3169853 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3169854 : term96 = term101.
Proof. exact (@lem3169853 term36). Qed.
Lemma lem3169855 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3169856 : term102 = term103.
Proof. exact (MK_COMB (@lem3169855) (@lem3169854)). Qed.
Lemma lem3169857 : term104 = term105.
Proof. exact (MK_COMB (@lem3169856) (@lem3169851)). Qed.
Lemma lem3169858 : term105 = term106.
Proof. exact (@lem1981613 term96 term35 term35 term35). Qed.
Lemma lem3169860 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3169861 : term109 = term110.
Proof. exact (@lem3169860 term36 term36). Qed.
Lemma lem3169862 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3169863 : term112 = term36.
Proof. exact (EQ_MP (@lem3169862) (@lem940073)). Qed.
Lemma lem3169864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3169865 : term110 = term35.
Proof. exact (MK_COMB (@lem3169864) (@lem3169863)). Qed.
Lemma lem3169866 : term109 = term35.
Proof. exact (TRANS (@lem3169861) (@lem3169865)). Qed.
Lemma lem3169868 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3169869 : term104 = term115.
Proof. exact (@lem3169868 term36 term36). Qed.
Lemma lem3169870 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3169871 : term112 = term36.
Proof. exact (EQ_MP (@lem3169870) (@lem940073)). Qed.
Lemma lem3169872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3169873 : term110 = term35.
Proof. exact (MK_COMB (@lem3169872) (@lem3169871)). Qed.
Lemma lem3169874 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3169875 : term115 = term96.
Proof. exact (MK_COMB (@lem3169874) (@lem3169873)). Qed.
Lemma lem3169876 : term104 = term96.
Proof. exact (TRANS (@lem3169869) (@lem3169875)). Qed.
Lemma lem3169877 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3169878 : term116 = term117.
Proof. exact (MK_COMB (@lem3169877) (@lem3169876)). Qed.
Lemma lem3169879 : term106 = term101.
Proof. exact (MK_COMB (@lem3169878) (@lem3169866)). Qed.
Lemma lem3169880 : term105 = term101.
Proof. exact (TRANS (@lem3169858) (@lem3169879)). Qed.
Lemma lem3169881 : term104 = term101.
Proof. exact (TRANS (@lem3169857) (@lem3169880)). Qed.
Lemma lem3169883 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3169884 : term101 = term96.
Proof. exact (@lem3169883 term96). Qed.
Lemma lem3169885 : term104 = term96.
Proof. exact (TRANS (@lem3169881) (@lem3169884)). Qed.
Lemma lem3169886 (n : int) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3169889 (n : int) : (term129 n) = (term130 n).
Proof. exact (MK_COMB (@lem3169886 n) (@lem3169885)). Qed.
Lemma lem3169890 (n : int) : (term128 n) = (term130 n).
Proof. exact (TRANS (@lem3169848 n) (@lem3169889 n)). Qed.
Lemma lem3169891 (n : int) : (term127 n) = (term130 n).
Proof. exact (TRANS (@lem3169847 n) (@lem3169890 n)). Qed.
Lemma lem3169892 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3169893 (n : int) : (term131 n) = (term132 n).
Proof. exact (MK_COMB (@lem3169892) (@lem3169891 n)). Qed.
Lemma lem3169894 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3169895 (n : int) : (term125 n) = (term133 n).
Proof. exact (MK_COMB (@lem3169893 n) (@lem3169894)). Qed.
Lemma lem3169896 (n : int) : (term56 n) = (term133 n).
Proof. exact (TRANS (@lem3169836 n) (@lem3169895 n)). Qed.
Lemma lem3169897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3169898 (n : int) : (term45 n) = (term134 n).
Proof. exact (MK_COMB (@lem3169897) (@lem3169835 n)). Qed.
Lemma lem3169899 (n : int) : (term57 n) = (term135 n).
Proof. exact (MK_COMB (@lem3169898 n) (@lem3169896 n)). Qed.
Lemma lem3169900 (n : int) : (term63 n) = (term136 n).
Proof. exact (@lem1988287 (term62 n) term42). Qed.
Lemma lem3169901 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3169908 (n : int) : (term62 n) = (term137 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem3169909 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem3169910 (n : int) : (term138 n) = (term139 n).
Proof. exact (MK_COMB (@lem3169909) (@lem3169908 n)). Qed.
Lemma lem3169911 (n : int) : (term140 n) = (term141 n).
Proof. exact (MK_COMB (@lem3169910 n) (@lem3169901)). Qed.
Lemma lem3169912 (n : int) : (term141 n) = (term142 n).
Proof. exact (@lem1982792 (term137 n) term42). Qed.
Lemma lem3169914 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3169915 : term42 = term143.
Proof. exact (@lem3169914 (NUMERAL 0)). Qed.
Lemma lem3169917 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3169918 : term96 = term101.
Proof. exact (@lem3169917 term36). Qed.
Lemma lem3169919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3169920 : term102 = term103.
Proof. exact (MK_COMB (@lem3169919) (@lem3169918)). Qed.
Lemma lem3169921 : term144 = term145.
Proof. exact (MK_COMB (@lem3169920) (@lem3169915)). Qed.
Lemma lem3169922 : term145 = term146.
Proof. exact (@lem1981613 term96 term42 term35 term35). Qed.
Lemma lem3169924 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3169925 : term109 = term110.
Proof. exact (@lem3169924 term36 term36). Qed.
Lemma lem3169926 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3169927 : term112 = term36.
Proof. exact (EQ_MP (@lem3169926) (@lem940073)). Qed.
Lemma lem3169928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3169929 : term110 = term35.
Proof. exact (MK_COMB (@lem3169928) (@lem3169927)). Qed.
Lemma lem3169930 : term109 = term35.
Proof. exact (TRANS (@lem3169925) (@lem3169929)). Qed.
Lemma lem3169932 (x : nat) : (term147 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3169933 : term144 = term42.
Proof. exact (@lem3169932 term36). Qed.
Lemma lem3169934 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3169935 : term148 = term149.
Proof. exact (MK_COMB (@lem3169934) (@lem3169933)). Qed.
Lemma lem3169936 : term146 = term143.
Proof. exact (MK_COMB (@lem3169935) (@lem3169930)). Qed.
Lemma lem3169937 : term145 = term143.
Proof. exact (TRANS (@lem3169922) (@lem3169936)). Qed.
Lemma lem3169938 : term144 = term143.
Proof. exact (TRANS (@lem3169921) (@lem3169937)). Qed.
Lemma lem3169940 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3169941 : term143 = term42.
Proof. exact (@lem3169940 term42). Qed.
Lemma lem3169942 : term144 = term42.
Proof. exact (TRANS (@lem3169938) (@lem3169941)). Qed.
Lemma lem3169943 (n : int) : (term119 n) = (term119 n).
Proof. exact (eq_refl (term119 n)). Qed.
Lemma lem3169944 (n : int) : (term142 n) = (term150 n).
Proof. exact (MK_COMB (@lem3169943 n) (@lem3169942)). Qed.
Lemma lem3169945 (n : int) : (term150 n) = (term137 n).
Proof. exact (@lem1982723 (term137 n)). Qed.
Lemma lem3169946 (n : int) : (term142 n) = (term137 n).
Proof. exact (TRANS (@lem3169944 n) (@lem3169945 n)). Qed.
Lemma lem3169947 (n : int) : (term141 n) = (term137 n).
Proof. exact (TRANS (@lem3169912 n) (@lem3169946 n)). Qed.
Lemma lem3169948 (n : int) : (term140 n) = (term137 n).
Proof. exact (TRANS (@lem3169911 n) (@lem3169947 n)). Qed.
Lemma lem3169949 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3169950 (n : int) : (term151 n) = (term152 n).
Proof. exact (MK_COMB (@lem3169949) (@lem3169948 n)). Qed.
Lemma lem3169951 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3169952 (n : int) : (term136 n) = (term153 n).
Proof. exact (MK_COMB (@lem3169950 n) (@lem3169951)). Qed.
Lemma lem3169953 (n : int) : (term63 n) = (term153 n).
Proof. exact (TRANS (@lem3169900 n) (@lem3169952 n)). Qed.
Lemma lem3169954 (n : int) : (term65 n) = (term154 n).
Proof. exact (@lem1988287 (real_of_int n) term42). Qed.
Lemma lem3169960 (n : int) : (term155 n) = (term156 n).
Proof. exact (@lem1982792 (real_of_int n) term42). Qed.
Lemma lem3169962 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3169963 : term42 = term143.
Proof. exact (@lem3169962 (NUMERAL 0)). Qed.
Lemma lem3169965 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3169966 : term96 = term101.
Proof. exact (@lem3169965 term36). Qed.
Lemma lem3169967 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3169968 : term102 = term103.
Proof. exact (MK_COMB (@lem3169967) (@lem3169966)). Qed.
Lemma lem3169969 : term144 = term145.
Proof. exact (MK_COMB (@lem3169968) (@lem3169963)). Qed.
Lemma lem3169970 : term145 = term146.
Proof. exact (@lem1981613 term96 term42 term35 term35). Qed.
Lemma lem3169972 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3169973 : term109 = term110.
Proof. exact (@lem3169972 term36 term36). Qed.
Lemma lem3169974 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3169975 : term112 = term36.
Proof. exact (EQ_MP (@lem3169974) (@lem940073)). Qed.
Lemma lem3169976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3169977 : term110 = term35.
Proof. exact (MK_COMB (@lem3169976) (@lem3169975)). Qed.
Lemma lem3169978 : term109 = term35.
Proof. exact (TRANS (@lem3169973) (@lem3169977)). Qed.
Lemma lem3169980 (x : nat) : (term147 x) = term42.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3169981 : term144 = term42.
Proof. exact (@lem3169980 term36). Qed.
Lemma lem3169982 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3169983 : term148 = term149.
Proof. exact (MK_COMB (@lem3169982) (@lem3169981)). Qed.
Lemma lem3169984 : term146 = term143.
Proof. exact (MK_COMB (@lem3169983) (@lem3169978)). Qed.
Lemma lem3169985 : term145 = term143.
Proof. exact (TRANS (@lem3169970) (@lem3169984)). Qed.
Lemma lem3169986 : term144 = term143.
Proof. exact (TRANS (@lem3169969) (@lem3169985)). Qed.
Lemma lem3169988 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3169989 : term143 = term42.
Proof. exact (@lem3169988 term42). Qed.
Lemma lem3169990 : term144 = term42.
Proof. exact (TRANS (@lem3169986) (@lem3169989)). Qed.
Lemma lem3169991 (n : int) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem3169992 (n : int) : (term156 n) = (term157 n).
Proof. exact (MK_COMB (@lem3169991 n) (@lem3169990)). Qed.
Lemma lem3169993 (n : int) : (term157 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem3169994 (n : int) : (term156 n) = (real_of_int n).
Proof. exact (TRANS (@lem3169992 n) (@lem3169993 n)). Qed.
Lemma lem3169996 (n : int) : (term155 n) = (real_of_int n).
Proof. exact (TRANS (@lem3169960 n) (@lem3169994 n)). Qed.
Lemma lem3169997 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3169998 (n : int) : (term158 n) = (term159 n).
Proof. exact (MK_COMB (@lem3169997) (@lem3169996 n)). Qed.
Lemma lem3169999 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170000 (n : int) : (term154 n) = (term160 n).
Proof. exact (MK_COMB (@lem3169998 n) (@lem3169999)). Qed.
Lemma lem3170001 (n : int) : (term65 n) = (term160 n).
Proof. exact (TRANS (@lem3169954 n) (@lem3170000 n)). Qed.
Lemma lem3170002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3170003 (n : int) : (term66 n) = (term161 n).
Proof. exact (MK_COMB (@lem3170002) (@lem3169953 n)). Qed.
Lemma lem3170004 (n : int) : (term67 n) = (term162 n).
Proof. exact (MK_COMB (@lem3170003 n) (@lem3170001 n)). Qed.
Lemma lem3170005 (n : int) : (term81 n) = (term163 n).
Proof. exact (@lem1988287 term42 (term78 n)). Qed.
Lemma lem3170006 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3170013 (n : int) : (term62 n) = (term137 n).
Proof. exact (@lem1982785 (real_of_int n)). Qed.
Lemma lem3170014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170015 (n : int) : (term77 n) = (term119 n).
Proof. exact (MK_COMB (@lem3170014) (@lem3170013 n)). Qed.
Lemma lem3170018 (n : int) : (term78 n) = (term164 n).
Proof. exact (MK_COMB (@lem3170015 n) (@lem3170006)). Qed.
Lemma lem3170021 : term165 = term165.
Proof. exact (eq_refl term165). Qed.
Lemma lem3170022 (n : int) : (term166 n) = (term167 n).
Proof. exact (MK_COMB (@lem3170021) (@lem3170018 n)). Qed.
Lemma lem3170023 (n : int) : (term167 n) = (term168 n).
Proof. exact (@lem1982792 term42 (term164 n)). Qed.
Lemma lem3170024 (n : int) : (term169 n) = (term170 n).
Proof. exact (@lem1982781 (term137 n) term96 term35). Qed.
Lemma lem3170026 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170027 : term35 = term98.
Proof. exact (@lem3170026 term36). Qed.
Lemma lem3170029 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170030 : term96 = term101.
Proof. exact (@lem3170029 term36). Qed.
Lemma lem3170031 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170032 : term102 = term103.
Proof. exact (MK_COMB (@lem3170031) (@lem3170030)). Qed.
Lemma lem3170033 : term104 = term105.
Proof. exact (MK_COMB (@lem3170032) (@lem3170027)). Qed.
Lemma lem3170034 : term105 = term106.
Proof. exact (@lem1981613 term96 term35 term35 term35). Qed.
Lemma lem3170036 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170037 : term109 = term110.
Proof. exact (@lem3170036 term36 term36). Qed.
Lemma lem3170038 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170039 : term112 = term36.
Proof. exact (EQ_MP (@lem3170038) (@lem940073)). Qed.
Lemma lem3170040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170041 : term110 = term35.
Proof. exact (MK_COMB (@lem3170040) (@lem3170039)). Qed.
Lemma lem3170042 : term109 = term35.
Proof. exact (TRANS (@lem3170037) (@lem3170041)). Qed.
Lemma lem3170044 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3170045 : term104 = term115.
Proof. exact (@lem3170044 term36 term36). Qed.
Lemma lem3170046 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170047 : term112 = term36.
Proof. exact (EQ_MP (@lem3170046) (@lem940073)). Qed.
Lemma lem3170048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170049 : term110 = term35.
Proof. exact (MK_COMB (@lem3170048) (@lem3170047)). Qed.
Lemma lem3170050 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3170051 : term115 = term96.
Proof. exact (MK_COMB (@lem3170050) (@lem3170049)). Qed.
Lemma lem3170052 : term104 = term96.
Proof. exact (TRANS (@lem3170045) (@lem3170051)). Qed.
Lemma lem3170053 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3170054 : term116 = term117.
Proof. exact (MK_COMB (@lem3170053) (@lem3170052)). Qed.
Lemma lem3170055 : term106 = term101.
Proof. exact (MK_COMB (@lem3170054) (@lem3170042)). Qed.
Lemma lem3170056 : term105 = term101.
Proof. exact (TRANS (@lem3170034) (@lem3170055)). Qed.
Lemma lem3170057 : term104 = term101.
Proof. exact (TRANS (@lem3170033) (@lem3170056)). Qed.
Lemma lem3170059 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3170060 : term101 = term96.
Proof. exact (@lem3170059 term96). Qed.
Lemma lem3170061 : term104 = term96.
Proof. exact (TRANS (@lem3170057) (@lem3170060)). Qed.
Lemma lem3170062 (n : int) : (term171 n) = (term172 n).
Proof. exact (@lem1982749 term96 term96 (real_of_int n)). Qed.
Lemma lem3170064 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170065 : term96 = term101.
Proof. exact (@lem3170064 term36). Qed.
Lemma lem3170067 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170068 : term96 = term101.
Proof. exact (@lem3170067 term36). Qed.
Lemma lem3170069 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170070 : term102 = term103.
Proof. exact (MK_COMB (@lem3170069) (@lem3170068)). Qed.
Lemma lem3170071 : term173 = term174.
Proof. exact (MK_COMB (@lem3170070) (@lem3170065)). Qed.
Lemma lem3170072 : term174 = term175.
Proof. exact (@lem1981613 term96 term96 term35 term35). Qed.
Lemma lem3170074 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170075 : term109 = term110.
Proof. exact (@lem3170074 term36 term36). Qed.
Lemma lem3170076 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170077 : term112 = term36.
Proof. exact (EQ_MP (@lem3170076) (@lem940073)). Qed.
Lemma lem3170078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170079 : term110 = term35.
Proof. exact (MK_COMB (@lem3170078) (@lem3170077)). Qed.
Lemma lem3170080 : term109 = term35.
Proof. exact (TRANS (@lem3170075) (@lem3170079)). Qed.
Lemma lem3170082 (m : nat) (n : nat) : (term176 m n) = (term108 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3170083 : term173 = term110.
Proof. exact (@lem3170082 term36 term36). Qed.
Lemma lem3170084 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170085 : term112 = term36.
Proof. exact (EQ_MP (@lem3170084) (@lem940073)). Qed.
Lemma lem3170086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170087 : term110 = term35.
Proof. exact (MK_COMB (@lem3170086) (@lem3170085)). Qed.
Lemma lem3170088 : term173 = term35.
Proof. exact (TRANS (@lem3170083) (@lem3170087)). Qed.
Lemma lem3170089 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3170090 : term177 = term178.
Proof. exact (MK_COMB (@lem3170089) (@lem3170088)). Qed.
Lemma lem3170091 : term175 = term98.
Proof. exact (MK_COMB (@lem3170090) (@lem3170080)). Qed.
Lemma lem3170092 : term174 = term98.
Proof. exact (TRANS (@lem3170072) (@lem3170091)). Qed.
Lemma lem3170093 : term173 = term98.
Proof. exact (TRANS (@lem3170071) (@lem3170092)). Qed.
Lemma lem3170095 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3170096 : term98 = term35.
Proof. exact (@lem3170095 term35). Qed.
Lemma lem3170097 : term173 = term35.
Proof. exact (TRANS (@lem3170093) (@lem3170096)). Qed.
Lemma lem3170098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170099 : term179 = term180.
Proof. exact (MK_COMB (@lem3170098) (@lem3170097)). Qed.
Lemma lem3170100 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3170101 (n : int) : (term172 n) = (term181 n).
Proof. exact (MK_COMB (@lem3170099) (@lem3170100 n)). Qed.
Lemma lem3170102 (n : int) : (term171 n) = (term181 n).
Proof. exact (TRANS (@lem3170062 n) (@lem3170101 n)). Qed.
Lemma lem3170103 (n : int) : (term181 n) = (real_of_int n).
Proof. exact (@lem1982709 (real_of_int n)). Qed.
Lemma lem3170104 (n : int) : (term171 n) = (real_of_int n).
Proof. exact (TRANS (@lem3170102 n) (@lem3170103 n)). Qed.
Lemma lem3170105 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170106 (n : int) : (term182 n) = (term37 n).
Proof. exact (MK_COMB (@lem3170105) (@lem3170104 n)). Qed.
Lemma lem3170107 (n : int) : (term170 n) = (term130 n).
Proof. exact (MK_COMB (@lem3170106 n) (@lem3170061)). Qed.
Lemma lem3170108 (n : int) : (term169 n) = (term130 n).
Proof. exact (TRANS (@lem3170024 n) (@lem3170107 n)). Qed.
Lemma lem3170109 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3170110 (n : int) : (term168 n) = (term183 n).
Proof. exact (MK_COMB (@lem3170109) (@lem3170108 n)). Qed.
Lemma lem3170111 (n : int) : (term183 n) = (term130 n).
Proof. exact (@lem1982721 (term130 n)). Qed.
Lemma lem3170112 (n : int) : (term168 n) = (term130 n).
Proof. exact (TRANS (@lem3170110 n) (@lem3170111 n)). Qed.
Lemma lem3170113 (n : int) : (term167 n) = (term130 n).
Proof. exact (TRANS (@lem3170023 n) (@lem3170112 n)). Qed.
Lemma lem3170114 (n : int) : (term166 n) = (term130 n).
Proof. exact (TRANS (@lem3170022 n) (@lem3170113 n)). Qed.
Lemma lem3170115 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170116 (n : int) : (term184 n) = (term132 n).
Proof. exact (MK_COMB (@lem3170115) (@lem3170114 n)). Qed.
Lemma lem3170117 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170118 (n : int) : (term163 n) = (term133 n).
Proof. exact (MK_COMB (@lem3170116 n) (@lem3170117)). Qed.
Lemma lem3170119 (n : int) : (term81 n) = (term133 n).
Proof. exact (TRANS (@lem3170005 n) (@lem3170118 n)). Qed.
Lemma lem3170120 (n : int) : (term43 n) = (term91 n).
Proof. exact (@lem1988287 term42 (term38 n)). Qed.
Lemma lem3170132 (n : int) : (term92 n) = (term93 n).
Proof. exact (@lem1982792 term42 (term38 n)). Qed.
Lemma lem3170133 (n : int) : (term94 n) = (term95 n).
Proof. exact (@lem1982781 (real_of_int n) term96 term35). Qed.
Lemma lem3170135 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170136 : term35 = term98.
Proof. exact (@lem3170135 term36). Qed.
Lemma lem3170138 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170139 : term96 = term101.
Proof. exact (@lem3170138 term36). Qed.
Lemma lem3170140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170141 : term102 = term103.
Proof. exact (MK_COMB (@lem3170140) (@lem3170139)). Qed.
Lemma lem3170142 : term104 = term105.
Proof. exact (MK_COMB (@lem3170141) (@lem3170136)). Qed.
Lemma lem3170143 : term105 = term106.
Proof. exact (@lem1981613 term96 term35 term35 term35). Qed.
Lemma lem3170145 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170146 : term109 = term110.
Proof. exact (@lem3170145 term36 term36). Qed.
Lemma lem3170147 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170148 : term112 = term36.
Proof. exact (EQ_MP (@lem3170147) (@lem940073)). Qed.
Lemma lem3170149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170150 : term110 = term35.
Proof. exact (MK_COMB (@lem3170149) (@lem3170148)). Qed.
Lemma lem3170151 : term109 = term35.
Proof. exact (TRANS (@lem3170146) (@lem3170150)). Qed.
Lemma lem3170153 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3170154 : term104 = term115.
Proof. exact (@lem3170153 term36 term36). Qed.
Lemma lem3170155 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170156 : term112 = term36.
Proof. exact (EQ_MP (@lem3170155) (@lem940073)). Qed.
Lemma lem3170157 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170158 : term110 = term35.
Proof. exact (MK_COMB (@lem3170157) (@lem3170156)). Qed.
Lemma lem3170159 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3170160 : term115 = term96.
Proof. exact (MK_COMB (@lem3170159) (@lem3170158)). Qed.
Lemma lem3170161 : term104 = term96.
Proof. exact (TRANS (@lem3170154) (@lem3170160)). Qed.
Lemma lem3170162 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3170163 : term116 = term117.
Proof. exact (MK_COMB (@lem3170162) (@lem3170161)). Qed.
Lemma lem3170164 : term106 = term101.
Proof. exact (MK_COMB (@lem3170163) (@lem3170151)). Qed.
Lemma lem3170165 : term105 = term101.
Proof. exact (TRANS (@lem3170143) (@lem3170164)). Qed.
Lemma lem3170166 : term104 = term101.
Proof. exact (TRANS (@lem3170142) (@lem3170165)). Qed.
Lemma lem3170168 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3170169 : term101 = term96.
Proof. exact (@lem3170168 term96). Qed.
Lemma lem3170170 : term104 = term96.
Proof. exact (TRANS (@lem3170166) (@lem3170169)). Qed.
Lemma lem3170173 (n : int) : (term119 n) = (term119 n).
Proof. exact (eq_refl (term119 n)). Qed.
Lemma lem3170174 (n : int) : (term95 n) = (term120 n).
Proof. exact (MK_COMB (@lem3170173 n) (@lem3170170)). Qed.
Lemma lem3170175 (n : int) : (term94 n) = (term120 n).
Proof. exact (TRANS (@lem3170133 n) (@lem3170174 n)). Qed.
Lemma lem3170176 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3170177 (n : int) : (term93 n) = (term121 n).
Proof. exact (MK_COMB (@lem3170176) (@lem3170175 n)). Qed.
Lemma lem3170178 (n : int) : (term121 n) = (term120 n).
Proof. exact (@lem1982721 (term120 n)). Qed.
Lemma lem3170179 (n : int) : (term93 n) = (term120 n).
Proof. exact (TRANS (@lem3170177 n) (@lem3170178 n)). Qed.
Lemma lem3170181 (n : int) : (term92 n) = (term120 n).
Proof. exact (TRANS (@lem3170132 n) (@lem3170179 n)). Qed.
Lemma lem3170182 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170183 (n : int) : (term122 n) = (term123 n).
Proof. exact (MK_COMB (@lem3170182) (@lem3170181 n)). Qed.
Lemma lem3170184 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170185 (n : int) : (term91 n) = (term124 n).
Proof. exact (MK_COMB (@lem3170183 n) (@lem3170184)). Qed.
Lemma lem3170186 (n : int) : (term43 n) = (term124 n).
Proof. exact (TRANS (@lem3170120 n) (@lem3170185 n)). Qed.
Lemma lem3170187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3170188 (n : int) : (term83 n) = (term185 n).
Proof. exact (MK_COMB (@lem3170187) (@lem3170119 n)). Qed.
Lemma lem3170189 (n : int) : (term84 n) = (term186 n).
Proof. exact (MK_COMB (@lem3170188 n) (@lem3170186 n)). Qed.
Lemma lem3170190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3170191 (n : int) : (term85 n) = (term187 n).
Proof. exact (MK_COMB (@lem3170190) (@lem3170004 n)). Qed.
Lemma lem3170192 (n : int) : (term86 n) = (term188 n).
Proof. exact (MK_COMB (@lem3170191 n) (@lem3170189 n)). Qed.
Lemma lem3170193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3170194 (n : int) : (term87 n) = (term189 n).
Proof. exact (MK_COMB (@lem3170193) (@lem3169899 n)). Qed.
Lemma lem3170195 (n : int) : (term88 n) = (term190 n).
Proof. exact (MK_COMB (@lem3170194 n) (@lem3170192 n)). Qed.
Lemma lem3170202 (n : int) : (term90 n) = (term190 n).
Proof. exact (TRANS (@lem3169768 n) (@lem3170195 n)). Qed.
Lemma lem3170228 (n : int) : (term190 n) = (term191 n).
Proof. exact (@lem19158 (term162 n) (term135 n) (term186 n)). Qed.
Lemma lem3170235 (n : int) : (term192 n) = (term193 n).
Proof. exact (@lem19367 (term124 n) (term133 n) (term186 n)). Qed.
Lemma lem3170242 (n : int) : (term194 n) = (term195 n).
Proof. exact (@lem19367 (term124 n) (term133 n) (term162 n)). Qed.
Lemma lem3170243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3170244 (n : int) : (term196 n) = (term197 n).
Proof. exact (MK_COMB (@lem3170243) (@lem3170242 n)). Qed.
Lemma lem3170245 (n : int) : (term191 n) = (term198 n).
Proof. exact (MK_COMB (@lem3170244 n) (@lem3170235 n)). Qed.
Lemma lem3170247 (n : int) : (term190 n) = (term198 n).
Proof. exact (TRANS (@lem3170228 n) (@lem3170245 n)). Qed.
Lemma lem3170248 (n : int) : (term90 n) = (term198 n).
Proof. exact (TRANS (@lem3170202 n) (@lem3170247 n)). Qed.
Lemma lem3170270 (n : int) (h1 : term198 n) : term198 n.
Proof. exact (h1). Qed.
Lemma lem3170271 (n : int) (h1 : term195 n) : term195 n.
Proof. exact (h1). Qed.
Lemma lem3170272 (n : int) (h1 : term199 n) : term199 n.
Proof. exact (h1). Qed.
Lemma lem3170273 (n : int) (h1 : term199 n) : term162 n.
Proof. exact (proj2 (@lem3170272 n h1)). Qed.
Lemma lem3170274 (n : int) (h1 : term199 n) : term124 n.
Proof. exact (proj1 (@lem3170272 n h1)). Qed.
Lemma lem3170275 (n : int) (h1 : term199 n) : term160 n.
Proof. exact (proj2 (@lem3170273 n h1)). Qed.
Lemma lem3170278 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3170279 : term200 = term201.
Proof. exact (@lem3170278 term42 term35). Qed.
Lemma lem3170281 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170282 : term35 = term98.
Proof. exact (@lem3170281 term36). Qed.
Lemma lem3170284 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170285 : term42 = term143.
Proof. exact (@lem3170284 (NUMERAL 0)). Qed.
Lemma lem3170286 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170287 : term202 = term203.
Proof. exact (MK_COMB (@lem3170286) (@lem3170285)). Qed.
Lemma lem3170288 : term201 = term204.
Proof. exact (MK_COMB (@lem3170287) (@lem3170282)). Qed.
Lemma lem3170289 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3170291 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170292 : term201 = term207.
Proof. exact (@lem3170291 (NUMERAL 0) term36). Qed.
Lemma lem3170293 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170294 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170295 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170294 h1) (fun h1 : term207 = True => @lem3170293)). Qed.
Lemma lem3170296 : term207 = True.
Proof. exact (EQ_MP (@lem3170295) (@lem3170293)). Qed.
Lemma lem3170297 : term201 = True.
Proof. exact (TRANS (@lem3170292) (@lem3170296)). Qed.
Lemma lem3170298 : True = term201.
Proof. exact (SYM (@lem3170297)). Qed.
Lemma lem3170299 : term201.
Proof. exact (EQ_MP (@lem3170298) (@lem0)). Qed.
Lemma lem3170300 : term209.
Proof. exact (@lem3170289 (@lem3170299)). Qed.
Lemma lem3170302 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170303 : term201 = term207.
Proof. exact (@lem3170302 (NUMERAL 0) term36). Qed.
Lemma lem3170304 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170305 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170306 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170305 h1) (fun h1 : term207 = True => @lem3170304)). Qed.
Lemma lem3170307 : term207 = True.
Proof. exact (EQ_MP (@lem3170306) (@lem3170304)). Qed.
Lemma lem3170308 : term201 = True.
Proof. exact (TRANS (@lem3170303) (@lem3170307)). Qed.
Lemma lem3170309 : True = term201.
Proof. exact (SYM (@lem3170308)). Qed.
Lemma lem3170310 : term201.
Proof. exact (EQ_MP (@lem3170309) (@lem0)). Qed.
Lemma lem3170311 : term204 = term210.
Proof. exact (@lem3170300 (@lem3170310)). Qed.
Lemma lem3170313 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170314 : term109 = term110.
Proof. exact (@lem3170313 term36 term36). Qed.
Lemma lem3170315 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170316 : term112 = term36.
Proof. exact (EQ_MP (@lem3170315) (@lem940073)). Qed.
Lemma lem3170317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170318 : term110 = term35.
Proof. exact (MK_COMB (@lem3170317) (@lem3170316)). Qed.
Lemma lem3170319 : term109 = term35.
Proof. exact (TRANS (@lem3170314) (@lem3170318)). Qed.
Lemma lem3170321 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170322 : term212 = term42.
Proof. exact (@lem3170321 term36). Qed.
Lemma lem3170323 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170324 : term213 = term202.
Proof. exact (MK_COMB (@lem3170323) (@lem3170322)). Qed.
Lemma lem3170325 : term210 = term201.
Proof. exact (MK_COMB (@lem3170324) (@lem3170319)). Qed.
Lemma lem3170327 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170328 : term201 = term207.
Proof. exact (@lem3170327 (NUMERAL 0) term36). Qed.
Lemma lem3170329 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170330 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170331 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170330 h1) (fun h1 : term207 = True => @lem3170329)). Qed.
Lemma lem3170332 : term207 = True.
Proof. exact (EQ_MP (@lem3170331) (@lem3170329)). Qed.
Lemma lem3170333 : term201 = True.
Proof. exact (TRANS (@lem3170328) (@lem3170332)). Qed.
Lemma lem3170334 : term210 = True.
Proof. exact (TRANS (@lem3170325) (@lem3170333)). Qed.
Lemma lem3170335 : term204 = True.
Proof. exact (TRANS (@lem3170311) (@lem3170334)). Qed.
Lemma lem3170336 : term201 = True.
Proof. exact (TRANS (@lem3170288) (@lem3170335)). Qed.
Lemma lem3170337 : term200 = True.
Proof. exact (TRANS (@lem3170279) (@lem3170336)). Qed.
Lemma lem3170338 : True = term200.
Proof. exact (SYM (@lem3170337)). Qed.
Lemma lem3170339 : term200.
Proof. exact (EQ_MP (@lem3170338) (@lem0)). Qed.
Lemma lem3170340 (n : int) (h1 : term199 n) : term214 n.
Proof. exact (conj (@lem3170339) (@lem3170275 n h1)). Qed.
Lemma lem3170342 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3170343 (n : int) : term216 n.
Proof. exact (@lem3170342 term35 (real_of_int n)). Qed.
Lemma lem3170344 (n : int) (h1 : term199 n) : term217 n.
Proof. exact (@lem3170343 n (@lem3170340 n h1)). Qed.
Lemma lem3170345 (n : int) : (term181 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem3170346 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170347 (n : int) : (term218 n) = (term159 n).
Proof. exact (MK_COMB (@lem3170346) (@lem3170345 n)). Qed.
Lemma lem3170348 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170349 (n : int) : (term217 n) = (term160 n).
Proof. exact (MK_COMB (@lem3170347 n) (@lem3170348)). Qed.
Lemma lem3170350 (n : int) (h1 : term199 n) : term160 n.
Proof. exact (EQ_MP (@lem3170349 n) (@lem3170344 n h1)). Qed.
Lemma lem3170352 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3170353 : term200 = term201.
Proof. exact (@lem3170352 term42 term35). Qed.
Lemma lem3170355 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170356 : term35 = term98.
Proof. exact (@lem3170355 term36). Qed.
Lemma lem3170358 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170359 : term42 = term143.
Proof. exact (@lem3170358 (NUMERAL 0)). Qed.
Lemma lem3170360 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170361 : term202 = term203.
Proof. exact (MK_COMB (@lem3170360) (@lem3170359)). Qed.
Lemma lem3170362 : term201 = term204.
Proof. exact (MK_COMB (@lem3170361) (@lem3170356)). Qed.
Lemma lem3170363 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3170365 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170366 : term201 = term207.
Proof. exact (@lem3170365 (NUMERAL 0) term36). Qed.
Lemma lem3170367 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170368 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170369 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170368 h1) (fun h1 : term207 = True => @lem3170367)). Qed.
Lemma lem3170370 : term207 = True.
Proof. exact (EQ_MP (@lem3170369) (@lem3170367)). Qed.
Lemma lem3170371 : term201 = True.
Proof. exact (TRANS (@lem3170366) (@lem3170370)). Qed.
Lemma lem3170372 : True = term201.
Proof. exact (SYM (@lem3170371)). Qed.
Lemma lem3170373 : term201.
Proof. exact (EQ_MP (@lem3170372) (@lem0)). Qed.
Lemma lem3170374 : term209.
Proof. exact (@lem3170363 (@lem3170373)). Qed.
Lemma lem3170376 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170377 : term201 = term207.
Proof. exact (@lem3170376 (NUMERAL 0) term36). Qed.
Lemma lem3170378 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170379 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170380 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170379 h1) (fun h1 : term207 = True => @lem3170378)). Qed.
Lemma lem3170381 : term207 = True.
Proof. exact (EQ_MP (@lem3170380) (@lem3170378)). Qed.
Lemma lem3170382 : term201 = True.
Proof. exact (TRANS (@lem3170377) (@lem3170381)). Qed.
Lemma lem3170383 : True = term201.
Proof. exact (SYM (@lem3170382)). Qed.
Lemma lem3170384 : term201.
Proof. exact (EQ_MP (@lem3170383) (@lem0)). Qed.
Lemma lem3170385 : term204 = term210.
Proof. exact (@lem3170374 (@lem3170384)). Qed.
Lemma lem3170387 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170388 : term109 = term110.
Proof. exact (@lem3170387 term36 term36). Qed.
Lemma lem3170389 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170390 : term112 = term36.
Proof. exact (EQ_MP (@lem3170389) (@lem940073)). Qed.
Lemma lem3170391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170392 : term110 = term35.
Proof. exact (MK_COMB (@lem3170391) (@lem3170390)). Qed.
Lemma lem3170393 : term109 = term35.
Proof. exact (TRANS (@lem3170388) (@lem3170392)). Qed.
Lemma lem3170395 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170396 : term212 = term42.
Proof. exact (@lem3170395 term36). Qed.
Lemma lem3170397 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170398 : term213 = term202.
Proof. exact (MK_COMB (@lem3170397) (@lem3170396)). Qed.
Lemma lem3170399 : term210 = term201.
Proof. exact (MK_COMB (@lem3170398) (@lem3170393)). Qed.
Lemma lem3170401 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170402 : term201 = term207.
Proof. exact (@lem3170401 (NUMERAL 0) term36). Qed.
Lemma lem3170403 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170404 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170405 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170404 h1) (fun h1 : term207 = True => @lem3170403)). Qed.
Lemma lem3170406 : term207 = True.
Proof. exact (EQ_MP (@lem3170405) (@lem3170403)). Qed.
Lemma lem3170407 : term201 = True.
Proof. exact (TRANS (@lem3170402) (@lem3170406)). Qed.
Lemma lem3170408 : term210 = True.
Proof. exact (TRANS (@lem3170399) (@lem3170407)). Qed.
Lemma lem3170409 : term204 = True.
Proof. exact (TRANS (@lem3170385) (@lem3170408)). Qed.
Lemma lem3170410 : term201 = True.
Proof. exact (TRANS (@lem3170362) (@lem3170409)). Qed.
Lemma lem3170411 : term200 = True.
Proof. exact (TRANS (@lem3170353) (@lem3170410)). Qed.
Lemma lem3170412 : True = term200.
Proof. exact (SYM (@lem3170411)). Qed.
Lemma lem3170413 : term200.
Proof. exact (EQ_MP (@lem3170412) (@lem0)). Qed.
Lemma lem3170414 (n : int) (h1 : term199 n) : term219 n.
Proof. exact (conj (@lem3170413) (@lem3170274 n h1)). Qed.
Lemma lem3170416 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3170417 (n : int) : term220 n.
Proof. exact (@lem3170416 term35 (term120 n)). Qed.
Lemma lem3170418 (n : int) (h1 : term199 n) : term221 n.
Proof. exact (@lem3170417 n (@lem3170414 n h1)). Qed.
Lemma lem3170419 (n : int) : (term222 n) = (term120 n).
Proof. exact (@lem1982733 (term120 n)). Qed.
Lemma lem3170420 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170421 (n : int) : (term223 n) = (term123 n).
Proof. exact (MK_COMB (@lem3170420) (@lem3170419 n)). Qed.
Lemma lem3170422 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170423 (n : int) : (term221 n) = (term124 n).
Proof. exact (MK_COMB (@lem3170421 n) (@lem3170422)). Qed.
Lemma lem3170424 (n : int) (h1 : term199 n) : term124 n.
Proof. exact (EQ_MP (@lem3170423 n) (@lem3170418 n h1)). Qed.
Lemma lem3170425 (n : int) (h1 : term199 n) : term224 n.
Proof. exact (conj (@lem3170424 n h1) (@lem3170350 n h1)). Qed.
Lemma lem3170427 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3170428 (n : int) : term226 n.
Proof. exact (@lem3170427 (term120 n) (real_of_int n)). Qed.
Lemma lem3170429 (n : int) (h1 : term199 n) : term227 n.
Proof. exact (@lem3170428 n (@lem3170425 n h1)). Qed.
Lemma lem3170430 (n : int) : (term228 n) = (term229 n).
Proof. exact (@lem1982759 (term137 n) (real_of_int n) term96). Qed.
Lemma lem3170431 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982713 term96 (real_of_int n)). Qed.
Lemma lem3170433 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170434 : term35 = term98.
Proof. exact (@lem3170433 term36). Qed.
Lemma lem3170436 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170437 : term96 = term101.
Proof. exact (@lem3170436 term36). Qed.
Lemma lem3170438 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170439 : term232 = term233.
Proof. exact (MK_COMB (@lem3170438) (@lem3170437)). Qed.
Lemma lem3170440 : term234 = term235.
Proof. exact (MK_COMB (@lem3170439) (@lem3170434)). Qed.
Lemma lem3170441 : term236.
Proof. exact (@lem1981473 term96 term35 term35 term35 term42 term35). Qed.
Lemma lem3170443 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170444 : term201 = term207.
Proof. exact (@lem3170443 (NUMERAL 0) term36). Qed.
Lemma lem3170445 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170446 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170447 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170446 h1) (fun h1 : term207 = True => @lem3170445)). Qed.
Lemma lem3170448 : term207 = True.
Proof. exact (EQ_MP (@lem3170447) (@lem3170445)). Qed.
Lemma lem3170449 : term201 = True.
Proof. exact (TRANS (@lem3170444) (@lem3170448)). Qed.
Lemma lem3170450 : True = term201.
Proof. exact (SYM (@lem3170449)). Qed.
Lemma lem3170451 : term201.
Proof. exact (EQ_MP (@lem3170450) (@lem0)). Qed.
Lemma lem3170452 : term237.
Proof. exact (@lem3170441 (@lem3170451)). Qed.
Lemma lem3170454 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170455 : term201 = term207.
Proof. exact (@lem3170454 (NUMERAL 0) term36). Qed.
Lemma lem3170456 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170457 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170458 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170457 h1) (fun h1 : term207 = True => @lem3170456)). Qed.
Lemma lem3170459 : term207 = True.
Proof. exact (EQ_MP (@lem3170458) (@lem3170456)). Qed.
Lemma lem3170460 : term201 = True.
Proof. exact (TRANS (@lem3170455) (@lem3170459)). Qed.
Lemma lem3170461 : True = term201.
Proof. exact (SYM (@lem3170460)). Qed.
Lemma lem3170462 : term201.
Proof. exact (EQ_MP (@lem3170461) (@lem0)). Qed.
Lemma lem3170463 : term238.
Proof. exact (@lem3170452 (@lem3170462)). Qed.
Lemma lem3170465 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170466 : term201 = term207.
Proof. exact (@lem3170465 (NUMERAL 0) term36). Qed.
Lemma lem3170467 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170468 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170469 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170468 h1) (fun h1 : term207 = True => @lem3170467)). Qed.
Lemma lem3170470 : term207 = True.
Proof. exact (EQ_MP (@lem3170469) (@lem3170467)). Qed.
Lemma lem3170471 : term201 = True.
Proof. exact (TRANS (@lem3170466) (@lem3170470)). Qed.
Lemma lem3170472 : True = term201.
Proof. exact (SYM (@lem3170471)). Qed.
Lemma lem3170473 : term201.
Proof. exact (EQ_MP (@lem3170472) (@lem0)). Qed.
Lemma lem3170474 : term239.
Proof. exact (@lem3170463 (@lem3170473)). Qed.
Lemma lem3170476 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170477 : term109 = term110.
Proof. exact (@lem3170476 term36 term36). Qed.
Lemma lem3170478 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170479 : term112 = term36.
Proof. exact (EQ_MP (@lem3170478) (@lem940073)). Qed.
Lemma lem3170480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170481 : term110 = term35.
Proof. exact (MK_COMB (@lem3170480) (@lem3170479)). Qed.
Lemma lem3170482 : term109 = term35.
Proof. exact (TRANS (@lem3170477) (@lem3170481)). Qed.
Lemma lem3170484 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3170485 : term104 = term115.
Proof. exact (@lem3170484 term36 term36). Qed.
Lemma lem3170486 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170487 : term112 = term36.
Proof. exact (EQ_MP (@lem3170486) (@lem940073)). Qed.
Lemma lem3170488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170489 : term110 = term35.
Proof. exact (MK_COMB (@lem3170488) (@lem3170487)). Qed.
Lemma lem3170490 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3170491 : term115 = term96.
Proof. exact (MK_COMB (@lem3170490) (@lem3170489)). Qed.
Lemma lem3170492 : term104 = term96.
Proof. exact (TRANS (@lem3170485) (@lem3170491)). Qed.
Lemma lem3170493 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170494 : term240 = term232.
Proof. exact (MK_COMB (@lem3170493) (@lem3170492)). Qed.
Lemma lem3170495 : term241 = term234.
Proof. exact (MK_COMB (@lem3170494) (@lem3170482)). Qed.
Lemma lem3170497 (m : nat) : (term242 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3170498 : term234 = term42.
Proof. exact (@lem3170497 term36). Qed.
Lemma lem3170499 : term241 = term42.
Proof. exact (TRANS (@lem3170495) (@lem3170498)). Qed.
Lemma lem3170500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170501 : term243 = term244.
Proof. exact (MK_COMB (@lem3170500) (@lem3170499)). Qed.
Lemma lem3170502 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3170503 : term245 = term212.
Proof. exact (MK_COMB (@lem3170501) (@lem3170502)). Qed.
Lemma lem3170505 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170506 : term212 = term42.
Proof. exact (@lem3170505 term36). Qed.
Lemma lem3170507 : term245 = term42.
Proof. exact (TRANS (@lem3170503) (@lem3170506)). Qed.
Lemma lem3170509 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170510 : term109 = term110.
Proof. exact (@lem3170509 term36 term36). Qed.
Lemma lem3170511 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170512 : term112 = term36.
Proof. exact (EQ_MP (@lem3170511) (@lem940073)). Qed.
Lemma lem3170513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170514 : term110 = term35.
Proof. exact (MK_COMB (@lem3170513) (@lem3170512)). Qed.
Lemma lem3170515 : term109 = term35.
Proof. exact (TRANS (@lem3170510) (@lem3170514)). Qed.
Lemma lem3170516 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3170517 : term246 = term212.
Proof. exact (MK_COMB (@lem3170516) (@lem3170515)). Qed.
Lemma lem3170519 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170520 : term212 = term42.
Proof. exact (@lem3170519 term36). Qed.
Lemma lem3170521 : term246 = term42.
Proof. exact (TRANS (@lem3170517) (@lem3170520)). Qed.
Lemma lem3170522 : term42 = term246.
Proof. exact (SYM (@lem3170521)). Qed.
Lemma lem3170523 : term245 = term246.
Proof. exact (TRANS (@lem3170507) (@lem3170522)). Qed.
Lemma lem3170524 : term235 = term143.
Proof. exact (@lem3170474 (@lem3170523)). Qed.
Lemma lem3170525 : term234 = term143.
Proof. exact (TRANS (@lem3170440) (@lem3170524)). Qed.
Lemma lem3170527 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3170528 : term143 = term42.
Proof. exact (@lem3170527 term42). Qed.
Lemma lem3170529 : term234 = term42.
Proof. exact (TRANS (@lem3170525) (@lem3170528)). Qed.
Lemma lem3170530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170531 : term247 = term244.
Proof. exact (MK_COMB (@lem3170530) (@lem3170529)). Qed.
Lemma lem3170532 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3170533 (n : int) : (term231 n) = (term248 n).
Proof. exact (MK_COMB (@lem3170531) (@lem3170532 n)). Qed.
Lemma lem3170534 (n : int) : (term230 n) = (term248 n).
Proof. exact (TRANS (@lem3170431 n) (@lem3170533 n)). Qed.
Lemma lem3170535 (n : int) : (term248 n) = term42.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem3170536 (n : int) : (term230 n) = term42.
Proof. exact (TRANS (@lem3170534 n) (@lem3170535 n)). Qed.
Lemma lem3170537 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170538 (n : int) : (term249 n) = term52.
Proof. exact (MK_COMB (@lem3170537) (@lem3170536 n)). Qed.
Lemma lem3170539 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem3170540 (n : int) : (term229 n) = term250.
Proof. exact (MK_COMB (@lem3170538 n) (@lem3170539)). Qed.
Lemma lem3170541 (n : int) : (term228 n) = term250.
Proof. exact (TRANS (@lem3170430 n) (@lem3170540 n)). Qed.
Lemma lem3170542 : term250 = term96.
Proof. exact (@lem1982721 term96). Qed.
Lemma lem3170543 (n : int) : (term228 n) = term96.
Proof. exact (TRANS (@lem3170541 n) (@lem3170542)). Qed.
Lemma lem3170544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170545 (n : int) : (term251 n) = term252.
Proof. exact (MK_COMB (@lem3170544) (@lem3170543 n)). Qed.
Lemma lem3170546 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170547 (n : int) : (term227 n) = term253.
Proof. exact (MK_COMB (@lem3170545 n) (@lem3170546)). Qed.
Lemma lem3170548 (n : int) (h1 : term199 n) : term253.
Proof. exact (EQ_MP (@lem3170547 n) (@lem3170429 n h1)). Qed.
Lemma lem3170550 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3170551 : term253 = term254.
Proof. exact (@lem3170550 term42 term96). Qed.
Lemma lem3170553 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170554 : term96 = term101.
Proof. exact (@lem3170553 term36). Qed.
Lemma lem3170556 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170557 : term42 = term143.
Proof. exact (@lem3170556 (NUMERAL 0)). Qed.
Lemma lem3170558 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3170559 : term60 = term255.
Proof. exact (MK_COMB (@lem3170558) (@lem3170557)). Qed.
Lemma lem3170560 : term254 = term256.
Proof. exact (MK_COMB (@lem3170559) (@lem3170554)). Qed.
Lemma lem3170561 : term257.
Proof. exact (@lem1980026 term42 term35 term96 term35). Qed.
Lemma lem3170563 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170564 : term201 = term207.
Proof. exact (@lem3170563 (NUMERAL 0) term36). Qed.
Lemma lem3170565 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170566 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170567 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170566 h1) (fun h1 : term207 = True => @lem3170565)). Qed.
Lemma lem3170568 : term207 = True.
Proof. exact (EQ_MP (@lem3170567) (@lem3170565)). Qed.
Lemma lem3170569 : term201 = True.
Proof. exact (TRANS (@lem3170564) (@lem3170568)). Qed.
Lemma lem3170570 : True = term201.
Proof. exact (SYM (@lem3170569)). Qed.
Lemma lem3170571 : term201.
Proof. exact (EQ_MP (@lem3170570) (@lem0)). Qed.
Lemma lem3170572 : term258.
Proof. exact (@lem3170561 (@lem3170571)). Qed.
Lemma lem3170574 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170575 : term201 = term207.
Proof. exact (@lem3170574 (NUMERAL 0) term36). Qed.
Lemma lem3170576 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170577 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170578 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170577 h1) (fun h1 : term207 = True => @lem3170576)). Qed.
Lemma lem3170579 : term207 = True.
Proof. exact (EQ_MP (@lem3170578) (@lem3170576)). Qed.
Lemma lem3170580 : term201 = True.
Proof. exact (TRANS (@lem3170575) (@lem3170579)). Qed.
Lemma lem3170581 : True = term201.
Proof. exact (SYM (@lem3170580)). Qed.
Lemma lem3170582 : term201.
Proof. exact (EQ_MP (@lem3170581) (@lem0)). Qed.
Lemma lem3170583 : term256 = term259.
Proof. exact (@lem3170572 (@lem3170582)). Qed.
Lemma lem3170585 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3170586 : term104 = term115.
Proof. exact (@lem3170585 term36 term36). Qed.
Lemma lem3170587 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170588 : term112 = term36.
Proof. exact (EQ_MP (@lem3170587) (@lem940073)). Qed.
Lemma lem3170589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170590 : term110 = term35.
Proof. exact (MK_COMB (@lem3170589) (@lem3170588)). Qed.
Lemma lem3170591 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3170592 : term115 = term96.
Proof. exact (MK_COMB (@lem3170591) (@lem3170590)). Qed.
Lemma lem3170593 : term104 = term96.
Proof. exact (TRANS (@lem3170586) (@lem3170592)). Qed.
Lemma lem3170595 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170596 : term212 = term42.
Proof. exact (@lem3170595 term36). Qed.
Lemma lem3170597 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3170598 : term260 = term60.
Proof. exact (MK_COMB (@lem3170597) (@lem3170596)). Qed.
Lemma lem3170599 : term259 = term254.
Proof. exact (MK_COMB (@lem3170598) (@lem3170593)). Qed.
Lemma lem3170601 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3170602 : term254 = term263.
Proof. exact (@lem3170601 (NUMERAL 0) term36). Qed.
Lemma lem3170603 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170604 (h1 : term208 = (BIT1 0)) : (term36 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3170605 : (term208 = (BIT1 0)) = ((term36 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170604 h1) (fun h1 : (term36 = (NUMERAL 0)) = False => @lem3170603)). Qed.
Lemma lem3170606 : (term36 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3170605) (@lem3170603)). Qed.
Lemma lem3170607 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3170608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3170609 : term264 = (and True).
Proof. exact (MK_COMB (@lem3170608) (@lem3170607)). Qed.
Lemma lem3170610 : term263 = (True /\ False).
Proof. exact (MK_COMB (@lem3170609) (@lem3170606)). Qed.
Lemma lem3170612 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3170613 : term263 = False.
Proof. exact (TRANS (@lem3170610) (@lem3170612)). Qed.
Lemma lem3170614 : term254 = False.
Proof. exact (TRANS (@lem3170602) (@lem3170613)). Qed.
Lemma lem3170615 : term259 = False.
Proof. exact (TRANS (@lem3170599) (@lem3170614)). Qed.
Lemma lem3170616 : term256 = False.
Proof. exact (TRANS (@lem3170583) (@lem3170615)). Qed.
Lemma lem3170617 : term254 = False.
Proof. exact (TRANS (@lem3170560) (@lem3170616)). Qed.
Lemma lem3170618 : term253 = False.
Proof. exact (TRANS (@lem3170551) (@lem3170617)). Qed.
Lemma lem3170619 (n : int) (h1 : term199 n) : False.
Proof. exact (EQ_MP (@lem3170618) (@lem3170548 n h1)). Qed.
Lemma lem3170620 (n : int) (h1 : term265 n) : term265 n.
Proof. exact (h1). Qed.
Lemma lem3170621 (n : int) (h1 : term265 n) : term162 n.
Proof. exact (proj2 (@lem3170620 n h1)). Qed.
Lemma lem3170622 (n : int) (h1 : term265 n) : term133 n.
Proof. exact (proj1 (@lem3170620 n h1)). Qed.
Lemma lem3170624 (n : int) (h1 : term265 n) : term153 n.
Proof. exact (proj1 (@lem3170621 n h1)). Qed.
Lemma lem3170626 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3170627 : term200 = term201.
Proof. exact (@lem3170626 term42 term35). Qed.
Lemma lem3170629 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170630 : term35 = term98.
Proof. exact (@lem3170629 term36). Qed.
Lemma lem3170632 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170633 : term42 = term143.
Proof. exact (@lem3170632 (NUMERAL 0)). Qed.
Lemma lem3170634 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170635 : term202 = term203.
Proof. exact (MK_COMB (@lem3170634) (@lem3170633)). Qed.
Lemma lem3170636 : term201 = term204.
Proof. exact (MK_COMB (@lem3170635) (@lem3170630)). Qed.
Lemma lem3170637 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3170639 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170640 : term201 = term207.
Proof. exact (@lem3170639 (NUMERAL 0) term36). Qed.
Lemma lem3170641 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170642 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170643 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170642 h1) (fun h1 : term207 = True => @lem3170641)). Qed.
Lemma lem3170644 : term207 = True.
Proof. exact (EQ_MP (@lem3170643) (@lem3170641)). Qed.
Lemma lem3170645 : term201 = True.
Proof. exact (TRANS (@lem3170640) (@lem3170644)). Qed.
Lemma lem3170646 : True = term201.
Proof. exact (SYM (@lem3170645)). Qed.
Lemma lem3170647 : term201.
Proof. exact (EQ_MP (@lem3170646) (@lem0)). Qed.
Lemma lem3170648 : term209.
Proof. exact (@lem3170637 (@lem3170647)). Qed.
Lemma lem3170650 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170651 : term201 = term207.
Proof. exact (@lem3170650 (NUMERAL 0) term36). Qed.
Lemma lem3170652 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170653 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170654 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170653 h1) (fun h1 : term207 = True => @lem3170652)). Qed.
Lemma lem3170655 : term207 = True.
Proof. exact (EQ_MP (@lem3170654) (@lem3170652)). Qed.
Lemma lem3170656 : term201 = True.
Proof. exact (TRANS (@lem3170651) (@lem3170655)). Qed.
Lemma lem3170657 : True = term201.
Proof. exact (SYM (@lem3170656)). Qed.
Lemma lem3170658 : term201.
Proof. exact (EQ_MP (@lem3170657) (@lem0)). Qed.
Lemma lem3170659 : term204 = term210.
Proof. exact (@lem3170648 (@lem3170658)). Qed.
Lemma lem3170661 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170662 : term109 = term110.
Proof. exact (@lem3170661 term36 term36). Qed.
Lemma lem3170663 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170664 : term112 = term36.
Proof. exact (EQ_MP (@lem3170663) (@lem940073)). Qed.
Lemma lem3170665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170666 : term110 = term35.
Proof. exact (MK_COMB (@lem3170665) (@lem3170664)). Qed.
Lemma lem3170667 : term109 = term35.
Proof. exact (TRANS (@lem3170662) (@lem3170666)). Qed.
Lemma lem3170669 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170670 : term212 = term42.
Proof. exact (@lem3170669 term36). Qed.
Lemma lem3170671 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170672 : term213 = term202.
Proof. exact (MK_COMB (@lem3170671) (@lem3170670)). Qed.
Lemma lem3170673 : term210 = term201.
Proof. exact (MK_COMB (@lem3170672) (@lem3170667)). Qed.
Lemma lem3170675 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170676 : term201 = term207.
Proof. exact (@lem3170675 (NUMERAL 0) term36). Qed.
Lemma lem3170677 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170678 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170679 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170678 h1) (fun h1 : term207 = True => @lem3170677)). Qed.
Lemma lem3170680 : term207 = True.
Proof. exact (EQ_MP (@lem3170679) (@lem3170677)). Qed.
Lemma lem3170681 : term201 = True.
Proof. exact (TRANS (@lem3170676) (@lem3170680)). Qed.
Lemma lem3170682 : term210 = True.
Proof. exact (TRANS (@lem3170673) (@lem3170681)). Qed.
Lemma lem3170683 : term204 = True.
Proof. exact (TRANS (@lem3170659) (@lem3170682)). Qed.
Lemma lem3170684 : term201 = True.
Proof. exact (TRANS (@lem3170636) (@lem3170683)). Qed.
Lemma lem3170685 : term200 = True.
Proof. exact (TRANS (@lem3170627) (@lem3170684)). Qed.
Lemma lem3170686 : True = term200.
Proof. exact (SYM (@lem3170685)). Qed.
Lemma lem3170687 : term200.
Proof. exact (EQ_MP (@lem3170686) (@lem0)). Qed.
Lemma lem3170688 (n : int) (h1 : term265 n) : term266 n.
Proof. exact (conj (@lem3170687) (@lem3170622 n h1)). Qed.
Lemma lem3170690 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3170691 (n : int) : term267 n.
Proof. exact (@lem3170690 term35 (term130 n)). Qed.
Lemma lem3170692 (n : int) (h1 : term265 n) : term268 n.
Proof. exact (@lem3170691 n (@lem3170688 n h1)). Qed.
Lemma lem3170693 (n : int) : (term269 n) = (term130 n).
Proof. exact (@lem1982733 (term130 n)). Qed.
Lemma lem3170694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170695 (n : int) : (term270 n) = (term132 n).
Proof. exact (MK_COMB (@lem3170694) (@lem3170693 n)). Qed.
Lemma lem3170696 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170697 (n : int) : (term268 n) = (term133 n).
Proof. exact (MK_COMB (@lem3170695 n) (@lem3170696)). Qed.
Lemma lem3170698 (n : int) (h1 : term265 n) : term133 n.
Proof. exact (EQ_MP (@lem3170697 n) (@lem3170692 n h1)). Qed.
Lemma lem3170700 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3170701 : term200 = term201.
Proof. exact (@lem3170700 term42 term35). Qed.
Lemma lem3170703 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170704 : term35 = term98.
Proof. exact (@lem3170703 term36). Qed.
Lemma lem3170706 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170707 : term42 = term143.
Proof. exact (@lem3170706 (NUMERAL 0)). Qed.
Lemma lem3170708 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170709 : term202 = term203.
Proof. exact (MK_COMB (@lem3170708) (@lem3170707)). Qed.
Lemma lem3170710 : term201 = term204.
Proof. exact (MK_COMB (@lem3170709) (@lem3170704)). Qed.
Lemma lem3170711 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3170713 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170714 : term201 = term207.
Proof. exact (@lem3170713 (NUMERAL 0) term36). Qed.
Lemma lem3170715 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170716 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170717 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170716 h1) (fun h1 : term207 = True => @lem3170715)). Qed.
Lemma lem3170718 : term207 = True.
Proof. exact (EQ_MP (@lem3170717) (@lem3170715)). Qed.
Lemma lem3170719 : term201 = True.
Proof. exact (TRANS (@lem3170714) (@lem3170718)). Qed.
Lemma lem3170720 : True = term201.
Proof. exact (SYM (@lem3170719)). Qed.
Lemma lem3170721 : term201.
Proof. exact (EQ_MP (@lem3170720) (@lem0)). Qed.
Lemma lem3170722 : term209.
Proof. exact (@lem3170711 (@lem3170721)). Qed.
Lemma lem3170724 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170725 : term201 = term207.
Proof. exact (@lem3170724 (NUMERAL 0) term36). Qed.
Lemma lem3170726 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170727 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170728 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170727 h1) (fun h1 : term207 = True => @lem3170726)). Qed.
Lemma lem3170729 : term207 = True.
Proof. exact (EQ_MP (@lem3170728) (@lem3170726)). Qed.
Lemma lem3170730 : term201 = True.
Proof. exact (TRANS (@lem3170725) (@lem3170729)). Qed.
Lemma lem3170731 : True = term201.
Proof. exact (SYM (@lem3170730)). Qed.
Lemma lem3170732 : term201.
Proof. exact (EQ_MP (@lem3170731) (@lem0)). Qed.
Lemma lem3170733 : term204 = term210.
Proof. exact (@lem3170722 (@lem3170732)). Qed.
Lemma lem3170735 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170736 : term109 = term110.
Proof. exact (@lem3170735 term36 term36). Qed.
Lemma lem3170737 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170738 : term112 = term36.
Proof. exact (EQ_MP (@lem3170737) (@lem940073)). Qed.
Lemma lem3170739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170740 : term110 = term35.
Proof. exact (MK_COMB (@lem3170739) (@lem3170738)). Qed.
Lemma lem3170741 : term109 = term35.
Proof. exact (TRANS (@lem3170736) (@lem3170740)). Qed.
Lemma lem3170743 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170744 : term212 = term42.
Proof. exact (@lem3170743 term36). Qed.
Lemma lem3170745 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170746 : term213 = term202.
Proof. exact (MK_COMB (@lem3170745) (@lem3170744)). Qed.
Lemma lem3170747 : term210 = term201.
Proof. exact (MK_COMB (@lem3170746) (@lem3170741)). Qed.
Lemma lem3170749 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170750 : term201 = term207.
Proof. exact (@lem3170749 (NUMERAL 0) term36). Qed.
Lemma lem3170751 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170752 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170753 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170752 h1) (fun h1 : term207 = True => @lem3170751)). Qed.
Lemma lem3170754 : term207 = True.
Proof. exact (EQ_MP (@lem3170753) (@lem3170751)). Qed.
Lemma lem3170755 : term201 = True.
Proof. exact (TRANS (@lem3170750) (@lem3170754)). Qed.
Lemma lem3170756 : term210 = True.
Proof. exact (TRANS (@lem3170747) (@lem3170755)). Qed.
Lemma lem3170757 : term204 = True.
Proof. exact (TRANS (@lem3170733) (@lem3170756)). Qed.
Lemma lem3170758 : term201 = True.
Proof. exact (TRANS (@lem3170710) (@lem3170757)). Qed.
Lemma lem3170759 : term200 = True.
Proof. exact (TRANS (@lem3170701) (@lem3170758)). Qed.
Lemma lem3170760 : True = term200.
Proof. exact (SYM (@lem3170759)). Qed.
Lemma lem3170761 : term200.
Proof. exact (EQ_MP (@lem3170760) (@lem0)). Qed.
Lemma lem3170762 (n : int) (h1 : term265 n) : term271 n.
Proof. exact (conj (@lem3170761) (@lem3170624 n h1)). Qed.
Lemma lem3170764 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3170765 (n : int) : term272 n.
Proof. exact (@lem3170764 term35 (term137 n)). Qed.
Lemma lem3170766 (n : int) (h1 : term265 n) : term273 n.
Proof. exact (@lem3170765 n (@lem3170762 n h1)). Qed.
Lemma lem3170767 (n : int) : (term274 n) = (term137 n).
Proof. exact (@lem1982733 (term137 n)). Qed.
Lemma lem3170768 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170769 (n : int) : (term275 n) = (term152 n).
Proof. exact (MK_COMB (@lem3170768) (@lem3170767 n)). Qed.
Lemma lem3170770 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170771 (n : int) : (term273 n) = (term153 n).
Proof. exact (MK_COMB (@lem3170769 n) (@lem3170770)). Qed.
Lemma lem3170772 (n : int) (h1 : term265 n) : term153 n.
Proof. exact (EQ_MP (@lem3170771 n) (@lem3170766 n h1)). Qed.
Lemma lem3170773 (n : int) (h1 : term265 n) : term276 n.
Proof. exact (conj (@lem3170772 n h1) (@lem3170698 n h1)). Qed.
Lemma lem3170775 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3170776 (n : int) : term277 n.
Proof. exact (@lem3170775 (term137 n) (term130 n)). Qed.
Lemma lem3170777 (n : int) (h1 : term265 n) : term278 n.
Proof. exact (@lem3170776 n (@lem3170773 n h1)). Qed.
Lemma lem3170778 (n : int) : (term279 n) = (term229 n).
Proof. exact (@lem1982763 (term137 n) (real_of_int n) term96). Qed.
Lemma lem3170779 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982713 term96 (real_of_int n)). Qed.
Lemma lem3170781 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170782 : term35 = term98.
Proof. exact (@lem3170781 term36). Qed.
Lemma lem3170784 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170785 : term96 = term101.
Proof. exact (@lem3170784 term36). Qed.
Lemma lem3170786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170787 : term232 = term233.
Proof. exact (MK_COMB (@lem3170786) (@lem3170785)). Qed.
Lemma lem3170788 : term234 = term235.
Proof. exact (MK_COMB (@lem3170787) (@lem3170782)). Qed.
Lemma lem3170789 : term236.
Proof. exact (@lem1981473 term96 term35 term35 term35 term42 term35). Qed.
Lemma lem3170791 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170792 : term201 = term207.
Proof. exact (@lem3170791 (NUMERAL 0) term36). Qed.
Lemma lem3170793 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170794 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170795 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170794 h1) (fun h1 : term207 = True => @lem3170793)). Qed.
Lemma lem3170796 : term207 = True.
Proof. exact (EQ_MP (@lem3170795) (@lem3170793)). Qed.
Lemma lem3170797 : term201 = True.
Proof. exact (TRANS (@lem3170792) (@lem3170796)). Qed.
Lemma lem3170798 : True = term201.
Proof. exact (SYM (@lem3170797)). Qed.
Lemma lem3170799 : term201.
Proof. exact (EQ_MP (@lem3170798) (@lem0)). Qed.
Lemma lem3170800 : term237.
Proof. exact (@lem3170789 (@lem3170799)). Qed.
Lemma lem3170802 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170803 : term201 = term207.
Proof. exact (@lem3170802 (NUMERAL 0) term36). Qed.
Lemma lem3170804 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170805 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170806 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170805 h1) (fun h1 : term207 = True => @lem3170804)). Qed.
Lemma lem3170807 : term207 = True.
Proof. exact (EQ_MP (@lem3170806) (@lem3170804)). Qed.
Lemma lem3170808 : term201 = True.
Proof. exact (TRANS (@lem3170803) (@lem3170807)). Qed.
Lemma lem3170809 : True = term201.
Proof. exact (SYM (@lem3170808)). Qed.
Lemma lem3170810 : term201.
Proof. exact (EQ_MP (@lem3170809) (@lem0)). Qed.
Lemma lem3170811 : term238.
Proof. exact (@lem3170800 (@lem3170810)). Qed.
Lemma lem3170813 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170814 : term201 = term207.
Proof. exact (@lem3170813 (NUMERAL 0) term36). Qed.
Lemma lem3170815 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170816 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170817 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170816 h1) (fun h1 : term207 = True => @lem3170815)). Qed.
Lemma lem3170818 : term207 = True.
Proof. exact (EQ_MP (@lem3170817) (@lem3170815)). Qed.
Lemma lem3170819 : term201 = True.
Proof. exact (TRANS (@lem3170814) (@lem3170818)). Qed.
Lemma lem3170820 : True = term201.
Proof. exact (SYM (@lem3170819)). Qed.
Lemma lem3170821 : term201.
Proof. exact (EQ_MP (@lem3170820) (@lem0)). Qed.
Lemma lem3170822 : term239.
Proof. exact (@lem3170811 (@lem3170821)). Qed.
Lemma lem3170824 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170825 : term109 = term110.
Proof. exact (@lem3170824 term36 term36). Qed.
Lemma lem3170826 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170827 : term112 = term36.
Proof. exact (EQ_MP (@lem3170826) (@lem940073)). Qed.
Lemma lem3170828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170829 : term110 = term35.
Proof. exact (MK_COMB (@lem3170828) (@lem3170827)). Qed.
Lemma lem3170830 : term109 = term35.
Proof. exact (TRANS (@lem3170825) (@lem3170829)). Qed.
Lemma lem3170832 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3170833 : term104 = term115.
Proof. exact (@lem3170832 term36 term36). Qed.
Lemma lem3170834 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170835 : term112 = term36.
Proof. exact (EQ_MP (@lem3170834) (@lem940073)). Qed.
Lemma lem3170836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170837 : term110 = term35.
Proof. exact (MK_COMB (@lem3170836) (@lem3170835)). Qed.
Lemma lem3170838 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3170839 : term115 = term96.
Proof. exact (MK_COMB (@lem3170838) (@lem3170837)). Qed.
Lemma lem3170840 : term104 = term96.
Proof. exact (TRANS (@lem3170833) (@lem3170839)). Qed.
Lemma lem3170841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170842 : term240 = term232.
Proof. exact (MK_COMB (@lem3170841) (@lem3170840)). Qed.
Lemma lem3170843 : term241 = term234.
Proof. exact (MK_COMB (@lem3170842) (@lem3170830)). Qed.
Lemma lem3170845 (m : nat) : (term242 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3170846 : term234 = term42.
Proof. exact (@lem3170845 term36). Qed.
Lemma lem3170847 : term241 = term42.
Proof. exact (TRANS (@lem3170843) (@lem3170846)). Qed.
Lemma lem3170848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170849 : term243 = term244.
Proof. exact (MK_COMB (@lem3170848) (@lem3170847)). Qed.
Lemma lem3170850 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3170851 : term245 = term212.
Proof. exact (MK_COMB (@lem3170849) (@lem3170850)). Qed.
Lemma lem3170853 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170854 : term212 = term42.
Proof. exact (@lem3170853 term36). Qed.
Lemma lem3170855 : term245 = term42.
Proof. exact (TRANS (@lem3170851) (@lem3170854)). Qed.
Lemma lem3170857 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3170858 : term109 = term110.
Proof. exact (@lem3170857 term36 term36). Qed.
Lemma lem3170859 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170860 : term112 = term36.
Proof. exact (EQ_MP (@lem3170859) (@lem940073)). Qed.
Lemma lem3170861 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170862 : term110 = term35.
Proof. exact (MK_COMB (@lem3170861) (@lem3170860)). Qed.
Lemma lem3170863 : term109 = term35.
Proof. exact (TRANS (@lem3170858) (@lem3170862)). Qed.
Lemma lem3170864 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3170865 : term246 = term212.
Proof. exact (MK_COMB (@lem3170864) (@lem3170863)). Qed.
Lemma lem3170867 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170868 : term212 = term42.
Proof. exact (@lem3170867 term36). Qed.
Lemma lem3170869 : term246 = term42.
Proof. exact (TRANS (@lem3170865) (@lem3170868)). Qed.
Lemma lem3170870 : term42 = term246.
Proof. exact (SYM (@lem3170869)). Qed.
Lemma lem3170871 : term245 = term246.
Proof. exact (TRANS (@lem3170855) (@lem3170870)). Qed.
Lemma lem3170872 : term235 = term143.
Proof. exact (@lem3170822 (@lem3170871)). Qed.
Lemma lem3170873 : term234 = term143.
Proof. exact (TRANS (@lem3170788) (@lem3170872)). Qed.
Lemma lem3170875 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3170876 : term143 = term42.
Proof. exact (@lem3170875 term42). Qed.
Lemma lem3170877 : term234 = term42.
Proof. exact (TRANS (@lem3170873) (@lem3170876)). Qed.
Lemma lem3170878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3170879 : term247 = term244.
Proof. exact (MK_COMB (@lem3170878) (@lem3170877)). Qed.
Lemma lem3170880 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3170881 (n : int) : (term231 n) = (term248 n).
Proof. exact (MK_COMB (@lem3170879) (@lem3170880 n)). Qed.
Lemma lem3170882 (n : int) : (term230 n) = (term248 n).
Proof. exact (TRANS (@lem3170779 n) (@lem3170881 n)). Qed.
Lemma lem3170883 (n : int) : (term248 n) = term42.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem3170884 (n : int) : (term230 n) = term42.
Proof. exact (TRANS (@lem3170882 n) (@lem3170883 n)). Qed.
Lemma lem3170885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3170886 (n : int) : (term249 n) = term52.
Proof. exact (MK_COMB (@lem3170885) (@lem3170884 n)). Qed.
Lemma lem3170887 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem3170888 (n : int) : (term229 n) = term250.
Proof. exact (MK_COMB (@lem3170886 n) (@lem3170887)). Qed.
Lemma lem3170889 (n : int) : (term279 n) = term250.
Proof. exact (TRANS (@lem3170778 n) (@lem3170888 n)). Qed.
Lemma lem3170890 : term250 = term96.
Proof. exact (@lem1982721 term96). Qed.
Lemma lem3170891 (n : int) : (term279 n) = term96.
Proof. exact (TRANS (@lem3170889 n) (@lem3170890)). Qed.
Lemma lem3170892 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3170893 (n : int) : (term280 n) = term252.
Proof. exact (MK_COMB (@lem3170892) (@lem3170891 n)). Qed.
Lemma lem3170894 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3170895 (n : int) : (term278 n) = term253.
Proof. exact (MK_COMB (@lem3170893 n) (@lem3170894)). Qed.
Lemma lem3170896 (n : int) (h1 : term265 n) : term253.
Proof. exact (EQ_MP (@lem3170895 n) (@lem3170777 n h1)). Qed.
Lemma lem3170898 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3170899 : term253 = term254.
Proof. exact (@lem3170898 term42 term96). Qed.
Lemma lem3170901 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3170902 : term96 = term101.
Proof. exact (@lem3170901 term36). Qed.
Lemma lem3170904 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170905 : term42 = term143.
Proof. exact (@lem3170904 (NUMERAL 0)). Qed.
Lemma lem3170906 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3170907 : term60 = term255.
Proof. exact (MK_COMB (@lem3170906) (@lem3170905)). Qed.
Lemma lem3170908 : term254 = term256.
Proof. exact (MK_COMB (@lem3170907) (@lem3170902)). Qed.
Lemma lem3170909 : term257.
Proof. exact (@lem1980026 term42 term35 term96 term35). Qed.
Lemma lem3170911 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170912 : term201 = term207.
Proof. exact (@lem3170911 (NUMERAL 0) term36). Qed.
Lemma lem3170913 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170914 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170915 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170914 h1) (fun h1 : term207 = True => @lem3170913)). Qed.
Lemma lem3170916 : term207 = True.
Proof. exact (EQ_MP (@lem3170915) (@lem3170913)). Qed.
Lemma lem3170917 : term201 = True.
Proof. exact (TRANS (@lem3170912) (@lem3170916)). Qed.
Lemma lem3170918 : True = term201.
Proof. exact (SYM (@lem3170917)). Qed.
Lemma lem3170919 : term201.
Proof. exact (EQ_MP (@lem3170918) (@lem0)). Qed.
Lemma lem3170920 : term258.
Proof. exact (@lem3170909 (@lem3170919)). Qed.
Lemma lem3170922 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170923 : term201 = term207.
Proof. exact (@lem3170922 (NUMERAL 0) term36). Qed.
Lemma lem3170924 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170925 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170926 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170925 h1) (fun h1 : term207 = True => @lem3170924)). Qed.
Lemma lem3170927 : term207 = True.
Proof. exact (EQ_MP (@lem3170926) (@lem3170924)). Qed.
Lemma lem3170928 : term201 = True.
Proof. exact (TRANS (@lem3170923) (@lem3170927)). Qed.
Lemma lem3170929 : True = term201.
Proof. exact (SYM (@lem3170928)). Qed.
Lemma lem3170930 : term201.
Proof. exact (EQ_MP (@lem3170929) (@lem0)). Qed.
Lemma lem3170931 : term256 = term259.
Proof. exact (@lem3170920 (@lem3170930)). Qed.
Lemma lem3170933 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3170934 : term104 = term115.
Proof. exact (@lem3170933 term36 term36). Qed.
Lemma lem3170935 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3170936 : term112 = term36.
Proof. exact (EQ_MP (@lem3170935) (@lem940073)). Qed.
Lemma lem3170937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3170938 : term110 = term35.
Proof. exact (MK_COMB (@lem3170937) (@lem3170936)). Qed.
Lemma lem3170939 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3170940 : term115 = term96.
Proof. exact (MK_COMB (@lem3170939) (@lem3170938)). Qed.
Lemma lem3170941 : term104 = term96.
Proof. exact (TRANS (@lem3170934) (@lem3170940)). Qed.
Lemma lem3170943 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3170944 : term212 = term42.
Proof. exact (@lem3170943 term36). Qed.
Lemma lem3170945 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3170946 : term260 = term60.
Proof. exact (MK_COMB (@lem3170945) (@lem3170944)). Qed.
Lemma lem3170947 : term259 = term254.
Proof. exact (MK_COMB (@lem3170946) (@lem3170941)). Qed.
Lemma lem3170949 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3170950 : term254 = term263.
Proof. exact (@lem3170949 (NUMERAL 0) term36). Qed.
Lemma lem3170951 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170952 (h1 : term208 = (BIT1 0)) : (term36 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3170953 : (term208 = (BIT1 0)) = ((term36 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170952 h1) (fun h1 : (term36 = (NUMERAL 0)) = False => @lem3170951)). Qed.
Lemma lem3170954 : (term36 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3170953) (@lem3170951)). Qed.
Lemma lem3170955 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3170956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3170957 : term264 = (and True).
Proof. exact (MK_COMB (@lem3170956) (@lem3170955)). Qed.
Lemma lem3170958 : term263 = (True /\ False).
Proof. exact (MK_COMB (@lem3170957) (@lem3170954)). Qed.
Lemma lem3170960 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3170961 : term263 = False.
Proof. exact (TRANS (@lem3170958) (@lem3170960)). Qed.
Lemma lem3170962 : term254 = False.
Proof. exact (TRANS (@lem3170950) (@lem3170961)). Qed.
Lemma lem3170963 : term259 = False.
Proof. exact (TRANS (@lem3170947) (@lem3170962)). Qed.
Lemma lem3170964 : term256 = False.
Proof. exact (TRANS (@lem3170931) (@lem3170963)). Qed.
Lemma lem3170965 : term254 = False.
Proof. exact (TRANS (@lem3170908) (@lem3170964)). Qed.
Lemma lem3170966 : term253 = False.
Proof. exact (TRANS (@lem3170899) (@lem3170965)). Qed.
Lemma lem3170967 (n : int) (h1 : term265 n) : False.
Proof. exact (EQ_MP (@lem3170966) (@lem3170896 n h1)). Qed.
Lemma lem3170968 (n : int) (h1 : term195 n) : False.
Proof. exact (or_elim (@lem3170271 n h1) (fun h0 : term199 n => @lem3170619 n h0) (fun h0 : term265 n => @lem3170967 n h0)). Qed.
Lemma lem3170969 (n : int) (h1 : term193 n) : term193 n.
Proof. exact (h1). Qed.
Lemma lem3170970 (n : int) (h1 : term281 n) : term281 n.
Proof. exact (h1). Qed.
Lemma lem3170971 (n : int) (h1 : term281 n) : term186 n.
Proof. exact (proj2 (@lem3170970 n h1)). Qed.
Lemma lem3170973 (n : int) (h1 : term281 n) : term124 n.
Proof. exact (proj2 (@lem3170971 n h1)). Qed.
Lemma lem3170974 (n : int) (h1 : term281 n) : term133 n.
Proof. exact (proj1 (@lem3170971 n h1)). Qed.
Lemma lem3170976 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3170977 : term200 = term201.
Proof. exact (@lem3170976 term42 term35). Qed.
Lemma lem3170979 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170980 : term35 = term98.
Proof. exact (@lem3170979 term36). Qed.
Lemma lem3170982 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3170983 : term42 = term143.
Proof. exact (@lem3170982 (NUMERAL 0)). Qed.
Lemma lem3170984 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3170985 : term202 = term203.
Proof. exact (MK_COMB (@lem3170984) (@lem3170983)). Qed.
Lemma lem3170986 : term201 = term204.
Proof. exact (MK_COMB (@lem3170985) (@lem3170980)). Qed.
Lemma lem3170987 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3170989 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3170990 : term201 = term207.
Proof. exact (@lem3170989 (NUMERAL 0) term36). Qed.
Lemma lem3170991 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3170992 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3170993 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3170992 h1) (fun h1 : term207 = True => @lem3170991)). Qed.
Lemma lem3170994 : term207 = True.
Proof. exact (EQ_MP (@lem3170993) (@lem3170991)). Qed.
Lemma lem3170995 : term201 = True.
Proof. exact (TRANS (@lem3170990) (@lem3170994)). Qed.
Lemma lem3170996 : True = term201.
Proof. exact (SYM (@lem3170995)). Qed.
Lemma lem3170997 : term201.
Proof. exact (EQ_MP (@lem3170996) (@lem0)). Qed.
Lemma lem3170998 : term209.
Proof. exact (@lem3170987 (@lem3170997)). Qed.
Lemma lem3171000 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171001 : term201 = term207.
Proof. exact (@lem3171000 (NUMERAL 0) term36). Qed.
Lemma lem3171002 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171003 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171004 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171003 h1) (fun h1 : term207 = True => @lem3171002)). Qed.
Lemma lem3171005 : term207 = True.
Proof. exact (EQ_MP (@lem3171004) (@lem3171002)). Qed.
Lemma lem3171006 : term201 = True.
Proof. exact (TRANS (@lem3171001) (@lem3171005)). Qed.
Lemma lem3171007 : True = term201.
Proof. exact (SYM (@lem3171006)). Qed.
Lemma lem3171008 : term201.
Proof. exact (EQ_MP (@lem3171007) (@lem0)). Qed.
Lemma lem3171009 : term204 = term210.
Proof. exact (@lem3170998 (@lem3171008)). Qed.
Lemma lem3171011 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171012 : term109 = term110.
Proof. exact (@lem3171011 term36 term36). Qed.
Lemma lem3171013 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171014 : term112 = term36.
Proof. exact (EQ_MP (@lem3171013) (@lem940073)). Qed.
Lemma lem3171015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171016 : term110 = term35.
Proof. exact (MK_COMB (@lem3171015) (@lem3171014)). Qed.
Lemma lem3171017 : term109 = term35.
Proof. exact (TRANS (@lem3171012) (@lem3171016)). Qed.
Lemma lem3171019 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171020 : term212 = term42.
Proof. exact (@lem3171019 term36). Qed.
Lemma lem3171021 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171022 : term213 = term202.
Proof. exact (MK_COMB (@lem3171021) (@lem3171020)). Qed.
Lemma lem3171023 : term210 = term201.
Proof. exact (MK_COMB (@lem3171022) (@lem3171017)). Qed.
Lemma lem3171025 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171026 : term201 = term207.
Proof. exact (@lem3171025 (NUMERAL 0) term36). Qed.
Lemma lem3171027 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171028 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171029 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171028 h1) (fun h1 : term207 = True => @lem3171027)). Qed.
Lemma lem3171030 : term207 = True.
Proof. exact (EQ_MP (@lem3171029) (@lem3171027)). Qed.
Lemma lem3171031 : term201 = True.
Proof. exact (TRANS (@lem3171026) (@lem3171030)). Qed.
Lemma lem3171032 : term210 = True.
Proof. exact (TRANS (@lem3171023) (@lem3171031)). Qed.
Lemma lem3171033 : term204 = True.
Proof. exact (TRANS (@lem3171009) (@lem3171032)). Qed.
Lemma lem3171034 : term201 = True.
Proof. exact (TRANS (@lem3170986) (@lem3171033)). Qed.
Lemma lem3171035 : term200 = True.
Proof. exact (TRANS (@lem3170977) (@lem3171034)). Qed.
Lemma lem3171036 : True = term200.
Proof. exact (SYM (@lem3171035)). Qed.
Lemma lem3171037 : term200.
Proof. exact (EQ_MP (@lem3171036) (@lem0)). Qed.
Lemma lem3171038 (n : int) (h1 : term281 n) : term266 n.
Proof. exact (conj (@lem3171037) (@lem3170974 n h1)). Qed.
Lemma lem3171040 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3171041 (n : int) : term267 n.
Proof. exact (@lem3171040 term35 (term130 n)). Qed.
Lemma lem3171042 (n : int) (h1 : term281 n) : term268 n.
Proof. exact (@lem3171041 n (@lem3171038 n h1)). Qed.
Lemma lem3171043 (n : int) : (term269 n) = (term130 n).
Proof. exact (@lem1982733 (term130 n)). Qed.
Lemma lem3171044 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3171045 (n : int) : (term270 n) = (term132 n).
Proof. exact (MK_COMB (@lem3171044) (@lem3171043 n)). Qed.
Lemma lem3171046 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3171047 (n : int) : (term268 n) = (term133 n).
Proof. exact (MK_COMB (@lem3171045 n) (@lem3171046)). Qed.
Lemma lem3171048 (n : int) (h1 : term281 n) : term133 n.
Proof. exact (EQ_MP (@lem3171047 n) (@lem3171042 n h1)). Qed.
Lemma lem3171050 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3171051 : term200 = term201.
Proof. exact (@lem3171050 term42 term35). Qed.
Lemma lem3171053 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171054 : term35 = term98.
Proof. exact (@lem3171053 term36). Qed.
Lemma lem3171056 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171057 : term42 = term143.
Proof. exact (@lem3171056 (NUMERAL 0)). Qed.
Lemma lem3171058 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171059 : term202 = term203.
Proof. exact (MK_COMB (@lem3171058) (@lem3171057)). Qed.
Lemma lem3171060 : term201 = term204.
Proof. exact (MK_COMB (@lem3171059) (@lem3171054)). Qed.
Lemma lem3171061 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3171063 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171064 : term201 = term207.
Proof. exact (@lem3171063 (NUMERAL 0) term36). Qed.
Lemma lem3171065 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171066 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171067 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171066 h1) (fun h1 : term207 = True => @lem3171065)). Qed.
Lemma lem3171068 : term207 = True.
Proof. exact (EQ_MP (@lem3171067) (@lem3171065)). Qed.
Lemma lem3171069 : term201 = True.
Proof. exact (TRANS (@lem3171064) (@lem3171068)). Qed.
Lemma lem3171070 : True = term201.
Proof. exact (SYM (@lem3171069)). Qed.
Lemma lem3171071 : term201.
Proof. exact (EQ_MP (@lem3171070) (@lem0)). Qed.
Lemma lem3171072 : term209.
Proof. exact (@lem3171061 (@lem3171071)). Qed.
Lemma lem3171074 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171075 : term201 = term207.
Proof. exact (@lem3171074 (NUMERAL 0) term36). Qed.
Lemma lem3171076 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171077 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171078 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171077 h1) (fun h1 : term207 = True => @lem3171076)). Qed.
Lemma lem3171079 : term207 = True.
Proof. exact (EQ_MP (@lem3171078) (@lem3171076)). Qed.
Lemma lem3171080 : term201 = True.
Proof. exact (TRANS (@lem3171075) (@lem3171079)). Qed.
Lemma lem3171081 : True = term201.
Proof. exact (SYM (@lem3171080)). Qed.
Lemma lem3171082 : term201.
Proof. exact (EQ_MP (@lem3171081) (@lem0)). Qed.
Lemma lem3171083 : term204 = term210.
Proof. exact (@lem3171072 (@lem3171082)). Qed.
Lemma lem3171085 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171086 : term109 = term110.
Proof. exact (@lem3171085 term36 term36). Qed.
Lemma lem3171087 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171088 : term112 = term36.
Proof. exact (EQ_MP (@lem3171087) (@lem940073)). Qed.
Lemma lem3171089 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171090 : term110 = term35.
Proof. exact (MK_COMB (@lem3171089) (@lem3171088)). Qed.
Lemma lem3171091 : term109 = term35.
Proof. exact (TRANS (@lem3171086) (@lem3171090)). Qed.
Lemma lem3171093 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171094 : term212 = term42.
Proof. exact (@lem3171093 term36). Qed.
Lemma lem3171095 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171096 : term213 = term202.
Proof. exact (MK_COMB (@lem3171095) (@lem3171094)). Qed.
Lemma lem3171097 : term210 = term201.
Proof. exact (MK_COMB (@lem3171096) (@lem3171091)). Qed.
Lemma lem3171099 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171100 : term201 = term207.
Proof. exact (@lem3171099 (NUMERAL 0) term36). Qed.
Lemma lem3171101 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171102 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171103 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171102 h1) (fun h1 : term207 = True => @lem3171101)). Qed.
Lemma lem3171104 : term207 = True.
Proof. exact (EQ_MP (@lem3171103) (@lem3171101)). Qed.
Lemma lem3171105 : term201 = True.
Proof. exact (TRANS (@lem3171100) (@lem3171104)). Qed.
Lemma lem3171106 : term210 = True.
Proof. exact (TRANS (@lem3171097) (@lem3171105)). Qed.
Lemma lem3171107 : term204 = True.
Proof. exact (TRANS (@lem3171083) (@lem3171106)). Qed.
Lemma lem3171108 : term201 = True.
Proof. exact (TRANS (@lem3171060) (@lem3171107)). Qed.
Lemma lem3171109 : term200 = True.
Proof. exact (TRANS (@lem3171051) (@lem3171108)). Qed.
Lemma lem3171110 : True = term200.
Proof. exact (SYM (@lem3171109)). Qed.
Lemma lem3171111 : term200.
Proof. exact (EQ_MP (@lem3171110) (@lem0)). Qed.
Lemma lem3171112 (n : int) (h1 : term281 n) : term219 n.
Proof. exact (conj (@lem3171111) (@lem3170973 n h1)). Qed.
Lemma lem3171114 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3171115 (n : int) : term220 n.
Proof. exact (@lem3171114 term35 (term120 n)). Qed.
Lemma lem3171116 (n : int) (h1 : term281 n) : term221 n.
Proof. exact (@lem3171115 n (@lem3171112 n h1)). Qed.
Lemma lem3171117 (n : int) : (term222 n) = (term120 n).
Proof. exact (@lem1982733 (term120 n)). Qed.
Lemma lem3171118 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3171119 (n : int) : (term223 n) = (term123 n).
Proof. exact (MK_COMB (@lem3171118) (@lem3171117 n)). Qed.
Lemma lem3171120 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3171121 (n : int) : (term221 n) = (term124 n).
Proof. exact (MK_COMB (@lem3171119 n) (@lem3171120)). Qed.
Lemma lem3171122 (n : int) (h1 : term281 n) : term124 n.
Proof. exact (EQ_MP (@lem3171121 n) (@lem3171116 n h1)). Qed.
Lemma lem3171123 (n : int) (h1 : term281 n) : term282 n.
Proof. exact (conj (@lem3171122 n h1) (@lem3171048 n h1)). Qed.
Lemma lem3171125 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3171126 (n : int) : term283 n.
Proof. exact (@lem3171125 (term120 n) (term130 n)). Qed.
Lemma lem3171127 (n : int) (h1 : term281 n) : term284 n.
Proof. exact (@lem3171126 n (@lem3171123 n h1)). Qed.
Lemma lem3171128 (n : int) : (term285 n) = (term286 n).
Proof. exact (@lem1982753 (term137 n) (real_of_int n) term96 term96). Qed.
Lemma lem3171129 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982713 term96 (real_of_int n)). Qed.
Lemma lem3171131 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171132 : term35 = term98.
Proof. exact (@lem3171131 term36). Qed.
Lemma lem3171134 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171135 : term96 = term101.
Proof. exact (@lem3171134 term36). Qed.
Lemma lem3171136 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171137 : term232 = term233.
Proof. exact (MK_COMB (@lem3171136) (@lem3171135)). Qed.
Lemma lem3171138 : term234 = term235.
Proof. exact (MK_COMB (@lem3171137) (@lem3171132)). Qed.
Lemma lem3171139 : term236.
Proof. exact (@lem1981473 term96 term35 term35 term35 term42 term35). Qed.
Lemma lem3171141 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171142 : term201 = term207.
Proof. exact (@lem3171141 (NUMERAL 0) term36). Qed.
Lemma lem3171143 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171144 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171145 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171144 h1) (fun h1 : term207 = True => @lem3171143)). Qed.
Lemma lem3171146 : term207 = True.
Proof. exact (EQ_MP (@lem3171145) (@lem3171143)). Qed.
Lemma lem3171147 : term201 = True.
Proof. exact (TRANS (@lem3171142) (@lem3171146)). Qed.
Lemma lem3171148 : True = term201.
Proof. exact (SYM (@lem3171147)). Qed.
Lemma lem3171149 : term201.
Proof. exact (EQ_MP (@lem3171148) (@lem0)). Qed.
Lemma lem3171150 : term237.
Proof. exact (@lem3171139 (@lem3171149)). Qed.
Lemma lem3171152 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171153 : term201 = term207.
Proof. exact (@lem3171152 (NUMERAL 0) term36). Qed.
Lemma lem3171154 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171155 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171156 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171155 h1) (fun h1 : term207 = True => @lem3171154)). Qed.
Lemma lem3171157 : term207 = True.
Proof. exact (EQ_MP (@lem3171156) (@lem3171154)). Qed.
Lemma lem3171158 : term201 = True.
Proof. exact (TRANS (@lem3171153) (@lem3171157)). Qed.
Lemma lem3171159 : True = term201.
Proof. exact (SYM (@lem3171158)). Qed.
Lemma lem3171160 : term201.
Proof. exact (EQ_MP (@lem3171159) (@lem0)). Qed.
Lemma lem3171161 : term238.
Proof. exact (@lem3171150 (@lem3171160)). Qed.
Lemma lem3171163 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171164 : term201 = term207.
Proof. exact (@lem3171163 (NUMERAL 0) term36). Qed.
Lemma lem3171165 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171166 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171167 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171166 h1) (fun h1 : term207 = True => @lem3171165)). Qed.
Lemma lem3171168 : term207 = True.
Proof. exact (EQ_MP (@lem3171167) (@lem3171165)). Qed.
Lemma lem3171169 : term201 = True.
Proof. exact (TRANS (@lem3171164) (@lem3171168)). Qed.
Lemma lem3171170 : True = term201.
Proof. exact (SYM (@lem3171169)). Qed.
Lemma lem3171171 : term201.
Proof. exact (EQ_MP (@lem3171170) (@lem0)). Qed.
Lemma lem3171172 : term239.
Proof. exact (@lem3171161 (@lem3171171)). Qed.
Lemma lem3171174 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171175 : term109 = term110.
Proof. exact (@lem3171174 term36 term36). Qed.
Lemma lem3171176 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171177 : term112 = term36.
Proof. exact (EQ_MP (@lem3171176) (@lem940073)). Qed.
Lemma lem3171178 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171179 : term110 = term35.
Proof. exact (MK_COMB (@lem3171178) (@lem3171177)). Qed.
Lemma lem3171180 : term109 = term35.
Proof. exact (TRANS (@lem3171175) (@lem3171179)). Qed.
Lemma lem3171182 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171183 : term104 = term115.
Proof. exact (@lem3171182 term36 term36). Qed.
Lemma lem3171184 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171185 : term112 = term36.
Proof. exact (EQ_MP (@lem3171184) (@lem940073)). Qed.
Lemma lem3171186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171187 : term110 = term35.
Proof. exact (MK_COMB (@lem3171186) (@lem3171185)). Qed.
Lemma lem3171188 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171189 : term115 = term96.
Proof. exact (MK_COMB (@lem3171188) (@lem3171187)). Qed.
Lemma lem3171190 : term104 = term96.
Proof. exact (TRANS (@lem3171183) (@lem3171189)). Qed.
Lemma lem3171191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171192 : term240 = term232.
Proof. exact (MK_COMB (@lem3171191) (@lem3171190)). Qed.
Lemma lem3171193 : term241 = term234.
Proof. exact (MK_COMB (@lem3171192) (@lem3171180)). Qed.
Lemma lem3171195 (m : nat) : (term242 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3171196 : term234 = term42.
Proof. exact (@lem3171195 term36). Qed.
Lemma lem3171197 : term241 = term42.
Proof. exact (TRANS (@lem3171193) (@lem3171196)). Qed.
Lemma lem3171198 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3171199 : term243 = term244.
Proof. exact (MK_COMB (@lem3171198) (@lem3171197)). Qed.
Lemma lem3171200 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3171201 : term245 = term212.
Proof. exact (MK_COMB (@lem3171199) (@lem3171200)). Qed.
Lemma lem3171203 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171204 : term212 = term42.
Proof. exact (@lem3171203 term36). Qed.
Lemma lem3171205 : term245 = term42.
Proof. exact (TRANS (@lem3171201) (@lem3171204)). Qed.
Lemma lem3171207 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171208 : term109 = term110.
Proof. exact (@lem3171207 term36 term36). Qed.
Lemma lem3171209 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171210 : term112 = term36.
Proof. exact (EQ_MP (@lem3171209) (@lem940073)). Qed.
Lemma lem3171211 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171212 : term110 = term35.
Proof. exact (MK_COMB (@lem3171211) (@lem3171210)). Qed.
Lemma lem3171213 : term109 = term35.
Proof. exact (TRANS (@lem3171208) (@lem3171212)). Qed.
Lemma lem3171214 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3171215 : term246 = term212.
Proof. exact (MK_COMB (@lem3171214) (@lem3171213)). Qed.
Lemma lem3171217 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171218 : term212 = term42.
Proof. exact (@lem3171217 term36). Qed.
Lemma lem3171219 : term246 = term42.
Proof. exact (TRANS (@lem3171215) (@lem3171218)). Qed.
Lemma lem3171220 : term42 = term246.
Proof. exact (SYM (@lem3171219)). Qed.
Lemma lem3171221 : term245 = term246.
Proof. exact (TRANS (@lem3171205) (@lem3171220)). Qed.
Lemma lem3171222 : term235 = term143.
Proof. exact (@lem3171172 (@lem3171221)). Qed.
Lemma lem3171223 : term234 = term143.
Proof. exact (TRANS (@lem3171138) (@lem3171222)). Qed.
Lemma lem3171225 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3171226 : term143 = term42.
Proof. exact (@lem3171225 term42). Qed.
Lemma lem3171227 : term234 = term42.
Proof. exact (TRANS (@lem3171223) (@lem3171226)). Qed.
Lemma lem3171228 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3171229 : term247 = term244.
Proof. exact (MK_COMB (@lem3171228) (@lem3171227)). Qed.
Lemma lem3171230 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3171231 (n : int) : (term231 n) = (term248 n).
Proof. exact (MK_COMB (@lem3171229) (@lem3171230 n)). Qed.
Lemma lem3171232 (n : int) : (term230 n) = (term248 n).
Proof. exact (TRANS (@lem3171129 n) (@lem3171231 n)). Qed.
Lemma lem3171233 (n : int) : (term248 n) = term42.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem3171234 (n : int) : (term230 n) = term42.
Proof. exact (TRANS (@lem3171232 n) (@lem3171233 n)). Qed.
Lemma lem3171235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171236 (n : int) : (term249 n) = term52.
Proof. exact (MK_COMB (@lem3171235) (@lem3171234 n)). Qed.
Lemma lem3171238 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171239 : term96 = term101.
Proof. exact (@lem3171238 term36). Qed.
Lemma lem3171241 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171242 : term96 = term101.
Proof. exact (@lem3171241 term36). Qed.
Lemma lem3171243 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171244 : term232 = term233.
Proof. exact (MK_COMB (@lem3171243) (@lem3171242)). Qed.
Lemma lem3171245 : term287 = term288.
Proof. exact (MK_COMB (@lem3171244) (@lem3171239)). Qed.
Lemma lem3171246 : term289.
Proof. exact (@lem1981473 term96 term35 term96 term35 term290 term35). Qed.
Lemma lem3171248 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171249 : term201 = term207.
Proof. exact (@lem3171248 (NUMERAL 0) term36). Qed.
Lemma lem3171250 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171251 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171252 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171251 h1) (fun h1 : term207 = True => @lem3171250)). Qed.
Lemma lem3171253 : term207 = True.
Proof. exact (EQ_MP (@lem3171252) (@lem3171250)). Qed.
Lemma lem3171254 : term201 = True.
Proof. exact (TRANS (@lem3171249) (@lem3171253)). Qed.
Lemma lem3171255 : True = term201.
Proof. exact (SYM (@lem3171254)). Qed.
Lemma lem3171256 : term201.
Proof. exact (EQ_MP (@lem3171255) (@lem0)). Qed.
Lemma lem3171257 : term291.
Proof. exact (@lem3171246 (@lem3171256)). Qed.
Lemma lem3171259 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171260 : term201 = term207.
Proof. exact (@lem3171259 (NUMERAL 0) term36). Qed.
Lemma lem3171261 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171262 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171263 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171262 h1) (fun h1 : term207 = True => @lem3171261)). Qed.
Lemma lem3171264 : term207 = True.
Proof. exact (EQ_MP (@lem3171263) (@lem3171261)). Qed.
Lemma lem3171265 : term201 = True.
Proof. exact (TRANS (@lem3171260) (@lem3171264)). Qed.
Lemma lem3171266 : True = term201.
Proof. exact (SYM (@lem3171265)). Qed.
Lemma lem3171267 : term201.
Proof. exact (EQ_MP (@lem3171266) (@lem0)). Qed.
Lemma lem3171268 : term292.
Proof. exact (@lem3171257 (@lem3171267)). Qed.
Lemma lem3171270 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171271 : term201 = term207.
Proof. exact (@lem3171270 (NUMERAL 0) term36). Qed.
Lemma lem3171272 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171273 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171274 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171273 h1) (fun h1 : term207 = True => @lem3171272)). Qed.
Lemma lem3171275 : term207 = True.
Proof. exact (EQ_MP (@lem3171274) (@lem3171272)). Qed.
Lemma lem3171276 : term201 = True.
Proof. exact (TRANS (@lem3171271) (@lem3171275)). Qed.
Lemma lem3171277 : True = term201.
Proof. exact (SYM (@lem3171276)). Qed.
Lemma lem3171278 : term201.
Proof. exact (EQ_MP (@lem3171277) (@lem0)). Qed.
Lemma lem3171279 : term293.
Proof. exact (@lem3171268 (@lem3171278)). Qed.
Lemma lem3171281 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171282 : term104 = term115.
Proof. exact (@lem3171281 term36 term36). Qed.
Lemma lem3171283 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171284 : term112 = term36.
Proof. exact (EQ_MP (@lem3171283) (@lem940073)). Qed.
Lemma lem3171285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171286 : term110 = term35.
Proof. exact (MK_COMB (@lem3171285) (@lem3171284)). Qed.
Lemma lem3171287 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171288 : term115 = term96.
Proof. exact (MK_COMB (@lem3171287) (@lem3171286)). Qed.
Lemma lem3171289 : term104 = term96.
Proof. exact (TRANS (@lem3171282) (@lem3171288)). Qed.
Lemma lem3171291 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171292 : term104 = term115.
Proof. exact (@lem3171291 term36 term36). Qed.
Lemma lem3171293 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171294 : term112 = term36.
Proof. exact (EQ_MP (@lem3171293) (@lem940073)). Qed.
Lemma lem3171295 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171296 : term110 = term35.
Proof. exact (MK_COMB (@lem3171295) (@lem3171294)). Qed.
Lemma lem3171297 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171298 : term115 = term96.
Proof. exact (MK_COMB (@lem3171297) (@lem3171296)). Qed.
Lemma lem3171299 : term104 = term96.
Proof. exact (TRANS (@lem3171292) (@lem3171298)). Qed.
Lemma lem3171300 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171301 : term240 = term232.
Proof. exact (MK_COMB (@lem3171300) (@lem3171299)). Qed.
Lemma lem3171302 : term294 = term287.
Proof. exact (MK_COMB (@lem3171301) (@lem3171289)). Qed.
Lemma lem3171303 : term287 = term295.
Proof. exact (@lem1367763 term36 term36). Qed.
Lemma lem3171304 : term296 = term297.
Proof. exact (@lem706885). Qed.
Lemma lem3171305 : (term296 = term297) = (term298 = term299).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term297). Qed.
Lemma lem3171306 : term298 = term299.
Proof. exact (EQ_MP (@lem3171305) (@lem3171304)). Qed.
Lemma lem3171307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171308 : term300 = term301.
Proof. exact (MK_COMB (@lem3171307) (@lem3171306)). Qed.
Lemma lem3171309 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171310 : term295 = term290.
Proof. exact (MK_COMB (@lem3171309) (@lem3171308)). Qed.
Lemma lem3171311 : term287 = term290.
Proof. exact (TRANS (@lem3171303) (@lem3171310)). Qed.
Lemma lem3171312 : term294 = term290.
Proof. exact (TRANS (@lem3171302) (@lem3171311)). Qed.
Lemma lem3171313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3171314 : term302 = term303.
Proof. exact (MK_COMB (@lem3171313) (@lem3171312)). Qed.
Lemma lem3171315 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3171316 : term304 = term305.
Proof. exact (MK_COMB (@lem3171314) (@lem3171315)). Qed.
Lemma lem3171318 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171319 : term305 = term306.
Proof. exact (@lem3171318 term299 term36). Qed.
Lemma lem3171320 : term307 = term297.
Proof. exact (@lem996237 term297). Qed.
Lemma lem3171321 : (term307 = term297) = (term308 = term299).
Proof. exact (@lem1007663 term297 (BIT1 0) term297). Qed.
Lemma lem3171322 : term308 = term299.
Proof. exact (EQ_MP (@lem3171321) (@lem3171320)). Qed.
Lemma lem3171323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171324 : term309 = term301.
Proof. exact (MK_COMB (@lem3171323) (@lem3171322)). Qed.
Lemma lem3171325 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171326 : term306 = term290.
Proof. exact (MK_COMB (@lem3171325) (@lem3171324)). Qed.
Lemma lem3171327 : term305 = term290.
Proof. exact (TRANS (@lem3171319) (@lem3171326)). Qed.
Lemma lem3171328 : term304 = term290.
Proof. exact (TRANS (@lem3171316) (@lem3171327)). Qed.
Lemma lem3171330 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171331 : term109 = term110.
Proof. exact (@lem3171330 term36 term36). Qed.
Lemma lem3171332 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171333 : term112 = term36.
Proof. exact (EQ_MP (@lem3171332) (@lem940073)). Qed.
Lemma lem3171334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171335 : term110 = term35.
Proof. exact (MK_COMB (@lem3171334) (@lem3171333)). Qed.
Lemma lem3171336 : term109 = term35.
Proof. exact (TRANS (@lem3171331) (@lem3171335)). Qed.
Lemma lem3171337 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem3171338 : term310 = term305.
Proof. exact (MK_COMB (@lem3171337) (@lem3171336)). Qed.
Lemma lem3171340 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171341 : term305 = term306.
Proof. exact (@lem3171340 term299 term36). Qed.
Lemma lem3171342 : term307 = term297.
Proof. exact (@lem996237 term297). Qed.
Lemma lem3171343 : (term307 = term297) = (term308 = term299).
Proof. exact (@lem1007663 term297 (BIT1 0) term297). Qed.
Lemma lem3171344 : term308 = term299.
Proof. exact (EQ_MP (@lem3171343) (@lem3171342)). Qed.
Lemma lem3171345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171346 : term309 = term301.
Proof. exact (MK_COMB (@lem3171345) (@lem3171344)). Qed.
Lemma lem3171347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171348 : term306 = term290.
Proof. exact (MK_COMB (@lem3171347) (@lem3171346)). Qed.
Lemma lem3171349 : term305 = term290.
Proof. exact (TRANS (@lem3171341) (@lem3171348)). Qed.
Lemma lem3171350 : term310 = term290.
Proof. exact (TRANS (@lem3171338) (@lem3171349)). Qed.
Lemma lem3171351 : term290 = term310.
Proof. exact (SYM (@lem3171350)). Qed.
Lemma lem3171352 : term304 = term310.
Proof. exact (TRANS (@lem3171328) (@lem3171351)). Qed.
Lemma lem3171353 : term288 = term311.
Proof. exact (@lem3171279 (@lem3171352)). Qed.
Lemma lem3171354 : term287 = term311.
Proof. exact (TRANS (@lem3171245) (@lem3171353)). Qed.
Lemma lem3171356 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3171357 : term311 = term290.
Proof. exact (@lem3171356 term290). Qed.
Lemma lem3171358 : term287 = term290.
Proof. exact (TRANS (@lem3171354) (@lem3171357)). Qed.
Lemma lem3171359 (n : int) : (term286 n) = term312.
Proof. exact (MK_COMB (@lem3171236 n) (@lem3171358)). Qed.
Lemma lem3171360 (n : int) : (term285 n) = term312.
Proof. exact (TRANS (@lem3171128 n) (@lem3171359 n)). Qed.
Lemma lem3171361 : term312 = term290.
Proof. exact (@lem1982721 term290). Qed.
Lemma lem3171362 (n : int) : (term285 n) = term290.
Proof. exact (TRANS (@lem3171360 n) (@lem3171361)). Qed.
Lemma lem3171363 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3171364 (n : int) : (term313 n) = term314.
Proof. exact (MK_COMB (@lem3171363) (@lem3171362 n)). Qed.
Lemma lem3171365 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3171366 (n : int) : (term284 n) = term315.
Proof. exact (MK_COMB (@lem3171364 n) (@lem3171365)). Qed.
Lemma lem3171367 (n : int) (h1 : term281 n) : term315.
Proof. exact (EQ_MP (@lem3171366 n) (@lem3171127 n h1)). Qed.
Lemma lem3171369 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3171370 : term315 = term316.
Proof. exact (@lem3171369 term42 term290). Qed.
Lemma lem3171372 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171373 : term290 = term311.
Proof. exact (@lem3171372 term299). Qed.
Lemma lem3171375 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171376 : term42 = term143.
Proof. exact (@lem3171375 (NUMERAL 0)). Qed.
Lemma lem3171377 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3171378 : term60 = term255.
Proof. exact (MK_COMB (@lem3171377) (@lem3171376)). Qed.
Lemma lem3171379 : term316 = term317.
Proof. exact (MK_COMB (@lem3171378) (@lem3171373)). Qed.
Lemma lem3171380 : term318.
Proof. exact (@lem1980026 term42 term35 term290 term35). Qed.
Lemma lem3171382 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171383 : term201 = term207.
Proof. exact (@lem3171382 (NUMERAL 0) term36). Qed.
Lemma lem3171384 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171385 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171386 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171385 h1) (fun h1 : term207 = True => @lem3171384)). Qed.
Lemma lem3171387 : term207 = True.
Proof. exact (EQ_MP (@lem3171386) (@lem3171384)). Qed.
Lemma lem3171388 : term201 = True.
Proof. exact (TRANS (@lem3171383) (@lem3171387)). Qed.
Lemma lem3171389 : True = term201.
Proof. exact (SYM (@lem3171388)). Qed.
Lemma lem3171390 : term201.
Proof. exact (EQ_MP (@lem3171389) (@lem0)). Qed.
Lemma lem3171391 : term319.
Proof. exact (@lem3171380 (@lem3171390)). Qed.
Lemma lem3171393 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171394 : term201 = term207.
Proof. exact (@lem3171393 (NUMERAL 0) term36). Qed.
Lemma lem3171395 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171396 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171397 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171396 h1) (fun h1 : term207 = True => @lem3171395)). Qed.
Lemma lem3171398 : term207 = True.
Proof. exact (EQ_MP (@lem3171397) (@lem3171395)). Qed.
Lemma lem3171399 : term201 = True.
Proof. exact (TRANS (@lem3171394) (@lem3171398)). Qed.
Lemma lem3171400 : True = term201.
Proof. exact (SYM (@lem3171399)). Qed.
Lemma lem3171401 : term201.
Proof. exact (EQ_MP (@lem3171400) (@lem0)). Qed.
Lemma lem3171402 : term317 = term320.
Proof. exact (@lem3171391 (@lem3171401)). Qed.
Lemma lem3171404 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171405 : term305 = term306.
Proof. exact (@lem3171404 term299 term36). Qed.
Lemma lem3171406 : term307 = term297.
Proof. exact (@lem996237 term297). Qed.
Lemma lem3171407 : (term307 = term297) = (term308 = term299).
Proof. exact (@lem1007663 term297 (BIT1 0) term297). Qed.
Lemma lem3171408 : term308 = term299.
Proof. exact (EQ_MP (@lem3171407) (@lem3171406)). Qed.
Lemma lem3171409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171410 : term309 = term301.
Proof. exact (MK_COMB (@lem3171409) (@lem3171408)). Qed.
Lemma lem3171411 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171412 : term306 = term290.
Proof. exact (MK_COMB (@lem3171411) (@lem3171410)). Qed.
Lemma lem3171413 : term305 = term290.
Proof. exact (TRANS (@lem3171405) (@lem3171412)). Qed.
Lemma lem3171415 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171416 : term212 = term42.
Proof. exact (@lem3171415 term36). Qed.
Lemma lem3171417 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3171418 : term260 = term60.
Proof. exact (MK_COMB (@lem3171417) (@lem3171416)). Qed.
Lemma lem3171419 : term320 = term316.
Proof. exact (MK_COMB (@lem3171418) (@lem3171413)). Qed.
Lemma lem3171421 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3171422 : term316 = term321.
Proof. exact (@lem3171421 (NUMERAL 0) term299). Qed.
Lemma lem3171423 : term322 = term297.
Proof. exact (@lem912803). Qed.
Lemma lem3171424 (h1 : term322 = term297) : (term299 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term297 h1). Qed.
Lemma lem3171425 : (term322 = term297) = ((term299 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term322 = term297 => @lem3171424 h1) (fun h1 : (term299 = (NUMERAL 0)) = False => @lem3171423)). Qed.
Lemma lem3171426 : (term299 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3171425) (@lem3171423)). Qed.
Lemma lem3171427 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3171428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3171429 : term264 = (and True).
Proof. exact (MK_COMB (@lem3171428) (@lem3171427)). Qed.
Lemma lem3171430 : term321 = (True /\ False).
Proof. exact (MK_COMB (@lem3171429) (@lem3171426)). Qed.
Lemma lem3171432 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3171433 : term321 = False.
Proof. exact (TRANS (@lem3171430) (@lem3171432)). Qed.
Lemma lem3171434 : term316 = False.
Proof. exact (TRANS (@lem3171422) (@lem3171433)). Qed.
Lemma lem3171435 : term320 = False.
Proof. exact (TRANS (@lem3171419) (@lem3171434)). Qed.
Lemma lem3171436 : term317 = False.
Proof. exact (TRANS (@lem3171402) (@lem3171435)). Qed.
Lemma lem3171437 : term316 = False.
Proof. exact (TRANS (@lem3171379) (@lem3171436)). Qed.
Lemma lem3171438 : term315 = False.
Proof. exact (TRANS (@lem3171370) (@lem3171437)). Qed.
Lemma lem3171439 (n : int) (h1 : term281 n) : False.
Proof. exact (EQ_MP (@lem3171438) (@lem3171367 n h1)). Qed.
Lemma lem3171440 (n : int) (h1 : term323 n) : term323 n.
Proof. exact (h1). Qed.
Lemma lem3171441 (n : int) (h1 : term323 n) : term186 n.
Proof. exact (proj2 (@lem3171440 n h1)). Qed.
Lemma lem3171443 (n : int) (h1 : term323 n) : term124 n.
Proof. exact (proj2 (@lem3171441 n h1)). Qed.
Lemma lem3171444 (n : int) (h1 : term323 n) : term133 n.
Proof. exact (proj1 (@lem3171441 n h1)). Qed.
Lemma lem3171446 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3171447 : term200 = term201.
Proof. exact (@lem3171446 term42 term35). Qed.
Lemma lem3171449 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171450 : term35 = term98.
Proof. exact (@lem3171449 term36). Qed.
Lemma lem3171452 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171453 : term42 = term143.
Proof. exact (@lem3171452 (NUMERAL 0)). Qed.
Lemma lem3171454 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171455 : term202 = term203.
Proof. exact (MK_COMB (@lem3171454) (@lem3171453)). Qed.
Lemma lem3171456 : term201 = term204.
Proof. exact (MK_COMB (@lem3171455) (@lem3171450)). Qed.
Lemma lem3171457 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3171459 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171460 : term201 = term207.
Proof. exact (@lem3171459 (NUMERAL 0) term36). Qed.
Lemma lem3171461 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171462 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171463 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171462 h1) (fun h1 : term207 = True => @lem3171461)). Qed.
Lemma lem3171464 : term207 = True.
Proof. exact (EQ_MP (@lem3171463) (@lem3171461)). Qed.
Lemma lem3171465 : term201 = True.
Proof. exact (TRANS (@lem3171460) (@lem3171464)). Qed.
Lemma lem3171466 : True = term201.
Proof. exact (SYM (@lem3171465)). Qed.
Lemma lem3171467 : term201.
Proof. exact (EQ_MP (@lem3171466) (@lem0)). Qed.
Lemma lem3171468 : term209.
Proof. exact (@lem3171457 (@lem3171467)). Qed.
Lemma lem3171470 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171471 : term201 = term207.
Proof. exact (@lem3171470 (NUMERAL 0) term36). Qed.
Lemma lem3171472 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171473 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171474 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171473 h1) (fun h1 : term207 = True => @lem3171472)). Qed.
Lemma lem3171475 : term207 = True.
Proof. exact (EQ_MP (@lem3171474) (@lem3171472)). Qed.
Lemma lem3171476 : term201 = True.
Proof. exact (TRANS (@lem3171471) (@lem3171475)). Qed.
Lemma lem3171477 : True = term201.
Proof. exact (SYM (@lem3171476)). Qed.
Lemma lem3171478 : term201.
Proof. exact (EQ_MP (@lem3171477) (@lem0)). Qed.
Lemma lem3171479 : term204 = term210.
Proof. exact (@lem3171468 (@lem3171478)). Qed.
Lemma lem3171481 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171482 : term109 = term110.
Proof. exact (@lem3171481 term36 term36). Qed.
Lemma lem3171483 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171484 : term112 = term36.
Proof. exact (EQ_MP (@lem3171483) (@lem940073)). Qed.
Lemma lem3171485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171486 : term110 = term35.
Proof. exact (MK_COMB (@lem3171485) (@lem3171484)). Qed.
Lemma lem3171487 : term109 = term35.
Proof. exact (TRANS (@lem3171482) (@lem3171486)). Qed.
Lemma lem3171489 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171490 : term212 = term42.
Proof. exact (@lem3171489 term36). Qed.
Lemma lem3171491 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171492 : term213 = term202.
Proof. exact (MK_COMB (@lem3171491) (@lem3171490)). Qed.
Lemma lem3171493 : term210 = term201.
Proof. exact (MK_COMB (@lem3171492) (@lem3171487)). Qed.
Lemma lem3171495 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171496 : term201 = term207.
Proof. exact (@lem3171495 (NUMERAL 0) term36). Qed.
Lemma lem3171497 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171498 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171499 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171498 h1) (fun h1 : term207 = True => @lem3171497)). Qed.
Lemma lem3171500 : term207 = True.
Proof. exact (EQ_MP (@lem3171499) (@lem3171497)). Qed.
Lemma lem3171501 : term201 = True.
Proof. exact (TRANS (@lem3171496) (@lem3171500)). Qed.
Lemma lem3171502 : term210 = True.
Proof. exact (TRANS (@lem3171493) (@lem3171501)). Qed.
Lemma lem3171503 : term204 = True.
Proof. exact (TRANS (@lem3171479) (@lem3171502)). Qed.
Lemma lem3171504 : term201 = True.
Proof. exact (TRANS (@lem3171456) (@lem3171503)). Qed.
Lemma lem3171505 : term200 = True.
Proof. exact (TRANS (@lem3171447) (@lem3171504)). Qed.
Lemma lem3171506 : True = term200.
Proof. exact (SYM (@lem3171505)). Qed.
Lemma lem3171507 : term200.
Proof. exact (EQ_MP (@lem3171506) (@lem0)). Qed.
Lemma lem3171508 (n : int) (h1 : term323 n) : term266 n.
Proof. exact (conj (@lem3171507) (@lem3171444 n h1)). Qed.
Lemma lem3171510 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3171511 (n : int) : term267 n.
Proof. exact (@lem3171510 term35 (term130 n)). Qed.
Lemma lem3171512 (n : int) (h1 : term323 n) : term268 n.
Proof. exact (@lem3171511 n (@lem3171508 n h1)). Qed.
Lemma lem3171513 (n : int) : (term269 n) = (term130 n).
Proof. exact (@lem1982733 (term130 n)). Qed.
Lemma lem3171514 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3171515 (n : int) : (term270 n) = (term132 n).
Proof. exact (MK_COMB (@lem3171514) (@lem3171513 n)). Qed.
Lemma lem3171516 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3171517 (n : int) : (term268 n) = (term133 n).
Proof. exact (MK_COMB (@lem3171515 n) (@lem3171516)). Qed.
Lemma lem3171518 (n : int) (h1 : term323 n) : term133 n.
Proof. exact (EQ_MP (@lem3171517 n) (@lem3171512 n h1)). Qed.
Lemma lem3171520 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3171521 : term200 = term201.
Proof. exact (@lem3171520 term42 term35). Qed.
Lemma lem3171523 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171524 : term35 = term98.
Proof. exact (@lem3171523 term36). Qed.
Lemma lem3171526 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171527 : term42 = term143.
Proof. exact (@lem3171526 (NUMERAL 0)). Qed.
Lemma lem3171528 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171529 : term202 = term203.
Proof. exact (MK_COMB (@lem3171528) (@lem3171527)). Qed.
Lemma lem3171530 : term201 = term204.
Proof. exact (MK_COMB (@lem3171529) (@lem3171524)). Qed.
Lemma lem3171531 : term205.
Proof. exact (@lem1980255 term42 term35 term35 term35). Qed.
Lemma lem3171533 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171534 : term201 = term207.
Proof. exact (@lem3171533 (NUMERAL 0) term36). Qed.
Lemma lem3171535 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171536 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171537 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171536 h1) (fun h1 : term207 = True => @lem3171535)). Qed.
Lemma lem3171538 : term207 = True.
Proof. exact (EQ_MP (@lem3171537) (@lem3171535)). Qed.
Lemma lem3171539 : term201 = True.
Proof. exact (TRANS (@lem3171534) (@lem3171538)). Qed.
Lemma lem3171540 : True = term201.
Proof. exact (SYM (@lem3171539)). Qed.
Lemma lem3171541 : term201.
Proof. exact (EQ_MP (@lem3171540) (@lem0)). Qed.
Lemma lem3171542 : term209.
Proof. exact (@lem3171531 (@lem3171541)). Qed.
Lemma lem3171544 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171545 : term201 = term207.
Proof. exact (@lem3171544 (NUMERAL 0) term36). Qed.
Lemma lem3171546 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171547 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171548 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171547 h1) (fun h1 : term207 = True => @lem3171546)). Qed.
Lemma lem3171549 : term207 = True.
Proof. exact (EQ_MP (@lem3171548) (@lem3171546)). Qed.
Lemma lem3171550 : term201 = True.
Proof. exact (TRANS (@lem3171545) (@lem3171549)). Qed.
Lemma lem3171551 : True = term201.
Proof. exact (SYM (@lem3171550)). Qed.
Lemma lem3171552 : term201.
Proof. exact (EQ_MP (@lem3171551) (@lem0)). Qed.
Lemma lem3171553 : term204 = term210.
Proof. exact (@lem3171542 (@lem3171552)). Qed.
Lemma lem3171555 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171556 : term109 = term110.
Proof. exact (@lem3171555 term36 term36). Qed.
Lemma lem3171557 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171558 : term112 = term36.
Proof. exact (EQ_MP (@lem3171557) (@lem940073)). Qed.
Lemma lem3171559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171560 : term110 = term35.
Proof. exact (MK_COMB (@lem3171559) (@lem3171558)). Qed.
Lemma lem3171561 : term109 = term35.
Proof. exact (TRANS (@lem3171556) (@lem3171560)). Qed.
Lemma lem3171563 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171564 : term212 = term42.
Proof. exact (@lem3171563 term36). Qed.
Lemma lem3171565 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3171566 : term213 = term202.
Proof. exact (MK_COMB (@lem3171565) (@lem3171564)). Qed.
Lemma lem3171567 : term210 = term201.
Proof. exact (MK_COMB (@lem3171566) (@lem3171561)). Qed.
Lemma lem3171569 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171570 : term201 = term207.
Proof. exact (@lem3171569 (NUMERAL 0) term36). Qed.
Lemma lem3171571 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171572 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171573 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171572 h1) (fun h1 : term207 = True => @lem3171571)). Qed.
Lemma lem3171574 : term207 = True.
Proof. exact (EQ_MP (@lem3171573) (@lem3171571)). Qed.
Lemma lem3171575 : term201 = True.
Proof. exact (TRANS (@lem3171570) (@lem3171574)). Qed.
Lemma lem3171576 : term210 = True.
Proof. exact (TRANS (@lem3171567) (@lem3171575)). Qed.
Lemma lem3171577 : term204 = True.
Proof. exact (TRANS (@lem3171553) (@lem3171576)). Qed.
Lemma lem3171578 : term201 = True.
Proof. exact (TRANS (@lem3171530) (@lem3171577)). Qed.
Lemma lem3171579 : term200 = True.
Proof. exact (TRANS (@lem3171521) (@lem3171578)). Qed.
Lemma lem3171580 : True = term200.
Proof. exact (SYM (@lem3171579)). Qed.
Lemma lem3171581 : term200.
Proof. exact (EQ_MP (@lem3171580) (@lem0)). Qed.
Lemma lem3171582 (n : int) (h1 : term323 n) : term219 n.
Proof. exact (conj (@lem3171581) (@lem3171443 n h1)). Qed.
Lemma lem3171584 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3171585 (n : int) : term220 n.
Proof. exact (@lem3171584 term35 (term120 n)). Qed.
Lemma lem3171586 (n : int) (h1 : term323 n) : term221 n.
Proof. exact (@lem3171585 n (@lem3171582 n h1)). Qed.
Lemma lem3171587 (n : int) : (term222 n) = (term120 n).
Proof. exact (@lem1982733 (term120 n)). Qed.
Lemma lem3171588 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3171589 (n : int) : (term223 n) = (term123 n).
Proof. exact (MK_COMB (@lem3171588) (@lem3171587 n)). Qed.
Lemma lem3171590 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3171591 (n : int) : (term221 n) = (term124 n).
Proof. exact (MK_COMB (@lem3171589 n) (@lem3171590)). Qed.
Lemma lem3171592 (n : int) (h1 : term323 n) : term124 n.
Proof. exact (EQ_MP (@lem3171591 n) (@lem3171586 n h1)). Qed.
Lemma lem3171593 (n : int) (h1 : term323 n) : term282 n.
Proof. exact (conj (@lem3171592 n h1) (@lem3171518 n h1)). Qed.
Lemma lem3171595 (x : real) (y : real) : term225 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3171596 (n : int) : term283 n.
Proof. exact (@lem3171595 (term120 n) (term130 n)). Qed.
Lemma lem3171597 (n : int) (h1 : term323 n) : term284 n.
Proof. exact (@lem3171596 n (@lem3171593 n h1)). Qed.
Lemma lem3171598 (n : int) : (term285 n) = (term286 n).
Proof. exact (@lem1982753 (term137 n) (real_of_int n) term96 term96). Qed.
Lemma lem3171599 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982713 term96 (real_of_int n)). Qed.
Lemma lem3171601 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171602 : term35 = term98.
Proof. exact (@lem3171601 term36). Qed.
Lemma lem3171604 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171605 : term96 = term101.
Proof. exact (@lem3171604 term36). Qed.
Lemma lem3171606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171607 : term232 = term233.
Proof. exact (MK_COMB (@lem3171606) (@lem3171605)). Qed.
Lemma lem3171608 : term234 = term235.
Proof. exact (MK_COMB (@lem3171607) (@lem3171602)). Qed.
Lemma lem3171609 : term236.
Proof. exact (@lem1981473 term96 term35 term35 term35 term42 term35). Qed.
Lemma lem3171611 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171612 : term201 = term207.
Proof. exact (@lem3171611 (NUMERAL 0) term36). Qed.
Lemma lem3171613 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171614 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171615 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171614 h1) (fun h1 : term207 = True => @lem3171613)). Qed.
Lemma lem3171616 : term207 = True.
Proof. exact (EQ_MP (@lem3171615) (@lem3171613)). Qed.
Lemma lem3171617 : term201 = True.
Proof. exact (TRANS (@lem3171612) (@lem3171616)). Qed.
Lemma lem3171618 : True = term201.
Proof. exact (SYM (@lem3171617)). Qed.
Lemma lem3171619 : term201.
Proof. exact (EQ_MP (@lem3171618) (@lem0)). Qed.
Lemma lem3171620 : term237.
Proof. exact (@lem3171609 (@lem3171619)). Qed.
Lemma lem3171622 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171623 : term201 = term207.
Proof. exact (@lem3171622 (NUMERAL 0) term36). Qed.
Lemma lem3171624 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171625 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171626 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171625 h1) (fun h1 : term207 = True => @lem3171624)). Qed.
Lemma lem3171627 : term207 = True.
Proof. exact (EQ_MP (@lem3171626) (@lem3171624)). Qed.
Lemma lem3171628 : term201 = True.
Proof. exact (TRANS (@lem3171623) (@lem3171627)). Qed.
Lemma lem3171629 : True = term201.
Proof. exact (SYM (@lem3171628)). Qed.
Lemma lem3171630 : term201.
Proof. exact (EQ_MP (@lem3171629) (@lem0)). Qed.
Lemma lem3171631 : term238.
Proof. exact (@lem3171620 (@lem3171630)). Qed.
Lemma lem3171633 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171634 : term201 = term207.
Proof. exact (@lem3171633 (NUMERAL 0) term36). Qed.
Lemma lem3171635 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171636 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171637 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171636 h1) (fun h1 : term207 = True => @lem3171635)). Qed.
Lemma lem3171638 : term207 = True.
Proof. exact (EQ_MP (@lem3171637) (@lem3171635)). Qed.
Lemma lem3171639 : term201 = True.
Proof. exact (TRANS (@lem3171634) (@lem3171638)). Qed.
Lemma lem3171640 : True = term201.
Proof. exact (SYM (@lem3171639)). Qed.
Lemma lem3171641 : term201.
Proof. exact (EQ_MP (@lem3171640) (@lem0)). Qed.
Lemma lem3171642 : term239.
Proof. exact (@lem3171631 (@lem3171641)). Qed.
Lemma lem3171644 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171645 : term109 = term110.
Proof. exact (@lem3171644 term36 term36). Qed.
Lemma lem3171646 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171647 : term112 = term36.
Proof. exact (EQ_MP (@lem3171646) (@lem940073)). Qed.
Lemma lem3171648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171649 : term110 = term35.
Proof. exact (MK_COMB (@lem3171648) (@lem3171647)). Qed.
Lemma lem3171650 : term109 = term35.
Proof. exact (TRANS (@lem3171645) (@lem3171649)). Qed.
Lemma lem3171652 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171653 : term104 = term115.
Proof. exact (@lem3171652 term36 term36). Qed.
Lemma lem3171654 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171655 : term112 = term36.
Proof. exact (EQ_MP (@lem3171654) (@lem940073)). Qed.
Lemma lem3171656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171657 : term110 = term35.
Proof. exact (MK_COMB (@lem3171656) (@lem3171655)). Qed.
Lemma lem3171658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171659 : term115 = term96.
Proof. exact (MK_COMB (@lem3171658) (@lem3171657)). Qed.
Lemma lem3171660 : term104 = term96.
Proof. exact (TRANS (@lem3171653) (@lem3171659)). Qed.
Lemma lem3171661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171662 : term240 = term232.
Proof. exact (MK_COMB (@lem3171661) (@lem3171660)). Qed.
Lemma lem3171663 : term241 = term234.
Proof. exact (MK_COMB (@lem3171662) (@lem3171650)). Qed.
Lemma lem3171665 (m : nat) : (term242 m) = term42.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3171666 : term234 = term42.
Proof. exact (@lem3171665 term36). Qed.
Lemma lem3171667 : term241 = term42.
Proof. exact (TRANS (@lem3171663) (@lem3171666)). Qed.
Lemma lem3171668 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3171669 : term243 = term244.
Proof. exact (MK_COMB (@lem3171668) (@lem3171667)). Qed.
Lemma lem3171670 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3171671 : term245 = term212.
Proof. exact (MK_COMB (@lem3171669) (@lem3171670)). Qed.
Lemma lem3171673 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171674 : term212 = term42.
Proof. exact (@lem3171673 term36). Qed.
Lemma lem3171675 : term245 = term42.
Proof. exact (TRANS (@lem3171671) (@lem3171674)). Qed.
Lemma lem3171677 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171678 : term109 = term110.
Proof. exact (@lem3171677 term36 term36). Qed.
Lemma lem3171679 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171680 : term112 = term36.
Proof. exact (EQ_MP (@lem3171679) (@lem940073)). Qed.
Lemma lem3171681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171682 : term110 = term35.
Proof. exact (MK_COMB (@lem3171681) (@lem3171680)). Qed.
Lemma lem3171683 : term109 = term35.
Proof. exact (TRANS (@lem3171678) (@lem3171682)). Qed.
Lemma lem3171684 : term244 = term244.
Proof. exact (eq_refl term244). Qed.
Lemma lem3171685 : term246 = term212.
Proof. exact (MK_COMB (@lem3171684) (@lem3171683)). Qed.
Lemma lem3171687 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171688 : term212 = term42.
Proof. exact (@lem3171687 term36). Qed.
Lemma lem3171689 : term246 = term42.
Proof. exact (TRANS (@lem3171685) (@lem3171688)). Qed.
Lemma lem3171690 : term42 = term246.
Proof. exact (SYM (@lem3171689)). Qed.
Lemma lem3171691 : term245 = term246.
Proof. exact (TRANS (@lem3171675) (@lem3171690)). Qed.
Lemma lem3171692 : term235 = term143.
Proof. exact (@lem3171642 (@lem3171691)). Qed.
Lemma lem3171693 : term234 = term143.
Proof. exact (TRANS (@lem3171608) (@lem3171692)). Qed.
Lemma lem3171695 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3171696 : term143 = term42.
Proof. exact (@lem3171695 term42). Qed.
Lemma lem3171697 : term234 = term42.
Proof. exact (TRANS (@lem3171693) (@lem3171696)). Qed.
Lemma lem3171698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3171699 : term247 = term244.
Proof. exact (MK_COMB (@lem3171698) (@lem3171697)). Qed.
Lemma lem3171700 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem3171701 (n : int) : (term231 n) = (term248 n).
Proof. exact (MK_COMB (@lem3171699) (@lem3171700 n)). Qed.
Lemma lem3171702 (n : int) : (term230 n) = (term248 n).
Proof. exact (TRANS (@lem3171599 n) (@lem3171701 n)). Qed.
Lemma lem3171703 (n : int) : (term248 n) = term42.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem3171704 (n : int) : (term230 n) = term42.
Proof. exact (TRANS (@lem3171702 n) (@lem3171703 n)). Qed.
Lemma lem3171705 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171706 (n : int) : (term249 n) = term52.
Proof. exact (MK_COMB (@lem3171705) (@lem3171704 n)). Qed.
Lemma lem3171708 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171709 : term96 = term101.
Proof. exact (@lem3171708 term36). Qed.
Lemma lem3171711 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171712 : term96 = term101.
Proof. exact (@lem3171711 term36). Qed.
Lemma lem3171713 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171714 : term232 = term233.
Proof. exact (MK_COMB (@lem3171713) (@lem3171712)). Qed.
Lemma lem3171715 : term287 = term288.
Proof. exact (MK_COMB (@lem3171714) (@lem3171709)). Qed.
Lemma lem3171716 : term289.
Proof. exact (@lem1981473 term96 term35 term96 term35 term290 term35). Qed.
Lemma lem3171718 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171719 : term201 = term207.
Proof. exact (@lem3171718 (NUMERAL 0) term36). Qed.
Lemma lem3171720 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171721 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171722 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171721 h1) (fun h1 : term207 = True => @lem3171720)). Qed.
Lemma lem3171723 : term207 = True.
Proof. exact (EQ_MP (@lem3171722) (@lem3171720)). Qed.
Lemma lem3171724 : term201 = True.
Proof. exact (TRANS (@lem3171719) (@lem3171723)). Qed.
Lemma lem3171725 : True = term201.
Proof. exact (SYM (@lem3171724)). Qed.
Lemma lem3171726 : term201.
Proof. exact (EQ_MP (@lem3171725) (@lem0)). Qed.
Lemma lem3171727 : term291.
Proof. exact (@lem3171716 (@lem3171726)). Qed.
Lemma lem3171729 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171730 : term201 = term207.
Proof. exact (@lem3171729 (NUMERAL 0) term36). Qed.
Lemma lem3171731 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171732 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171733 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171732 h1) (fun h1 : term207 = True => @lem3171731)). Qed.
Lemma lem3171734 : term207 = True.
Proof. exact (EQ_MP (@lem3171733) (@lem3171731)). Qed.
Lemma lem3171735 : term201 = True.
Proof. exact (TRANS (@lem3171730) (@lem3171734)). Qed.
Lemma lem3171736 : True = term201.
Proof. exact (SYM (@lem3171735)). Qed.
Lemma lem3171737 : term201.
Proof. exact (EQ_MP (@lem3171736) (@lem0)). Qed.
Lemma lem3171738 : term292.
Proof. exact (@lem3171727 (@lem3171737)). Qed.
Lemma lem3171740 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171741 : term201 = term207.
Proof. exact (@lem3171740 (NUMERAL 0) term36). Qed.
Lemma lem3171742 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171743 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171744 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171743 h1) (fun h1 : term207 = True => @lem3171742)). Qed.
Lemma lem3171745 : term207 = True.
Proof. exact (EQ_MP (@lem3171744) (@lem3171742)). Qed.
Lemma lem3171746 : term201 = True.
Proof. exact (TRANS (@lem3171741) (@lem3171745)). Qed.
Lemma lem3171747 : True = term201.
Proof. exact (SYM (@lem3171746)). Qed.
Lemma lem3171748 : term201.
Proof. exact (EQ_MP (@lem3171747) (@lem0)). Qed.
Lemma lem3171749 : term293.
Proof. exact (@lem3171738 (@lem3171748)). Qed.
Lemma lem3171751 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171752 : term104 = term115.
Proof. exact (@lem3171751 term36 term36). Qed.
Lemma lem3171753 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171754 : term112 = term36.
Proof. exact (EQ_MP (@lem3171753) (@lem940073)). Qed.
Lemma lem3171755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171756 : term110 = term35.
Proof. exact (MK_COMB (@lem3171755) (@lem3171754)). Qed.
Lemma lem3171757 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171758 : term115 = term96.
Proof. exact (MK_COMB (@lem3171757) (@lem3171756)). Qed.
Lemma lem3171759 : term104 = term96.
Proof. exact (TRANS (@lem3171752) (@lem3171758)). Qed.
Lemma lem3171761 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171762 : term104 = term115.
Proof. exact (@lem3171761 term36 term36). Qed.
Lemma lem3171763 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171764 : term112 = term36.
Proof. exact (EQ_MP (@lem3171763) (@lem940073)). Qed.
Lemma lem3171765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171766 : term110 = term35.
Proof. exact (MK_COMB (@lem3171765) (@lem3171764)). Qed.
Lemma lem3171767 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171768 : term115 = term96.
Proof. exact (MK_COMB (@lem3171767) (@lem3171766)). Qed.
Lemma lem3171769 : term104 = term96.
Proof. exact (TRANS (@lem3171762) (@lem3171768)). Qed.
Lemma lem3171770 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3171771 : term240 = term232.
Proof. exact (MK_COMB (@lem3171770) (@lem3171769)). Qed.
Lemma lem3171772 : term294 = term287.
Proof. exact (MK_COMB (@lem3171771) (@lem3171759)). Qed.
Lemma lem3171773 : term287 = term295.
Proof. exact (@lem1367763 term36 term36). Qed.
Lemma lem3171774 : term296 = term297.
Proof. exact (@lem706885). Qed.
Lemma lem3171775 : (term296 = term297) = (term298 = term299).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term297). Qed.
Lemma lem3171776 : term298 = term299.
Proof. exact (EQ_MP (@lem3171775) (@lem3171774)). Qed.
Lemma lem3171777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171778 : term300 = term301.
Proof. exact (MK_COMB (@lem3171777) (@lem3171776)). Qed.
Lemma lem3171779 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171780 : term295 = term290.
Proof. exact (MK_COMB (@lem3171779) (@lem3171778)). Qed.
Lemma lem3171781 : term287 = term290.
Proof. exact (TRANS (@lem3171773) (@lem3171780)). Qed.
Lemma lem3171782 : term294 = term290.
Proof. exact (TRANS (@lem3171772) (@lem3171781)). Qed.
Lemma lem3171783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3171784 : term302 = term303.
Proof. exact (MK_COMB (@lem3171783) (@lem3171782)). Qed.
Lemma lem3171785 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem3171786 : term304 = term305.
Proof. exact (MK_COMB (@lem3171784) (@lem3171785)). Qed.
Lemma lem3171788 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171789 : term305 = term306.
Proof. exact (@lem3171788 term299 term36). Qed.
Lemma lem3171790 : term307 = term297.
Proof. exact (@lem996237 term297). Qed.
Lemma lem3171791 : (term307 = term297) = (term308 = term299).
Proof. exact (@lem1007663 term297 (BIT1 0) term297). Qed.
Lemma lem3171792 : term308 = term299.
Proof. exact (EQ_MP (@lem3171791) (@lem3171790)). Qed.
Lemma lem3171793 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171794 : term309 = term301.
Proof. exact (MK_COMB (@lem3171793) (@lem3171792)). Qed.
Lemma lem3171795 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171796 : term306 = term290.
Proof. exact (MK_COMB (@lem3171795) (@lem3171794)). Qed.
Lemma lem3171797 : term305 = term290.
Proof. exact (TRANS (@lem3171789) (@lem3171796)). Qed.
Lemma lem3171798 : term304 = term290.
Proof. exact (TRANS (@lem3171786) (@lem3171797)). Qed.
Lemma lem3171800 (m : nat) (n : nat) : (term107 m n) = (term108 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3171801 : term109 = term110.
Proof. exact (@lem3171800 term36 term36). Qed.
Lemma lem3171802 : (term111 = (BIT1 0)) = (term112 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3171803 : term112 = term36.
Proof. exact (EQ_MP (@lem3171802) (@lem940073)). Qed.
Lemma lem3171804 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171805 : term110 = term35.
Proof. exact (MK_COMB (@lem3171804) (@lem3171803)). Qed.
Lemma lem3171806 : term109 = term35.
Proof. exact (TRANS (@lem3171801) (@lem3171805)). Qed.
Lemma lem3171807 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem3171808 : term310 = term305.
Proof. exact (MK_COMB (@lem3171807) (@lem3171806)). Qed.
Lemma lem3171810 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171811 : term305 = term306.
Proof. exact (@lem3171810 term299 term36). Qed.
Lemma lem3171812 : term307 = term297.
Proof. exact (@lem996237 term297). Qed.
Lemma lem3171813 : (term307 = term297) = (term308 = term299).
Proof. exact (@lem1007663 term297 (BIT1 0) term297). Qed.
Lemma lem3171814 : term308 = term299.
Proof. exact (EQ_MP (@lem3171813) (@lem3171812)). Qed.
Lemma lem3171815 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171816 : term309 = term301.
Proof. exact (MK_COMB (@lem3171815) (@lem3171814)). Qed.
Lemma lem3171817 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171818 : term306 = term290.
Proof. exact (MK_COMB (@lem3171817) (@lem3171816)). Qed.
Lemma lem3171819 : term305 = term290.
Proof. exact (TRANS (@lem3171811) (@lem3171818)). Qed.
Lemma lem3171820 : term310 = term290.
Proof. exact (TRANS (@lem3171808) (@lem3171819)). Qed.
Lemma lem3171821 : term290 = term310.
Proof. exact (SYM (@lem3171820)). Qed.
Lemma lem3171822 : term304 = term310.
Proof. exact (TRANS (@lem3171798) (@lem3171821)). Qed.
Lemma lem3171823 : term288 = term311.
Proof. exact (@lem3171749 (@lem3171822)). Qed.
Lemma lem3171824 : term287 = term311.
Proof. exact (TRANS (@lem3171715) (@lem3171823)). Qed.
Lemma lem3171826 (x : real) : (term118 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3171827 : term311 = term290.
Proof. exact (@lem3171826 term290). Qed.
Lemma lem3171828 : term287 = term290.
Proof. exact (TRANS (@lem3171824) (@lem3171827)). Qed.
Lemma lem3171829 (n : int) : (term286 n) = term312.
Proof. exact (MK_COMB (@lem3171706 n) (@lem3171828)). Qed.
Lemma lem3171830 (n : int) : (term285 n) = term312.
Proof. exact (TRANS (@lem3171598 n) (@lem3171829 n)). Qed.
Lemma lem3171831 : term312 = term290.
Proof. exact (@lem1982721 term290). Qed.
Lemma lem3171832 (n : int) : (term285 n) = term290.
Proof. exact (TRANS (@lem3171830 n) (@lem3171831)). Qed.
Lemma lem3171833 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3171834 (n : int) : (term313 n) = term314.
Proof. exact (MK_COMB (@lem3171833) (@lem3171832 n)). Qed.
Lemma lem3171835 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem3171836 (n : int) : (term284 n) = term315.
Proof. exact (MK_COMB (@lem3171834 n) (@lem3171835)). Qed.
Lemma lem3171837 (n : int) (h1 : term323 n) : term315.
Proof. exact (EQ_MP (@lem3171836 n) (@lem3171597 n h1)). Qed.
Lemma lem3171839 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3171840 : term315 = term316.
Proof. exact (@lem3171839 term42 term290). Qed.
Lemma lem3171842 (x : nat) : (term99 x) = (term100 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3171843 : term290 = term311.
Proof. exact (@lem3171842 term299). Qed.
Lemma lem3171845 (x : nat) : (real_of_num x) = (term97 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3171846 : term42 = term143.
Proof. exact (@lem3171845 (NUMERAL 0)). Qed.
Lemma lem3171847 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3171848 : term60 = term255.
Proof. exact (MK_COMB (@lem3171847) (@lem3171846)). Qed.
Lemma lem3171849 : term316 = term317.
Proof. exact (MK_COMB (@lem3171848) (@lem3171843)). Qed.
Lemma lem3171850 : term318.
Proof. exact (@lem1980026 term42 term35 term290 term35). Qed.
Lemma lem3171852 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171853 : term201 = term207.
Proof. exact (@lem3171852 (NUMERAL 0) term36). Qed.
Lemma lem3171854 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171855 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171856 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171855 h1) (fun h1 : term207 = True => @lem3171854)). Qed.
Lemma lem3171857 : term207 = True.
Proof. exact (EQ_MP (@lem3171856) (@lem3171854)). Qed.
Lemma lem3171858 : term201 = True.
Proof. exact (TRANS (@lem3171853) (@lem3171857)). Qed.
Lemma lem3171859 : True = term201.
Proof. exact (SYM (@lem3171858)). Qed.
Lemma lem3171860 : term201.
Proof. exact (EQ_MP (@lem3171859) (@lem0)). Qed.
Lemma lem3171861 : term319.
Proof. exact (@lem3171850 (@lem3171860)). Qed.
Lemma lem3171863 (m : nat) (n : nat) : (term206 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3171864 : term201 = term207.
Proof. exact (@lem3171863 (NUMERAL 0) term36). Qed.
Lemma lem3171865 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3171866 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3171867 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem3171866 h1) (fun h1 : term207 = True => @lem3171865)). Qed.
Lemma lem3171868 : term207 = True.
Proof. exact (EQ_MP (@lem3171867) (@lem3171865)). Qed.
Lemma lem3171869 : term201 = True.
Proof. exact (TRANS (@lem3171864) (@lem3171868)). Qed.
Lemma lem3171870 : True = term201.
Proof. exact (SYM (@lem3171869)). Qed.
Lemma lem3171871 : term201.
Proof. exact (EQ_MP (@lem3171870) (@lem0)). Qed.
Lemma lem3171872 : term317 = term320.
Proof. exact (@lem3171861 (@lem3171871)). Qed.
Lemma lem3171874 (m : nat) (n : nat) : (term113 m n) = (term114 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3171875 : term305 = term306.
Proof. exact (@lem3171874 term299 term36). Qed.
Lemma lem3171876 : term307 = term297.
Proof. exact (@lem996237 term297). Qed.
Lemma lem3171877 : (term307 = term297) = (term308 = term299).
Proof. exact (@lem1007663 term297 (BIT1 0) term297). Qed.
Lemma lem3171878 : term308 = term299.
Proof. exact (EQ_MP (@lem3171877) (@lem3171876)). Qed.
Lemma lem3171879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3171880 : term309 = term301.
Proof. exact (MK_COMB (@lem3171879) (@lem3171878)). Qed.
Lemma lem3171881 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3171882 : term306 = term290.
Proof. exact (MK_COMB (@lem3171881) (@lem3171880)). Qed.
Lemma lem3171883 : term305 = term290.
Proof. exact (TRANS (@lem3171875) (@lem3171882)). Qed.
Lemma lem3171885 (x : nat) : (term211 x) = term42.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3171886 : term212 = term42.
Proof. exact (@lem3171885 term36). Qed.
Lemma lem3171887 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3171888 : term260 = term60.
Proof. exact (MK_COMB (@lem3171887) (@lem3171886)). Qed.
Lemma lem3171889 : term320 = term316.
Proof. exact (MK_COMB (@lem3171888) (@lem3171883)). Qed.
Lemma lem3171891 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3171892 : term316 = term321.
Proof. exact (@lem3171891 (NUMERAL 0) term299). Qed.
Lemma lem3171893 : term322 = term297.
Proof. exact (@lem912803). Qed.
Lemma lem3171894 (h1 : term322 = term297) : (term299 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term297 h1). Qed.
Lemma lem3171895 : (term322 = term297) = ((term299 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term322 = term297 => @lem3171894 h1) (fun h1 : (term299 = (NUMERAL 0)) = False => @lem3171893)). Qed.
Lemma lem3171896 : (term299 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3171895) (@lem3171893)). Qed.
Lemma lem3171897 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3171898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3171899 : term264 = (and True).
Proof. exact (MK_COMB (@lem3171898) (@lem3171897)). Qed.
Lemma lem3171900 : term321 = (True /\ False).
Proof. exact (MK_COMB (@lem3171899) (@lem3171896)). Qed.
Lemma lem3171902 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3171903 : term321 = False.
Proof. exact (TRANS (@lem3171900) (@lem3171902)). Qed.
Lemma lem3171904 : term316 = False.
Proof. exact (TRANS (@lem3171892) (@lem3171903)). Qed.
Lemma lem3171905 : term320 = False.
Proof. exact (TRANS (@lem3171889) (@lem3171904)). Qed.
Lemma lem3171906 : term317 = False.
Proof. exact (TRANS (@lem3171872) (@lem3171905)). Qed.
Lemma lem3171907 : term316 = False.
Proof. exact (TRANS (@lem3171849) (@lem3171906)). Qed.
Lemma lem3171908 : term315 = False.
Proof. exact (TRANS (@lem3171840) (@lem3171907)). Qed.
Lemma lem3171909 (n : int) (h1 : term323 n) : False.
Proof. exact (EQ_MP (@lem3171908) (@lem3171837 n h1)). Qed.
Lemma lem3171910 (n : int) (h1 : term193 n) : False.
Proof. exact (or_elim (@lem3170969 n h1) (fun h0 : term281 n => @lem3171439 n h0) (fun h0 : term323 n => @lem3171909 n h0)). Qed.
Lemma lem3171911 (n : int) (h1 : term198 n) : False.
Proof. exact (or_elim (@lem3170270 n h1) (fun h0 : term195 n => @lem3170968 n h0) (fun h0 : term193 n => @lem3171910 n h0)). Qed.
Lemma lem3171913 (n : int) (h1 : term198 n) : term198 n.
Proof. exact (h1). Qed.
Lemma lem3171914 (n : int) (h1 : term198 n) : (term198 n) = False.
Proof. exact (prop_ext (fun h2 : term198 n => @lem3171911 n h1) (fun h2 : False => @lem3171913 n h1)). Qed.
Lemma lem3171915 (n : int) (h1 : term198 n) : False.
Proof. exact (EQ_MP (@lem3171914 n h1) (@lem3171913 n h1)). Qed.
Lemma lem3171916 (n : int) (h1 : term90 n) : term90 n.
Proof. exact (h1). Qed.
Lemma lem3171917 (n : int) (h1 : term90 n) : term198 n.
Proof. exact (EQ_MP (@lem3170248 n) (@lem3171916 n h1)). Qed.
Lemma lem3171918 (n : int) (h1 : term90 n) : (term198 n) = False.
Proof. exact (prop_ext (fun h2 : term198 n => @lem3171915 n h2) (fun h2 : False => @lem3171917 n h1)). Qed.
Lemma lem3171919 (n : int) (h1 : term90 n) : False.
Proof. exact (EQ_MP (@lem3171918 n h1) (@lem3171917 n h1)). Qed.
Lemma lem3171920 (n : int) : term324 n.
Proof. exact (fun h0 : term90 n => @lem3171919 n h0). Qed.
Lemma lem3171921 (n : int) : term325 n.
Proof. exact (@lem1386578 (term326 n)). Qed.
Lemma lem3171924 (n : int) : term326 n.
Proof. exact (@lem3171921 n (@lem3171920 n)). Qed.
Lemma lem3171925 (n : int) : (term88 n) = (term18 n).
Proof. exact (SYM (@lem3169708 n)). Qed.
Lemma lem3171926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3171927 (n : int) : (term326 n) = (term0 n).
Proof. exact (MK_COMB (@lem3171926) (@lem3171925 n)). Qed.
Lemma lem3171928 (n : int) : term0 n.
Proof. exact (EQ_MP (@lem3171927 n) (@lem3171924 n)). Qed.
Lemma lem3171929 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem3169501 n) (@lem3171928 n)). Qed.
Lemma lem3171930 (n : int) : term327 n.
Proof. exact (@lem9784 (n = term23)). Qed.
Lemma lem3171931 (n : int) : (term327 n) = (term328 n).
Proof. exact (eq_refl (term327 n)). Qed.
Lemma lem3171932 (n : int) : term328 n.
Proof. exact (EQ_MP (@lem3171931 n) (@lem3171930 n)). Qed.
Lemma lem3171934 (n : int) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem3171935 (x : real) : term329 x.
Proof. exact (@lem3169346 x). Qed.
Lemma lem3171936 (x : real) : (term329 x) = ((term330 x) = term35).
Proof. exact (eq_refl (term329 x)). Qed.
Lemma lem3171941 (n : int) (h1 : n = term23) : n = term23.
Proof. exact (h1). Qed.
Lemma lem3171942 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem3171943 (n : int) (h1 : n = term23) : (int_neg n) = term331.
Proof. exact (MK_COMB (@lem3171942) (@lem3171941 n h1)). Qed.
Lemma lem3171945 : term331 = term23.
Proof. exact (EQ_MP (@lem2306330) (@lem1362041)). Qed.
Lemma lem3171946 (n : int) (h1 : n = term23) : (int_neg n) = term23.
Proof. exact (TRANS (@lem3171943 n h1) (@lem3171945)). Qed.
Lemma lem3171947 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3171948 (x : real) (n : int) (h1 : n = term23) : (term332 x n) = (term330 x).
Proof. exact (MK_COMB (@lem3171947 x) (@lem3171946 n h1)). Qed.
Lemma lem3171950 (x : real) : (term330 x) = term35.
Proof. exact (EQ_MP (@lem3171936 x) (@lem3171935 x)). Qed.
Lemma lem3171951 (x : real) (n : int) (h1 : n = term23) : (term332 x n) = term35.
Proof. exact (TRANS (@lem3171948 x n h1) (@lem3171950 x)). Qed.
Lemma lem3171952 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3171953 (x : real) (n : int) (h1 : n = term23) : (term333 x n) = term334.
Proof. exact (MK_COMB (@lem3171952) (@lem3171951 x n h1)). Qed.
Lemma lem3171955 (n : int) (h1 : n = term23) : n = term23.
Proof. exact (h1). Qed.
Lemma lem3171956 (x : real) : (real_zpow x) = (real_zpow x).
Proof. exact (eq_refl (real_zpow x)). Qed.
Lemma lem3171957 (x : real) (n : int) (h1 : n = term23) : (real_zpow x n) = (term330 x).
Proof. exact (MK_COMB (@lem3171956 x) (@lem3171955 n h1)). Qed.
Lemma lem3171959 (x : real) : (term330 x) = term35.
Proof. exact (EQ_MP (@lem3171936 x) (@lem3171935 x)). Qed.
Lemma lem3171960 (x : real) (n : int) (h1 : n = term23) : (real_zpow x n) = term35.
Proof. exact (TRANS (@lem3171957 x n h1) (@lem3171959 x)). Qed.
Lemma lem3171961 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3171962 (x : real) (n : int) (h1 : n = term23) : (term335 x n) = term336.
Proof. exact (MK_COMB (@lem3171961) (@lem3171960 x n h1)). Qed.
Lemma lem3171964 : term336 = term35.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem3171965 (x : real) (n : int) (h1 : n = term23) : (term335 x n) = term35.
Proof. exact (TRANS (@lem3171962 x n h1) (@lem3171964)). Qed.
Lemma lem3171966 (x : real) (n : int) (h1 : n = term23) : ((term332 x n) = (term335 x n)) = (term35 = term35).
Proof. exact (MK_COMB (@lem3171953 x n h1) (@lem3171965 x n h1)). Qed.
Lemma lem3171968 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3171969 (x : real) : (x = x) = True.
Proof. exact (@lem3171968 real x). Qed.
Lemma lem3171970 : (term35 = term35) = True.
Proof. exact (@lem3171969 term35). Qed.
Lemma lem3171971 (x : real) (n : int) (h1 : n = term23) : ((term332 x n) = (term335 x n)) = True.
Proof. exact (TRANS (@lem3171966 x n h1) (@lem3171970)). Qed.
Lemma lem3171972 (x : real) (n : int) (h1 : n = term23) : True = ((term332 x n) = (term335 x n)).
Proof. exact (SYM (@lem3171971 x n h1)). Qed.
Lemma lem3171973 (x : real) (n : int) (h1 : n = term23) : (term332 x n) = (term335 x n).
Proof. exact (EQ_MP (@lem3171972 x n h1) (@lem0)). Qed.
Lemma lem3171994 (n : int) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem3171995 (n : int) (h1 : term19 n) : (term13 n) = (term14 n).
Proof. exact (@lem3171929 n (@lem3171994 n h1)). Qed.
Lemma lem3172001 (x : int) : term337 x.
Proof. exact (@lem2306663 x). Qed.
Lemma lem3172002 (x : int) : (term337 x) = ((term338 x) = x).
Proof. exact (eq_refl (term337 x)). Qed.
Lemma lem3172004 {A : Type'} (p : Prop) : term339 A p.
Proof. exact (@lem13262 A p). Qed.
Lemma lem3172005 {A : Type'} (p : Prop) : (term339 A p) = (term340 A p).
Proof. exact (eq_refl (term339 A p)). Qed.
Lemma lem3172006 {A : Type'} (p : Prop) : term340 A p.
Proof. exact (EQ_MP (@lem3172005 A p) (@lem3172004 A p)). Qed.
Lemma lem3172007 {A : Type'} (p : Prop) (x : A) : term341 A p x.
Proof. exact (@lem3172006 A p x). Qed.
Lemma lem3172008 {A : Type'} (p : Prop) (x : A) : (term341 A p x) = (term342 A p x).
Proof. exact (eq_refl (term341 A p x)). Qed.
Lemma lem3172009 {A : Type'} (p : Prop) (x : A) : term342 A p x.
Proof. exact (EQ_MP (@lem3172008 A p x) (@lem3172007 A p x)). Qed.
Lemma lem3172010 {A : Type'} (p : Prop) (x : A) (y : A) : term343 A p x y.
Proof. exact (@lem3172009 A p x y). Qed.
Lemma lem3172011 {A : Type'} (p : Prop) (y : A) (x : A) : (term343 A p x y) = ((term344 A p x y) = (@COND A p y x)).
Proof. exact (eq_refl (term343 A p x y)). Qed.
Lemma lem3172013 (z : real) : term345 z.
Proof. exact (@lem3169164 z). Qed.
Lemma lem3172014 (z : real) : (term345 z) = (term346 z).
Proof. exact (eq_refl (term345 z)). Qed.
Lemma lem3172015 (z : real) : term346 z.
Proof. exact (EQ_MP (@lem3172014 z) (@lem3172013 z)). Qed.
Lemma lem3172016 (z : real) (i : int) : term347 z i.
Proof. exact (@lem3172015 z i). Qed.
Lemma lem3172017 (z : real) (i : int) : (term347 z i) = ((real_zpow z i) = (term348 z i)).
Proof. exact (eq_refl (term347 z i)). Qed.
Lemma lem3172019 (n : int) : term349 n.
Proof. exact (@lem82 (n = term23)). Qed.
Lemma lem3172035 (z : real) (i : int) : (real_zpow z i) = (term348 z i).
Proof. exact (EQ_MP (@lem3172017 z i) (@lem3172016 z i)). Qed.
Lemma lem3172036 (x : real) (n : int) : (term332 x n) = (term350 x n).
Proof. exact (@lem3172035 x (int_neg n)). Qed.
Lemma lem3172038 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term351 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3172039 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term352 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3172038 _2963 g t e g' t' e'). Qed.
Lemma lem3172040 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term353 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3172039 _2963 g t e g' t'). Qed.
Lemma lem3172041 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term354 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3172040 _2963 g t e g'). Qed.
Lemma lem3172042 (g : Prop) (t : real) (e : real) : term355 g t e.
Proof. exact (@lem3172041 real g t e). Qed.
Lemma lem3172043 (x : real) (n : int) : term356 x n.
Proof. exact (@lem3172042 (term13 n) (term357 x n) (term358 x n)). Qed.
Lemma lem3172044 (x : real) (n : int) (g' : Prop) : term359 x n g'.
Proof. exact (@lem3172043 x n g'). Qed.
Lemma lem3172045 (x : real) (n : int) (g' : Prop) : (term359 x n g') = (term360 x n g').
Proof. exact (eq_refl (term359 x n g')). Qed.
Lemma lem3172046 (x : real) (n : int) (g' : Prop) : term360 x n g'.
Proof. exact (EQ_MP (@lem3172045 x n g') (@lem3172044 x n g')). Qed.
Lemma lem3172047 (x : real) (n : int) (g' : Prop) (t' : real) : term361 x n g' t'.
Proof. exact (@lem3172046 x n g' t'). Qed.
Lemma lem3172048 (x : real) (n : int) (g' : Prop) (t' : real) : (term361 x n g' t') = (term362 x n g' t').
Proof. exact (eq_refl (term361 x n g' t')). Qed.
Lemma lem3172049 (x : real) (n : int) (g' : Prop) (t' : real) : term362 x n g' t'.
Proof. exact (EQ_MP (@lem3172048 x n g' t') (@lem3172047 x n g' t')). Qed.
Lemma lem3172050 (x : real) (n : int) (g' : Prop) (t' : real) (e' : real) : term363 x n g' t' e'.
Proof. exact (@lem3172049 x n g' t' e'). Qed.
Lemma lem3172051 (x : real) (n : int) (g' : Prop) (t' : real) (e' : real) : (term363 x n g' t' e') = (term364 x n g' t' e').
Proof. exact (eq_refl (term363 x n g' t' e')). Qed.
Lemma lem3172052 (x : real) (n : int) (g' : Prop) (t' : real) (e' : real) : term364 x n g' t' e'.
Proof. exact (EQ_MP (@lem3172051 x n g' t' e') (@lem3172050 x n g' t' e')). Qed.
Lemma lem3172054 (n : int) : term1 n.
Proof. exact (fun h0 : term19 n => @lem3171995 n h0). Qed.
Lemma lem3172056 (n : int) (h1 : term19 n) : (n = term23) = False.
Proof. exact (@lem3172019 n (@lem3171934 n h1)). Qed.
Lemma lem3172057 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3172058 (n : int) (h1 : term19 n) : (term19 n) = (~ False).
Proof. exact (MK_COMB (@lem3172057) (@lem3172056 n h1)). Qed.
Lemma lem3172060 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3172061 (n : int) (h1 : term19 n) : (term19 n) = True.
Proof. exact (TRANS (@lem3172058 n h1) (@lem3172060)). Qed.
Lemma lem3172062 (n : int) (h1 : term19 n) : True = (term19 n).
Proof. exact (SYM (@lem3172061 n h1)). Qed.
Lemma lem3172063 (n : int) (h1 : term19 n) : term19 n.
Proof. exact (EQ_MP (@lem3172062 n h1) (@lem0)). Qed.
Lemma lem3172064 (n : int) (h1 : term19 n) : (term13 n) = (term14 n).
Proof. exact (@lem3172054 n (@lem3172063 n h1)). Qed.
Lemma lem3172065 (x : real) (n : int) (t' : real) (e' : real) : term365 x n t' e'.
Proof. exact (@lem3172052 x n (term14 n) t' e'). Qed.
Lemma lem3172066 (x : real) (t' : real) (e' : real) (n : int) (h1 : term19 n) : term366 x n t' e'.
Proof. exact (@lem3172065 x n t' e' (@lem3172064 n h1)). Qed.
Lemma lem3172070 (x : real) (n : int) : (term357 x n) = (term357 x n).
Proof. exact (eq_refl (term357 x n)). Qed.
Lemma lem3172071 (x : real) (n : int) : term367 x n.
Proof. exact (fun h0 : term14 n => @lem3172070 x n). Qed.
Lemma lem3172072 (x : real) (e' : real) (n : int) (h1 : term19 n) : term368 x n e'.
Proof. exact (@lem3172066 x (term357 x n) e' n h1). Qed.
Lemma lem3172073 (x : real) (e' : real) (n : int) (h1 : term19 n) : term369 x n e'.
Proof. exact (@lem3172072 x e' n h1 (@lem3172071 x n)). Qed.
Lemma lem3172078 (x : int) : (term338 x) = x.
Proof. exact (EQ_MP (@lem3172002 x) (@lem3172001 x)). Qed.
Lemma lem3172079 (n : int) : (term338 n) = n.
Proof. exact (@lem3172078 n). Qed.
Lemma lem3172080 : num_of_int = num_of_int.
Proof. exact (eq_refl num_of_int). Qed.
Lemma lem3172081 (n : int) : (term370 n) = (num_of_int n).
Proof. exact (MK_COMB (@lem3172080) (@lem3172079 n)). Qed.
Lemma lem3172082 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem3172083 (x : real) (n : int) : (term371 x n) = (term372 x n).
Proof. exact (MK_COMB (@lem3172082 x) (@lem3172081 n)). Qed.
Lemma lem3172084 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3172085 (x : real) (n : int) : (term358 x n) = (term373 x n).
Proof. exact (MK_COMB (@lem3172084) (@lem3172083 x n)). Qed.
Lemma lem3172086 (x : real) (n : int) : term374 x n.
Proof. exact (fun h0 : term2 n => @lem3172085 x n). Qed.
Lemma lem3172087 (x : real) (n : int) (h1 : term19 n) : term375 x n.
Proof. exact (@lem3172073 x (term373 x n) n h1). Qed.
Lemma lem3172088 (x : real) (n : int) (h1 : term19 n) : (term350 x n) = (term376 x n).
Proof. exact (@lem3172087 x n h1 (@lem3172086 x n)). Qed.
Lemma lem3172090 {A : Type'} (p : Prop) (y : A) (x : A) : (term344 A p x y) = (@COND A p y x).
Proof. exact (EQ_MP (@lem3172011 A p y x) (@lem3172010 A p x y)). Qed.
Lemma lem3172091 (p : Prop) (y : real) (x : real) : (term377 p x y) = (@COND real p y x).
Proof. exact (@lem3172090 real p y x). Qed.
Lemma lem3172092 (x : real) (n : int) : (term376 x n) = (term378 x n).
Proof. exact (@lem3172091 (term3 n) (term373 x n) (term357 x n)). Qed.
Lemma lem3172126 (x : real) (n : int) (h1 : term19 n) : (term350 x n) = (term378 x n).
Proof. exact (TRANS (@lem3172088 x n h1) (@lem3172092 x n)). Qed.
Lemma lem3172127 (x : real) (n : int) (h1 : term19 n) : (term332 x n) = (term378 x n).
Proof. exact (TRANS (@lem3172036 x n) (@lem3172126 x n h1)). Qed.
Lemma lem3172128 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3172129 (x : real) (n : int) (h1 : term19 n) : (term333 x n) = (term379 x n).
Proof. exact (MK_COMB (@lem3172128) (@lem3172127 x n h1)). Qed.
Lemma lem3172164 (z : real) (i : int) : (real_zpow z i) = (term348 z i).
Proof. exact (EQ_MP (@lem3172017 z i) (@lem3172016 z i)). Qed.
Lemma lem3172165 (x : real) (n : int) : (real_zpow x n) = (term348 x n).
Proof. exact (@lem3172164 x n). Qed.
Lemma lem3172199 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3172200 (x : real) (n : int) : (term335 x n) = (term380 x n).
Proof. exact (MK_COMB (@lem3172199) (@lem3172165 x n)). Qed.
Lemma lem3172234 (x : real) (n : int) (h1 : term19 n) : ((term332 x n) = (term335 x n)) = ((term378 x n) = (term380 x n)).
Proof. exact (MK_COMB (@lem3172129 x n h1) (@lem3172200 x n)). Qed.
Lemma lem3172303 (x : real) (n : int) (h1 : term19 n) : ((term378 x n) = (term380 x n)) = ((term332 x n) = (term335 x n)).
Proof. exact (SYM (@lem3172234 x n h1)). Qed.
Lemma lem3172305 (p : Prop) : p = (term381 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3172306 (x : real) (n : int) : ((term378 x n) = (term380 x n)) = (term382 x n).
Proof. exact (@lem3172305 ((term378 x n) = (term380 x n))). Qed.
Lemma lem3172307 (x : real) (n : int) : (term382 x n) = ((term378 x n) = (term380 x n)).
Proof. exact (SYM (@lem3172306 x n)). Qed.
Lemma lem3172308 (x : real) (n : int) (h1 : term383 x n) : term383 x n.
Proof. exact (h1). Qed.
Lemma lem3172311 (x : real) (n : int) (h1 : term384 x n) : term384 x n.
Proof. exact (h1). Qed.
Lemma lem3172312 (x : real) (n : int) : term385 x n.
Proof. exact (fun h0 : term384 x n => @lem3172311 x n h0). Qed.
Lemma lem3172313 (x : real) (n : int) (h1 : term385 x n) : term385 x n.
Proof. exact (h1). Qed.
Lemma lem3172314 (x : real) (n : int) (h1 : term384 x n) : term384 x n.
Proof. exact (h1). Qed.
Lemma lem3172315 (x : real) (n : int) (h1 : term384 x n) (h2 : term385 x n) : term384 x n.
Proof. exact (@lem3172313 x n h2 (@lem3172314 x n h1)). Qed.
Lemma lem3172316 (x : real) (n : int) (h1 : term384 x n) : term386 x n.
Proof. exact (fun h0 : term385 x n => @lem3172315 x n h1 h0). Qed.
Lemma lem3172317 (x : real) (n : int) (h1 : term385 x n) : term385 x n.
Proof. exact (h1). Qed.
Lemma lem3172318 (x : real) (n : int) (h1 : term384 x n) (h2 : term385 x n) : term384 x n.
Proof. exact (@lem3172316 x n h1 (@lem3172317 x n h2)). Qed.
Lemma lem3172319 (x : real) (n : int) (h1 : term385 x n) : term385 x n.
Proof. exact (fun h0 : term384 x n => @lem3172318 x n h0 h1). Qed.
Lemma lem3172320 (x : real) (n : int) : term387 x n.
Proof. exact (fun h0 : term385 x n => @lem3172319 x n h0). Qed.
Lemma lem3172323 (x : real) (n : int) : term385 x n.
Proof. exact (@lem3172320 x n (@lem3172312 x n)). Qed.
Lemma lem3172335 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3172336 : term388 = term389.
Proof. exact (@lem3172335 term390). Qed.
Lemma lem3172341 (x : real) (n : int) : (term391 x n) = (term391 x n).
Proof. exact (eq_refl (term391 x n)). Qed.
Lemma lem3172342 (x : real) (n : int) : (term384 x n) = (term392 x n).
Proof. exact (MK_COMB (@lem3172341 x n) (@lem3172336)). Qed.
Lemma lem3172345 (n : int) : (term393 n) = (term394 n).
Proof. exact (fun_ext (fun x : real => @lem3172342 x n)). Qed.
Lemma lem3172346 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172347 (n : int) : (term395 n) = (term396 n).
Proof. exact (MK_COMB (@lem3172346) (@lem3172345 n)). Qed.
Lemma lem3172352 : term397 = term398.
Proof. exact (fun_ext (fun n : int => @lem3172347 n)). Qed.
Lemma lem3172353 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3172362 : term399 = term400.
Proof. exact (MK_COMB (@lem3172353) (@lem3172352)). Qed.
Lemma lem3172366 (n : int) (h1 : (term3 n) = False) : (term3 n) = False.
Proof. exact (h1). Qed.
Lemma lem3172367 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3172368 (n : int) (h1 : (term3 n) = False) : (term401 n) = (@COND real False).
Proof. exact (MK_COMB (@lem3172367) (@lem3172366 n h1)). Qed.
Lemma lem3172369 (x : real) (n : int) : (term373 x n) = (term373 x n).
Proof. exact (eq_refl (term373 x n)). Qed.
Lemma lem3172370 (x : real) (n : int) (h1 : (term3 n) = False) : (term402 x n) = (term403 x n).
Proof. exact (MK_COMB (@lem3172368 n h1) (@lem3172369 x n)). Qed.
Lemma lem3172371 (x : real) (n : int) : (term357 x n) = (term357 x n).
Proof. exact (eq_refl (term357 x n)). Qed.
Lemma lem3172372 (x : real) (n : int) (h1 : (term3 n) = False) : (term378 x n) = (term404 x n).
Proof. exact (MK_COMB (@lem3172370 x n h1) (@lem3172371 x n)). Qed.
Lemma lem3172374 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3172375 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem3172374 real t1 t2). Qed.
Lemma lem3172376 (x : real) (n : int) : (term404 x n) = (term357 x n).
Proof. exact (@lem3172375 (term373 x n) (term357 x n)). Qed.
Lemma lem3172377 (x : real) (n : int) (h1 : (term3 n) = False) : (term378 x n) = (term357 x n).
Proof. exact (TRANS (@lem3172372 x n h1) (@lem3172376 x n)). Qed.
Lemma lem3172378 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3172379 (x : real) (n : int) (h1 : (term3 n) = False) : (term379 x n) = (term405 x n).
Proof. exact (MK_COMB (@lem3172378) (@lem3172377 x n h1)). Qed.
Lemma lem3172381 (n : int) (h1 : (term3 n) = False) : (term3 n) = False.
Proof. exact (h1). Qed.
Lemma lem3172382 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3172383 (n : int) (h1 : (term3 n) = False) : (term401 n) = (@COND real False).
Proof. exact (MK_COMB (@lem3172382) (@lem3172381 n h1)). Qed.
Lemma lem3172384 (x : real) (n : int) : (term372 x n) = (term372 x n).
Proof. exact (eq_refl (term372 x n)). Qed.
Lemma lem3172385 (x : real) (n : int) (h1 : (term3 n) = False) : (term406 x n) = (term407 x n).
Proof. exact (MK_COMB (@lem3172383 n h1) (@lem3172384 x n)). Qed.
Lemma lem3172386 (x : real) (n : int) : (term408 x n) = (term408 x n).
Proof. exact (eq_refl (term408 x n)). Qed.
Lemma lem3172387 (x : real) (n : int) (h1 : (term3 n) = False) : (term348 x n) = (term409 x n).
Proof. exact (MK_COMB (@lem3172385 x n h1) (@lem3172386 x n)). Qed.
Lemma lem3172389 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3172390 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem3172389 real t1 t2). Qed.
Lemma lem3172391 (x : real) (n : int) : (term409 x n) = (term408 x n).
Proof. exact (@lem3172390 (term372 x n) (term408 x n)). Qed.
Lemma lem3172392 (x : real) (n : int) (h1 : (term3 n) = False) : (term348 x n) = (term408 x n).
Proof. exact (TRANS (@lem3172387 x n h1) (@lem3172391 x n)). Qed.
Lemma lem3172393 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3172394 (x : real) (n : int) (h1 : (term3 n) = False) : (term380 x n) = (term410 x n).
Proof. exact (MK_COMB (@lem3172393) (@lem3172392 x n h1)). Qed.
Lemma lem3172395 (x : real) (n : int) (h1 : (term3 n) = False) : ((term378 x n) = (term380 x n)) = ((term357 x n) = (term410 x n)).
Proof. exact (MK_COMB (@lem3172379 x n h1) (@lem3172394 x n h1)). Qed.
Lemma lem3172398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3172399 (x : real) (n : int) (h1 : (term3 n) = False) : (term383 x n) = (term411 x n).
Proof. exact (MK_COMB (@lem3172398) (@lem3172395 x n h1)). Qed.
Lemma lem3172400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3172401 (x : real) (n : int) (h1 : (term3 n) = False) : (term391 x n) = (term412 x n).
Proof. exact (MK_COMB (@lem3172400) (@lem3172399 x n h1)). Qed.
Lemma lem3172408 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem3172409 (x : real) (n : int) (h1 : (term3 n) = False) : (term392 x n) = (term413 x n).
Proof. exact (MK_COMB (@lem3172401 x n h1) (@lem3172408)). Qed.
Lemma lem3172412 (n : int) (h1 : (term3 n) = False) : (term394 n) = (term414 n).
Proof. exact (fun_ext (fun x : real => @lem3172409 x n h1)). Qed.
Lemma lem3172413 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172414 (n : int) (h1 : (term3 n) = False) : (term396 n) = (term415 n).
Proof. exact (MK_COMB (@lem3172413) (@lem3172412 n h1)). Qed.
Lemma lem3172419 (n : int) : term416 n.
Proof. exact (fun h0 : (term3 n) = False => @lem3172414 n h0). Qed.
Lemma lem3172421 (n : int) (h1 : (term3 n) = True) : (term3 n) = True.
Proof. exact (h1). Qed.
Lemma lem3172422 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3172423 (n : int) (h1 : (term3 n) = True) : (term401 n) = (@COND real True).
Proof. exact (MK_COMB (@lem3172422) (@lem3172421 n h1)). Qed.
Lemma lem3172424 (x : real) (n : int) : (term373 x n) = (term373 x n).
Proof. exact (eq_refl (term373 x n)). Qed.
Lemma lem3172425 (x : real) (n : int) (h1 : (term3 n) = True) : (term402 x n) = (term417 x n).
Proof. exact (MK_COMB (@lem3172423 n h1) (@lem3172424 x n)). Qed.
Lemma lem3172426 (x : real) (n : int) : (term357 x n) = (term357 x n).
Proof. exact (eq_refl (term357 x n)). Qed.
Lemma lem3172427 (x : real) (n : int) (h1 : (term3 n) = True) : (term378 x n) = (term418 x n).
Proof. exact (MK_COMB (@lem3172425 x n h1) (@lem3172426 x n)). Qed.
Lemma lem3172429 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3172430 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem3172429 real t2 t1). Qed.
Lemma lem3172431 (x : real) (n : int) : (term418 x n) = (term373 x n).
Proof. exact (@lem3172430 (term357 x n) (term373 x n)). Qed.
Lemma lem3172432 (x : real) (n : int) (h1 : (term3 n) = True) : (term378 x n) = (term373 x n).
Proof. exact (TRANS (@lem3172427 x n h1) (@lem3172431 x n)). Qed.
Lemma lem3172433 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3172434 (x : real) (n : int) (h1 : (term3 n) = True) : (term379 x n) = (term419 x n).
Proof. exact (MK_COMB (@lem3172433) (@lem3172432 x n h1)). Qed.
Lemma lem3172436 (n : int) (h1 : (term3 n) = True) : (term3 n) = True.
Proof. exact (h1). Qed.
Lemma lem3172437 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem3172438 (n : int) (h1 : (term3 n) = True) : (term401 n) = (@COND real True).
Proof. exact (MK_COMB (@lem3172437) (@lem3172436 n h1)). Qed.
Lemma lem3172439 (x : real) (n : int) : (term372 x n) = (term372 x n).
Proof. exact (eq_refl (term372 x n)). Qed.
Lemma lem3172440 (x : real) (n : int) (h1 : (term3 n) = True) : (term406 x n) = (term420 x n).
Proof. exact (MK_COMB (@lem3172438 n h1) (@lem3172439 x n)). Qed.
Lemma lem3172441 (x : real) (n : int) : (term408 x n) = (term408 x n).
Proof. exact (eq_refl (term408 x n)). Qed.
Lemma lem3172442 (x : real) (n : int) (h1 : (term3 n) = True) : (term348 x n) = (term421 x n).
Proof. exact (MK_COMB (@lem3172440 x n h1) (@lem3172441 x n)). Qed.
Lemma lem3172444 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3172445 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem3172444 real t2 t1). Qed.
Lemma lem3172446 (x : real) (n : int) : (term421 x n) = (term372 x n).
Proof. exact (@lem3172445 (term408 x n) (term372 x n)). Qed.
Lemma lem3172447 (x : real) (n : int) (h1 : (term3 n) = True) : (term348 x n) = (term372 x n).
Proof. exact (TRANS (@lem3172442 x n h1) (@lem3172446 x n)). Qed.
Lemma lem3172448 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3172449 (x : real) (n : int) (h1 : (term3 n) = True) : (term380 x n) = (term373 x n).
Proof. exact (MK_COMB (@lem3172448) (@lem3172447 x n h1)). Qed.
Lemma lem3172450 (x : real) (n : int) (h1 : (term3 n) = True) : ((term378 x n) = (term380 x n)) = ((term373 x n) = (term373 x n)).
Proof. exact (MK_COMB (@lem3172434 x n h1) (@lem3172449 x n h1)). Qed.
Lemma lem3172452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3172453 (x : real) : (x = x) = True.
Proof. exact (@lem3172452 real x). Qed.
Lemma lem3172454 (x : real) (n : int) : ((term373 x n) = (term373 x n)) = True.
Proof. exact (@lem3172453 (term373 x n)). Qed.
Lemma lem3172455 (x : real) (n : int) (h1 : (term3 n) = True) : ((term378 x n) = (term380 x n)) = True.
Proof. exact (TRANS (@lem3172450 x n h1) (@lem3172454 x n)). Qed.
Lemma lem3172456 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3172457 (x : real) (n : int) (h1 : (term3 n) = True) : (term383 x n) = (~ True).
Proof. exact (MK_COMB (@lem3172456) (@lem3172455 x n h1)). Qed.
Lemma lem3172459 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3172460 (x : real) (n : int) (h1 : (term3 n) = True) : (term383 x n) = False.
Proof. exact (TRANS (@lem3172457 x n h1) (@lem3172459)). Qed.
Lemma lem3172461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3172462 (x : real) (n : int) (h1 : (term3 n) = True) : (term391 x n) = (imp False).
Proof. exact (MK_COMB (@lem3172461) (@lem3172460 x n h1)). Qed.
Lemma lem3172469 : term389 = term389.
Proof. exact (eq_refl term389). Qed.
Lemma lem3172470 (x : real) (n : int) (h1 : (term3 n) = True) : (term392 x n) = term422.
Proof. exact (MK_COMB (@lem3172462 x n h1) (@lem3172469)). Qed.
Lemma lem3172472 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3172473 : term422 = True.
Proof. exact (@lem3172472 term389). Qed.
Lemma lem3172474 (x : real) (n : int) (h1 : (term3 n) = True) : (term392 x n) = True.
Proof. exact (TRANS (@lem3172470 x n h1) (@lem3172473)). Qed.
Lemma lem3172475 (n : int) (h1 : (term3 n) = True) : (term394 n) = term423.
Proof. exact (fun_ext (fun x : real => @lem3172474 x n h1)). Qed.
Lemma lem3172476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172477 (n : int) (h1 : (term3 n) = True) : (term396 n) = term424.
Proof. exact (MK_COMB (@lem3172476) (@lem3172475 n h1)). Qed.
Lemma lem3172479 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3172480 (t : Prop) : (term426 t) = t.
Proof. exact (@lem3172479 real t). Qed.
Lemma lem3172481 : term424 = True.
Proof. exact (@lem3172480 True). Qed.
Lemma lem3172482 (n : int) (h1 : (term3 n) = True) : (term396 n) = True.
Proof. exact (TRANS (@lem3172477 n h1) (@lem3172481)). Qed.
Lemma lem3172483 (n : int) : term427 n.
Proof. exact (fun h0 : (term3 n) = True => @lem3172482 n h0). Qed.
Lemma lem3172484 (n : int) : term428 n.
Proof. exact (conj (@lem3172419 n) (@lem3172483 n)). Qed.
Lemma lem3172486 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term429 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem3172487 (n : int) : term430 n.
Proof. exact (@lem3172486 (term396 n) True (term3 n) (term415 n)). Qed.
Lemma lem3172488 (n : int) : (term396 n) = (term431 n).
Proof. exact (@lem3172487 n (@lem3172484 n)). Qed.
Lemma lem3172491 (n : int) : (term432 n) = (term432 n).
Proof. exact (eq_refl (term432 n)). Qed.
Lemma lem3172493 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3172494 (n : int) : (term433 n) = True.
Proof. exact (@lem3172493 (term14 n)). Qed.
Lemma lem3172495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3172496 (n : int) : (term434 n) = (and True).
Proof. exact (MK_COMB (@lem3172495) (@lem3172494 n)). Qed.
Lemma lem3172497 (n : int) : (term431 n) = (term435 n).
Proof. exact (MK_COMB (@lem3172496 n) (@lem3172491 n)). Qed.
Lemma lem3172499 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3172500 (n : int) : (term435 n) = (term432 n).
Proof. exact (@lem3172499 (term432 n)). Qed.
Lemma lem3172501 (n : int) : (term431 n) = (term432 n).
Proof. exact (TRANS (@lem3172497 n) (@lem3172500 n)). Qed.
Lemma lem3172502 (n : int) : (term396 n) = (term432 n).
Proof. exact (TRANS (@lem3172488 n) (@lem3172501 n)). Qed.
Lemma lem3172503 (x : real) : ((term436 x) = x) = ((term436 x) = x).
Proof. exact (eq_refl ((term436 x) = x)). Qed.
Lemma lem3172504 : term437 = term437.
Proof. exact (fun_ext (fun x : real => @lem3172503 x)). Qed.
Lemma lem3172505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172506 : term390 = term390.
Proof. exact (MK_COMB (@lem3172505) (@lem3172504)). Qed.
Lemma lem3172507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3172508 : term389 = term389.
Proof. exact (MK_COMB (@lem3172507) (@lem3172506)). Qed.
Lemma lem3172513 (x : real) (n : int) : (term412 x n) = (term412 x n).
Proof. exact (eq_refl (term412 x n)). Qed.
Lemma lem3172514 (x : real) (n : int) : (term413 x n) = (term413 x n).
Proof. exact (MK_COMB (@lem3172513 x n) (@lem3172508)). Qed.
Lemma lem3172515 (n : int) : (term414 n) = (term414 n).
Proof. exact (fun_ext (fun x : real => @lem3172514 x n)). Qed.
Lemma lem3172516 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172517 (n : int) : (term415 n) = (term415 n).
Proof. exact (MK_COMB (@lem3172516) (@lem3172515 n)). Qed.
Lemma lem3172520 (n : int) : (term438 n) = (term438 n).
Proof. exact (eq_refl (term438 n)). Qed.
Lemma lem3172521 (n : int) : (term432 n) = (term432 n).
Proof. exact (MK_COMB (@lem3172520 n) (@lem3172517 n)). Qed.
Lemma lem3172522 (n : int) : (term439 n) = (term439 n).
Proof. exact (eq_refl (term439 n)). Qed.
Lemma lem3172523 (n : int) : ((term396 n) = (term432 n)) = ((term396 n) = (term432 n)).
Proof. exact (MK_COMB (@lem3172522 n) (@lem3172521 n)). Qed.
Lemma lem3172524 (n : int) : (term396 n) = (term432 n).
Proof. exact (EQ_MP (@lem3172523 n) (@lem3172502 n)). Qed.
Lemma lem3172525 : term398 = term440.
Proof. exact (fun_ext (fun n : int => @lem3172524 n)). Qed.
Lemma lem3172526 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3172527 : term400 = term441.
Proof. exact (MK_COMB (@lem3172526) (@lem3172525)). Qed.
Lemma lem3172552 : term399 = term441.
Proof. exact (TRANS (@lem3172362) (@lem3172527)). Qed.
Lemma lem3172553 : term441 = term399.
Proof. exact (SYM (@lem3172552)). Qed.
Lemma lem3172555 (p : Prop) : p = (term381 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3172556 (n : int) : (term432 n) = (term442 n).
Proof. exact (@lem3172555 (term432 n)). Qed.
Lemma lem3172557 (n : int) : (term442 n) = (term432 n).
Proof. exact (SYM (@lem3172556 n)). Qed.
Lemma lem3172558 (n : int) (h1 : term443 n) : term443 n.
Proof. exact (h1). Qed.
Lemma lem3172561 (x : real) : ((term436 x) = x) = ((term436 x) = x).
Proof. exact (eq_refl ((term436 x) = x)). Qed.
Lemma lem3172562 : term437 = term437.
Proof. exact (fun_ext (fun x : real => @lem3172561 x)). Qed.
Lemma lem3172563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172564 : term390 = term390.
Proof. exact (MK_COMB (@lem3172563) (@lem3172562)). Qed.
Lemma lem3172565 : term444 = term390.
Proof. exact (@lem16933 term390). Qed.
Lemma lem3172566 : term444 = term390.
Proof. exact (TRANS (@lem3172565) (@lem3172564)). Qed.
Lemma lem3172568 (x : real) (n : int) : (term445 x n) = (term445 x n).
Proof. exact (eq_refl (term445 x n)). Qed.
Lemma lem3172569 (x : real) (n : int) : (term446 x n) = (term447 x n).
Proof. exact (MK_COMB (@lem3172568 x n) (@lem3172566)). Qed.
Lemma lem3172570 (x : real) (n : int) : (term448 x n) = (term446 x n).
Proof. exact (@lem17362 (term411 x n) term389). Qed.
Lemma lem3172571 (x : real) (n : int) : (term448 x n) = (term447 x n).
Proof. exact (TRANS (@lem3172570 x n) (@lem3172569 x n)). Qed.
Lemma lem3172572 (P : real -> Prop) : (term449 P) = (term450 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem3172573 (n : int) : (term451 n) = (term452 n).
Proof. exact (@lem3172572 (term414 n)). Qed.
Lemma lem3172574 (x : real) (n : int) : (term453 n x) = (term413 x n).
Proof. exact (eq_refl (term453 n x)). Qed.
Lemma lem3172575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3172576 (x : real) (n : int) : (term454 n x) = (term448 x n).
Proof. exact (MK_COMB (@lem3172575) (@lem3172574 x n)). Qed.
Lemma lem3172577 (x : real) (n : int) : (term454 n x) = (term447 x n).
Proof. exact (TRANS (@lem3172576 x n) (@lem3172571 x n)). Qed.
Lemma lem3172578 (n : int) : (term455 n) = (term456 n).
Proof. exact (fun_ext (fun x : real => @lem3172577 x n)). Qed.
Lemma lem3172579 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172580 (n : int) : (term452 n) = (term457 n).
Proof. exact (MK_COMB (@lem3172579) (@lem3172578 n)). Qed.
Lemma lem3172581 (n : int) : (term451 n) = (term457 n).
Proof. exact (TRANS (@lem3172573 n) (@lem3172580 n)). Qed.
Lemma lem3172583 (n : int) : (term458 n) = (term458 n).
Proof. exact (eq_refl (term458 n)). Qed.
Lemma lem3172584 (n : int) : (term459 n) = (term460 n).
Proof. exact (MK_COMB (@lem3172583 n) (@lem3172581 n)). Qed.
Lemma lem3172585 (n : int) : (term443 n) = (term459 n).
Proof. exact (@lem17160 (term3 n) (term415 n)). Qed.
Lemma lem3172586 (n : int) : (term443 n) = (term460 n).
Proof. exact (TRANS (@lem3172585 n) (@lem3172584 n)). Qed.
Lemma lem3172608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term461 A P Q) = (term462 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem3172609 (P : real -> Prop) (Q : Prop) : (term463 P Q) = (term464 P Q).
Proof. exact (@lem3172608 real P Q). Qed.
Lemma lem3172610 (n : int) : (term465 n) = (term466 n).
Proof. exact (@lem3172609 (term467 n) term390). Qed.
Lemma lem3172611 (x : real) (n : int) : (term468 n x) = (term411 x n).
Proof. exact (eq_refl (term468 n x)). Qed.
Lemma lem3172612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3172613 (x : real) (n : int) : (term469 n x) = (term445 x n).
Proof. exact (MK_COMB (@lem3172612) (@lem3172611 x n)). Qed.
Lemma lem3172614 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem3172615 (x : real) (n : int) : (term470 n x) = (term447 x n).
Proof. exact (MK_COMB (@lem3172613 x n) (@lem3172614)). Qed.
Lemma lem3172616 (n : int) : (term471 n) = (term456 n).
Proof. exact (fun_ext (fun x : real => @lem3172615 x n)). Qed.
Lemma lem3172617 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172618 (n : int) : (term465 n) = (term457 n).
Proof. exact (MK_COMB (@lem3172617) (@lem3172616 n)). Qed.
Lemma lem3172619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3172620 (n : int) : (term472 n) = (term473 n).
Proof. exact (MK_COMB (@lem3172619) (@lem3172618 n)). Qed.
Lemma lem3172621 (x : real) (n : int) : (term468 n x) = (term411 x n).
Proof. exact (eq_refl (term468 n x)). Qed.
Lemma lem3172622 (n : int) : (term474 n) = (term467 n).
Proof. exact (fun_ext (fun x : real => @lem3172621 x n)). Qed.
Lemma lem3172623 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172624 (n : int) : (term475 n) = (term476 n).
Proof. exact (MK_COMB (@lem3172623) (@lem3172622 n)). Qed.
Lemma lem3172625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3172626 (n : int) : (term477 n) = (term478 n).
Proof. exact (MK_COMB (@lem3172625) (@lem3172624 n)). Qed.
Lemma lem3172627 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem3172628 (n : int) : (term466 n) = (term479 n).
Proof. exact (MK_COMB (@lem3172626 n) (@lem3172627)). Qed.
Lemma lem3172629 (n : int) : ((term465 n) = (term466 n)) = ((term457 n) = (term479 n)).
Proof. exact (MK_COMB (@lem3172620 n) (@lem3172628 n)). Qed.
Lemma lem3172630 (n : int) : (term457 n) = (term479 n).
Proof. exact (EQ_MP (@lem3172629 n) (@lem3172610 n)). Qed.
Lemma lem3172639 (n : int) : (term458 n) = (term458 n).
Proof. exact (eq_refl (term458 n)). Qed.
Lemma lem3172640 (n : int) : (term460 n) = (term480 n).
Proof. exact (MK_COMB (@lem3172639 n) (@lem3172630 n)). Qed.
Lemma lem3172642 {A : Type'} (P : A -> Prop) (Q : Prop) : (term462 A P Q) = (term461 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3172643 (P : real -> Prop) (Q : Prop) : (term464 P Q) = (term463 P Q).
Proof. exact (@lem3172642 real P Q). Qed.
Lemma lem3172644 (n : int) : (term466 n) = (term465 n).
Proof. exact (@lem3172643 (term467 n) term390). Qed.
Lemma lem3172645 (x : real) (n : int) : (term468 n x) = (term411 x n).
Proof. exact (eq_refl (term468 n x)). Qed.
Lemma lem3172646 (n : int) : (term474 n) = (term467 n).
Proof. exact (fun_ext (fun x : real => @lem3172645 x n)). Qed.
Lemma lem3172647 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172648 (n : int) : (term475 n) = (term476 n).
Proof. exact (MK_COMB (@lem3172647) (@lem3172646 n)). Qed.
Lemma lem3172649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3172650 (n : int) : (term477 n) = (term478 n).
Proof. exact (MK_COMB (@lem3172649) (@lem3172648 n)). Qed.
Lemma lem3172651 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem3172652 (n : int) : (term466 n) = (term479 n).
Proof. exact (MK_COMB (@lem3172650 n) (@lem3172651)). Qed.
Lemma lem3172653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3172654 (n : int) : (term481 n) = (term482 n).
Proof. exact (MK_COMB (@lem3172653) (@lem3172652 n)). Qed.
Lemma lem3172655 (x : real) (n : int) : (term468 n x) = (term411 x n).
Proof. exact (eq_refl (term468 n x)). Qed.
Lemma lem3172656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3172657 (x : real) (n : int) : (term469 n x) = (term445 x n).
Proof. exact (MK_COMB (@lem3172656) (@lem3172655 x n)). Qed.
Lemma lem3172658 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem3172659 (x : real) (n : int) : (term470 n x) = (term447 x n).
Proof. exact (MK_COMB (@lem3172657 x n) (@lem3172658)). Qed.
Lemma lem3172660 (n : int) : (term471 n) = (term456 n).
Proof. exact (fun_ext (fun x : real => @lem3172659 x n)). Qed.
Lemma lem3172661 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172662 (n : int) : (term465 n) = (term457 n).
Proof. exact (MK_COMB (@lem3172661) (@lem3172660 n)). Qed.
Lemma lem3172663 (n : int) : ((term466 n) = (term465 n)) = ((term479 n) = (term457 n)).
Proof. exact (MK_COMB (@lem3172654 n) (@lem3172662 n)). Qed.
Lemma lem3172664 (n : int) : (term479 n) = (term457 n).
Proof. exact (EQ_MP (@lem3172663 n) (@lem3172644 n)). Qed.
Lemma lem3172665 (n : int) : (term458 n) = (term458 n).
Proof. exact (eq_refl (term458 n)). Qed.
Lemma lem3172666 (n : int) : (term480 n) = (term460 n).
Proof. exact (MK_COMB (@lem3172665 n) (@lem3172664 n)). Qed.
Lemma lem3172668 {A : Type'} (P : Prop) (Q : A -> Prop) : (term483 A P Q) = (term484 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3172669 (P : Prop) (Q : real -> Prop) : (term485 P Q) = (term486 P Q).
Proof. exact (@lem3172668 real P Q). Qed.
Lemma lem3172670 (n : int) : (term487 n) = (term488 n).
Proof. exact (@lem3172669 (term14 n) (term456 n)). Qed.
Lemma lem3172671 (x : real) (n : int) : (term489 n x) = (term447 x n).
Proof. exact (eq_refl (term489 n x)). Qed.
Lemma lem3172672 (n : int) : (term490 n) = (term456 n).
Proof. exact (fun_ext (fun x : real => @lem3172671 x n)). Qed.
Lemma lem3172673 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172674 (n : int) : (term491 n) = (term457 n).
Proof. exact (MK_COMB (@lem3172673) (@lem3172672 n)). Qed.
Lemma lem3172675 (n : int) : (term458 n) = (term458 n).
Proof. exact (eq_refl (term458 n)). Qed.
Lemma lem3172676 (n : int) : (term487 n) = (term460 n).
Proof. exact (MK_COMB (@lem3172675 n) (@lem3172674 n)). Qed.
Lemma lem3172677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3172678 (n : int) : (term492 n) = (term493 n).
Proof. exact (MK_COMB (@lem3172677) (@lem3172676 n)). Qed.
Lemma lem3172679 (x : real) (n : int) : (term489 n x) = (term447 x n).
Proof. exact (eq_refl (term489 n x)). Qed.
Lemma lem3172680 (n : int) : (term458 n) = (term458 n).
Proof. exact (eq_refl (term458 n)). Qed.
Lemma lem3172681 (x : real) (n : int) : (term494 n x) = (term495 x n).
Proof. exact (MK_COMB (@lem3172680 n) (@lem3172679 x n)). Qed.
Lemma lem3172682 (n : int) : (term496 n) = (term497 n).
Proof. exact (fun_ext (fun x : real => @lem3172681 x n)). Qed.
Lemma lem3172683 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem3172684 (n : int) : (term488 n) = (term498 n).
Proof. exact (MK_COMB (@lem3172683) (@lem3172682 n)). Qed.
Lemma lem3172685 (n : int) : ((term487 n) = (term488 n)) = ((term460 n) = (term498 n)).
Proof. exact (MK_COMB (@lem3172678 n) (@lem3172684 n)). Qed.
Lemma lem3172686 (n : int) : (term460 n) = (term498 n).
Proof. exact (EQ_MP (@lem3172685 n) (@lem3172670 n)). Qed.
Lemma lem3172687 (n : int) : (term480 n) = (term498 n).
Proof. exact (TRANS (@lem3172666 n) (@lem3172686 n)). Qed.
Lemma lem3172688 (n : int) : (term460 n) = (term498 n).
Proof. exact (TRANS (@lem3172640 n) (@lem3172687 n)). Qed.
Lemma lem3172689 (n : int) : (term443 n) = (term498 n).
Proof. exact (TRANS (@lem3172586 n) (@lem3172688 n)). Qed.
Lemma lem3172690 (n : int) (h1 : term443 n) : term498 n.
Proof. exact (EQ_MP (@lem3172689 n) (@lem3172558 n h1)). Qed.
Lemma lem3172691 (x : real) (n : int) (h1 : term495 x n) : term495 x n.
Proof. exact (h1). Qed.
Lemma lem3172700 (x : real) : ((term436 x) = x) = ((term436 x) = x).
Proof. exact (eq_refl ((term436 x) = x)). Qed.
Lemma lem3172701 : term437 = term437.
Proof. exact (fun_ext (fun x : real => @lem3172700 x)). Qed.
Lemma lem3172702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172703 : term390 = term390.
Proof. exact (MK_COMB (@lem3172702) (@lem3172701)). Qed.
Lemma lem3172732 (x : real) (n : int) : (term445 x n) = (term445 x n).
Proof. exact (eq_refl (term445 x n)). Qed.
Lemma lem3172733 (x : real) (n : int) : (term447 x n) = (term447 x n).
Proof. exact (MK_COMB (@lem3172732 x n) (@lem3172703)). Qed.
Lemma lem3172746 (n : int) : (term458 n) = (term458 n).
Proof. exact (eq_refl (term458 n)). Qed.
Lemma lem3172747 (x : real) (n : int) : (term495 x n) = (term495 x n).
Proof. exact (MK_COMB (@lem3172746 n) (@lem3172733 x n)). Qed.
Lemma lem3172748 (x : real) (n : int) (h1 : term495 x n) : term495 x n.
Proof. exact (EQ_MP (@lem3172747 x n) (@lem3172691 x n h1)). Qed.
Lemma lem3172749 (x : real) (n : int) (h1 : term495 x n) : term447 x n.
Proof. exact (proj2 (@lem3172748 x n h1)). Qed.
Lemma lem3172751 (x : real) (n : int) (h1 : term495 x n) : term390.
Proof. exact (proj2 (@lem3172749 x n h1)). Qed.
Lemma lem3172762 (x : real) : ((term436 x) = x) = ((term436 x) = x).
Proof. exact (eq_refl ((term436 x) = x)). Qed.
Lemma lem3172763 : term437 = term437.
Proof. exact (fun_ext (fun x : real => @lem3172762 x)). Qed.
Lemma lem3172764 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3172766 : term390 = term390.
Proof. exact (MK_COMB (@lem3172764) (@lem3172763)). Qed.
Lemma lem3172767 (x : real) (n : int) (h1 : term495 x n) : term390.
Proof. exact (EQ_MP (@lem3172766) (@lem3172751 x n h1)). Qed.
Lemma lem3172768 (_32638 : real) (x : real) (n : int) (h1 : term495 x n) : term499 _32638.
Proof. exact (@lem3172767 x n h1 _32638). Qed.
Lemma lem3172769 (_32638 : real) : (term499 _32638) = ((term436 _32638) = _32638).
Proof. exact (eq_refl (term499 _32638)). Qed.
Lemma lem3172774 (x : real) (n : int) (h1 : term495 x n) : term411 x n.
Proof. exact (proj1 (@lem3172749 x n h1)). Qed.
Lemma lem3172856 (x : real) (y : real) (z : real) : term500 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem3172858 (_32638 : real) (x : real) (n : int) (h1 : term495 x n) : (term436 _32638) = _32638.
Proof. exact (EQ_MP (@lem3172769 _32638) (@lem3172768 _32638 x n h1)). Qed.
Lemma lem3172859 (x : real) (n : int) (h1 : term495 x n) : (term410 x n) = (term357 x n).
Proof. exact (@lem3172858 (term357 x n) x n h1). Qed.
Lemma lem3172860 (x : real) (n : int) (h1 : term495 x n) : term501 x n.
Proof. exact (fun h0 : term502 x n => @lem3172859 x n h1). Qed.
Lemma lem3172862 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3172863 (x : real) (n : int) : (term501 x n) = ((term410 x n) = (term357 x n)).
Proof. exact (@lem3172862 ((term410 x n) = (term357 x n))). Qed.
Lemma lem3172864 (x : real) (n : int) (h1 : term495 x n) : (term410 x n) = (term357 x n).
Proof. exact (EQ_MP (@lem3172863 x n) (@lem3172860 x n h1)). Qed.
Lemma lem3172866 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem3172867 (x : real) (n : int) : (term410 x n) = (term410 x n).
Proof. exact (@lem3172866 (term410 x n)). Qed.
Lemma lem3172868 (x : real) (n : int) : term504 x n.
Proof. exact (fun h0 : term505 x n => @lem3172867 x n). Qed.
Lemma lem3172870 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3172871 (x : real) (n : int) : (term504 x n) = ((term410 x n) = (term410 x n)).
Proof. exact (@lem3172870 ((term410 x n) = (term410 x n))). Qed.
Lemma lem3172872 (x : real) (n : int) : (term410 x n) = (term410 x n).
Proof. exact (EQ_MP (@lem3172871 x n) (@lem3172868 x n)). Qed.
Lemma lem3172890 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3172891 (y : real) (x : real) (z : real) : (term506 x y z) = (term507 y x z).
Proof. exact (@lem3172890 (y = z) (term508 x z)). Qed.
Lemma lem3172901 (x : real) (y : real) : (term509 x y) = (term509 x y).
Proof. exact (eq_refl (term509 x y)). Qed.
Lemma lem3172902 (y : real) (x : real) (z : real) : (term500 x y z) = (term510 y x z).
Proof. exact (MK_COMB (@lem3172901 x y) (@lem3172891 y x z)). Qed.
Lemma lem3172906 (q : Prop) (p : Prop) (r : Prop) : (term511 p q r) = (term511 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3172907 (y : real) (x : real) (z : real) : (term510 y x z) = (term512 y x z).
Proof. exact (@lem3172906 (y = z) (term508 x y) (term508 x z)). Qed.
Lemma lem3172929 (y : real) (x : real) (z : real) : (term500 x y z) = (term512 y x z).
Proof. exact (TRANS (@lem3172902 y x z) (@lem3172907 y x z)). Qed.
Lemma lem3172930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3172931 (y : real) (x : real) (z : real) : (term513 x y z) = (term514 y x z).
Proof. exact (MK_COMB (@lem3172930) (@lem3172929 y x z)). Qed.
Lemma lem3172953 (y : real) (x : real) (z : real) : (term512 y x z) = (term512 y x z).
Proof. exact (eq_refl (term512 y x z)). Qed.
Lemma lem3172954 (y : real) (x : real) (z : real) : ((term500 x y z) = (term512 y x z)) = ((term512 y x z) = (term512 y x z)).
Proof. exact (MK_COMB (@lem3172931 y x z) (@lem3172953 y x z)). Qed.
Lemma lem3172956 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3172957 (x : Prop) : (x = x) = True.
Proof. exact (@lem3172956 Prop x). Qed.
Lemma lem3172958 (y : real) (x : real) (z : real) : ((term512 y x z) = (term512 y x z)) = True.
Proof. exact (@lem3172957 (term512 y x z)). Qed.
Lemma lem3172959 (y : real) (x : real) (z : real) : ((term500 x y z) = (term512 y x z)) = True.
Proof. exact (TRANS (@lem3172954 y x z) (@lem3172958 y x z)). Qed.
Lemma lem3172960 (y : real) (x : real) (z : real) : True = ((term500 x y z) = (term512 y x z)).
Proof. exact (SYM (@lem3172959 y x z)). Qed.
Lemma lem3172961 (y : real) (x : real) (z : real) : (term500 x y z) = (term512 y x z).
Proof. exact (EQ_MP (@lem3172960 y x z) (@lem0)). Qed.
Lemma lem3172962 (y : real) (x : real) (z : real) : term512 y x z.
Proof. exact (EQ_MP (@lem3172961 y x z) (@lem3172856 x y z)). Qed.
Lemma lem3172964 (b : Prop) (a : Prop) : (a \/ b) = (term515 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3172965 (x : real) (y : real) (z : real) : (term512 y x z) = (term516 x y z).
Proof. exact (@lem3172964 (term517 y x z) (y = z)). Qed.
Lemma lem3172967 (a : Prop) (b : Prop) : (term518 a b) = (term519 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3172968 (y : real) (x : real) (z : real) : (term520 y x z) = (term521 y x z).
Proof. exact (@lem3172967 (term508 x y) (term508 x z)). Qed.
Lemma lem3172970 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3172971 (x : real) (y : real) : (term522 x y) = (x = y).
Proof. exact (@lem3172970 (x = y)). Qed.
Lemma lem3172972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3172973 (x : real) (y : real) : (term523 x y) = (term524 x y).
Proof. exact (MK_COMB (@lem3172972) (@lem3172971 x y)). Qed.
Lemma lem3172975 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3172976 (x : real) (z : real) : (term522 x z) = (x = z).
Proof. exact (@lem3172975 (x = z)). Qed.
Lemma lem3172977 (y : real) (x : real) (z : real) : (term521 y x z) = (term525 y x z).
Proof. exact (MK_COMB (@lem3172973 x y) (@lem3172976 x z)). Qed.
Lemma lem3172978 (y : real) (x : real) (z : real) : (term520 y x z) = (term525 y x z).
Proof. exact (TRANS (@lem3172968 y x z) (@lem3172977 y x z)). Qed.
Lemma lem3172979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3172980 (y : real) (x : real) (z : real) : (term526 y x z) = (term527 y x z).
Proof. exact (MK_COMB (@lem3172979) (@lem3172978 y x z)). Qed.
Lemma lem3172981 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3172982 (x : real) (y : real) (z : real) : (term516 x y z) = (term528 x y z).
Proof. exact (MK_COMB (@lem3172980 y x z) (@lem3172981 y z)). Qed.
Lemma lem3172983 (x : real) (y : real) (z : real) : (term512 y x z) = (term528 x y z).
Proof. exact (TRANS (@lem3172965 x y z) (@lem3172982 x y z)). Qed.
Lemma lem3172985 (x : real) (n : int) (h1 : term495 x n) : term529 x n.
Proof. exact (conj (@lem3172864 x n h1) (@lem3172872 x n)). Qed.
Lemma lem3172987 (x : real) (y : real) (z : real) : term528 x y z.
Proof. exact (EQ_MP (@lem3172983 x y z) (@lem3172962 y x z)). Qed.
Lemma lem3172988 (x : real) (n : int) : term530 x n.
Proof. exact (@lem3172987 (term410 x n) (term357 x n) (term410 x n)). Qed.
Lemma lem3172991 (x : real) (n : int) (h1 : term495 x n) : (term357 x n) = (term410 x n).
Proof. exact (@lem3172988 x n (@lem3172985 x n h1)). Qed.
Lemma lem3172992 (x : real) (n : int) (h1 : term495 x n) : term531 x n.
Proof. exact (fun h0 : term411 x n => @lem3172991 x n h1). Qed.
Lemma lem3172994 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3172995 (x : real) (n : int) : (term531 x n) = ((term357 x n) = (term410 x n)).
Proof. exact (@lem3172994 ((term357 x n) = (term410 x n))). Qed.
Lemma lem3172996 (x : real) (n : int) (h1 : term495 x n) : (term357 x n) = (term410 x n).
Proof. exact (EQ_MP (@lem3172995 x n) (@lem3172992 x n h1)). Qed.
Lemma lem3172999 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3173001 (x : real) (n : int) : (term411 x n) = (term532 x n).
Proof. exact (@lem3172999 ((term357 x n) = (term410 x n))). Qed.
Lemma lem3173004 (x : real) (n : int) (h1 : term495 x n) : term532 x n.
Proof. exact (EQ_MP (@lem3173001 x n) (@lem3172774 x n h1)). Qed.
Lemma lem3173007 (x : real) (n : int) (h1 : term495 x n) : False.
Proof. exact (@lem3173004 x n h1 (@lem3172996 x n h1)). Qed.
Lemma lem3173008 (x : real) (n : int) (h1 : term495 x n) : term533.
Proof. exact (fun h0 : ~ False => @lem3173007 x n h1). Qed.
Lemma lem3173010 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3173011 : term533 = False.
Proof. exact (@lem3173010 False). Qed.
Lemma lem3173012 (x : real) (n : int) (h1 : term495 x n) : False.
Proof. exact (EQ_MP (@lem3173011) (@lem3173008 x n h1)). Qed.
Lemma lem3173013 (x : real) (n : int) (h1 : term495 x n) : (term495 x n) = False.
Proof. exact (prop_ext (fun h2 : term495 x n => @lem3173012 x n h1) (fun h2 : False => @lem3172748 x n h1)). Qed.
Lemma lem3173014 (x : real) (n : int) (h1 : term495 x n) : False.
Proof. exact (EQ_MP (@lem3173013 x n h1) (@lem3172748 x n h1)). Qed.
Lemma lem3173015 (n : int) (h1 : term443 n) : False.
Proof. exact (ex_elim (@lem3172690 n h1) (fun x : real => fun h0 : term497 n x => @lem3173014 x n h0)). Qed.
Lemma lem3173016 (n : int) (h1 : term443 n) : (term443 n) = False.
Proof. exact (prop_ext (fun h2 : term443 n => @lem3173015 n h1) (fun h2 : False => @lem3172558 n h1)). Qed.
Lemma lem3173017 (n : int) (h1 : term443 n) : False.
Proof. exact (EQ_MP (@lem3173016 n h1) (@lem3172558 n h1)). Qed.
Lemma lem3173018 (n : int) : term442 n.
Proof. exact (fun h0 : term443 n => @lem3173017 n h0). Qed.
Lemma lem3173019 (n : int) : term432 n.
Proof. exact (EQ_MP (@lem3172557 n) (@lem3173018 n)). Qed.
Lemma lem3173024 : term441.
Proof. exact (fun n : int => @lem3173019 n). Qed.
Lemma lem3173025 : term399.
Proof. exact (EQ_MP (@lem3172553) (@lem3173024)). Qed.
Lemma lem3173026 (n : int) : term534 n.
Proof. exact (@lem3173025 n). Qed.
Lemma lem3173027 (n : int) : (term534 n) = (term395 n).
Proof. exact (eq_refl (term534 n)). Qed.
Lemma lem3173028 (n : int) : term395 n.
Proof. exact (EQ_MP (@lem3173027 n) (@lem3173026 n)). Qed.
Lemma lem3173029 (n : int) (x : real) : term535 n x.
Proof. exact (@lem3173028 n x). Qed.
Lemma lem3173030 (x : real) (n : int) : (term535 n x) = (term384 x n).
Proof. exact (eq_refl (term535 n x)). Qed.
Lemma lem3173031 (x : real) (n : int) : term384 x n.
Proof. exact (EQ_MP (@lem3173030 x n) (@lem3173029 n x)). Qed.
Lemma lem3173033 (x : real) (n : int) : term384 x n.
Proof. exact (@lem3172323 x n (@lem3173031 x n)). Qed.
Lemma lem3173034 (x : real) (n : int) (h1 : term383 x n) : term388.
Proof. exact (@lem3173033 x n (@lem3172308 x n h1)). Qed.
Lemma lem3173035 (x : real) (n : int) (h1 : term383 x n) : False.
Proof. exact (@lem3173034 x n h1 (@lem1587920)). Qed.
Lemma lem3173036 (x : real) (n : int) (h1 : term383 x n) : (term383 x n) = False.
Proof. exact (prop_ext (fun h2 : term383 x n => @lem3173035 x n h1) (fun h2 : False => @lem3172308 x n h1)). Qed.
Lemma lem3173037 (x : real) (n : int) (h1 : term383 x n) : False.
Proof. exact (EQ_MP (@lem3173036 x n h1) (@lem3172308 x n h1)). Qed.
Lemma lem3173038 (x : real) (n : int) : term382 x n.
Proof. exact (fun h0 : term383 x n => @lem3173037 x n h0). Qed.
Lemma lem3173039 (x : real) (n : int) : (term378 x n) = (term380 x n).
Proof. exact (EQ_MP (@lem3172307 x n) (@lem3173038 x n)). Qed.
Lemma lem3173041 (x : real) (n : int) (h1 : term19 n) : (term332 x n) = (term335 x n).
Proof. exact (EQ_MP (@lem3172303 x n h1) (@lem3173039 x n)). Qed.
Lemma lem3173042 (x : real) (n : int) : (term332 x n) = (term335 x n).
Proof. exact (or_elim (@lem3171932 n) (fun h0 : n = term23 => @lem3171973 x n h0) (fun h0 : term19 n => @lem3173041 x n h0)). Qed.
Lemma lem3173047 (x : real) : term536 x.
Proof. exact (fun n : int => @lem3173042 x n). Qed.
Lemma lem3173052 : term537.
Proof. exact (fun x : real => @lem3173047 x). Qed.
