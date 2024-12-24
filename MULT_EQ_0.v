Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_EQ_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem83518 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem83519 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem83520 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem83519 n) (@lem83518 n)). Qed.
Lemma lem83521 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem83534 : term3.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem83535 : term4.
Proof. exact (proj2 (@lem83534)). Qed.
Lemma lem83536 : term5.
Proof. exact (proj2 (@lem83535)). Qed.
Lemma lem83537 (m : nat) : term6 m.
Proof. exact (@lem83536 m). Qed.
Lemma lem83538 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem83539 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem83538 m) (@lem83537 m)). Qed.
Lemma lem83540 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem83539 m n). Qed.
Lemma lem83541 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem83550 : term11.
Proof. exact (proj1 (@lem83534)). Qed.
Lemma lem83551 (m : nat) : term12 m.
Proof. exact (@lem83550 m). Qed.
Lemma lem83552 (m : nat) : (term12 m) = ((term13 m) = m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem83558 : term14.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem83559 : term15.
Proof. exact (proj2 (@lem83558)). Qed.
Lemma lem83560 : term16.
Proof. exact (proj2 (@lem83559)). Qed.
Lemma lem83561 : term17.
Proof. exact (proj2 (@lem83560)). Qed.
Lemma lem83562 : term18.
Proof. exact (proj2 (@lem83561)). Qed.
Lemma lem83563 (m : nat) : term19 m.
Proof. exact (@lem83562 m). Qed.
Lemma lem83564 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem83565 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem83564 m) (@lem83563 m)). Qed.
Lemma lem83566 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem83565 m n). Qed.
Lemma lem83567 (m : nat) (n : nat) : (term21 m n) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem83569 : term24.
Proof. exact (proj1 (@lem83561)). Qed.
Lemma lem83570 (m : nat) : term25 m.
Proof. exact (@lem83569 m). Qed.
Lemma lem83571 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem83572 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem83571 m) (@lem83570 m)). Qed.
Lemma lem83573 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem83572 m n). Qed.
Lemma lem83574 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (term29 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem83584 : term30.
Proof. exact (proj1 (@lem83558)). Qed.
Lemma lem83585 (m : nat) : term31 m.
Proof. exact (@lem83584 m). Qed.
Lemma lem83586 (m : nat) : (term31 m) = ((term32 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem83588 : term33.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem83589 (n : nat) : term34 n.
Proof. exact (@lem83588 n). Qed.
Lemma lem83590 (n : nat) : (term34 n) = ((term35 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem83593 (P : nat -> Prop) : term36 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem83594 : term37.
Proof. exact (@lem83593 term38). Qed.
Lemma lem83595 : term39 = term40.
Proof. exact (eq_refl term39). Qed.
Lemma lem83596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83597 : term41 = term42.
Proof. exact (MK_COMB (@lem83596) (@lem83595)). Qed.
Lemma lem83598 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem83599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83600 (m : nat) : (term45 m) = (term46 m).
Proof. exact (MK_COMB (@lem83599) (@lem83598 m)). Qed.
Lemma lem83601 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem83602 (m : nat) : (term49 m) = (term50 m).
Proof. exact (MK_COMB (@lem83600 m) (@lem83601 m)). Qed.
Lemma lem83603 : term51 = term52.
Proof. exact (fun_ext (fun m : nat => @lem83602 m)). Qed.
Lemma lem83604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83605 : term53 = term54.
Proof. exact (MK_COMB (@lem83604) (@lem83603)). Qed.
Lemma lem83606 : term55 = term56.
Proof. exact (MK_COMB (@lem83597) (@lem83605)). Qed.
Lemma lem83607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83608 : term57 = term58.
Proof. exact (MK_COMB (@lem83607) (@lem83606)). Qed.
Lemma lem83609 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem83610 : term59 = term38.
Proof. exact (fun_ext (fun m : nat => @lem83609 m)). Qed.
Lemma lem83611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83612 : term60 = term61.
Proof. exact (MK_COMB (@lem83611) (@lem83610)). Qed.
Lemma lem83613 : term37 = term62.
Proof. exact (MK_COMB (@lem83608) (@lem83612)). Qed.
Lemma lem83614 : term62.
Proof. exact (EQ_MP (@lem83613) (@lem83594)). Qed.
Lemma lem83617 (P : nat -> Prop) : term36 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem83618 : term63.
Proof. exact (@lem83617 term64). Qed.
Lemma lem83619 : term65 = ((term66 = (NUMERAL 0)) = term67).
Proof. exact (eq_refl term65). Qed.
Lemma lem83620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83621 : term68 = term69.
Proof. exact (MK_COMB (@lem83620) (@lem83619)). Qed.
Lemma lem83622 (n : nat) : (term70 n) = (((term35 n) = (NUMERAL 0)) = (term71 n)).
Proof. exact (eq_refl (term70 n)). Qed.
Lemma lem83623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83624 (n : nat) : (term72 n) = (term73 n).
Proof. exact (MK_COMB (@lem83623) (@lem83622 n)). Qed.
Lemma lem83625 (n : nat) : (term74 n) = (((term75 n) = (NUMERAL 0)) = (term76 n)).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem83626 (n : nat) : (term77 n) = (term78 n).
Proof. exact (MK_COMB (@lem83624 n) (@lem83625 n)). Qed.
Lemma lem83627 : term79 = term80.
Proof. exact (fun_ext (fun n : nat => @lem83626 n)). Qed.
Lemma lem83628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83629 : term81 = term82.
Proof. exact (MK_COMB (@lem83628) (@lem83627)). Qed.
Lemma lem83630 : term83 = term84.
Proof. exact (MK_COMB (@lem83621) (@lem83629)). Qed.
Lemma lem83631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83632 : term85 = term86.
Proof. exact (MK_COMB (@lem83631) (@lem83630)). Qed.
Lemma lem83633 (n : nat) : (term70 n) = (((term35 n) = (NUMERAL 0)) = (term71 n)).
Proof. exact (eq_refl (term70 n)). Qed.
Lemma lem83634 : term87 = term64.
Proof. exact (fun_ext (fun n : nat => @lem83633 n)). Qed.
Lemma lem83635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83636 : term88 = term40.
Proof. exact (MK_COMB (@lem83635) (@lem83634)). Qed.
Lemma lem83637 : term63 = term89.
Proof. exact (MK_COMB (@lem83632) (@lem83636)). Qed.
Lemma lem83638 : term89.
Proof. exact (EQ_MP (@lem83637) (@lem83618)). Qed.
Lemma lem83645 (P : nat -> Prop) : term36 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem83646 (m : nat) : term90 m.
Proof. exact (@lem83645 (term91 m)). Qed.
Lemma lem83647 (m : nat) : (term92 m) = (((term93 m) = (NUMERAL 0)) = (term94 m)).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem83648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem83649 (m : nat) : (term95 m) = (term96 m).
Proof. exact (MK_COMB (@lem83648) (@lem83647 m)). Qed.
Lemma lem83650 (m : nat) (n : nat) : (term97 m n) = (((term28 m n) = (NUMERAL 0)) = (term98 m n)).
Proof. exact (eq_refl (term97 m n)). Qed.
Lemma lem83651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83652 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem83651) (@lem83650 m n)). Qed.
Lemma lem83653 (m : nat) (n : nat) : (term101 m n) = (((term102 m n) = (NUMERAL 0)) = (term103 m n)).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem83654 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem83652 m n) (@lem83653 m n)). Qed.
Lemma lem83655 (m : nat) : (term106 m) = (term107 m).
Proof. exact (fun_ext (fun n : nat => @lem83654 m n)). Qed.
Lemma lem83656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83657 (m : nat) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem83656) (@lem83655 m)). Qed.
Lemma lem83658 (m : nat) : (term110 m) = (term111 m).
Proof. exact (MK_COMB (@lem83649 m) (@lem83657 m)). Qed.
Lemma lem83659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem83660 (m : nat) : (term112 m) = (term113 m).
Proof. exact (MK_COMB (@lem83659) (@lem83658 m)). Qed.
Lemma lem83661 (m : nat) (n : nat) : (term97 m n) = (((term28 m n) = (NUMERAL 0)) = (term98 m n)).
Proof. exact (eq_refl (term97 m n)). Qed.
Lemma lem83662 (m : nat) : (term114 m) = (term91 m).
Proof. exact (fun_ext (fun n : nat => @lem83661 m n)). Qed.
Lemma lem83663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem83664 (m : nat) : (term115 m) = (term48 m).
Proof. exact (MK_COMB (@lem83663) (@lem83662 m)). Qed.
Lemma lem83665 (m : nat) : (term90 m) = (term116 m).
Proof. exact (MK_COMB (@lem83660 m) (@lem83664 m)). Qed.
Lemma lem83666 (m : nat) : term116 m.
Proof. exact (EQ_MP (@lem83665 m) (@lem83646 m)). Qed.
Lemma lem83677 (n : nat) : (term35 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem83590 n) (@lem83589 n)). Qed.
Lemma lem83678 : term66 = (NUMERAL 0).
Proof. exact (@lem83677 (NUMERAL 0)). Qed.
Lemma lem83679 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem83680 : term117 = term118.
Proof. exact (MK_COMB (@lem83679) (@lem83678)). Qed.
Lemma lem83681 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem83682 : (term66 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem83680) (@lem83681)). Qed.
Lemma lem83684 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83685 (x : nat) : (x = x) = True.
Proof. exact (@lem83684 nat x). Qed.
Lemma lem83686 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83685 (NUMERAL 0)). Qed.
Lemma lem83687 : (term66 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem83682) (@lem83686)). Qed.
Lemma lem83688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83689 : term119 = (@eq Prop True).
Proof. exact (MK_COMB (@lem83688) (@lem83687)). Qed.
Lemma lem83691 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem83692 : term67 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem83691 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem83694 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83695 (x : nat) : (x = x) = True.
Proof. exact (@lem83694 nat x). Qed.
Lemma lem83696 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83695 (NUMERAL 0)). Qed.
Lemma lem83697 : term67 = True.
Proof. exact (TRANS (@lem83692) (@lem83696)). Qed.
Lemma lem83698 : ((term66 = (NUMERAL 0)) = term67) = (True = True).
Proof. exact (MK_COMB (@lem83689) (@lem83697)). Qed.
Lemma lem83700 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem83701 : (True = True) = True.
Proof. exact (@lem83700 True). Qed.
Lemma lem83702 : ((term66 = (NUMERAL 0)) = term67) = True.
Proof. exact (TRANS (@lem83698) (@lem83701)). Qed.
Lemma lem83703 : True = ((term66 = (NUMERAL 0)) = term67).
Proof. exact (SYM (@lem83702)). Qed.
Lemma lem83704 : (term66 = (NUMERAL 0)) = term67.
Proof. exact (EQ_MP (@lem83703) (@lem0)). Qed.
Lemma lem83710 (n : nat) : (term35 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem83590 n) (@lem83589 n)). Qed.
Lemma lem83711 (n : nat) : (term75 n) = (NUMERAL 0).
Proof. exact (@lem83710 (S n)). Qed.
Lemma lem83712 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem83713 (n : nat) : (term120 n) = term118.
Proof. exact (MK_COMB (@lem83712) (@lem83711 n)). Qed.
Lemma lem83714 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem83715 (n : nat) : ((term75 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem83713 n) (@lem83714)). Qed.
Lemma lem83717 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83718 (x : nat) : (x = x) = True.
Proof. exact (@lem83717 nat x). Qed.
Lemma lem83719 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83718 (NUMERAL 0)). Qed.
Lemma lem83720 (n : nat) : ((term75 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem83715 n) (@lem83719)). Qed.
Lemma lem83721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83722 (n : nat) : (term121 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem83721) (@lem83720 n)). Qed.
Lemma lem83726 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83727 (x : nat) : (x = x) = True.
Proof. exact (@lem83726 nat x). Qed.
Lemma lem83728 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83727 (NUMERAL 0)). Qed.
Lemma lem83729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem83730 : term122 = (or True).
Proof. exact (MK_COMB (@lem83729) (@lem83728)). Qed.
Lemma lem83732 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem83521 n (@lem83520 n)). Qed.
Lemma lem83733 (n : nat) : (term76 n) = (True \/ False).
Proof. exact (MK_COMB (@lem83730) (@lem83732 n)). Qed.
Lemma lem83735 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem83736 : (True \/ False) = True.
Proof. exact (@lem83735 False). Qed.
Lemma lem83737 (n : nat) : (term76 n) = True.
Proof. exact (TRANS (@lem83733 n) (@lem83736)). Qed.
Lemma lem83738 (n : nat) : (((term75 n) = (NUMERAL 0)) = (term76 n)) = (True = True).
Proof. exact (MK_COMB (@lem83722 n) (@lem83737 n)). Qed.
Lemma lem83740 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem83741 : (True = True) = True.
Proof. exact (@lem83740 True). Qed.
Lemma lem83742 (n : nat) : (((term75 n) = (NUMERAL 0)) = (term76 n)) = True.
Proof. exact (TRANS (@lem83738 n) (@lem83741)). Qed.
Lemma lem83743 (n : nat) : True = (((term75 n) = (NUMERAL 0)) = (term76 n)).
Proof. exact (SYM (@lem83742 n)). Qed.
Lemma lem83744 (n : nat) : ((term75 n) = (NUMERAL 0)) = (term76 n).
Proof. exact (EQ_MP (@lem83743 n) (@lem0)). Qed.
Lemma lem83750 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem83574 m n) (@lem83573 m n)). Qed.
Lemma lem83751 (m : nat) : (term93 m) = (term123 m).
Proof. exact (@lem83750 m (NUMERAL 0)). Qed.
Lemma lem83753 (m : nat) : (term13 m) = m.
Proof. exact (EQ_MP (@lem83552 m) (@lem83551 m)). Qed.
Lemma lem83754 (m : nat) : (term123 m) = (term32 m).
Proof. exact (@lem83753 (term32 m)). Qed.
Lemma lem83756 (m : nat) : (term32 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem83586 m) (@lem83585 m)). Qed.
Lemma lem83757 (m : nat) : (term123 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem83754 m) (@lem83756 m)). Qed.
Lemma lem83758 (m : nat) : (term93 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem83751 m) (@lem83757 m)). Qed.
Lemma lem83759 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem83760 (m : nat) : (term124 m) = term118.
Proof. exact (MK_COMB (@lem83759) (@lem83758 m)). Qed.
Lemma lem83761 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem83762 (m : nat) : ((term93 m) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem83760 m) (@lem83761)). Qed.
Lemma lem83764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83765 (x : nat) : (x = x) = True.
Proof. exact (@lem83764 nat x). Qed.
Lemma lem83766 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83765 (NUMERAL 0)). Qed.
Lemma lem83767 (m : nat) : ((term93 m) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem83762 m) (@lem83766)). Qed.
Lemma lem83768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83769 (m : nat) : (term125 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem83768) (@lem83767 m)). Qed.
Lemma lem83773 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem83521 n (@lem83520 n)). Qed.
Lemma lem83774 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem83773 m). Qed.
Lemma lem83775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem83776 (m : nat) : (term126 m) = (or False).
Proof. exact (MK_COMB (@lem83775) (@lem83774 m)). Qed.
Lemma lem83778 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem83779 (x : nat) : (x = x) = True.
Proof. exact (@lem83778 nat x). Qed.
Lemma lem83780 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem83779 (NUMERAL 0)). Qed.
Lemma lem83781 (m : nat) : (term94 m) = (False \/ True).
Proof. exact (MK_COMB (@lem83776 m) (@lem83780)). Qed.
Lemma lem83783 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem83784 : (False \/ True) = True.
Proof. exact (@lem83783 True). Qed.
Lemma lem83785 (m : nat) : (term94 m) = True.
Proof. exact (TRANS (@lem83781 m) (@lem83784)). Qed.
Lemma lem83786 (m : nat) : (((term93 m) = (NUMERAL 0)) = (term94 m)) = (True = True).
Proof. exact (MK_COMB (@lem83769 m) (@lem83785 m)). Qed.
Lemma lem83788 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem83789 : (True = True) = True.
Proof. exact (@lem83788 True). Qed.
Lemma lem83790 (m : nat) : (((term93 m) = (NUMERAL 0)) = (term94 m)) = True.
Proof. exact (TRANS (@lem83786 m) (@lem83789)). Qed.
Lemma lem83791 (m : nat) : True = (((term93 m) = (NUMERAL 0)) = (term94 m)).
Proof. exact (SYM (@lem83790 m)). Qed.
Lemma lem83792 (m : nat) : ((term93 m) = (NUMERAL 0)) = (term94 m).
Proof. exact (EQ_MP (@lem83791 m) (@lem0)). Qed.
Lemma lem83798 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem83574 m n) (@lem83573 m n)). Qed.
Lemma lem83799 (m : nat) (n : nat) : (term102 m n) = (term127 m n).
Proof. exact (@lem83798 m (S n)). Qed.
Lemma lem83801 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem83541 m n) (@lem83540 m n)). Qed.
Lemma lem83802 (m : nat) (n : nat) : (term127 m n) = (term128 m n).
Proof. exact (@lem83801 (term22 m n) n). Qed.
Lemma lem83803 (m : nat) (n : nat) : (term102 m n) = (term128 m n).
Proof. exact (TRANS (@lem83799 m n) (@lem83802 m n)). Qed.
Lemma lem83805 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (EQ_MP (@lem83567 m n) (@lem83566 m n)). Qed.
Lemma lem83806 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem83807 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem83806) (@lem83805 m n)). Qed.
Lemma lem83808 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem83809 (m : nat) (n : nat) : (term131 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem83807 m n) (@lem83808 n)). Qed.
Lemma lem83810 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem83811 (m : nat) (n : nat) : (term128 m n) = (term133 m n).
Proof. exact (MK_COMB (@lem83810) (@lem83809 m n)). Qed.
Lemma lem83812 (m : nat) (n : nat) : (term102 m n) = (term133 m n).
Proof. exact (TRANS (@lem83803 m n) (@lem83811 m n)). Qed.
Lemma lem83813 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem83814 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (MK_COMB (@lem83813) (@lem83812 m n)). Qed.
Lemma lem83815 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem83816 (m : nat) (n : nat) : ((term102 m n) = (NUMERAL 0)) = ((term133 m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem83814 m n) (@lem83815)). Qed.
Lemma lem83818 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem83521 n (@lem83520 n)). Qed.
Lemma lem83819 (m : nat) (n : nat) : ((term133 m n) = (NUMERAL 0)) = False.
Proof. exact (@lem83818 (term132 m n)). Qed.
Lemma lem83820 (m : nat) (n : nat) : ((term102 m n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem83816 m n) (@lem83819 m n)). Qed.
Lemma lem83821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem83822 (m : nat) (n : nat) : (term136 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem83821) (@lem83820 m n)). Qed.
Lemma lem83826 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem83521 n (@lem83520 n)). Qed.
Lemma lem83827 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem83826 m). Qed.
Lemma lem83828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem83829 (m : nat) : (term126 m) = (or False).
Proof. exact (MK_COMB (@lem83828) (@lem83827 m)). Qed.
Lemma lem83831 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem83521 n (@lem83520 n)). Qed.
Lemma lem83832 (m : nat) (n : nat) : (term103 m n) = (False \/ False).
Proof. exact (MK_COMB (@lem83829 m) (@lem83831 n)). Qed.
Lemma lem83834 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem83835 : (False \/ False) = False.
Proof. exact (@lem83834 False). Qed.
Lemma lem83836 (m : nat) (n : nat) : (term103 m n) = False.
Proof. exact (TRANS (@lem83832 m n) (@lem83835)). Qed.
Lemma lem83837 (m : nat) (n : nat) : (((term102 m n) = (NUMERAL 0)) = (term103 m n)) = (False = False).
Proof. exact (MK_COMB (@lem83822 m n) (@lem83836 m n)). Qed.
Lemma lem83839 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem83840 : (False = False) = (~ False).
Proof. exact (@lem83839 False). Qed.
Lemma lem83842 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem83843 : (False = False) = True.
Proof. exact (TRANS (@lem83840) (@lem83842)). Qed.
Lemma lem83844 (m : nat) (n : nat) : (((term102 m n) = (NUMERAL 0)) = (term103 m n)) = True.
Proof. exact (TRANS (@lem83837 m n) (@lem83843)). Qed.
Lemma lem83845 (m : nat) (n : nat) : True = (((term102 m n) = (NUMERAL 0)) = (term103 m n)).
Proof. exact (SYM (@lem83844 m n)). Qed.
Lemma lem83846 (m : nat) (n : nat) : ((term102 m n) = (NUMERAL 0)) = (term103 m n).
Proof. exact (EQ_MP (@lem83845 m n) (@lem0)). Qed.
Lemma lem83847 (m : nat) (n : nat) : term105 m n.
Proof. exact (fun h0 : ((term28 m n) = (NUMERAL 0)) = (term98 m n) => @lem83846 m n). Qed.
Lemma lem83852 (m : nat) : term109 m.
Proof. exact (fun n : nat => @lem83847 m n). Qed.
Lemma lem83853 (m : nat) : term111 m.
Proof. exact (conj (@lem83792 m) (@lem83852 m)). Qed.
Lemma lem83854 (m : nat) : term48 m.
Proof. exact (@lem83666 m (@lem83853 m)). Qed.
Lemma lem83855 (n : nat) : term78 n.
Proof. exact (fun h0 : ((term35 n) = (NUMERAL 0)) = (term71 n) => @lem83744 n). Qed.
Lemma lem83860 : term82.
Proof. exact (fun n : nat => @lem83855 n). Qed.
Lemma lem83861 : term84.
Proof. exact (conj (@lem83704) (@lem83860)). Qed.
Lemma lem83862 : term40.
Proof. exact (@lem83638 (@lem83861)). Qed.
Lemma lem83863 (m : nat) : term50 m.
Proof. exact (fun h0 : term44 m => @lem83854 m). Qed.
Lemma lem83868 : term54.
Proof. exact (fun m : nat => @lem83863 m). Qed.
Lemma lem83869 : term56.
Proof. exact (conj (@lem83862) (@lem83868)). Qed.
Lemma lem83870 : term61.
Proof. exact (@lem83614 (@lem83869)). Qed.
