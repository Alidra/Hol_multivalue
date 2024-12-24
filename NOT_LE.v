Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_LE_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem97540 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem97541 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem97542 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem97541 n) (@lem97540 n)). Qed.
Lemma lem97543 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem97547 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem97548 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem97547 n h1)). Qed.
Lemma lem97549 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem97550 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem97549 n h1)). Qed.
Lemma lem97551 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem97548 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem97550 n h1)). Qed.
Lemma lem97552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97553 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem97552) (@lem97551 n)). Qed.
Lemma lem97554 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem97553 n)). Qed.
Lemma lem97555 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97556 : term6 = term7.
Proof. exact (MK_COMB (@lem97555) (@lem97554)). Qed.
Lemma lem97557 : term7.
Proof. exact (EQ_MP (@lem97556) (@lem75570)). Qed.
Lemma lem97558 (n : nat) : term8 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem97559 (n : nat) : (term8 n) = (term9 n).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem97560 (n : nat) : term9 n.
Proof. exact (EQ_MP (@lem97559 n) (@lem97558 n)). Qed.
Lemma lem97561 (n : nat) : (term9 n) = ((term9 n) = True).
Proof. exact (@lem7 (term9 n)). Qed.
Lemma lem97563 (n : nat) : term10 n.
Proof. exact (@lem97557 n). Qed.
Lemma lem97564 (n : nat) : (term10 n) = (term3 n).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem97565 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem97564 n) (@lem97563 n)). Qed.
Lemma lem97569 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem97570 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem97569 n h1)). Qed.
Lemma lem97571 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem97572 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem97571 n h1)). Qed.
Lemma lem97573 (n : nat) : ((NUMERAL 0) = (S n)) = ((S n) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = (S n) => @lem97570 n h1) (fun h1 : (S n) = (NUMERAL 0) => @lem97572 n h1)). Qed.
Lemma lem97574 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97575 (n : nat) : (term3 n) = (term2 n).
Proof. exact (MK_COMB (@lem97574) (@lem97573 n)). Qed.
Lemma lem97576 (n : nat) : term2 n.
Proof. exact (EQ_MP (@lem97575 n) (@lem97565 n)). Qed.
Lemma lem97577 (n : nat) : term11 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem97595 : term12.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem97596 (m : nat) : term13 m.
Proof. exact (@lem97595 m). Qed.
Lemma lem97597 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem97598 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem97597 m) (@lem97596 m)). Qed.
Lemma lem97599 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem97598 m n). Qed.
Lemma lem97600 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (term17 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem97602 : term18.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem97603 (m : nat) : term19 m.
Proof. exact (@lem97602 m). Qed.
Lemma lem97604 (m : nat) : (term19 m) = ((term20 m) = False).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem97613 : term21.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem97614 (m : nat) : term22 m.
Proof. exact (@lem97613 m). Qed.
Lemma lem97615 (m : nat) : (term22 m) = ((term23 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem97618 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem97619 : term25.
Proof. exact (@lem97618 term26). Qed.
Lemma lem97620 : term27 = term28.
Proof. exact (eq_refl term27). Qed.
Lemma lem97621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97622 : term29 = term30.
Proof. exact (MK_COMB (@lem97621) (@lem97620)). Qed.
Lemma lem97623 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem97624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97625 (m : nat) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem97624) (@lem97623 m)). Qed.
Lemma lem97626 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem97627 (m : nat) : (term37 m) = (term38 m).
Proof. exact (MK_COMB (@lem97625 m) (@lem97626 m)). Qed.
Lemma lem97628 : term39 = term40.
Proof. exact (fun_ext (fun m : nat => @lem97627 m)). Qed.
Lemma lem97629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97630 : term41 = term42.
Proof. exact (MK_COMB (@lem97629) (@lem97628)). Qed.
Lemma lem97631 : term43 = term44.
Proof. exact (MK_COMB (@lem97622) (@lem97630)). Qed.
Lemma lem97632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97633 : term45 = term46.
Proof. exact (MK_COMB (@lem97632) (@lem97631)). Qed.
Lemma lem97634 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem97635 : term47 = term26.
Proof. exact (fun_ext (fun m : nat => @lem97634 m)). Qed.
Lemma lem97636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97637 : term48 = term49.
Proof. exact (MK_COMB (@lem97636) (@lem97635)). Qed.
Lemma lem97638 : term25 = term50.
Proof. exact (MK_COMB (@lem97633) (@lem97637)). Qed.
Lemma lem97639 : term50.
Proof. exact (EQ_MP (@lem97638) (@lem97619)). Qed.
Lemma lem97640 (m : nat) (h1 : term32 m) : term32 m.
Proof. exact (h1). Qed.
Lemma lem97642 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem97643 : term51.
Proof. exact (@lem97642 term52). Qed.
Lemma lem97644 : term53 = (term54 = term55).
Proof. exact (eq_refl term53). Qed.
Lemma lem97645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97646 : term56 = term57.
Proof. exact (MK_COMB (@lem97645) (@lem97644)). Qed.
Lemma lem97647 (n : nat) : (term58 n) = ((term59 n) = (term20 n)).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem97648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97649 (n : nat) : (term60 n) = (term61 n).
Proof. exact (MK_COMB (@lem97648) (@lem97647 n)). Qed.
Lemma lem97650 (n : nat) : (term62 n) = ((term63 n) = (term64 n)).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem97651 (n : nat) : (term65 n) = (term66 n).
Proof. exact (MK_COMB (@lem97649 n) (@lem97650 n)). Qed.
Lemma lem97652 : term67 = term68.
Proof. exact (fun_ext (fun n : nat => @lem97651 n)). Qed.
Lemma lem97653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97654 : term69 = term70.
Proof. exact (MK_COMB (@lem97653) (@lem97652)). Qed.
Lemma lem97655 : term71 = term72.
Proof. exact (MK_COMB (@lem97646) (@lem97654)). Qed.
Lemma lem97656 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97657 : term73 = term74.
Proof. exact (MK_COMB (@lem97656) (@lem97655)). Qed.
Lemma lem97658 (n : nat) : (term58 n) = ((term59 n) = (term20 n)).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem97659 : term75 = term52.
Proof. exact (fun_ext (fun n : nat => @lem97658 n)). Qed.
Lemma lem97660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97661 : term76 = term28.
Proof. exact (MK_COMB (@lem97660) (@lem97659)). Qed.
Lemma lem97662 : term51 = term77.
Proof. exact (MK_COMB (@lem97657) (@lem97661)). Qed.
Lemma lem97663 : term77.
Proof. exact (EQ_MP (@lem97662) (@lem97643)). Qed.
Lemma lem97670 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem97671 (m : nat) : term78 m.
Proof. exact (@lem97670 (term79 m)). Qed.
Lemma lem97672 (m : nat) : (term80 m) = ((term81 m) = (term1 m)).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem97673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97674 (m : nat) : (term82 m) = (term83 m).
Proof. exact (MK_COMB (@lem97673) (@lem97672 m)). Qed.
Lemma lem97675 (n : nat) (m : nat) : (term84 m n) = ((term85 m n) = (term16 n m)).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem97676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97677 (n : nat) (m : nat) : (term86 m n) = (term87 n m).
Proof. exact (MK_COMB (@lem97676) (@lem97675 n m)). Qed.
Lemma lem97678 (n : nat) (m : nat) : (term88 m n) = ((term89 m n) = (term90 n m)).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem97679 (n : nat) (m : nat) : (term91 m n) = (term92 n m).
Proof. exact (MK_COMB (@lem97677 n m) (@lem97678 n m)). Qed.
Lemma lem97680 (m : nat) : (term93 m) = (term94 m).
Proof. exact (fun_ext (fun n : nat => @lem97679 n m)). Qed.
Lemma lem97681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97682 (m : nat) : (term95 m) = (term96 m).
Proof. exact (MK_COMB (@lem97681) (@lem97680 m)). Qed.
Lemma lem97683 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem97674 m) (@lem97682 m)). Qed.
Lemma lem97684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97685 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem97684) (@lem97683 m)). Qed.
Lemma lem97686 (n : nat) (m : nat) : (term84 m n) = ((term85 m n) = (term16 n m)).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem97687 (m : nat) : (term101 m) = (term79 m).
Proof. exact (fun_ext (fun n : nat => @lem97686 n m)). Qed.
Lemma lem97688 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97689 (m : nat) : (term102 m) = (term36 m).
Proof. exact (MK_COMB (@lem97688) (@lem97687 m)). Qed.
Lemma lem97690 (m : nat) : (term78 m) = (term103 m).
Proof. exact (MK_COMB (@lem97685 m) (@lem97689 m)). Qed.
Lemma lem97691 (m : nat) : term103 m.
Proof. exact (EQ_MP (@lem97690 m) (@lem97671 m)). Qed.
Lemma lem97748 (m : nat) : term104 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem97749 (m : nat) : (term104 m) = (term105 m).
Proof. exact (eq_refl (term104 m)). Qed.
Lemma lem97750 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem97749 m) (@lem97748 m)). Qed.
Lemma lem97751 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem97750 m n). Qed.
Lemma lem97752 (m : nat) (n : nat) : (term106 m n) = ((term90 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem97754 (m : nat) : term107 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem97755 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem97756 (m : nat) : term108 m.
Proof. exact (EQ_MP (@lem97755 m) (@lem97754 m)). Qed.
Lemma lem97757 (m : nat) (n : nat) : term109 m n.
Proof. exact (@lem97756 m n). Qed.
Lemma lem97758 (m : nat) (n : nat) : (term109 m n) = ((term110 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term109 m n)). Qed.
Lemma lem97760 (n : nat) (m : nat) (h1 : term32 m) : term111 m n.
Proof. exact (@lem97640 m h1 n). Qed.
Lemma lem97761 (n : nat) (m : nat) : (term111 m n) = ((term112 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term111 m n)). Qed.
Lemma lem97766 (m : nat) (n : nat) : (term110 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem97758 m n) (@lem97757 m n)). Qed.
Lemma lem97767 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97768 (m : nat) (n : nat) : (term89 m n) = (term112 m n).
Proof. exact (MK_COMB (@lem97767) (@lem97766 m n)). Qed.
Lemma lem97770 (n : nat) (m : nat) (h1 : term32 m) : (term112 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem97761 n m) (@lem97760 n m h1)). Qed.
Lemma lem97771 (n : nat) (m : nat) (h1 : term32 m) : (term89 m n) = (Peano.lt n m).
Proof. exact (TRANS (@lem97768 m n) (@lem97770 n m h1)). Qed.
Lemma lem97772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97773 (n : nat) (m : nat) (h1 : term32 m) : (term113 m n) = (term114 n m).
Proof. exact (MK_COMB (@lem97772) (@lem97771 n m h1)). Qed.
Lemma lem97775 (m : nat) (n : nat) : (term90 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem97752 m n) (@lem97751 m n)). Qed.
Lemma lem97776 (n : nat) (m : nat) : (term90 n m) = (Peano.lt n m).
Proof. exact (@lem97775 n m). Qed.
Lemma lem97777 (n : nat) (m : nat) (h1 : term32 m) : ((term89 m n) = (term90 n m)) = ((Peano.lt n m) = (Peano.lt n m)).
Proof. exact (MK_COMB (@lem97773 n m h1) (@lem97776 n m)). Qed.
Lemma lem97779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem97780 (x : Prop) : (x = x) = True.
Proof. exact (@lem97779 Prop x). Qed.
Lemma lem97781 (n : nat) (m : nat) : ((Peano.lt n m) = (Peano.lt n m)) = True.
Proof. exact (@lem97780 (Peano.lt n m)). Qed.
Lemma lem97782 (n : nat) (m : nat) (h1 : term32 m) : ((term89 m n) = (term90 n m)) = True.
Proof. exact (TRANS (@lem97777 n m h1) (@lem97781 n m)). Qed.
Lemma lem97783 (n : nat) (m : nat) (h1 : term32 m) : True = ((term89 m n) = (term90 n m)).
Proof. exact (SYM (@lem97782 n m h1)). Qed.
Lemma lem97784 (n : nat) (m : nat) (h1 : term32 m) : (term89 m n) = (term90 n m).
Proof. exact (EQ_MP (@lem97783 n m h1) (@lem0)). Qed.
Lemma lem97788 (n : nat) : (term9 n) = True.
Proof. exact (EQ_MP (@lem97561 n) (@lem97560 n)). Qed.
Lemma lem97789 : term115 = True.
Proof. exact (@lem97788 (NUMERAL 0)). Qed.
Lemma lem97790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97791 : term54 = (~ True).
Proof. exact (MK_COMB (@lem97790) (@lem97789)). Qed.
Lemma lem97793 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem97794 : term54 = False.
Proof. exact (TRANS (@lem97791) (@lem97793)). Qed.
Lemma lem97795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97796 : term116 = (@eq Prop False).
Proof. exact (MK_COMB (@lem97795) (@lem97794)). Qed.
Lemma lem97798 (m : nat) : (term20 m) = False.
Proof. exact (EQ_MP (@lem97604 m) (@lem97603 m)). Qed.
Lemma lem97799 : term55 = False.
Proof. exact (@lem97798 (NUMERAL 0)). Qed.
Lemma lem97800 : (term54 = term55) = (False = False).
Proof. exact (MK_COMB (@lem97796) (@lem97799)). Qed.
Lemma lem97802 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem97803 : (False = False) = (~ False).
Proof. exact (@lem97802 False). Qed.
Lemma lem97805 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem97806 : (False = False) = True.
Proof. exact (TRANS (@lem97803) (@lem97805)). Qed.
Lemma lem97807 : (term54 = term55) = True.
Proof. exact (TRANS (@lem97800) (@lem97806)). Qed.
Lemma lem97808 : True = (term54 = term55).
Proof. exact (SYM (@lem97807)). Qed.
Lemma lem97813 (n : nat) : (term9 n) = True.
Proof. exact (EQ_MP (@lem97561 n) (@lem97560 n)). Qed.
Lemma lem97814 (n : nat) : (term117 n) = True.
Proof. exact (@lem97813 (S n)). Qed.
Lemma lem97815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97816 (n : nat) : (term63 n) = (~ True).
Proof. exact (MK_COMB (@lem97815) (@lem97814 n)). Qed.
Lemma lem97818 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem97819 (n : nat) : (term63 n) = False.
Proof. exact (TRANS (@lem97816 n) (@lem97818)). Qed.
Lemma lem97820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97821 (n : nat) : (term118 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem97820) (@lem97819 n)). Qed.
Lemma lem97823 (m : nat) : (term20 m) = False.
Proof. exact (EQ_MP (@lem97604 m) (@lem97603 m)). Qed.
Lemma lem97824 (n : nat) : (term64 n) = False.
Proof. exact (@lem97823 (S n)). Qed.
Lemma lem97825 (n : nat) : ((term63 n) = (term64 n)) = (False = False).
Proof. exact (MK_COMB (@lem97821 n) (@lem97824 n)). Qed.
Lemma lem97827 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem97828 : (False = False) = (~ False).
Proof. exact (@lem97827 False). Qed.
Lemma lem97830 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem97831 : (False = False) = True.
Proof. exact (TRANS (@lem97828) (@lem97830)). Qed.
Lemma lem97832 (n : nat) : ((term63 n) = (term64 n)) = True.
Proof. exact (TRANS (@lem97825 n) (@lem97831)). Qed.
Lemma lem97833 (n : nat) : True = ((term63 n) = (term64 n)).
Proof. exact (SYM (@lem97832 n)). Qed.
Lemma lem97838 (m : nat) : (term23 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem97615 m) (@lem97614 m)). Qed.
Lemma lem97839 (m : nat) : (term119 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem97838 (S m)). Qed.
Lemma lem97841 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem97577 n (@lem97576 n)). Qed.
Lemma lem97842 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem97841 m). Qed.
Lemma lem97843 (m : nat) : (term119 m) = False.
Proof. exact (TRANS (@lem97839 m) (@lem97842 m)). Qed.
Lemma lem97844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem97845 (m : nat) : (term81 m) = (~ False).
Proof. exact (MK_COMB (@lem97844) (@lem97843 m)). Qed.
Lemma lem97847 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem97848 (m : nat) : (term81 m) = True.
Proof. exact (TRANS (@lem97845 m) (@lem97847)). Qed.
Lemma lem97849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem97850 (m : nat) : (term120 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem97849) (@lem97848 m)). Qed.
Lemma lem97852 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem97600 m n) (@lem97599 m n)). Qed.
Lemma lem97853 (m : nat) : (term1 m) = (term121 m).
Proof. exact (@lem97852 (NUMERAL 0) m). Qed.
Lemma lem97858 (m : nat) : ((term81 m) = (term1 m)) = (True = (term121 m)).
Proof. exact (MK_COMB (@lem97850 m) (@lem97853 m)). Qed.
Lemma lem97860 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem97861 (m : nat) : (True = (term121 m)) = (term121 m).
Proof. exact (@lem97860 (term121 m)). Qed.
Lemma lem97866 (m : nat) : ((term81 m) = (term1 m)) = (term121 m).
Proof. exact (TRANS (@lem97858 m) (@lem97861 m)). Qed.
Lemma lem97867 (m : nat) : (term121 m) = ((term81 m) = (term1 m)).
Proof. exact (SYM (@lem97866 m)). Qed.
Lemma lem97869 (P : nat -> Prop) : term24 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem97870 : term122.
Proof. exact (@lem97869 term123). Qed.
Lemma lem97871 : term124 = term125.
Proof. exact (eq_refl term124). Qed.
Lemma lem97872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem97873 : term126 = term127.
Proof. exact (MK_COMB (@lem97872) (@lem97871)). Qed.
Lemma lem97874 (m : nat) : (term128 m) = (term121 m).
Proof. exact (eq_refl (term128 m)). Qed.
Lemma lem97875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97876 (m : nat) : (term129 m) = (term130 m).
Proof. exact (MK_COMB (@lem97875) (@lem97874 m)). Qed.
Lemma lem97877 (m : nat) : (term131 m) = (term132 m).
Proof. exact (eq_refl (term131 m)). Qed.
Lemma lem97878 (m : nat) : (term133 m) = (term134 m).
Proof. exact (MK_COMB (@lem97876 m) (@lem97877 m)). Qed.
Lemma lem97879 : term135 = term136.
Proof. exact (fun_ext (fun m : nat => @lem97878 m)). Qed.
Lemma lem97880 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97881 : term137 = term138.
Proof. exact (MK_COMB (@lem97880) (@lem97879)). Qed.
Lemma lem97882 : term139 = term140.
Proof. exact (MK_COMB (@lem97873) (@lem97881)). Qed.
Lemma lem97883 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem97884 : term141 = term142.
Proof. exact (MK_COMB (@lem97883) (@lem97882)). Qed.
Lemma lem97885 (m : nat) : (term128 m) = (term121 m).
Proof. exact (eq_refl (term128 m)). Qed.
Lemma lem97886 : term143 = term123.
Proof. exact (fun_ext (fun m : nat => @lem97885 m)). Qed.
Lemma lem97887 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem97888 : term144 = term145.
Proof. exact (MK_COMB (@lem97887) (@lem97886)). Qed.
Lemma lem97889 : term122 = term146.
Proof. exact (MK_COMB (@lem97884) (@lem97888)). Qed.
Lemma lem97890 : term146.
Proof. exact (EQ_MP (@lem97889) (@lem97870)). Qed.
Lemma lem97895 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem97896 (x : nat) : (x = x) = True.
Proof. exact (@lem97895 nat x). Qed.
Lemma lem97897 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem97896 (NUMERAL 0)). Qed.
Lemma lem97898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem97899 : term147 = (or True).
Proof. exact (MK_COMB (@lem97898) (@lem97897)). Qed.
Lemma lem97900 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem97901 : term125 = term148.
Proof. exact (MK_COMB (@lem97899) (@lem97900)). Qed.
Lemma lem97903 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem97904 : term148 = True.
Proof. exact (@lem97903 term55). Qed.
Lemma lem97905 : term125 = True.
Proof. exact (TRANS (@lem97901) (@lem97904)). Qed.
Lemma lem97906 : True = term125.
Proof. exact (SYM (@lem97905)). Qed.
Lemma lem97907 : term125.
Proof. exact (EQ_MP (@lem97906) (@lem0)). Qed.
Lemma lem97913 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem97543 n) (@lem97542 n)). Qed.
Lemma lem97914 (m' : nat) : (term1 m') = True.
Proof. exact (@lem97913 m'). Qed.
Lemma lem97915 (m' : nat) : (term149 m') = (term149 m').
Proof. exact (eq_refl (term149 m')). Qed.
Lemma lem97916 (m' : nat) : (term132 m') = (term150 m').
Proof. exact (MK_COMB (@lem97915 m') (@lem97914 m')). Qed.
Lemma lem97918 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem97919 (m' : nat) : (term150 m') = True.
Proof. exact (@lem97918 ((NUMERAL 0) = (S m'))). Qed.
Lemma lem97920 (m' : nat) : (term132 m') = True.
Proof. exact (TRANS (@lem97916 m') (@lem97919 m')). Qed.
Lemma lem97921 (m' : nat) : True = (term132 m').
Proof. exact (SYM (@lem97920 m')). Qed.
Lemma lem97922 (m' : nat) : term132 m'.
Proof. exact (EQ_MP (@lem97921 m') (@lem0)). Qed.
Lemma lem97923 (m' : nat) : term134 m'.
Proof. exact (fun h0 : term121 m' => @lem97922 m'). Qed.
Lemma lem97928 : term138.
Proof. exact (fun m' : nat => @lem97923 m'). Qed.
Lemma lem97929 : term140.
Proof. exact (conj (@lem97907) (@lem97928)). Qed.
Lemma lem97930 : term145.
Proof. exact (@lem97890 (@lem97929)). Qed.
Lemma lem97931 (m : nat) : term128 m.
Proof. exact (@lem97930 m). Qed.
Lemma lem97932 (m : nat) : (term128 m) = (term121 m).
Proof. exact (eq_refl (term128 m)). Qed.
Lemma lem97933 (m : nat) : term121 m.
Proof. exact (EQ_MP (@lem97932 m) (@lem97931 m)). Qed.
Lemma lem97935 (m : nat) : (term81 m) = (term1 m).
Proof. exact (EQ_MP (@lem97867 m) (@lem97933 m)). Qed.
Lemma lem97936 (n : nat) : (term63 n) = (term64 n).
Proof. exact (EQ_MP (@lem97833 n) (@lem0)). Qed.
Lemma lem97937 : term54 = term55.
Proof. exact (EQ_MP (@lem97808) (@lem0)). Qed.
Lemma lem97938 (n : nat) (m : nat) (h1 : term32 m) : term92 n m.
Proof. exact (fun h0 : (term85 m n) = (term16 n m) => @lem97784 n m h1). Qed.
Lemma lem97943 (m : nat) (h1 : term32 m) : term96 m.
Proof. exact (fun n : nat => @lem97938 n m h1). Qed.
Lemma lem97944 (m : nat) (h1 : term32 m) : term98 m.
Proof. exact (conj (@lem97935 m) (@lem97943 m h1)). Qed.
Lemma lem97945 (m : nat) (h1 : term32 m) : term36 m.
Proof. exact (@lem97691 m (@lem97944 m h1)). Qed.
Lemma lem97946 (n : nat) : term66 n.
Proof. exact (fun h0 : (term59 n) = (term20 n) => @lem97936 n). Qed.
Lemma lem97951 : term70.
Proof. exact (fun n : nat => @lem97946 n). Qed.
Lemma lem97952 : term72.
Proof. exact (conj (@lem97937) (@lem97951)). Qed.
Lemma lem97953 : term28.
Proof. exact (@lem97663 (@lem97952)). Qed.
Lemma lem97954 (m : nat) : term38 m.
Proof. exact (fun h0 : term32 m => @lem97945 m h0). Qed.
Lemma lem97959 : term42.
Proof. exact (fun m : nat => @lem97954 m). Qed.
Lemma lem97960 : term44.
Proof. exact (conj (@lem97953) (@lem97959)). Qed.
Lemma lem97961 : term49.
Proof. exact (@lem97639 (@lem97960)). Qed.
