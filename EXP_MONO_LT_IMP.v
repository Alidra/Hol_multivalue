Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_MONO_LT_IMP_term_abbrevs.
Require Import EXP_EQ_0_spec.
Require Import EXP_MONO_LE_IMP_spec.
Require Import LET_TRANS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LT_IMP_LE_spec.
Require Import LT_MULT_RCANCEL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Require Import thm89994_spec.
Lemma lem150646 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem150657 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem150658 (m : nat) (h1 : term1) : term2 m.
Proof. exact (@lem150657 h1 m). Qed.
Lemma lem150659 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem150660 (m : nat) (h1 : term1) : term3 m.
Proof. exact (EQ_MP (@lem150659 m) (@lem150658 m h1)). Qed.
Lemma lem150661 (m : nat) (n : nat) (h1 : term1) : term4 m n.
Proof. exact (@lem150660 m h1 n). Qed.
Lemma lem150662 (n : nat) (m : nat) : (term4 m n) = (term5 n m).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem150663 (n : nat) (m : nat) (h1 : term1) : term5 n m.
Proof. exact (EQ_MP (@lem150662 n m) (@lem150661 m n h1)). Qed.
Lemma lem150664 (n : nat) (m : nat) (p : nat) (h1 : term1) : term6 n m p.
Proof. exact (@lem150663 n m h1 p). Qed.
Lemma lem150665 (n : nat) (m : nat) (p : nat) : (term6 n m p) = (term7 n m p).
Proof. exact (eq_refl (term6 n m p)). Qed.
Lemma lem150666 (n : nat) (m : nat) (p : nat) (h1 : term1) : term7 n m p.
Proof. exact (EQ_MP (@lem150665 n m p) (@lem150664 n m p h1)). Qed.
Lemma lem150667 (m : nat) (n : nat) (p : nat) (h1 : term8 m n p) : term8 m n p.
Proof. exact (h1). Qed.
Lemma lem150668 (m : nat) (n : nat) (p : nat) (h1 : term1) (h2 : term8 m n p) : Peano.lt m p.
Proof. exact (@lem150666 n m p h1 (@lem150667 m n p h2)). Qed.
Lemma lem150669 (m : nat) (n : nat) (p : nat) (h1 : term8 m n p) : term9 m p.
Proof. exact (fun h0 : term1 => @lem150668 m n p h0 h1). Qed.
Lemma lem150670 (m : nat) (p : nat) (h1 : term10 m p) : term10 m p.
Proof. exact (h1). Qed.
Lemma lem150671 (m : nat) (p : nat) (h1 : term10 m p) : term9 m p.
Proof. exact (ex_elim (@lem150670 m p h1) (fun n : nat => fun h0 : term11 m p n => @lem150669 m n p h0)). Qed.
Lemma lem150672 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem150673 (m : nat) (p : nat) (h1 : term1) (h2 : term10 m p) : Peano.lt m p.
Proof. exact (@lem150671 m p h2 (@lem150672 h1)). Qed.
Lemma lem150674 (m : nat) (p : nat) (h1 : term1) : term12 m p.
Proof. exact (fun h0 : term10 m p => @lem150673 m p h1 h0). Qed.
Lemma lem150675 (m : nat) (h1 : term1) : term13 m.
Proof. exact (fun p : nat => @lem150674 m p h1). Qed.
Lemma lem150676 (h1 : term1) : term14.
Proof. exact (fun m : nat => @lem150675 m h1). Qed.
Lemma lem150677 : term15.
Proof. exact (fun h0 : term1 => @lem150676 h0). Qed.
Lemma lem150678 : term14.
Proof. exact (@lem150677 (@lem95173)). Qed.
Lemma lem150679 (m : nat) : term16 m.
Proof. exact (@lem150678 m). Qed.
Lemma lem150680 (m : nat) : (term16 m) = (term13 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem150681 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem150680 m) (@lem150679 m)). Qed.
Lemma lem150682 (m : nat) (p : nat) : term17 m p.
Proof. exact (@lem150681 m p). Qed.
Lemma lem150683 (m : nat) (p : nat) : (term17 m p) = (term12 m p).
Proof. exact (eq_refl (term17 m p)). Qed.
Lemma lem150685 : term18.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem150686 (m : nat) : term19 m.
Proof. exact (@lem150685 m). Qed.
Lemma lem150687 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem150688 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem150687 m) (@lem150686 m)). Qed.
Lemma lem150689 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem150688 m n). Qed.
Lemma lem150690 (m : nat) (n : nat) : (term21 m n) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem150692 : term24.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem150693 (m : nat) : term25 m.
Proof. exact (@lem150692 m). Qed.
Lemma lem150694 (m : nat) : (term25 m) = ((term26 m) = term27).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem150696 (n : nat) : term28 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem150697 (n : nat) : (term28 n) = (term29 n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem150698 (n : nat) : term29 n.
Proof. exact (EQ_MP (@lem150697 n) (@lem150696 n)). Qed.
Lemma lem150699 (n : nat) : term30 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem150713 (P : nat -> Prop) : term31 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem150714 (x : nat) (y : nat) : term32 x y.
Proof. exact (@lem150713 (term33 x y)). Qed.
Lemma lem150715 (x : nat) (y : nat) : (term34 x y) = (term35 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem150716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150717 (x : nat) (y : nat) : (term36 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem150716) (@lem150715 x y)). Qed.
Lemma lem150718 (x : nat) (y : nat) (n : nat) : (term38 x y n) = (term39 x y n).
Proof. exact (eq_refl (term38 x y n)). Qed.
Lemma lem150719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150720 (x : nat) (y : nat) (n : nat) : (term40 x y n) = (term41 x y n).
Proof. exact (MK_COMB (@lem150719) (@lem150718 x y n)). Qed.
Lemma lem150721 (x : nat) (y : nat) (n : nat) : (term42 x y n) = (term43 x y n).
Proof. exact (eq_refl (term42 x y n)). Qed.
Lemma lem150722 (x : nat) (y : nat) (n : nat) : (term44 x y n) = (term45 x y n).
Proof. exact (MK_COMB (@lem150720 x y n) (@lem150721 x y n)). Qed.
Lemma lem150723 (x : nat) (y : nat) : (term46 x y) = (term47 x y).
Proof. exact (fun_ext (fun n : nat => @lem150722 x y n)). Qed.
Lemma lem150724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150725 (x : nat) (y : nat) : (term48 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem150724) (@lem150723 x y)). Qed.
Lemma lem150726 (x : nat) (y : nat) : (term50 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem150717 x y) (@lem150725 x y)). Qed.
Lemma lem150727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150728 (x : nat) (y : nat) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem150727) (@lem150726 x y)). Qed.
Lemma lem150729 (x : nat) (y : nat) (n : nat) : (term38 x y n) = (term39 x y n).
Proof. exact (eq_refl (term38 x y n)). Qed.
Lemma lem150730 (x : nat) (y : nat) : (term54 x y) = (term33 x y).
Proof. exact (fun_ext (fun n : nat => @lem150729 x y n)). Qed.
Lemma lem150731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem150732 (x : nat) (y : nat) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem150731) (@lem150730 x y)). Qed.
Lemma lem150733 (x : nat) (y : nat) : (term32 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem150728 x y) (@lem150732 x y)). Qed.
Lemma lem150734 (x : nat) (y : nat) : term57 x y.
Proof. exact (EQ_MP (@lem150733 x y) (@lem150714 x y)). Qed.
Lemma lem150735 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term39 x y n.
Proof. exact (h1). Qed.
Lemma lem150741 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem150742 (x : nat) : (x = x) = True.
Proof. exact (@lem150741 nat x). Qed.
Lemma lem150743 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem150742 (NUMERAL 0)). Qed.
Lemma lem150744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem150745 : term58 = (~ True).
Proof. exact (MK_COMB (@lem150744) (@lem150743)). Qed.
Lemma lem150747 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem150748 : term58 = False.
Proof. exact (TRANS (@lem150745) (@lem150747)). Qed.
Lemma lem150749 (x : nat) (y : nat) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem150750 (x : nat) (y : nat) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem150749 x y) (@lem150748)). Qed.
Lemma lem150752 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem150753 (x : nat) (y : nat) : (term61 x y) = False.
Proof. exact (@lem150752 (Peano.lt x y)). Qed.
Lemma lem150754 (x : nat) (y : nat) : (term60 x y) = False.
Proof. exact (TRANS (@lem150750 x y) (@lem150753 x y)). Qed.
Lemma lem150755 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150756 (x : nat) (y : nat) : (term62 x y) = (imp False).
Proof. exact (MK_COMB (@lem150755) (@lem150754 x y)). Qed.
Lemma lem150758 (m : nat) : (term26 m) = term27.
Proof. exact (EQ_MP (@lem150694 m) (@lem150693 m)). Qed.
Lemma lem150759 (x : nat) : (term26 x) = term27.
Proof. exact (@lem150758 x). Qed.
Lemma lem150760 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem150761 (x : nat) : (term63 x) = term64.
Proof. exact (MK_COMB (@lem150760) (@lem150759 x)). Qed.
Lemma lem150763 (m : nat) : (term26 m) = term27.
Proof. exact (EQ_MP (@lem150694 m) (@lem150693 m)). Qed.
Lemma lem150764 (y : nat) : (term26 y) = term27.
Proof. exact (@lem150763 y). Qed.
Lemma lem150765 (x : nat) (y : nat) : (term65 x y) = term66.
Proof. exact (MK_COMB (@lem150761 x) (@lem150764 y)). Qed.
Lemma lem150766 (x : nat) (y : nat) : (term35 x y) = term67.
Proof. exact (MK_COMB (@lem150756 x y) (@lem150765 x y)). Qed.
Lemma lem150768 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem150769 : term67 = True.
Proof. exact (@lem150768 term66). Qed.
Lemma lem150770 (x : nat) (y : nat) : (term35 x y) = True.
Proof. exact (TRANS (@lem150766 x y) (@lem150769)). Qed.
Lemma lem150771 (x : nat) (y : nat) : True = (term35 x y).
Proof. exact (SYM (@lem150770 x y)). Qed.
Lemma lem150772 (x : nat) (y : nat) : term35 x y.
Proof. exact (EQ_MP (@lem150771 x y) (@lem0)). Qed.
Lemma lem150778 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem150699 n (@lem150698 n)). Qed.
Lemma lem150779 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem150780 (n : nat) : (term29 n) = (~ False).
Proof. exact (MK_COMB (@lem150779) (@lem150778 n)). Qed.
Lemma lem150782 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem150783 (n : nat) : (term29 n) = True.
Proof. exact (TRANS (@lem150780 n) (@lem150782)). Qed.
Lemma lem150784 (x : nat) (y : nat) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem150785 (n : nat) (x : nat) (y : nat) : (term68 x y n) = (term69 x y).
Proof. exact (MK_COMB (@lem150784 x y) (@lem150783 n)). Qed.
Lemma lem150787 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem150788 (x : nat) (y : nat) : (term69 x y) = (Peano.lt x y).
Proof. exact (@lem150787 (Peano.lt x y)). Qed.
Lemma lem150789 (n : nat) (x : nat) (y : nat) : (term68 x y n) = (Peano.lt x y).
Proof. exact (TRANS (@lem150785 n x y) (@lem150788 x y)). Qed.
Lemma lem150790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem150791 (n : nat) (x : nat) (y : nat) : (term70 x y n) = (term71 x y).
Proof. exact (MK_COMB (@lem150790) (@lem150789 n x y)). Qed.
Lemma lem150793 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (EQ_MP (@lem150690 m n) (@lem150689 m n)). Qed.
Lemma lem150794 (x : nat) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (@lem150793 x n). Qed.
Lemma lem150795 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem150796 (x : nat) (n : nat) : (term72 x n) = (term73 x n).
Proof. exact (MK_COMB (@lem150795) (@lem150794 x n)). Qed.
Lemma lem150798 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (EQ_MP (@lem150690 m n) (@lem150689 m n)). Qed.
Lemma lem150799 (y : nat) (n : nat) : (term22 y n) = (term23 y n).
Proof. exact (@lem150798 y n). Qed.
Lemma lem150800 (x : nat) (y : nat) (n : nat) : (term74 x y n) = (term75 x y n).
Proof. exact (MK_COMB (@lem150796 x n) (@lem150799 y n)). Qed.
Lemma lem150801 (x : nat) (y : nat) (n : nat) : (term43 x y n) = (term76 x y n).
Proof. exact (MK_COMB (@lem150791 n x y) (@lem150800 x y n)). Qed.
Lemma lem150804 (x : nat) (y : nat) (n : nat) : (term76 x y n) = (term43 x y n).
Proof. exact (SYM (@lem150801 x y n)). Qed.
Lemma lem150805 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem150807 (m : nat) (p : nat) : term12 m p.
Proof. exact (EQ_MP (@lem150683 m p) (@lem150682 m p)). Qed.
Lemma lem150808 (x : nat) (y : nat) (n : nat) : term77 x y n.
Proof. exact (@lem150807 (term23 x n) (term23 y n)). Qed.
Lemma lem150809 (m : nat) : term78 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem150810 (m : nat) : (term78 m) = (term79 m).
Proof. exact (eq_refl (term78 m)). Qed.
Lemma lem150811 (m : nat) : term79 m.
Proof. exact (EQ_MP (@lem150810 m) (@lem150809 m)). Qed.
Lemma lem150812 (m : nat) (n : nat) : term80 m n.
Proof. exact (@lem150811 m n). Qed.
Lemma lem150813 (m : nat) (n : nat) : (term80 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term81 m n)).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem150815 (x : nat) : term82 x.
Proof. exact (@lem150645 x). Qed.
Lemma lem150816 (x : nat) : (term82 x) = (term83 x).
Proof. exact (eq_refl (term82 x)). Qed.
Lemma lem150817 (x : nat) : term83 x.
Proof. exact (EQ_MP (@lem150816 x) (@lem150815 x)). Qed.
Lemma lem150818 (x : nat) (y : nat) : term84 x y.
Proof. exact (@lem150817 x y). Qed.
Lemma lem150819 (x : nat) (y : nat) : (term84 x y) = (term85 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem150820 (x : nat) (y : nat) : term85 x y.
Proof. exact (EQ_MP (@lem150819 x y) (@lem150818 x y)). Qed.
Lemma lem150821 (x : nat) (y : nat) (n : nat) : term86 x y n.
Proof. exact (@lem150820 x y n). Qed.
Lemma lem150822 (x : nat) (y : nat) (n : nat) : (term86 x y n) = (term87 x y n).
Proof. exact (eq_refl (term86 x y n)). Qed.
Lemma lem150823 (x : nat) (y : nat) (n : nat) : term87 x y n.
Proof. exact (EQ_MP (@lem150822 x y n) (@lem150821 x y n)). Qed.
Lemma lem150824 (x : nat) (y : nat) (h1 : Peano.le x y) : Peano.le x y.
Proof. exact (h1). Qed.
Lemma lem150825 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : term88 x y n.
Proof. exact (@lem150823 x y n (@lem150824 x y h1)). Qed.
Lemma lem150826 (x : nat) (y : nat) (n : nat) : (term88 x y n) = ((term88 x y n) = True).
Proof. exact (@lem7 (term88 x y n)). Qed.
Lemma lem150827 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : (term88 x y n) = True.
Proof. exact (EQ_MP (@lem150826 x y n) (@lem150825 n x y h1)). Qed.
Lemma lem150833 (m : nat) : term89 m.
Proof. exact (@lem105963 m). Qed.
Lemma lem150834 (m : nat) : (term89 m) = (term90 m).
Proof. exact (eq_refl (term89 m)). Qed.
Lemma lem150835 (m : nat) : term90 m.
Proof. exact (EQ_MP (@lem150834 m) (@lem150833 m)). Qed.
Lemma lem150836 (m : nat) (n : nat) : term91 m n.
Proof. exact (@lem150835 m n). Qed.
Lemma lem150837 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (eq_refl (term91 m n)). Qed.
Lemma lem150838 (m : nat) (n : nat) : term92 m n.
Proof. exact (EQ_MP (@lem150837 m n) (@lem150836 m n)). Qed.
Lemma lem150839 (m : nat) (n : nat) (p : nat) : term93 m n p.
Proof. exact (@lem150838 m n p). Qed.
Lemma lem150840 (m : nat) (n : nat) (p : nat) : (term93 m n p) = ((term94 m n p) = (term95 m n p)).
Proof. exact (eq_refl (term93 m n p)). Qed.
Lemma lem150842 (m : nat) : term96 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem150843 (m : nat) : (term96 m) = (term97 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem150844 (m : nat) : term97 m.
Proof. exact (EQ_MP (@lem150843 m) (@lem150842 m)). Qed.
Lemma lem150845 (m : nat) (n : nat) : term98 m n.
Proof. exact (@lem150844 m n). Qed.
Lemma lem150846 (m : nat) (n : nat) : (term98 m n) = (term99 m n).
Proof. exact (eq_refl (term98 m n)). Qed.
Lemma lem150847 (m : nat) (n : nat) : term99 m n.
Proof. exact (EQ_MP (@lem150846 m n) (@lem150845 m n)). Qed.
Lemma lem150848 (m : nat) (n : nat) (p : nat) : term100 m n p.
Proof. exact (@lem150847 m n p). Qed.
Lemma lem150849 (m : nat) (n : nat) (p : nat) : (term100 m n p) = ((term101 n m p) = (term102 m n p)).
Proof. exact (eq_refl (term100 m n p)). Qed.
Lemma lem150851 (m : nat) : term103 m.
Proof. exact (@lem98439 m). Qed.
Lemma lem150852 (m : nat) : (term103 m) = (term104 m).
Proof. exact (eq_refl (term103 m)). Qed.
Lemma lem150853 (m : nat) : term104 m.
Proof. exact (EQ_MP (@lem150852 m) (@lem150851 m)). Qed.
Lemma lem150854 (m : nat) (n : nat) : term105 m n.
Proof. exact (@lem150853 m n). Qed.
Lemma lem150855 (m : nat) (n : nat) : (term105 m n) = (term106 m n).
Proof. exact (eq_refl (term105 m n)). Qed.
Lemma lem150856 (m : nat) (n : nat) : term106 m n.
Proof. exact (EQ_MP (@lem150855 m n) (@lem150854 m n)). Qed.
Lemma lem150857 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem150858 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.le m n.
Proof. exact (@lem150856 m n (@lem150857 m n h1)). Qed.
Lemma lem150859 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem150860 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem150859 m n) (@lem150858 m n h1)). Qed.
Lemma lem150875 (x : nat) (y : nat) : (Peano.lt x y) = ((Peano.lt x y) = True).
Proof. exact (@lem7 (Peano.lt x y)). Qed.
Lemma lem150880 (m : nat) (n : nat) (p : nat) : (term101 n m p) = (term102 m n p).
Proof. exact (EQ_MP (@lem150849 m n p) (@lem150848 m n p)). Qed.
Lemma lem150881 (x : nat) (y : nat) (n : nat) : (term107 x y n) = (term108 x y n).
Proof. exact (@lem150880 x (Nat.pow x n) (Nat.pow y n)). Qed.
Lemma lem150887 (x : nat) (y : nat) (n : nat) : term109 x y n.
Proof. exact (fun h0 : Peano.le x y => @lem150827 n x y h0). Qed.
Lemma lem150889 (m : nat) (n : nat) : term110 m n.
Proof. exact (fun h0 : Peano.lt m n => @lem150860 m n h0). Qed.
Lemma lem150890 (x : nat) (y : nat) : term110 x y.
Proof. exact (@lem150889 x y). Qed.
Lemma lem150892 (x : nat) (y : nat) (h1 : Peano.lt x y) : (Peano.lt x y) = True.
Proof. exact (EQ_MP (@lem150875 x y) (@lem150805 x y h1)). Qed.
Lemma lem150893 (x : nat) (y : nat) (h1 : Peano.lt x y) : True = (Peano.lt x y).
Proof. exact (SYM (@lem150892 x y h1)). Qed.
Lemma lem150894 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (EQ_MP (@lem150893 x y h1) (@lem0)). Qed.
Lemma lem150895 (x : nat) (y : nat) (h1 : Peano.lt x y) : (Peano.le x y) = True.
Proof. exact (@lem150890 x y (@lem150894 x y h1)). Qed.
Lemma lem150896 (x : nat) (y : nat) (h1 : Peano.lt x y) : True = (Peano.le x y).
Proof. exact (SYM (@lem150895 x y h1)). Qed.
Lemma lem150897 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.le x y.
Proof. exact (EQ_MP (@lem150896 x y h1) (@lem0)). Qed.
Lemma lem150898 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term88 x y n) = True.
Proof. exact (@lem150887 x y n (@lem150897 x y h1)). Qed.
Lemma lem150899 (x : nat) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem150900 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term108 x y n) = (term112 x).
Proof. exact (MK_COMB (@lem150899 x) (@lem150898 n x y h1)). Qed.
Lemma lem150902 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem150903 (x : nat) : (term112 x) = True.
Proof. exact (@lem150902 (x = (NUMERAL 0))). Qed.
Lemma lem150904 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term108 x y n) = True.
Proof. exact (TRANS (@lem150900 n x y h1) (@lem150903 x)). Qed.
Lemma lem150905 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term107 x y n) = True.
Proof. exact (TRANS (@lem150881 x y n) (@lem150904 n x y h1)). Qed.
Lemma lem150906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150907 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term113 x y n) = (and True).
Proof. exact (MK_COMB (@lem150906) (@lem150905 n x y h1)). Qed.
Lemma lem150909 (m : nat) (n : nat) (p : nat) : (term94 m n p) = (term95 m n p).
Proof. exact (EQ_MP (@lem150840 m n p) (@lem150839 m n p)). Qed.
Lemma lem150910 (x : nat) (y : nat) (n : nat) : (term114 x y n) = (term115 x y n).
Proof. exact (@lem150909 x y (Nat.pow y n)). Qed.
Lemma lem150914 (x : nat) (y : nat) (h1 : Peano.lt x y) : (Peano.lt x y) = True.
Proof. exact (EQ_MP (@lem150875 x y) (@lem150805 x y h1)). Qed.
Lemma lem150915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem150916 (x : nat) (y : nat) (h1 : Peano.lt x y) : (term59 x y) = (and True).
Proof. exact (MK_COMB (@lem150915) (@lem150914 x y h1)). Qed.
Lemma lem150918 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term81 m n).
Proof. exact (EQ_MP (@lem150813 m n) (@lem150812 m n)). Qed.
Lemma lem150919 (y : nat) (n : nat) : ((Nat.pow y n) = (NUMERAL 0)) = (term81 y n).
Proof. exact (@lem150918 y n). Qed.
Lemma lem150926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem150927 (y : nat) (n : nat) : (term116 y n) = (term117 y n).
Proof. exact (MK_COMB (@lem150926) (@lem150919 y n)). Qed.
Lemma lem150934 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term115 x y n) = (term118 y n).
Proof. exact (MK_COMB (@lem150916 x y h1) (@lem150927 y n)). Qed.
Lemma lem150936 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150937 (y : nat) (n : nat) : (term118 y n) = (term117 y n).
Proof. exact (@lem150936 (term117 y n)). Qed.
Lemma lem150944 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term115 x y n) = (term117 y n).
Proof. exact (TRANS (@lem150934 n x y h1) (@lem150937 y n)). Qed.
Lemma lem150945 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term114 x y n) = (term117 y n).
Proof. exact (TRANS (@lem150910 x y n) (@lem150944 n x y h1)). Qed.
Lemma lem150946 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term119 x y n) = (term118 y n).
Proof. exact (MK_COMB (@lem150907 n x y h1) (@lem150945 n x y h1)). Qed.
Lemma lem150948 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem150949 (y : nat) (n : nat) : (term118 y n) = (term117 y n).
Proof. exact (@lem150948 (term117 y n)). Qed.
Lemma lem150956 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term119 x y n) = (term117 y n).
Proof. exact (TRANS (@lem150946 n x y h1) (@lem150949 y n)). Qed.
Lemma lem150957 (n : nat) (x : nat) (y : nat) (h1 : Peano.lt x y) : (term117 y n) = (term119 x y n).
Proof. exact (SYM (@lem150956 n x y h1)). Qed.
Lemma lem150958 (y : nat) (n : nat) (h1 : term81 y n) : term81 y n.
Proof. exact (h1). Qed.
Lemma lem150961 (x : nat) (y : nat) (n : nat) (h1 : term120 x y n) : term120 x y n.
Proof. exact (h1). Qed.
Lemma lem150962 (x : nat) (y : nat) (n : nat) : term121 x y n.
Proof. exact (fun h0 : term120 x y n => @lem150961 x y n h0). Qed.
Lemma lem150963 (x : nat) (y : nat) (n : nat) (h1 : term121 x y n) : term121 x y n.
Proof. exact (h1). Qed.
Lemma lem150964 (x : nat) (y : nat) (n : nat) (h1 : term120 x y n) : term120 x y n.
Proof. exact (h1). Qed.
Lemma lem150965 (x : nat) (y : nat) (n : nat) (h1 : term120 x y n) (h2 : term121 x y n) : term120 x y n.
Proof. exact (@lem150963 x y n h2 (@lem150964 x y n h1)). Qed.
Lemma lem150966 (x : nat) (y : nat) (n : nat) (h1 : term120 x y n) : term122 x y n.
Proof. exact (fun h0 : term121 x y n => @lem150965 x y n h1 h0). Qed.
Lemma lem150967 (x : nat) (y : nat) (n : nat) (h1 : term121 x y n) : term121 x y n.
Proof. exact (h1). Qed.
Lemma lem150968 (x : nat) (y : nat) (n : nat) (h1 : term120 x y n) (h2 : term121 x y n) : term120 x y n.
Proof. exact (@lem150966 x y n h1 (@lem150967 x y n h2)). Qed.
Lemma lem150969 (x : nat) (y : nat) (n : nat) (h1 : term121 x y n) : term121 x y n.
Proof. exact (fun h0 : term120 x y n => @lem150968 x y n h0 h1). Qed.
Lemma lem150970 (x : nat) (y : nat) (n : nat) : term123 x y n.
Proof. exact (fun h0 : term121 x y n => @lem150969 x y n h0). Qed.
Lemma lem150973 (x : nat) (y : nat) (n : nat) : term121 x y n.
Proof. exact (@lem150970 x y n (@lem150962 x y n)). Qed.
Lemma lem150999 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem151000 : term124 = term125.
Proof. exact (@lem150999 term0). Qed.
Lemma lem151006 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem151007 (m : nat) : ((term126 m) = False) = (term127 m).
Proof. exact (@lem151006 (term126 m)). Qed.
Lemma lem151008 : term128 = term129.
Proof. exact (fun_ext (fun m : nat => @lem151007 m)). Qed.
Lemma lem151009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151010 : term0 = term130.
Proof. exact (MK_COMB (@lem151009) (@lem151008)). Qed.
Lemma lem151015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem151016 : term125 = term131.
Proof. exact (MK_COMB (@lem151015) (@lem151010)). Qed.
Lemma lem151017 : term124 = term131.
Proof. exact (TRANS (@lem151000) (@lem151016)). Qed.
Lemma lem151018 (y : nat) (n : nat) : (term132 y n) = (term132 y n).
Proof. exact (eq_refl (term132 y n)). Qed.
Lemma lem151019 (y : nat) (n : nat) : (term133 y n) = (term134 y n).
Proof. exact (MK_COMB (@lem151018 y n) (@lem151017)). Qed.
Lemma lem151022 (x : nat) (y : nat) : (term71 x y) = (term71 x y).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem151023 (x : nat) (y : nat) (n : nat) : (term135 x y n) = (term136 x y n).
Proof. exact (MK_COMB (@lem151022 x y) (@lem151019 y n)). Qed.
Lemma lem151026 (x : nat) (y : nat) (n : nat) : (term41 x y n) = (term41 x y n).
Proof. exact (eq_refl (term41 x y n)). Qed.
Lemma lem151027 (x : nat) (y : nat) (n : nat) : (term120 x y n) = (term137 x y n).
Proof. exact (MK_COMB (@lem151026 x y n) (@lem151023 x y n)). Qed.
Lemma lem151030 (y : nat) (n : nat) : (term138 y n) = (term139 y n).
Proof. exact (fun_ext (fun x : nat => @lem151027 x y n)). Qed.
Lemma lem151031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151032 (y : nat) (n : nat) : (term140 y n) = (term141 y n).
Proof. exact (MK_COMB (@lem151031) (@lem151030 y n)). Qed.
Lemma lem151037 (n : nat) : (term142 n) = (term143 n).
Proof. exact (fun_ext (fun y : nat => @lem151032 y n)). Qed.
Lemma lem151038 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151039 (n : nat) : (term144 n) = (term145 n).
Proof. exact (MK_COMB (@lem151038) (@lem151037 n)). Qed.
Lemma lem151044 : term146 = term147.
Proof. exact (fun_ext (fun n : nat => @lem151039 n)). Qed.
Lemma lem151045 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151054 : term148 = term149.
Proof. exact (MK_COMB (@lem151045) (@lem151044)). Qed.
Lemma lem151057 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem151058 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem151057 m)). Qed.
Lemma lem151059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151060 : term130 = term130.
Proof. exact (MK_COMB (@lem151059) (@lem151058)). Qed.
Lemma lem151061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem151062 : term131 = term131.
Proof. exact (MK_COMB (@lem151061) (@lem151060)). Qed.
Lemma lem151071 (y : nat) (n : nat) : (term132 y n) = (term132 y n).
Proof. exact (eq_refl (term132 y n)). Qed.
Lemma lem151072 (y : nat) (n : nat) : (term134 y n) = (term134 y n).
Proof. exact (MK_COMB (@lem151071 y n) (@lem151062)). Qed.
Lemma lem151075 (x : nat) (y : nat) : (term71 x y) = (term71 x y).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem151076 (x : nat) (y : nat) (n : nat) : (term136 x y n) = (term136 x y n).
Proof. exact (MK_COMB (@lem151075 x y) (@lem151072 y n)). Qed.
Lemma lem151089 (x : nat) (y : nat) (n : nat) : (term41 x y n) = (term41 x y n).
Proof. exact (eq_refl (term41 x y n)). Qed.
Lemma lem151090 (x : nat) (y : nat) (n : nat) : (term137 x y n) = (term137 x y n).
Proof. exact (MK_COMB (@lem151089 x y n) (@lem151076 x y n)). Qed.
Lemma lem151091 (y : nat) (n : nat) : (term139 y n) = (term139 y n).
Proof. exact (fun_ext (fun x : nat => @lem151090 x y n)). Qed.
Lemma lem151092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151093 (y : nat) (n : nat) : (term141 y n) = (term141 y n).
Proof. exact (MK_COMB (@lem151092) (@lem151091 y n)). Qed.
Lemma lem151094 (n : nat) : (term143 n) = (term143 n).
Proof. exact (fun_ext (fun y : nat => @lem151093 y n)). Qed.
Lemma lem151095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151096 (n : nat) : (term145 n) = (term145 n).
Proof. exact (MK_COMB (@lem151095) (@lem151094 n)). Qed.
Lemma lem151097 : term147 = term147.
Proof. exact (fun_ext (fun n : nat => @lem151096 n)). Qed.
Lemma lem151098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151099 : term149 = term149.
Proof. exact (MK_COMB (@lem151098) (@lem151097)). Qed.
Lemma lem151138 : term148 = term149.
Proof. exact (TRANS (@lem151054) (@lem151099)). Qed.
Lemma lem151139 : term149 = term148.
Proof. exact (SYM (@lem151138)). Qed.
Lemma lem151140 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term39 x y n.
Proof. exact (h1). Qed.
Lemma lem151143 (h1 : term130) : term130.
Proof. exact (h1). Qed.
Lemma lem151147 (n : nat) : (term150 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem151149 (x : nat) (y : nat) : (term151 x y) = (term151 x y).
Proof. exact (eq_refl (term151 x y)). Qed.
Lemma lem151150 (x : nat) (y : nat) (n : nat) : (term152 x y n) = (term153 x y n).
Proof. exact (MK_COMB (@lem151149 x y) (@lem151147 n)). Qed.
Lemma lem151151 (x : nat) (y : nat) (n : nat) : (term154 x y n) = (term152 x y n).
Proof. exact (@lem17045 (Peano.lt x y) (term155 n)). Qed.
Lemma lem151152 (x : nat) (y : nat) (n : nat) : (term154 x y n) = (term153 x y n).
Proof. exact (TRANS (@lem151151 x y n) (@lem151150 x y n)). Qed.
Lemma lem151153 (x : nat) (y : nat) (n : nat) : (term156 x y n) = (term156 x y n).
Proof. exact (eq_refl (term156 x y n)). Qed.
Lemma lem151154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem151155 (x : nat) (y : nat) (n : nat) : (term157 x y n) = (term158 x y n).
Proof. exact (MK_COMB (@lem151154) (@lem151152 x y n)). Qed.
Lemma lem151156 (x : nat) (y : nat) (n : nat) : (term159 x y n) = (term160 x y n).
Proof. exact (MK_COMB (@lem151155 x y n) (@lem151153 x y n)). Qed.
Lemma lem151157 (x : nat) (y : nat) (n : nat) : (term39 x y n) = (term159 x y n).
Proof. exact (@lem17265 (term95 x y n) (term156 x y n)). Qed.
Lemma lem151162 (x : nat) (y : nat) (n : nat) : (term39 x y n) = (term160 x y n).
Proof. exact (TRANS (@lem151157 x y n) (@lem151156 x y n)). Qed.
Lemma lem151169 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem151179 (y : nat) (n : nat) (h1 : term81 y n) : term81 y n.
Proof. exact (h1). Qed.
Lemma lem151180 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem151181 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem151180 m)). Qed.
Lemma lem151182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151191 : term130 = term130.
Proof. exact (MK_COMB (@lem151182) (@lem151181)). Qed.
Lemma lem151192 (h1 : term130) : term130.
Proof. exact (EQ_MP (@lem151191) (@lem151143 h1)). Qed.
Lemma lem151226 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term160 x y n.
Proof. exact (EQ_MP (@lem151162 x y n) (@lem151140 x y n h1)). Qed.
Lemma lem151232 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem151252 (y : nat) (n : nat) (h1 : term81 y n) : term81 y n.
Proof. exact (h1). Qed.
Lemma lem151261 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem151262 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem151261 m)). Qed.
Lemma lem151263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151264 : term130 = term130.
Proof. exact (MK_COMB (@lem151263) (@lem151262)). Qed.
Lemma lem151265 (h1 : term130) : term130.
Proof. exact (EQ_MP (@lem151264) (@lem151192 h1)). Qed.
Lemma lem151268 (x : nat) (y : nat) (n : nat) (h1 : term153 x y n) : term153 x y n.
Proof. exact (h1). Qed.
Lemma lem151275 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem151294 (x : nat) (y : nat) (h1 : term161 x y) : term161 x y.
Proof. exact (h1). Qed.
Lemma lem151317 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem151321 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem151323 (m : nat) : (term127 m) = (term127 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem151324 : term129 = term129.
Proof. exact (fun_ext (fun m : nat => @lem151323 m)). Qed.
Lemma lem151325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem151327 : term130 = term130.
Proof. exact (MK_COMB (@lem151325) (@lem151324)). Qed.
Lemma lem151328 (h1 : term130) : term130.
Proof. exact (EQ_MP (@lem151327) (@lem151265 h1)). Qed.
Lemma lem151347 (_2985 : nat) (h1 : term130) : term162 _2985.
Proof. exact (@lem151328 h1 _2985). Qed.
Lemma lem151348 (_2985 : nat) : (term162 _2985) = (term127 _2985).
Proof. exact (eq_refl (term162 _2985)). Qed.
Lemma lem151351 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem151355 (y : nat) (n : nat) (h1 : term81 y n) : y = (NUMERAL 0).
Proof. exact (proj1 (@lem151252 y n h1)). Qed.
Lemma lem151359 (x : nat) (y : nat) (h1 : term161 x y) : term161 x y.
Proof. exact (h1). Qed.
Lemma lem151367 (y : nat) (n : nat) (h1 : term81 y n) : term155 n.
Proof. exact (proj2 (@lem151252 y n h1)). Qed.
Lemma lem151369 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem151371 (x : nat) (y : nat) (h1 : Peano.lt x y) : Peano.lt x y.
Proof. exact (h1). Qed.
Lemma lem151375 (y : nat) (n : nat) (h1 : term81 y n) : y = (NUMERAL 0).
Proof. exact (proj1 (@lem151252 y n h1)). Qed.
Lemma lem151394 (x : nat) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem151395 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) : (term164 x y) = (term165 x).
Proof. exact (MK_COMB (@lem151394 x) (@lem151355 y n h1)). Qed.
Lemma lem151396 (x : nat) : (term165 x) = (term126 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem151397 (x : nat) (y : nat) : (term166 x y) = (term166 x y).
Proof. exact (eq_refl (term166 x y)). Qed.
Lemma lem151398 (y : nat) (x : nat) : ((term164 x y) = (term165 x)) = ((term164 x y) = (term126 x)).
Proof. exact (MK_COMB (@lem151397 x y) (@lem151396 x)). Qed.
Lemma lem151399 (x : nat) (y : nat) : (term164 x y) = (Peano.lt x y).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem151400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem151401 (x : nat) (y : nat) : (term166 x y) = (term167 x y).
Proof. exact (MK_COMB (@lem151400) (@lem151399 x y)). Qed.
Lemma lem151402 (x : nat) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem151403 (y : nat) (x : nat) : ((term164 x y) = (term126 x)) = ((Peano.lt x y) = (term126 x)).
Proof. exact (MK_COMB (@lem151401 x y) (@lem151402 x)). Qed.
Lemma lem151404 (y : nat) (x : nat) : ((term164 x y) = (term165 x)) = ((Peano.lt x y) = (term126 x)).
Proof. exact (TRANS (@lem151398 y x) (@lem151403 y x)). Qed.
Lemma lem151405 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) : (Peano.lt x y) = (term126 x).
Proof. exact (EQ_MP (@lem151404 y x) (@lem151395 x y n h1)). Qed.
Lemma lem151435 (x : nat) : (term168 x) = (term168 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem151436 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) : (term169 x y) = (term170 x).
Proof. exact (MK_COMB (@lem151435 x) (@lem151355 y n h1)). Qed.
Lemma lem151437 (x : nat) : (term170 x) = (term127 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem151438 (x : nat) (y : nat) : (term171 x y) = (term171 x y).
Proof. exact (eq_refl (term171 x y)). Qed.
Lemma lem151439 (y : nat) (x : nat) : ((term169 x y) = (term170 x)) = ((term169 x y) = (term127 x)).
Proof. exact (MK_COMB (@lem151438 x y) (@lem151437 x)). Qed.
Lemma lem151440 (x : nat) (y : nat) : (term169 x y) = (term161 x y).
Proof. exact (eq_refl (term169 x y)). Qed.
Lemma lem151441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem151442 (x : nat) (y : nat) : (term171 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem151441) (@lem151440 x y)). Qed.
Lemma lem151443 (x : nat) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem151444 (y : nat) (x : nat) : ((term169 x y) = (term127 x)) = ((term161 x y) = (term127 x)).
Proof. exact (MK_COMB (@lem151442 x y) (@lem151443 x)). Qed.
Lemma lem151445 (y : nat) (x : nat) : ((term169 x y) = (term170 x)) = ((term161 x y) = (term127 x)).
Proof. exact (TRANS (@lem151439 y x) (@lem151444 y x)). Qed.
Lemma lem151446 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) : (term161 x y) = (term127 x).
Proof. exact (EQ_MP (@lem151445 y x) (@lem151436 x y n h1)). Qed.
Lemma lem151447 (x : nat) (y : nat) (n : nat) (h1 : term161 x y) (h2 : term81 y n) : term127 x.
Proof. exact (EQ_MP (@lem151446 x y n h2) (@lem151359 x y h1)). Qed.
Lemma lem151504 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem151505 (n : nat) (h1 : n = (NUMERAL 0)) : (term174 n) = term175.
Proof. exact (MK_COMB (@lem151504) (@lem151369 n h1)). Qed.
Lemma lem151506 : term175 = term58.
Proof. exact (eq_refl term175). Qed.
Lemma lem151507 (n : nat) : (term176 n) = (term176 n).
Proof. exact (eq_refl (term176 n)). Qed.
Lemma lem151508 (n : nat) : ((term174 n) = term175) = ((term174 n) = term58).
Proof. exact (MK_COMB (@lem151507 n) (@lem151506)). Qed.
Lemma lem151509 (n : nat) : (term174 n) = (term155 n).
Proof. exact (eq_refl (term174 n)). Qed.
Lemma lem151510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem151511 (n : nat) : (term176 n) = (term177 n).
Proof. exact (MK_COMB (@lem151510) (@lem151509 n)). Qed.
Lemma lem151512 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem151513 (n : nat) : ((term174 n) = term58) = ((term155 n) = term58).
Proof. exact (MK_COMB (@lem151511 n) (@lem151512)). Qed.
Lemma lem151514 (n : nat) : ((term174 n) = term175) = ((term155 n) = term58).
Proof. exact (TRANS (@lem151508 n) (@lem151513 n)). Qed.
Lemma lem151515 (n : nat) (h1 : n = (NUMERAL 0)) : (term155 n) = term58.
Proof. exact (EQ_MP (@lem151514 n) (@lem151505 n h1)). Qed.
Lemma lem151571 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : term58.
Proof. exact (EQ_MP (@lem151515 n h2) (@lem151367 y n h1)). Qed.
Lemma lem151586 (x : nat) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem151587 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) : (term164 x y) = (term165 x).
Proof. exact (MK_COMB (@lem151586 x) (@lem151375 y n h1)). Qed.
Lemma lem151588 (x : nat) : (term165 x) = (term126 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem151589 (x : nat) (y : nat) : (term166 x y) = (term166 x y).
Proof. exact (eq_refl (term166 x y)). Qed.
Lemma lem151590 (y : nat) (x : nat) : ((term164 x y) = (term165 x)) = ((term164 x y) = (term126 x)).
Proof. exact (MK_COMB (@lem151589 x y) (@lem151588 x)). Qed.
Lemma lem151591 (x : nat) (y : nat) : (term164 x y) = (Peano.lt x y).
Proof. exact (eq_refl (term164 x y)). Qed.
Lemma lem151592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem151593 (x : nat) (y : nat) : (term166 x y) = (term167 x y).
Proof. exact (MK_COMB (@lem151592) (@lem151591 x y)). Qed.
Lemma lem151594 (x : nat) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem151595 (y : nat) (x : nat) : ((term164 x y) = (term126 x)) = ((Peano.lt x y) = (term126 x)).
Proof. exact (MK_COMB (@lem151593 x y) (@lem151594 x)). Qed.
Lemma lem151596 (y : nat) (x : nat) : ((term164 x y) = (term165 x)) = ((Peano.lt x y) = (term126 x)).
Proof. exact (TRANS (@lem151590 y x) (@lem151595 y x)). Qed.
Lemma lem151597 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) : (Peano.lt x y) = (term126 x).
Proof. exact (EQ_MP (@lem151596 y x) (@lem151587 x y n h1)). Qed.
Lemma lem151612 (_2985 : nat) (h1 : term130) : term127 _2985.
Proof. exact (EQ_MP (@lem151348 _2985) (@lem151347 _2985 h1)). Qed.
Lemma lem151670 (n : nat) (x : nat) (y : nat) (h1 : term81 y n) (h2 : Peano.lt x y) : term126 x.
Proof. exact (EQ_MP (@lem151405 x y n h1) (@lem151351 x y h2)). Qed.
Lemma lem151671 (n : nat) (x : nat) (y : nat) (h1 : term81 y n) (h2 : Peano.lt x y) : term178 x.
Proof. exact (fun h0 : term127 x => @lem151670 n x y h1 h2). Qed.
Lemma lem151673 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem151674 (x : nat) : (term178 x) = (term126 x).
Proof. exact (@lem151673 (term126 x)). Qed.
Lemma lem151675 (n : nat) (x : nat) (y : nat) (h1 : term81 y n) (h2 : Peano.lt x y) : term126 x.
Proof. exact (EQ_MP (@lem151674 x) (@lem151671 n x y h1 h2)). Qed.
Lemma lem151678 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem151680 (x : nat) : (term127 x) = (term180 x).
Proof. exact (@lem151678 (term126 x)). Qed.
Lemma lem151683 (x : nat) (y : nat) (n : nat) (h1 : term161 x y) (h2 : term81 y n) : term180 x.
Proof. exact (EQ_MP (@lem151680 x) (@lem151447 x y n h1 h2)). Qed.
Lemma lem151686 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (@lem151683 x y n h1 h2 (@lem151675 n x y h2 h3)). Qed.
Lemma lem151687 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : term181.
Proof. exact (fun h0 : ~ False => @lem151686 n x y h1 h2 h3). Qed.
Lemma lem151689 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem151690 : term181 = False.
Proof. exact (@lem151689 False). Qed.
Lemma lem151722 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem151723 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (@lem151722 (NUMERAL 0)). Qed.
Lemma lem151724 : term182.
Proof. exact (fun h0 : term58 => @lem151723). Qed.
Lemma lem151726 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem151727 : term182 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem151726 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem151728 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem151727) (@lem151724)). Qed.
Lemma lem151731 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem151733 : term58 = term183.
Proof. exact (@lem151731 ((NUMERAL 0) = (NUMERAL 0))). Qed.
Lemma lem151736 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : term183.
Proof. exact (EQ_MP (@lem151733) (@lem151571 y n h1 h2)). Qed.
Lemma lem151739 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (@lem151736 y n h1 h2 (@lem151728)). Qed.
Lemma lem151740 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : term181.
Proof. exact (fun h0 : ~ False => @lem151739 y n h1 h2). Qed.
Lemma lem151742 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem151743 : term181 = False.
Proof. exact (@lem151742 False). Qed.
Lemma lem151790 (n : nat) (x : nat) (y : nat) (h1 : term81 y n) (h2 : Peano.lt x y) : term126 x.
Proof. exact (EQ_MP (@lem151597 x y n h1) (@lem151371 x y h2)). Qed.
Lemma lem151791 (n : nat) (x : nat) (y : nat) (h1 : term81 y n) (h2 : Peano.lt x y) : term178 x.
Proof. exact (fun h0 : term127 x => @lem151790 n x y h1 h2). Qed.
Lemma lem151793 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem151794 (x : nat) : (term178 x) = (term126 x).
Proof. exact (@lem151793 (term126 x)). Qed.
Lemma lem151795 (n : nat) (x : nat) (y : nat) (h1 : term81 y n) (h2 : Peano.lt x y) : term126 x.
Proof. exact (EQ_MP (@lem151794 x) (@lem151791 n x y h1 h2)). Qed.
Lemma lem151798 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem151800 (_2985 : nat) : (term127 _2985) = (term180 _2985).
Proof. exact (@lem151798 (term126 _2985)). Qed.
Lemma lem151803 (_2985 : nat) (h1 : term130) : term180 _2985.
Proof. exact (EQ_MP (@lem151800 _2985) (@lem151612 _2985 h1)). Qed.
Lemma lem151804 (x : nat) (h1 : term130) : term180 x.
Proof. exact (@lem151803 x h1). Qed.
Lemma lem151807 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (@lem151804 x h1 (@lem151795 n x y h2 h3)). Qed.
Lemma lem151808 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : term181.
Proof. exact (fun h0 : ~ False => @lem151807 n x y h1 h2 h3). Qed.
Lemma lem151810 (p : Prop) : (term179 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem151811 : term181 = False.
Proof. exact (@lem151810 False). Qed.
Lemma lem151813 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151811) (@lem151808 n x y h1 h2 h3)). Qed.
Lemma lem151815 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem151743) (@lem151740 y n h1 h2)). Qed.
Lemma lem151816 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151690) (@lem151687 n x y h1 h2 h3)). Qed.
Lemma lem151817 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt x y => @lem151813 n x y h1 h2 h3) (fun h4 : False => @lem151371 x y h3)). Qed.
Lemma lem151818 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151817 n x y h1 h2 h3) (@lem151371 x y h3)). Qed.
Lemma lem151819 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem151815 y n h1 h2) (fun h3 : False => @lem151369 n h2)). Qed.
Lemma lem151820 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem151819 y n h1 h2) (@lem151369 n h2)). Qed.
Lemma lem151821 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : (term161 x y) = False.
Proof. exact (prop_ext (fun h4 : term161 x y => @lem151816 n x y h1 h2 h3) (fun h4 : False => @lem151359 x y h1)). Qed.
Lemma lem151822 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151821 n x y h1 h2 h3) (@lem151359 x y h1)). Qed.
Lemma lem151823 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt x y => @lem151822 n x y h1 h2 h3) (fun h4 : False => @lem151351 x y h3)). Qed.
Lemma lem151824 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151823 n x y h1 h2 h3) (@lem151351 x y h3)). Qed.
Lemma lem151825 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt x y => @lem151818 n x y h1 h2 h3) (fun h4 : False => @lem151321 x y h3)). Qed.
Lemma lem151826 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151825 n x y h1 h2 h3) (@lem151321 x y h3)). Qed.
Lemma lem151827 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem151820 y n h1 h2) (fun h3 : False => @lem151317 n h2)). Qed.
Lemma lem151828 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem151827 y n h1 h2) (@lem151317 n h2)). Qed.
Lemma lem151829 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : (term161 x y) = False.
Proof. exact (prop_ext (fun h4 : term161 x y => @lem151824 n x y h1 h2 h3) (fun h4 : False => @lem151294 x y h1)). Qed.
Lemma lem151830 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151829 n x y h1 h2 h3) (@lem151294 x y h1)). Qed.
Lemma lem151831 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt x y => @lem151830 n x y h1 h2 h3) (fun h4 : False => @lem151275 x y h3)). Qed.
Lemma lem151832 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151831 n x y h1 h2 h3) (@lem151275 x y h3)). Qed.
Lemma lem151833 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : term130 = False.
Proof. exact (prop_ext (fun h4 : term130 => @lem151826 n x y h1 h2 h3) (fun h4 : False => @lem151328 h1)). Qed.
Lemma lem151834 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151833 n x y h1 h2 h3) (@lem151328 h1)). Qed.
Lemma lem151835 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt x y => @lem151834 n x y h1 h2 h3) (fun h4 : False => @lem151321 x y h3)). Qed.
Lemma lem151836 (n : nat) (x : nat) (y : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151835 n x y h1 h2 h3) (@lem151321 x y h3)). Qed.
Lemma lem151837 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h3 : n = (NUMERAL 0) => @lem151828 y n h1 h2) (fun h3 : False => @lem151317 n h2)). Qed.
Lemma lem151838 (y : nat) (n : nat) (h1 : term81 y n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem151837 y n h1 h2) (@lem151317 n h2)). Qed.
Lemma lem151839 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : (term161 x y) = False.
Proof. exact (prop_ext (fun h4 : term161 x y => @lem151832 n x y h1 h2 h3) (fun h4 : False => @lem151294 x y h1)). Qed.
Lemma lem151840 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151839 n x y h1 h2 h3) (@lem151294 x y h1)). Qed.
Lemma lem151841 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt x y => @lem151840 n x y h1 h2 h3) (fun h4 : False => @lem151275 x y h3)). Qed.
Lemma lem151842 (n : nat) (x : nat) (y : nat) (h1 : term161 x y) (h2 : term81 y n) (h3 : Peano.lt x y) : False.
Proof. exact (EQ_MP (@lem151841 n x y h1 h2 h3) (@lem151275 x y h3)). Qed.
Lemma lem151843 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term153 x y n) : False.
Proof. exact (or_elim (@lem151268 x y n h3) (fun h0 : term161 x y => @lem151842 n x y h0 h1 h2) (fun h0 : n = (NUMERAL 0) => @lem151838 y n h1 h0)). Qed.
Lemma lem151844 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (or_elim (@lem151226 x y n h4) (fun h0 : term153 x y n => @lem151843 x y n h2 h3 h0) (fun h0 : term156 x y n => @lem151836 n x y h1 h2 h3)). Qed.
Lemma lem151845 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : term130 = False.
Proof. exact (prop_ext (fun h5 : term130 => @lem151844 x y n h1 h2 h3 h4) (fun h5 : False => @lem151265 h1)). Qed.
Lemma lem151846 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151845 x y n h1 h2 h3 h4) (@lem151265 h1)). Qed.
Lemma lem151847 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : (term81 y n) = False.
Proof. exact (prop_ext (fun h5 : term81 y n => @lem151846 x y n h1 h2 h3 h4) (fun h5 : False => @lem151252 y n h2)). Qed.
Lemma lem151848 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151847 x y n h1 h2 h3 h4) (@lem151252 y n h2)). Qed.
Lemma lem151849 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt x y => @lem151848 x y n h1 h2 h3 h4) (fun h5 : False => @lem151232 x y h3)). Qed.
Lemma lem151850 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151849 x y n h1 h2 h3 h4) (@lem151232 x y h3)). Qed.
Lemma lem151851 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : term130 = False.
Proof. exact (prop_ext (fun h5 : term130 => @lem151850 x y n h1 h2 h3 h4) (fun h5 : False => @lem151192 h1)). Qed.
Lemma lem151852 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151851 x y n h1 h2 h3 h4) (@lem151192 h1)). Qed.
Lemma lem151853 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : (term81 y n) = False.
Proof. exact (prop_ext (fun h5 : term81 y n => @lem151852 x y n h1 h2 h3 h4) (fun h5 : False => @lem151179 y n h2)). Qed.
Lemma lem151854 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151853 x y n h1 h2 h3 h4) (@lem151179 y n h2)). Qed.
Lemma lem151855 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : (Peano.lt x y) = False.
Proof. exact (prop_ext (fun h5 : Peano.lt x y => @lem151854 x y n h1 h2 h3 h4) (fun h5 : False => @lem151169 x y h3)). Qed.
Lemma lem151856 (x : nat) (y : nat) (n : nat) (h1 : term130) (h2 : term81 y n) (h3 : Peano.lt x y) (h4 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151855 x y n h1 h2 h3 h4) (@lem151169 x y h3)). Qed.
Lemma lem151857 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term39 x y n) : term184.
Proof. exact (fun h0 : term130 => @lem151856 x y n h0 h1 h2 h3). Qed.
Lemma lem151858 : term184 = term131.
Proof. exact (@lem69 term130). Qed.
Lemma lem151859 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term39 x y n) : term131.
Proof. exact (EQ_MP (@lem151858) (@lem151857 x y n h1 h2 h3)). Qed.
Lemma lem151860 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term134 y n.
Proof. exact (fun h0 : term81 y n => @lem151859 x y n h0 h1 h2). Qed.
Lemma lem151861 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term136 x y n.
Proof. exact (fun h0 : Peano.lt x y => @lem151860 x y n h0 h1). Qed.
Lemma lem151862 (x : nat) (y : nat) (n : nat) : term137 x y n.
Proof. exact (fun h0 : term39 x y n => @lem151861 x y n h0). Qed.
Lemma lem151867 (y : nat) (n : nat) : term141 y n.
Proof. exact (fun x : nat => @lem151862 x y n). Qed.
Lemma lem151872 (n : nat) : term145 n.
Proof. exact (fun y : nat => @lem151867 y n). Qed.
Lemma lem151877 : term149.
Proof. exact (fun n : nat => @lem151872 n). Qed.
Lemma lem151878 : term148.
Proof. exact (EQ_MP (@lem151139) (@lem151877)). Qed.
Lemma lem151879 (n : nat) : term185 n.
Proof. exact (@lem151878 n). Qed.
Lemma lem151880 (n : nat) : (term185 n) = (term144 n).
Proof. exact (eq_refl (term185 n)). Qed.
Lemma lem151881 (n : nat) : term144 n.
Proof. exact (EQ_MP (@lem151880 n) (@lem151879 n)). Qed.
Lemma lem151882 (n : nat) (y : nat) : term186 n y.
Proof. exact (@lem151881 n y). Qed.
Lemma lem151883 (y : nat) (n : nat) : (term186 n y) = (term140 y n).
Proof. exact (eq_refl (term186 n y)). Qed.
Lemma lem151884 (y : nat) (n : nat) : term140 y n.
Proof. exact (EQ_MP (@lem151883 y n) (@lem151882 n y)). Qed.
Lemma lem151885 (y : nat) (n : nat) (x : nat) : term187 y n x.
Proof. exact (@lem151884 y n x). Qed.
Lemma lem151886 (x : nat) (y : nat) (n : nat) : (term187 y n x) = (term120 x y n).
Proof. exact (eq_refl (term187 y n x)). Qed.
Lemma lem151887 (x : nat) (y : nat) (n : nat) : term120 x y n.
Proof. exact (EQ_MP (@lem151886 x y n) (@lem151885 y n x)). Qed.
Lemma lem151889 (x : nat) (y : nat) (n : nat) : term120 x y n.
Proof. exact (@lem150973 x y n (@lem151887 x y n)). Qed.
Lemma lem151890 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term135 x y n.
Proof. exact (@lem151889 x y n (@lem150735 x y n h1)). Qed.
Lemma lem151891 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term133 y n.
Proof. exact (@lem151890 x y n h2 (@lem150805 x y h1)). Qed.
Lemma lem151892 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term39 x y n) : term124.
Proof. exact (@lem151891 x y n h2 h3 (@lem150958 y n h1)). Qed.
Lemma lem151893 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term39 x y n) : False.
Proof. exact (@lem151892 x y n h1 h2 h3 (@lem150646)). Qed.
Lemma lem151894 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term39 x y n) : (term81 y n) = False.
Proof. exact (prop_ext (fun h4 : term81 y n => @lem151893 x y n h1 h2 h3) (fun h4 : False => @lem150958 y n h1)). Qed.
Lemma lem151895 (x : nat) (y : nat) (n : nat) (h1 : term81 y n) (h2 : Peano.lt x y) (h3 : term39 x y n) : False.
Proof. exact (EQ_MP (@lem151894 x y n h1 h2 h3) (@lem150958 y n h1)). Qed.
Lemma lem151896 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term188 y n.
Proof. exact (fun h0 : term81 y n => @lem151895 x y n h0 h1 h2). Qed.
Lemma lem151897 (y : nat) (n : nat) : (term188 y n) = (term117 y n).
Proof. exact (@lem69 (term81 y n)). Qed.
Lemma lem151898 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term117 y n.
Proof. exact (EQ_MP (@lem151897 y n) (@lem151896 x y n h1 h2)). Qed.
Lemma lem151899 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term119 x y n.
Proof. exact (EQ_MP (@lem150957 n x y h1) (@lem151898 x y n h1 h2)). Qed.
Lemma lem151900 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term189 x y n.
Proof. exact (ex_intro (term190 x y n) (term191 x y n) (@lem151899 x y n h1 h2)). Qed.
Lemma lem151901 (x : nat) (y : nat) (n : nat) (h1 : Peano.lt x y) (h2 : term39 x y n) : term75 x y n.
Proof. exact (@lem150808 x y n (@lem151900 x y n h1 h2)). Qed.
Lemma lem151902 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term76 x y n.
Proof. exact (fun h0 : Peano.lt x y => @lem151901 x y n h0 h1). Qed.
Lemma lem151903 (x : nat) (y : nat) (n : nat) (h1 : term39 x y n) : term43 x y n.
Proof. exact (EQ_MP (@lem150804 x y n) (@lem151902 x y n h1)). Qed.
Lemma lem151904 (x : nat) (y : nat) (n : nat) : term45 x y n.
Proof. exact (fun h0 : term39 x y n => @lem151903 x y n h0). Qed.
Lemma lem151909 (x : nat) (y : nat) : term49 x y.
Proof. exact (fun n : nat => @lem151904 x y n). Qed.
Lemma lem151910 (x : nat) (y : nat) : term51 x y.
Proof. exact (conj (@lem150772 x y) (@lem151909 x y)). Qed.
Lemma lem151911 (x : nat) (y : nat) : term56 x y.
Proof. exact (@lem150734 x y (@lem151910 x y)). Qed.
Lemma lem151916 (x : nat) : term192 x.
Proof. exact (fun y : nat => @lem151911 x y). Qed.
Lemma lem151921 : term193.
Proof. exact (fun x : nat => @lem151916 x). Qed.
