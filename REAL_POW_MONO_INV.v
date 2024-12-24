Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_MONO_INV_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_INV_1_LE_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_LE_INV2_spec.
Require Import REAL_LT_INV_EQ_spec.
Require Import REAL_LT_LE_spec.
Require Import REAL_POS_spec.
Require Import REAL_POW_INV_spec.
Require Import REAL_POW_LT_spec.
Require Import REAL_POW_MONO_spec.
Require Import REAL_POW_ZERO_spec.
Require Import thm0_spec.
Require Import thm1339240_spec.
Require Import thm13473_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem1648696 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1648697 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1648696 h1 x). Qed.
Lemma lem1648698 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1648699 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1648698 x) (@lem1648697 x h1)). Qed.
Lemma lem1648700 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1648701 (x : real) (h1 : term0) (h2 : term3 x) : term4 x.
Proof. exact (@lem1648699 x h1 (@lem1648700 x h2)). Qed.
Lemma lem1648702 (x : real) (h1 : term3 x) : term5 x.
Proof. exact (fun h0 : term0 => @lem1648701 x h0 h1). Qed.
Lemma lem1648703 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1648704 (x : real) (h1 : term0) (h2 : term3 x) : term4 x.
Proof. exact (@lem1648702 x h2 (@lem1648703 h1)). Qed.
Lemma lem1648705 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun h0 : term3 x => @lem1648704 x h1 h0). Qed.
Lemma lem1648706 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1648705 x h1). Qed.
Lemma lem1648707 : term6.
Proof. exact (fun h0 : term0 => @lem1648706 h0). Qed.
Lemma lem1648708 : term0.
Proof. exact (@lem1648707 (@lem1633036)). Qed.
Lemma lem1648709 (x : real) : term1 x.
Proof. exact (@lem1648708 x). Qed.
Lemma lem1648710 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1648712 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1648713 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem1648712 h1 m). Qed.
Lemma lem1648714 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1648715 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem1648714 m) (@lem1648713 m h1)). Qed.
Lemma lem1648716 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem1648715 m h1 n). Qed.
Lemma lem1648717 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1648718 (m : nat) (n : nat) (h1 : term7) : term11 m n.
Proof. exact (EQ_MP (@lem1648717 m n) (@lem1648716 m n h1)). Qed.
Lemma lem1648719 (m : nat) (n : nat) (x : real) (h1 : term7) : term12 m n x.
Proof. exact (@lem1648718 m n h1 x). Qed.
Lemma lem1648720 (m : nat) (x : real) (n : nat) : (term12 m n x) = (term13 m x n).
Proof. exact (eq_refl (term12 m n x)). Qed.
Lemma lem1648721 (m : nat) (x : real) (n : nat) (h1 : term7) : term13 m x n.
Proof. exact (EQ_MP (@lem1648720 m x n) (@lem1648719 m n x h1)). Qed.
Lemma lem1648722 (x : real) (m : nat) (n : nat) (h1 : term14 x m n) : term14 x m n.
Proof. exact (h1). Qed.
Lemma lem1648723 (x : real) (m : nat) (n : nat) (h1 : term7) (h2 : term14 x m n) : term15 m x n.
Proof. exact (@lem1648721 m x n h1 (@lem1648722 x m n h2)). Qed.
Lemma lem1648724 (x : real) (m : nat) (n : nat) (h1 : term14 x m n) : term16 m x n.
Proof. exact (fun h0 : term7 => @lem1648723 x m n h0 h1). Qed.
Lemma lem1648725 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1648726 (x : real) (m : nat) (n : nat) (h1 : term7) (h2 : term14 x m n) : term15 m x n.
Proof. exact (@lem1648724 x m n h2 (@lem1648725 h1)). Qed.
Lemma lem1648727 (m : nat) (x : real) (n : nat) (h1 : term7) : term13 m x n.
Proof. exact (fun h0 : term14 x m n => @lem1648726 x m n h1 h0). Qed.
Lemma lem1648728 (m : nat) (x : real) (h1 : term7) : term17 m x.
Proof. exact (fun n : nat => @lem1648727 m x n h1). Qed.
Lemma lem1648729 (m : nat) (h1 : term7) : term18 m.
Proof. exact (fun x : real => @lem1648728 m x h1). Qed.
Lemma lem1648730 (h1 : term7) : term19.
Proof. exact (fun m : nat => @lem1648729 m h1). Qed.
Lemma lem1648731 : term20.
Proof. exact (fun h0 : term7 => @lem1648730 h0). Qed.
Lemma lem1648732 : term19.
Proof. exact (@lem1648731 (@lem1637789)). Qed.
Lemma lem1648733 (m : nat) : term21 m.
Proof. exact (@lem1648732 m). Qed.
Lemma lem1648734 (m : nat) : (term21 m) = (term18 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1648735 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1648734 m) (@lem1648733 m)). Qed.
Lemma lem1648736 (m : nat) (x : real) : term22 m x.
Proof. exact (@lem1648735 m x). Qed.
Lemma lem1648737 (m : nat) (x : real) : (term22 m x) = (term17 m x).
Proof. exact (eq_refl (term22 m x)). Qed.
Lemma lem1648738 (m : nat) (x : real) : term17 m x.
Proof. exact (EQ_MP (@lem1648737 m x) (@lem1648736 m x)). Qed.
Lemma lem1648739 (m : nat) (x : real) (n : nat) : term23 m x n.
Proof. exact (@lem1648738 m x n). Qed.
Lemma lem1648740 (m : nat) (x : real) (n : nat) : (term23 m x n) = (term13 m x n).
Proof. exact (eq_refl (term23 m x n)). Qed.
Lemma lem1648742 (x : real) : term24 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem1648743 (x : real) : (term24 x) = ((term25 x) = (term26 x)).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1648745 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1648746 (x : real) (h1 : term27) : term28 x.
Proof. exact (@lem1648745 h1 x). Qed.
Lemma lem1648747 (x : real) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1648748 (x : real) (h1 : term27) : term29 x.
Proof. exact (EQ_MP (@lem1648747 x) (@lem1648746 x h1)). Qed.
Lemma lem1648749 (x : real) (n : nat) (h1 : term27) : term30 x n.
Proof. exact (@lem1648748 x h1 n). Qed.
Lemma lem1648750 (x : real) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (eq_refl (term30 x n)). Qed.
Lemma lem1648751 (x : real) (n : nat) (h1 : term27) : term31 x n.
Proof. exact (EQ_MP (@lem1648750 x n) (@lem1648749 x n h1)). Qed.
Lemma lem1648752 (x : real) (h1 : term26 x) : term26 x.
Proof. exact (h1). Qed.
Lemma lem1648753 (n : nat) (x : real) (h1 : term27) (h2 : term26 x) : term32 x n.
Proof. exact (@lem1648751 x n h1 (@lem1648752 x h2)). Qed.
Lemma lem1648754 (n : nat) (x : real) (h1 : term26 x) : term33 x n.
Proof. exact (fun h0 : term27 => @lem1648753 n x h0 h1). Qed.
Lemma lem1648755 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1648756 (n : nat) (x : real) (h1 : term27) (h2 : term26 x) : term32 x n.
Proof. exact (@lem1648754 n x h2 (@lem1648755 h1)). Qed.
Lemma lem1648757 (x : real) (n : nat) (h1 : term27) : term31 x n.
Proof. exact (fun h0 : term26 x => @lem1648756 n x h1 h0). Qed.
Lemma lem1648758 (x : real) (h1 : term27) : term29 x.
Proof. exact (fun n : nat => @lem1648757 x n h1). Qed.
Lemma lem1648759 (h1 : term27) : term27.
Proof. exact (fun x : real => @lem1648758 x h1). Qed.
Lemma lem1648760 : term34.
Proof. exact (fun h0 : term27 => @lem1648759 h0). Qed.
Lemma lem1648761 : term27.
Proof. exact (@lem1648760 (@lem1582551)). Qed.
Lemma lem1648762 (x : real) : term28 x.
Proof. exact (@lem1648761 x). Qed.
Lemma lem1648763 (x : real) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1648764 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1648763 x) (@lem1648762 x)). Qed.
Lemma lem1648765 (x : real) (n : nat) : term30 x n.
Proof. exact (@lem1648764 x n). Qed.
Lemma lem1648766 (x : real) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (eq_refl (term30 x n)). Qed.
Lemma lem1648770 (x : real) (n : nat) (h1 : (term35 x n) = (term36 x n)) : (term35 x n) = (term36 x n).
Proof. exact (h1). Qed.
Lemma lem1648771 (x : real) (n : nat) (h1 : (term35 x n) = (term36 x n)) : (term36 x n) = (term35 x n).
Proof. exact (SYM (@lem1648770 x n h1)). Qed.
Lemma lem1648772 (x : real) (n : nat) (h1 : (term36 x n) = (term35 x n)) : (term36 x n) = (term35 x n).
Proof. exact (h1). Qed.
Lemma lem1648773 (x : real) (n : nat) (h1 : (term36 x n) = (term35 x n)) : (term35 x n) = (term36 x n).
Proof. exact (SYM (@lem1648772 x n h1)). Qed.
Lemma lem1648774 (x : real) (n : nat) : ((term35 x n) = (term36 x n)) = ((term36 x n) = (term35 x n)).
Proof. exact (prop_ext (fun h1 : (term35 x n) = (term36 x n) => @lem1648771 x n h1) (fun h1 : (term36 x n) = (term35 x n) => @lem1648773 x n h1)). Qed.
Lemma lem1648775 (x : real) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun n : nat => @lem1648774 x n)). Qed.
Lemma lem1648776 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1648777 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1648776) (@lem1648775 x)). Qed.
Lemma lem1648778 : term41 = term42.
Proof. exact (fun_ext (fun x : real => @lem1648777 x)). Qed.
Lemma lem1648779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1648780 : term43 = term44.
Proof. exact (MK_COMB (@lem1648779) (@lem1648778)). Qed.
Lemma lem1648781 : term44.
Proof. exact (EQ_MP (@lem1648780) (@lem1595679)). Qed.
Lemma lem1648782 (x : real) : term45 x.
Proof. exact (@lem1648781 x). Qed.
Lemma lem1648783 (x : real) : (term45 x) = (term40 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1648784 (x : real) : term40 x.
Proof. exact (EQ_MP (@lem1648783 x) (@lem1648782 x)). Qed.
Lemma lem1648785 (x : real) (n : nat) : term46 x n.
Proof. exact (@lem1648784 x n). Qed.
Lemma lem1648786 (x : real) (n : nat) : (term46 x n) = ((term36 x n) = (term35 x n)).
Proof. exact (eq_refl (term46 x n)). Qed.
Lemma lem1648788 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1648789 (x : real) (h1 : term47) : term48 x.
Proof. exact (@lem1648788 h1 x). Qed.
Lemma lem1648790 (x : real) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1648791 (x : real) (h1 : term47) : term49 x.
Proof. exact (EQ_MP (@lem1648790 x) (@lem1648789 x h1)). Qed.
Lemma lem1648792 (x : real) (y : real) (h1 : term47) : term50 x y.
Proof. exact (@lem1648791 x h1 y). Qed.
Lemma lem1648793 (y : real) (x : real) : (term50 x y) = (term51 y x).
Proof. exact (eq_refl (term50 x y)). Qed.
Lemma lem1648794 (y : real) (x : real) (h1 : term47) : term51 y x.
Proof. exact (EQ_MP (@lem1648793 y x) (@lem1648792 x y h1)). Qed.
Lemma lem1648795 (x : real) (y : real) (h1 : term52 x y) : term52 x y.
Proof. exact (h1). Qed.
Lemma lem1648796 (x : real) (y : real) (h1 : term47) (h2 : term52 x y) : term53 y x.
Proof. exact (@lem1648794 y x h1 (@lem1648795 x y h2)). Qed.
Lemma lem1648797 (x : real) (y : real) (h1 : term52 x y) : term54 y x.
Proof. exact (fun h0 : term47 => @lem1648796 x y h0 h1). Qed.
Lemma lem1648798 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1648799 (x : real) (y : real) (h1 : term47) (h2 : term52 x y) : term53 y x.
Proof. exact (@lem1648797 x y h2 (@lem1648798 h1)). Qed.
Lemma lem1648800 (y : real) (x : real) (h1 : term47) : term51 y x.
Proof. exact (fun h0 : term52 x y => @lem1648799 x y h1 h0). Qed.
Lemma lem1648801 (y : real) (h1 : term47) : term55 y.
Proof. exact (fun x : real => @lem1648800 y x h1). Qed.
Lemma lem1648802 (h1 : term47) : term56.
Proof. exact (fun y : real => @lem1648801 y h1). Qed.
Lemma lem1648803 : term57.
Proof. exact (fun h0 : term47 => @lem1648802 h0). Qed.
Lemma lem1648804 : term56.
Proof. exact (@lem1648803 (@lem1632440)). Qed.
Lemma lem1648805 (y : real) : term58 y.
Proof. exact (@lem1648804 y). Qed.
Lemma lem1648806 (y : real) : (term58 y) = (term55 y).
Proof. exact (eq_refl (term58 y)). Qed.
Lemma lem1648807 (y : real) : term55 y.
Proof. exact (EQ_MP (@lem1648806 y) (@lem1648805 y)). Qed.
Lemma lem1648808 (y : real) (x : real) : term59 y x.
Proof. exact (@lem1648807 y x). Qed.
Lemma lem1648809 (y : real) (x : real) : (term59 y x) = (term51 y x).
Proof. exact (eq_refl (term59 y x)). Qed.
Lemma lem1648812 (x : real) (h1 : (term60 x) = x) : (term60 x) = x.
Proof. exact (h1). Qed.
Lemma lem1648813 (x : real) (h1 : (term60 x) = x) : x = (term60 x).
Proof. exact (SYM (@lem1648812 x h1)). Qed.
Lemma lem1648814 (x : real) (h1 : x = (term60 x)) : x = (term60 x).
Proof. exact (h1). Qed.
Lemma lem1648815 (x : real) (h1 : x = (term60 x)) : (term60 x) = x.
Proof. exact (SYM (@lem1648814 x h1)). Qed.
Lemma lem1648816 (x : real) : ((term60 x) = x) = (x = (term60 x)).
Proof. exact (prop_ext (fun h1 : (term60 x) = x => @lem1648813 x h1) (fun h1 : x = (term60 x) => @lem1648815 x h1)). Qed.
Lemma lem1648817 : term61 = term62.
Proof. exact (fun_ext (fun x : real => @lem1648816 x)). Qed.
Lemma lem1648818 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1648819 : term63 = term64.
Proof. exact (MK_COMB (@lem1648818) (@lem1648817)). Qed.
Lemma lem1648820 : term64.
Proof. exact (EQ_MP (@lem1648819) (@lem1587920)). Qed.
Lemma lem1648821 (x : real) : term65 x.
Proof. exact (@lem1648820 x). Qed.
Lemma lem1648822 (x : real) : (term65 x) = (x = (term60 x)).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1648824 (x : real) : term66 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1648825 (x : real) : (term66 x) = (real_le x x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1648826 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1648825 x) (@lem1648824 x)). Qed.
Lemma lem1648827 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1648829 (n : nat) : term67 n.
Proof. exact (@lem1384343 n). Qed.
Lemma lem1648830 (n : nat) : (term67 n) = (term68 n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem1648831 (n : nat) : term68 n.
Proof. exact (EQ_MP (@lem1648830 n) (@lem1648829 n)). Qed.
Lemma lem1648832 (n : nat) : (term68 n) = ((term68 n) = True).
Proof. exact (@lem7 (term68 n)). Qed.
Lemma lem1648834 (x : real) : term69 x.
Proof. exact (@lem9784 (x = term70)). Qed.
Lemma lem1648835 (x : real) : (term69 x) = (term71 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem1648836 (x : real) : term71 x.
Proof. exact (EQ_MP (@lem1648835 x) (@lem1648834 x)). Qed.
Lemma lem1648838 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1648839 (x : real) (n : nat) (m : nat) (h1 : term73 x n m) : term73 x n m.
Proof. exact (h1). Qed.
Lemma lem1648840 (x : real) (n : nat) (m : nat) (h1 : term74 x n m) : term74 x n m.
Proof. exact (h1). Qed.
Lemma lem1648841 (x : real) (h1 : term75 x) : term75 x.
Proof. exact (h1). Qed.
Lemma lem1648842 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem1648843 (x : real) (h1 : term76 x) : term76 x.
Proof. exact (h1). Qed.
Lemma lem1648844 (n : nat) : term77 n.
Proof. exact (@lem1648695 n). Qed.
Lemma lem1648845 (n : nat) : (term77 n) = ((term78 n) = (term79 n)).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem1648854 (x : real) (h1 : x = term70) : x = term70.
Proof. exact (h1). Qed.
Lemma lem1648855 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1648856 (x : real) (h1 : x = term70) : (real_pow x) = term80.
Proof. exact (MK_COMB (@lem1648855) (@lem1648854 x h1)). Qed.
Lemma lem1648857 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1648858 (m : nat) (x : real) (h1 : x = term70) : (real_pow x m) = (term78 m).
Proof. exact (MK_COMB (@lem1648856 x h1) (@lem1648857 m)). Qed.
Lemma lem1648860 (n : nat) : (term78 n) = (term79 n).
Proof. exact (EQ_MP (@lem1648845 n) (@lem1648844 n)). Qed.
Lemma lem1648861 (m : nat) : (term78 m) = (term79 m).
Proof. exact (@lem1648860 m). Qed.
Lemma lem1648866 (m : nat) (x : real) (h1 : x = term70) : (real_pow x m) = (term79 m).
Proof. exact (TRANS (@lem1648858 m x h1) (@lem1648861 m)). Qed.
Lemma lem1648867 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1648868 (m : nat) (x : real) (h1 : x = term70) : (term81 x m) = (term82 m).
Proof. exact (MK_COMB (@lem1648867) (@lem1648866 m x h1)). Qed.
Lemma lem1648870 (x : real) (h1 : x = term70) : x = term70.
Proof. exact (h1). Qed.
Lemma lem1648871 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1648872 (x : real) (h1 : x = term70) : (real_pow x) = term80.
Proof. exact (MK_COMB (@lem1648871) (@lem1648870 x h1)). Qed.
Lemma lem1648873 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1648874 (n : nat) (x : real) (h1 : x = term70) : (real_pow x n) = (term78 n).
Proof. exact (MK_COMB (@lem1648872 x h1) (@lem1648873 n)). Qed.
Lemma lem1648876 (n : nat) : (term78 n) = (term79 n).
Proof. exact (EQ_MP (@lem1648845 n) (@lem1648844 n)). Qed.
Lemma lem1648881 (n : nat) (x : real) (h1 : x = term70) : (real_pow x n) = (term79 n).
Proof. exact (TRANS (@lem1648874 n x h1) (@lem1648876 n)). Qed.
Lemma lem1648882 (m : nat) (n : nat) (x : real) (h1 : x = term70) : (term15 m x n) = (term83 m n).
Proof. exact (MK_COMB (@lem1648868 m x h1) (@lem1648881 n x h1)). Qed.
Lemma lem1648883 (m : nat) (n : nat) (x : real) (h1 : x = term70) : (term83 m n) = (term15 m x n).
Proof. exact (SYM (@lem1648882 m n x h1)). Qed.
Lemma lem1648884 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term84 _476 _475 _474 _477) = (term85 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1648885 (_474 : real) (_475 : Prop) (n : nat) (_477 : real) : (term86 n _475 _474 _477) = (term87 _474 _475 n _477).
Proof. exact (@lem1648884 _474 _475 (term88 n) _477). Qed.
Lemma lem1648886 (m : nat) (n : nat) : (term89 n m) = (term90 m n).
Proof. exact (@lem1648885 term91 (m = (NUMERAL 0)) n term70). Qed.
Lemma lem1648887 (n : nat) : (term92 n) = (term93 n).
Proof. exact (eq_refl (term92 n)). Qed.
Lemma lem1648888 (m : nat) : (term94 m) = (term94 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem1648889 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem1648888 m) (@lem1648887 n)). Qed.
Lemma lem1648890 (n : nat) : (term97 n) = (term98 n).
Proof. exact (eq_refl (term97 n)). Qed.
Lemma lem1648891 (m : nat) : (term99 m) = (term99 m).
Proof. exact (eq_refl (term99 m)). Qed.
Lemma lem1648892 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (MK_COMB (@lem1648891 m) (@lem1648890 n)). Qed.
Lemma lem1648893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1648894 (m : nat) (n : nat) : (term102 m n) = (term103 m n).
Proof. exact (MK_COMB (@lem1648893) (@lem1648892 m n)). Qed.
Lemma lem1648895 (m : nat) (n : nat) : (term90 m n) = (term104 m n).
Proof. exact (MK_COMB (@lem1648894 m n) (@lem1648889 m n)). Qed.
Lemma lem1648896 (m : nat) (n : nat) : (term89 n m) = (term83 m n).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem1648897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1648898 (m : nat) (n : nat) : (term105 n m) = (term106 m n).
Proof. exact (MK_COMB (@lem1648897) (@lem1648896 m n)). Qed.
Lemma lem1648899 (m : nat) (n : nat) : ((term89 n m) = (term90 m n)) = ((term83 m n) = (term104 m n)).
Proof. exact (MK_COMB (@lem1648898 m n) (@lem1648895 m n)). Qed.
Lemma lem1648900 (m : nat) (n : nat) : (term83 m n) = (term104 m n).
Proof. exact (EQ_MP (@lem1648899 m n) (@lem1648886 m n)). Qed.
Lemma lem1648901 (m : nat) (n : nat) : (term104 m n) = (term83 m n).
Proof. exact (SYM (@lem1648900 m n)). Qed.
Lemma lem1648902 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1648952 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term84 _476 _475 _474 _477) = (term85 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1648953 (_474 : real) (_475 : Prop) (_477 : real) : (term107 _475 _474 _477) = (term108 _474 _475 _477).
Proof. exact (@lem1648952 _474 _475 term109 _477). Qed.
Lemma lem1648954 (n : nat) : (term110 n) = (term111 n).
Proof. exact (@lem1648953 term91 (n = (NUMERAL 0)) term70). Qed.
Lemma lem1648955 : term112 = term113.
Proof. exact (eq_refl term112). Qed.
Lemma lem1648956 (n : nat) : (term94 n) = (term94 n).
Proof. exact (eq_refl (term94 n)). Qed.
Lemma lem1648957 (n : nat) : (term114 n) = (term115 n).
Proof. exact (MK_COMB (@lem1648956 n) (@lem1648955)). Qed.
Lemma lem1648958 : term116 = term117.
Proof. exact (eq_refl term116). Qed.
Lemma lem1648959 (n : nat) : (term99 n) = (term99 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem1648960 (n : nat) : (term118 n) = (term119 n).
Proof. exact (MK_COMB (@lem1648959 n) (@lem1648958)). Qed.
Lemma lem1648961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1648962 (n : nat) : (term120 n) = (term121 n).
Proof. exact (MK_COMB (@lem1648961) (@lem1648960 n)). Qed.
Lemma lem1648963 (n : nat) : (term111 n) = (term122 n).
Proof. exact (MK_COMB (@lem1648962 n) (@lem1648957 n)). Qed.
Lemma lem1648964 (n : nat) : (term110 n) = (term98 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem1648965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1648966 (n : nat) : (term123 n) = (term124 n).
Proof. exact (MK_COMB (@lem1648965) (@lem1648964 n)). Qed.
Lemma lem1648967 (n : nat) : ((term110 n) = (term111 n)) = ((term98 n) = (term122 n)).
Proof. exact (MK_COMB (@lem1648966 n) (@lem1648963 n)). Qed.
Lemma lem1648968 (n : nat) : (term98 n) = (term122 n).
Proof. exact (EQ_MP (@lem1648967 n) (@lem1648954 n)). Qed.
Lemma lem1648969 (n : nat) : (term122 n) = (term98 n).
Proof. exact (SYM (@lem1648968 n)). Qed.
Lemma lem1648987 (n : nat) (h1 : term125 n) : term125 n.
Proof. exact (h1). Qed.
Lemma lem1649005 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1648827 x) (@lem1648826 x)). Qed.
Lemma lem1649006 : term117 = True.
Proof. exact (@lem1649005 term91). Qed.
Lemma lem1649007 : True = term117.
Proof. exact (SYM (@lem1649006)). Qed.
Lemma lem1649013 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term84 _476 _475 _474 _477) = (term85 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1649014 (_474 : real) (_475 : Prop) (_477 : real) : (term126 _475 _474 _477) = (term127 _474 _475 _477).
Proof. exact (@lem1649013 _474 _475 term128 _477). Qed.
Lemma lem1649015 (n : nat) : (term129 n) = (term130 n).
Proof. exact (@lem1649014 term91 (n = (NUMERAL 0)) term70). Qed.
Lemma lem1649016 : term131 = term132.
Proof. exact (eq_refl term131). Qed.
Lemma lem1649017 (n : nat) : (term94 n) = (term94 n).
Proof. exact (eq_refl (term94 n)). Qed.
Lemma lem1649018 (n : nat) : (term133 n) = (term134 n).
Proof. exact (MK_COMB (@lem1649017 n) (@lem1649016)). Qed.
Lemma lem1649019 : term135 = term136.
Proof. exact (eq_refl term135). Qed.
Lemma lem1649020 (n : nat) : (term99 n) = (term99 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem1649021 (n : nat) : (term137 n) = (term138 n).
Proof. exact (MK_COMB (@lem1649020 n) (@lem1649019)). Qed.
Lemma lem1649022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649023 (n : nat) : (term139 n) = (term140 n).
Proof. exact (MK_COMB (@lem1649022) (@lem1649021 n)). Qed.
Lemma lem1649024 (n : nat) : (term130 n) = (term141 n).
Proof. exact (MK_COMB (@lem1649023 n) (@lem1649018 n)). Qed.
Lemma lem1649025 (n : nat) : (term129 n) = (term93 n).
Proof. exact (eq_refl (term129 n)). Qed.
Lemma lem1649026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1649027 (n : nat) : (term142 n) = (term143 n).
Proof. exact (MK_COMB (@lem1649026) (@lem1649025 n)). Qed.
Lemma lem1649028 (n : nat) : ((term129 n) = (term130 n)) = ((term93 n) = (term141 n)).
Proof. exact (MK_COMB (@lem1649027 n) (@lem1649024 n)). Qed.
Lemma lem1649029 (n : nat) : (term93 n) = (term141 n).
Proof. exact (EQ_MP (@lem1649028 n) (@lem1649015 n)). Qed.
Lemma lem1649030 (n : nat) : (term141 n) = (term93 n).
Proof. exact (SYM (@lem1649029 n)). Qed.
Lemma lem1649066 (n : nat) : (term68 n) = True.
Proof. exact (EQ_MP (@lem1648832 n) (@lem1648831 n)). Qed.
Lemma lem1649067 : term136 = True.
Proof. exact (@lem1649066 term144). Qed.
Lemma lem1649068 : True = term136.
Proof. exact (SYM (@lem1649067)). Qed.
Lemma lem1649071 (n : nat) : (term68 n) = True.
Proof. exact (EQ_MP (@lem1648832 n) (@lem1648831 n)). Qed.
Lemma lem1649072 : term132 = True.
Proof. exact (@lem1649071 (NUMERAL 0)). Qed.
Lemma lem1649073 : True = term132.
Proof. exact (SYM (@lem1649072)). Qed.
Lemma lem1649075 : term132.
Proof. exact (EQ_MP (@lem1649073) (@lem0)). Qed.
Lemma lem1649076 (n : nat) : term134 n.
Proof. exact (fun h0 : term125 n => @lem1649075). Qed.
Lemma lem1649077 : term136.
Proof. exact (EQ_MP (@lem1649068) (@lem0)). Qed.
Lemma lem1649078 (n : nat) : term138 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1649077). Qed.
Lemma lem1649079 (n : nat) : term141 n.
Proof. exact (conj (@lem1649078 n) (@lem1649076 n)). Qed.
Lemma lem1649088 : term145.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1649089 (m : nat) : term146 m.
Proof. exact (@lem1649088 m). Qed.
Lemma lem1649090 (m : nat) : (term146 m) = ((term147 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem1649096 (n : nat) : term148 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1649112 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1649113 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem1649114 (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (Peano.le n m) = (term147 n).
Proof. exact (MK_COMB (@lem1649113 n) (@lem1649112 m h1)). Qed.
Lemma lem1649116 (m : nat) : (term147 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1649090 m) (@lem1649089 m)). Qed.
Lemma lem1649117 (n : nat) : (term147 n) = (n = (NUMERAL 0)).
Proof. exact (@lem1649116 n). Qed.
Lemma lem1649119 (n : nat) (h1 : term125 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1649096 n (@lem1648987 n h1)). Qed.
Lemma lem1649120 (n : nat) (h1 : term125 n) : (term147 n) = False.
Proof. exact (TRANS (@lem1649117 n) (@lem1649119 n h1)). Qed.
Lemma lem1649121 (n : nat) (m : nat) (h1 : term125 n) (h2 : m = (NUMERAL 0)) : (Peano.le n m) = False.
Proof. exact (TRANS (@lem1649114 n m h2) (@lem1649120 n h1)). Qed.
Lemma lem1649122 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1649123 (n : nat) (m : nat) (h1 : term125 n) (h2 : m = (NUMERAL 0)) : (term149 n m) = (imp False).
Proof. exact (MK_COMB (@lem1649122) (@lem1649121 n m h1 h2)). Qed.
Lemma lem1649124 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem1649125 (n : nat) (m : nat) (h1 : term125 n) (h2 : m = (NUMERAL 0)) : (term150 n m) = term151.
Proof. exact (MK_COMB (@lem1649123 n m h1 h2) (@lem1649124)). Qed.
Lemma lem1649127 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1649128 : term151 = True.
Proof. exact (@lem1649127 term113). Qed.
Lemma lem1649129 (n : nat) (m : nat) (h1 : term125 n) (h2 : m = (NUMERAL 0)) : (term150 n m) = True.
Proof. exact (TRANS (@lem1649125 n m h1 h2) (@lem1649128)). Qed.
Lemma lem1649130 (n : nat) (m : nat) (h1 : term125 n) (h2 : m = (NUMERAL 0)) : True = (term150 n m).
Proof. exact (SYM (@lem1649129 n m h1 h2)). Qed.
Lemma lem1649131 (n : nat) (m : nat) (h1 : term125 n) (h2 : m = (NUMERAL 0)) : term150 n m.
Proof. exact (EQ_MP (@lem1649130 n m h1 h2) (@lem0)). Qed.
Lemma lem1649134 (n : nat) (m : nat) (h1 : term125 n) (h2 : Peano.le n m) (h3 : m = (NUMERAL 0)) : term113.
Proof. exact (@lem1649131 n m h1 h3 (@lem1648842 n m h2)). Qed.
Lemma lem1649135 (n : nat) (m : nat) (h1 : term125 n) (h2 : Peano.le n m) (h3 : m = (NUMERAL 0)) : (term125 n) = term113.
Proof. exact (prop_ext (fun h4 : term125 n => @lem1649134 n m h1 h2 h3) (fun h4 : term113 => @lem1648987 n h1)). Qed.
Lemma lem1649136 (n : nat) (m : nat) (h1 : term125 n) (h2 : Peano.le n m) (h3 : m = (NUMERAL 0)) : term113.
Proof. exact (EQ_MP (@lem1649135 n m h1 h2 h3) (@lem1648987 n h1)). Qed.
Lemma lem1649137 (n : nat) (m : nat) (h1 : Peano.le n m) (h2 : m = (NUMERAL 0)) : term115 n.
Proof. exact (fun h0 : term125 n => @lem1649136 n m h0 h1 h2). Qed.
Lemma lem1649138 : term117.
Proof. exact (EQ_MP (@lem1649007) (@lem0)). Qed.
Lemma lem1649139 (n : nat) : term119 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1649138). Qed.
Lemma lem1649140 (n : nat) (m : nat) (h1 : Peano.le n m) (h2 : m = (NUMERAL 0)) : term122 n.
Proof. exact (conj (@lem1649139 n) (@lem1649137 n m h1 h2)). Qed.
Lemma lem1649144 (n : nat) : term93 n.
Proof. exact (EQ_MP (@lem1649030 n) (@lem1649079 n)). Qed.
Lemma lem1649145 (m : nat) (n : nat) : term96 m n.
Proof. exact (fun h0 : term125 m => @lem1649144 n). Qed.
Lemma lem1649146 (n : nat) (m : nat) (h1 : Peano.le n m) (h2 : m = (NUMERAL 0)) : term98 n.
Proof. exact (EQ_MP (@lem1648969 n) (@lem1649140 n m h1 h2)). Qed.
Lemma lem1649147 (n : nat) (m : nat) (h1 : Peano.le n m) (h2 : m = (NUMERAL 0)) : (m = (NUMERAL 0)) = (term98 n).
Proof. exact (prop_ext (fun h3 : m = (NUMERAL 0) => @lem1649146 n m h1 h2) (fun h3 : term98 n => @lem1648902 m h2)). Qed.
Lemma lem1649148 (n : nat) (m : nat) (h1 : Peano.le n m) (h2 : m = (NUMERAL 0)) : term98 n.
Proof. exact (EQ_MP (@lem1649147 n m h1 h2) (@lem1648902 m h2)). Qed.
Lemma lem1649149 (n : nat) (m : nat) (h1 : Peano.le n m) : term101 m n.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem1649148 n m h1 h0). Qed.
Lemma lem1649150 (n : nat) (m : nat) (h1 : Peano.le n m) : term104 m n.
Proof. exact (conj (@lem1649149 n m h1) (@lem1649145 m n)). Qed.
Lemma lem1649151 (n : nat) (m : nat) (h1 : Peano.le n m) : term83 m n.
Proof. exact (EQ_MP (@lem1648901 m n) (@lem1649150 n m h1)). Qed.
Lemma lem1649152 (n : nat) (m : nat) (x : real) (h1 : Peano.le n m) (h2 : x = term70) : term15 m x n.
Proof. exact (EQ_MP (@lem1648883 m n x h2) (@lem1649151 n m h1)). Qed.
Lemma lem1649154 (x : real) : x = (term60 x).
Proof. exact (EQ_MP (@lem1648822 x) (@lem1648821 x)). Qed.
Lemma lem1649155 (x : real) (n : nat) : (real_pow x n) = (term152 x n).
Proof. exact (@lem1649154 (real_pow x n)). Qed.
Lemma lem1649157 (x : real) : x = (term60 x).
Proof. exact (EQ_MP (@lem1648822 x) (@lem1648821 x)). Qed.
Lemma lem1649158 (x : real) (m : nat) : (real_pow x m) = (term152 x m).
Proof. exact (@lem1649157 (real_pow x m)). Qed.
Lemma lem1649159 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1649160 (x : real) (m : nat) : (term81 x m) = (term153 x m).
Proof. exact (MK_COMB (@lem1649159) (@lem1649158 x m)). Qed.
Lemma lem1649161 (m : nat) (x : real) (n : nat) : (term15 m x n) = (term154 m x n).
Proof. exact (MK_COMB (@lem1649160 x m) (@lem1649155 x n)). Qed.
Lemma lem1649162 (m : nat) (x : real) (n : nat) : (term154 m x n) = (term15 m x n).
Proof. exact (SYM (@lem1649161 m x n)). Qed.
Lemma lem1649164 (y : real) (x : real) : term51 y x.
Proof. exact (EQ_MP (@lem1648809 y x) (@lem1648808 y x)). Qed.
Lemma lem1649165 (m : nat) (x : real) (n : nat) : term155 m x n.
Proof. exact (@lem1649164 (term36 x m) (term36 x n)). Qed.
Lemma lem1649169 (x : real) (n : nat) : (term36 x n) = (term35 x n).
Proof. exact (EQ_MP (@lem1648786 x n) (@lem1648785 x n)). Qed.
Lemma lem1649170 : term156 = term156.
Proof. exact (eq_refl term156). Qed.
Lemma lem1649171 (x : real) (n : nat) : (term157 x n) = (term158 x n).
Proof. exact (MK_COMB (@lem1649170) (@lem1649169 x n)). Qed.
Lemma lem1649172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649173 (x : real) (n : nat) : (term159 x n) = (term160 x n).
Proof. exact (MK_COMB (@lem1649172) (@lem1649171 x n)). Qed.
Lemma lem1649175 (x : real) (n : nat) : (term36 x n) = (term35 x n).
Proof. exact (EQ_MP (@lem1648786 x n) (@lem1648785 x n)). Qed.
Lemma lem1649176 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1649177 (x : real) (n : nat) : (term161 x n) = (term162 x n).
Proof. exact (MK_COMB (@lem1649176) (@lem1649175 x n)). Qed.
Lemma lem1649179 (x : real) (n : nat) : (term36 x n) = (term35 x n).
Proof. exact (EQ_MP (@lem1648786 x n) (@lem1648785 x n)). Qed.
Lemma lem1649180 (x : real) (m : nat) : (term36 x m) = (term35 x m).
Proof. exact (@lem1649179 x m). Qed.
Lemma lem1649181 (n : nat) (x : real) (m : nat) : (term163 n x m) = (term164 n x m).
Proof. exact (MK_COMB (@lem1649177 x n) (@lem1649180 x m)). Qed.
Lemma lem1649182 (n : nat) (x : real) (m : nat) : (term165 n x m) = (term166 n x m).
Proof. exact (MK_COMB (@lem1649173 x n) (@lem1649181 n x m)). Qed.
Lemma lem1649185 (n : nat) (x : real) (m : nat) : (term166 n x m) = (term165 n x m).
Proof. exact (SYM (@lem1649182 n x m)). Qed.
Lemma lem1649187 (x : real) (n : nat) : term31 x n.
Proof. exact (EQ_MP (@lem1648766 x n) (@lem1648765 x n)). Qed.
Lemma lem1649188 (x : real) (n : nat) : term167 x n.
Proof. exact (@lem1649187 (real_inv x) n). Qed.
Lemma lem1649190 (x : real) : (term25 x) = (term26 x).
Proof. exact (EQ_MP (@lem1648743 x) (@lem1648742 x)). Qed.
Lemma lem1649191 (x : real) : (term26 x) = (term25 x).
Proof. exact (SYM (@lem1649190 x)). Qed.
Lemma lem1649193 (m : nat) (x : real) (n : nat) : term13 m x n.
Proof. exact (EQ_MP (@lem1648740 m x n) (@lem1648739 m x n)). Qed.
Lemma lem1649194 (n : nat) (x : real) (m : nat) : term168 n x m.
Proof. exact (@lem1649193 n (real_inv x) m). Qed.
Lemma lem1649199 (n : nat) (m : nat) : (Peano.le n m) = ((Peano.le n m) = True).
Proof. exact (@lem7 (Peano.le n m)). Qed.
Lemma lem1649217 (n : nat) (m : nat) (h1 : Peano.le n m) : (Peano.le n m) = True.
Proof. exact (EQ_MP (@lem1649199 n m) (@lem1648842 n m h1)). Qed.
Lemma lem1649218 (x : real) : (term169 x) = (term169 x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1649219 (x : real) (n : nat) (m : nat) (h1 : Peano.le n m) : (term170 x n m) = (term171 x).
Proof. exact (MK_COMB (@lem1649218 x) (@lem1649217 n m h1)). Qed.
Lemma lem1649221 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1649222 (x : real) : (term171 x) = (term4 x).
Proof. exact (@lem1649221 (term4 x)). Qed.
Lemma lem1649223 (x : real) (n : nat) (m : nat) (h1 : Peano.le n m) : (term170 x n m) = (term4 x).
Proof. exact (TRANS (@lem1649219 x n m h1) (@lem1649222 x)). Qed.
Lemma lem1649224 (x : real) (n : nat) (m : nat) (h1 : Peano.le n m) : (term4 x) = (term170 x n m).
Proof. exact (SYM (@lem1649223 x n m h1)). Qed.
Lemma lem1649226 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1648710 x) (@lem1648709 x)). Qed.
Lemma lem1649227 (x : real) : term172 x.
Proof. exact (@lem1379381 x). Qed.
Lemma lem1649228 (x : real) : (term172 x) = (term173 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1649229 (x : real) : term173 x.
Proof. exact (EQ_MP (@lem1649228 x) (@lem1649227 x)). Qed.
Lemma lem1649230 (x : real) (y : real) : term174 x y.
Proof. exact (@lem1649229 x y). Qed.
Lemma lem1649231 (x : real) (y : real) : (term174 x y) = ((real_lt x y) = (term175 x y)).
Proof. exact (eq_refl (term174 x y)). Qed.
Lemma lem1649233 (x : real) : (term75 x) = ((term75 x) = True).
Proof. exact (@lem7 (term75 x)). Qed.
Lemma lem1649242 (x : real) (h1 : x = term70) : x = term70.
Proof. exact (h1). Qed.
Lemma lem1649243 (x : real) (h1 : x = term70) : term70 = x.
Proof. exact (SYM (@lem1649242 x h1)). Qed.
Lemma lem1649244 (x : real) (h1 : term70 = x) : term70 = x.
Proof. exact (h1). Qed.
Lemma lem1649245 (x : real) (h1 : term70 = x) : x = term70.
Proof. exact (SYM (@lem1649244 x h1)). Qed.
Lemma lem1649246 (x : real) : (x = term70) = (term70 = x).
Proof. exact (prop_ext (fun h1 : x = term70 => @lem1649243 x h1) (fun h1 : term70 = x => @lem1649245 x h1)). Qed.
Lemma lem1649247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649248 (x : real) : (term72 x) = (term176 x).
Proof. exact (MK_COMB (@lem1649247) (@lem1649246 x)). Qed.
Lemma lem1649249 (x : real) (h1 : term72 x) : term176 x.
Proof. exact (EQ_MP (@lem1649248 x) (@lem1648838 x h1)). Qed.
Lemma lem1649250 (x : real) : term177 x.
Proof. exact (@lem82 (term70 = x)). Qed.
Lemma lem1649253 (x : real) (y : real) : (real_lt x y) = (term175 x y).
Proof. exact (EQ_MP (@lem1649231 x y) (@lem1649230 x y)). Qed.
Lemma lem1649254 (x : real) : (term26 x) = (term178 x).
Proof. exact (@lem1649253 term70 x). Qed.
Lemma lem1649258 (x : real) (h1 : term75 x) : (term75 x) = True.
Proof. exact (EQ_MP (@lem1649233 x) (@lem1648841 x h1)). Qed.
Lemma lem1649259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649260 (x : real) (h1 : term75 x) : (term179 x) = (and True).
Proof. exact (MK_COMB (@lem1649259) (@lem1649258 x h1)). Qed.
Lemma lem1649262 (x : real) (h1 : term72 x) : (term70 = x) = False.
Proof. exact (@lem1649250 x (@lem1649249 x h1)). Qed.
Lemma lem1649263 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649264 (x : real) (h1 : term72 x) : (term176 x) = (~ False).
Proof. exact (MK_COMB (@lem1649263) (@lem1649262 x h1)). Qed.
Lemma lem1649266 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1649267 (x : real) (h1 : term72 x) : (term176 x) = True.
Proof. exact (TRANS (@lem1649264 x h1) (@lem1649266)). Qed.
Lemma lem1649268 (x : real) (h1 : term72 x) (h2 : term75 x) : (term178 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1649260 x h2) (@lem1649267 x h1)). Qed.
Lemma lem1649270 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1649271 : (True /\ True) = True.
Proof. exact (@lem1649270 True). Qed.
Lemma lem1649272 (x : real) (h1 : term72 x) (h2 : term75 x) : (term178 x) = True.
Proof. exact (TRANS (@lem1649268 x h1 h2) (@lem1649271)). Qed.
Lemma lem1649273 (x : real) (h1 : term72 x) (h2 : term75 x) : (term26 x) = True.
Proof. exact (TRANS (@lem1649254 x) (@lem1649272 x h1 h2)). Qed.
Lemma lem1649274 (x : real) (h1 : term72 x) (h2 : term75 x) : True = (term26 x).
Proof. exact (SYM (@lem1649273 x h1 h2)). Qed.
Lemma lem1649275 (x : real) (h1 : term72 x) (h2 : term75 x) : term26 x.
Proof. exact (EQ_MP (@lem1649274 x h1 h2) (@lem0)). Qed.
Lemma lem1649276 (x : real) : term172 x.
Proof. exact (@lem1379381 x). Qed.
Lemma lem1649277 (x : real) : (term172 x) = (term173 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1649278 (x : real) : term173 x.
Proof. exact (EQ_MP (@lem1649277 x) (@lem1649276 x)). Qed.
Lemma lem1649279 (x : real) (y : real) : term174 x y.
Proof. exact (@lem1649278 x y). Qed.
Lemma lem1649280 (x : real) (y : real) : (term174 x y) = ((real_lt x y) = (term175 x y)).
Proof. exact (eq_refl (term174 x y)). Qed.
Lemma lem1649282 (x : real) : (term75 x) = ((term75 x) = True).
Proof. exact (@lem7 (term75 x)). Qed.
Lemma lem1649284 (x : real) : (term76 x) = ((term76 x) = True).
Proof. exact (@lem7 (term76 x)). Qed.
Lemma lem1649291 (x : real) (h1 : x = term70) : x = term70.
Proof. exact (h1). Qed.
Lemma lem1649292 (x : real) (h1 : x = term70) : term70 = x.
Proof. exact (SYM (@lem1649291 x h1)). Qed.
Lemma lem1649293 (x : real) (h1 : term70 = x) : term70 = x.
Proof. exact (h1). Qed.
Lemma lem1649294 (x : real) (h1 : term70 = x) : x = term70.
Proof. exact (SYM (@lem1649293 x h1)). Qed.
Lemma lem1649295 (x : real) : (x = term70) = (term70 = x).
Proof. exact (prop_ext (fun h1 : x = term70 => @lem1649292 x h1) (fun h1 : term70 = x => @lem1649294 x h1)). Qed.
Lemma lem1649296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649297 (x : real) : (term72 x) = (term176 x).
Proof. exact (MK_COMB (@lem1649296) (@lem1649295 x)). Qed.
Lemma lem1649298 (x : real) (h1 : term72 x) : term176 x.
Proof. exact (EQ_MP (@lem1649297 x) (@lem1648838 x h1)). Qed.
Lemma lem1649299 (x : real) : term177 x.
Proof. exact (@lem82 (term70 = x)). Qed.
Lemma lem1649304 (x : real) (y : real) : (real_lt x y) = (term175 x y).
Proof. exact (EQ_MP (@lem1649280 x y) (@lem1649279 x y)). Qed.
Lemma lem1649305 (x : real) : (term26 x) = (term178 x).
Proof. exact (@lem1649304 term70 x). Qed.
Lemma lem1649309 (x : real) (h1 : term75 x) : (term75 x) = True.
Proof. exact (EQ_MP (@lem1649282 x) (@lem1648841 x h1)). Qed.
Lemma lem1649310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649311 (x : real) (h1 : term75 x) : (term179 x) = (and True).
Proof. exact (MK_COMB (@lem1649310) (@lem1649309 x h1)). Qed.
Lemma lem1649313 (x : real) (h1 : term72 x) : (term70 = x) = False.
Proof. exact (@lem1649299 x (@lem1649298 x h1)). Qed.
Lemma lem1649314 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1649315 (x : real) (h1 : term72 x) : (term176 x) = (~ False).
Proof. exact (MK_COMB (@lem1649314) (@lem1649313 x h1)). Qed.
Lemma lem1649317 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1649318 (x : real) (h1 : term72 x) : (term176 x) = True.
Proof. exact (TRANS (@lem1649315 x h1) (@lem1649317)). Qed.
Lemma lem1649319 (x : real) (h1 : term72 x) (h2 : term75 x) : (term178 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1649311 x h2) (@lem1649318 x h1)). Qed.
Lemma lem1649321 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1649322 : (True /\ True) = True.
Proof. exact (@lem1649321 True). Qed.
Lemma lem1649323 (x : real) (h1 : term72 x) (h2 : term75 x) : (term178 x) = True.
Proof. exact (TRANS (@lem1649319 x h1 h2) (@lem1649322)). Qed.
Lemma lem1649324 (x : real) (h1 : term72 x) (h2 : term75 x) : (term26 x) = True.
Proof. exact (TRANS (@lem1649305 x) (@lem1649323 x h1 h2)). Qed.
Lemma lem1649325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1649326 (x : real) (h1 : term72 x) (h2 : term75 x) : (term180 x) = (and True).
Proof. exact (MK_COMB (@lem1649325) (@lem1649324 x h1 h2)). Qed.
Lemma lem1649328 (x : real) (h1 : term76 x) : (term76 x) = True.
Proof. exact (EQ_MP (@lem1649284 x) (@lem1648843 x h1)). Qed.
Lemma lem1649329 (x : real) (h1 : term72 x) (h2 : term76 x) (h3 : term75 x) : (term3 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1649326 x h1 h3) (@lem1649328 x h2)). Qed.
Lemma lem1649331 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1649332 : (True /\ True) = True.
Proof. exact (@lem1649331 True). Qed.
Lemma lem1649333 (x : real) (h1 : term72 x) (h2 : term76 x) (h3 : term75 x) : (term3 x) = True.
Proof. exact (TRANS (@lem1649329 x h1 h2 h3) (@lem1649332)). Qed.
Lemma lem1649334 (x : real) (h1 : term72 x) (h2 : term76 x) (h3 : term75 x) : True = (term3 x).
Proof. exact (SYM (@lem1649333 x h1 h2 h3)). Qed.
Lemma lem1649335 (x : real) (h1 : term72 x) (h2 : term76 x) (h3 : term75 x) : term3 x.
Proof. exact (EQ_MP (@lem1649334 x h1 h2 h3) (@lem0)). Qed.
Lemma lem1649336 (x : real) (h1 : term72 x) (h2 : term76 x) (h3 : term75 x) : term4 x.
Proof. exact (@lem1649226 x (@lem1649335 x h1 h2 h3)). Qed.
Lemma lem1649337 (n : nat) (m : nat) (x : real) (h1 : term72 x) (h2 : Peano.le n m) (h3 : term76 x) (h4 : term75 x) : term170 x n m.
Proof. exact (EQ_MP (@lem1649224 x n m h2) (@lem1649336 x h1 h3 h4)). Qed.
Lemma lem1649338 (n : nat) (m : nat) (x : real) (h1 : term72 x) (h2 : Peano.le n m) (h3 : term76 x) (h4 : term75 x) : term164 n x m.
Proof. exact (@lem1649194 n x m (@lem1649337 n m x h1 h2 h3 h4)). Qed.
Lemma lem1649339 (x : real) (h1 : term72 x) (h2 : term75 x) : term25 x.
Proof. exact (EQ_MP (@lem1649191 x) (@lem1649275 x h1 h2)). Qed.
Lemma lem1649340 (n : nat) (x : real) (h1 : term72 x) (h2 : term75 x) : term158 x n.
Proof. exact (@lem1649188 x n (@lem1649339 x h1 h2)). Qed.
Lemma lem1649341 (n : nat) (m : nat) (x : real) (h1 : term72 x) (h2 : Peano.le n m) (h3 : term76 x) (h4 : term75 x) : term166 n x m.
Proof. exact (conj (@lem1649340 n x h1 h4) (@lem1649338 n m x h1 h2 h3 h4)). Qed.
Lemma lem1649342 (n : nat) (m : nat) (x : real) (h1 : term72 x) (h2 : Peano.le n m) (h3 : term76 x) (h4 : term75 x) : term165 n x m.
Proof. exact (EQ_MP (@lem1649185 n x m) (@lem1649341 n m x h1 h2 h3 h4)). Qed.
Lemma lem1649343 (n : nat) (m : nat) (x : real) (h1 : term72 x) (h2 : Peano.le n m) (h3 : term76 x) (h4 : term75 x) : term154 m x n.
Proof. exact (@lem1649165 m x n (@lem1649342 n m x h1 h2 h3 h4)). Qed.
Lemma lem1649344 (n : nat) (m : nat) (x : real) (h1 : term72 x) (h2 : Peano.le n m) (h3 : term76 x) (h4 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649162 m x n) (@lem1649343 n m x h1 h2 h3 h4)). Qed.
Lemma lem1649345 (n : nat) (m : nat) (x : real) (h1 : Peano.le n m) (h2 : term76 x) (h3 : term75 x) : term15 m x n.
Proof. exact (or_elim (@lem1648836 x) (fun h0 : x = term70 => @lem1649152 n m x h1 h0) (fun h0 : term72 x => @lem1649344 n m x h0 h1 h2 h3)). Qed.
Lemma lem1649346 (x : real) (n : nat) (m : nat) (h1 : term73 x n m) : term74 x n m.
Proof. exact (proj2 (@lem1648839 x n m h1)). Qed.
Lemma lem1649347 (x : real) (n : nat) (m : nat) (h1 : term73 x n m) : term75 x.
Proof. exact (proj1 (@lem1648839 x n m h1)). Qed.
Lemma lem1649348 (x : real) (n : nat) (m : nat) (h1 : term74 x n m) : Peano.le n m.
Proof. exact (proj2 (@lem1648840 x n m h1)). Qed.
Lemma lem1649349 (x : real) (n : nat) (m : nat) (h1 : term74 x n m) : term76 x.
Proof. exact (proj1 (@lem1648840 x n m h1)). Qed.
Lemma lem1649350 (n : nat) (m : nat) (x : real) (h1 : Peano.le n m) (h2 : term76 x) (h3 : term75 x) : (Peano.le n m) = (term15 m x n).
Proof. exact (prop_ext (fun h4 : Peano.le n m => @lem1649345 n m x h1 h2 h3) (fun h4 : term15 m x n => @lem1648842 n m h1)). Qed.
Lemma lem1649351 (n : nat) (m : nat) (x : real) (h1 : Peano.le n m) (h2 : term76 x) (h3 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649350 n m x h1 h2 h3) (@lem1648842 n m h1)). Qed.
Lemma lem1649352 (n : nat) (m : nat) (x : real) (h1 : Peano.le n m) (h2 : term76 x) (h3 : term75 x) : (term76 x) = (term15 m x n).
Proof. exact (prop_ext (fun h4 : term76 x => @lem1649351 n m x h1 h2 h3) (fun h4 : term15 m x n => @lem1648843 x h2)). Qed.
Lemma lem1649353 (n : nat) (m : nat) (x : real) (h1 : Peano.le n m) (h2 : term76 x) (h3 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649352 n m x h1 h2 h3) (@lem1648843 x h2)). Qed.
Lemma lem1649354 (n : nat) (m : nat) (x : real) (h1 : term74 x n m) (h2 : term76 x) (h3 : term75 x) : (Peano.le n m) = (term15 m x n).
Proof. exact (prop_ext (fun h4 : Peano.le n m => @lem1649353 n m x h4 h2 h3) (fun h4 : term15 m x n => @lem1649348 x n m h1)). Qed.
Lemma lem1649355 (n : nat) (m : nat) (x : real) (h1 : term74 x n m) (h2 : term76 x) (h3 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649354 n m x h1 h2 h3) (@lem1649348 x n m h1)). Qed.
Lemma lem1649356 (n : nat) (m : nat) (x : real) (h1 : term74 x n m) (h2 : term75 x) : (term76 x) = (term15 m x n).
Proof. exact (prop_ext (fun h3 : term76 x => @lem1649355 n m x h1 h3 h2) (fun h3 : term15 m x n => @lem1649349 x n m h1)). Qed.
Lemma lem1649357 (n : nat) (m : nat) (x : real) (h1 : term74 x n m) (h2 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649356 n m x h1 h2) (@lem1649349 x n m h1)). Qed.
Lemma lem1649358 (n : nat) (m : nat) (x : real) (h1 : term74 x n m) (h2 : term75 x) : (term75 x) = (term15 m x n).
Proof. exact (prop_ext (fun h3 : term75 x => @lem1649357 n m x h1 h2) (fun h3 : term15 m x n => @lem1648841 x h2)). Qed.
Lemma lem1649359 (n : nat) (m : nat) (x : real) (h1 : term74 x n m) (h2 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649358 n m x h1 h2) (@lem1648841 x h2)). Qed.
Lemma lem1649360 (n : nat) (m : nat) (x : real) (h1 : term73 x n m) (h2 : term75 x) : (term74 x n m) = (term15 m x n).
Proof. exact (prop_ext (fun h3 : term74 x n m => @lem1649359 n m x h3 h2) (fun h3 : term15 m x n => @lem1649346 x n m h1)). Qed.
Lemma lem1649361 (n : nat) (m : nat) (x : real) (h1 : term73 x n m) (h2 : term75 x) : term15 m x n.
Proof. exact (EQ_MP (@lem1649360 n m x h1 h2) (@lem1649346 x n m h1)). Qed.
Lemma lem1649362 (x : real) (n : nat) (m : nat) (h1 : term73 x n m) : (term75 x) = (term15 m x n).
Proof. exact (prop_ext (fun h2 : term75 x => @lem1649361 n m x h1 h2) (fun h2 : term15 m x n => @lem1649347 x n m h1)). Qed.
Lemma lem1649363 (x : real) (n : nat) (m : nat) (h1 : term73 x n m) : term15 m x n.
Proof. exact (EQ_MP (@lem1649362 x n m h1) (@lem1649347 x n m h1)). Qed.
Lemma lem1649364 (m : nat) (x : real) (n : nat) : term181 m x n.
Proof. exact (fun h0 : term73 x n m => @lem1649363 x n m h0). Qed.
Lemma lem1649369 (m : nat) (n : nat) : term182 m n.
Proof. exact (fun x : real => @lem1649364 m x n). Qed.
Lemma lem1649374 (m : nat) : term183 m.
Proof. exact (fun n : nat => @lem1649369 m n). Qed.
Lemma lem1649379 : term184.
Proof. exact (fun m : nat => @lem1649374 m). Qed.
