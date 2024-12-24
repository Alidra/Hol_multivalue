Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1013352_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import DE_MORGAN_THM_spec.
Require Import DISJ_ACI_spec.
Require Import LE_ANTISYM_spec.
Require Import LT_EXISTS_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1012682 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1012683 : term1.
Proof. exact (proj2 (@lem1012682)). Qed.
Lemma lem1012684 : term2.
Proof. exact (proj2 (@lem1012683)). Qed.
Lemma lem1012685 (m : nat) : term3 m.
Proof. exact (@lem1012684 m). Qed.
Lemma lem1012686 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1012687 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1012686 m) (@lem1012685 m)). Qed.
Lemma lem1012688 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1012687 m n). Qed.
Lemma lem1012689 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1012691 : term8.
Proof. exact (proj1 (@lem1012683)). Qed.
Lemma lem1012692 (m : nat) : term9 m.
Proof. exact (@lem1012691 m). Qed.
Lemma lem1012693 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1012694 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1012693 m) (@lem1012692 m)). Qed.
Lemma lem1012695 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1012694 m n). Qed.
Lemma lem1012696 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (term7 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1012706 (m : nat) : term13 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem1012707 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1012708 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1012707 m) (@lem1012706 m)). Qed.
Lemma lem1012709 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1012708 m n). Qed.
Lemma lem1012710 (n : nat) (m : nat) : (term15 m n) = ((Peano.lt m n) = (term16 n m)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1012712 (m : nat) : term17 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem1012713 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1012714 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1012713 m) (@lem1012712 m)). Qed.
Lemma lem1012715 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1012714 m n). Qed.
Lemma lem1012716 (n : nat) (m : nat) : (term19 m n) = ((term20 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1012720 (m : nat) (n : nat) (h1 : (term21 n m) = (m = n)) : (term21 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem1012721 (m : nat) (n : nat) (h1 : (term21 n m) = (m = n)) : (m = n) = (term21 n m).
Proof. exact (SYM (@lem1012720 m n h1)). Qed.
Lemma lem1012722 (n : nat) (m : nat) (h1 : (m = n) = (term21 n m)) : (m = n) = (term21 n m).
Proof. exact (h1). Qed.
Lemma lem1012723 (n : nat) (m : nat) (h1 : (m = n) = (term21 n m)) : (term21 n m) = (m = n).
Proof. exact (SYM (@lem1012722 n m h1)). Qed.
Lemma lem1012724 (n : nat) (m : nat) : ((term21 n m) = (m = n)) = ((m = n) = (term21 n m)).
Proof. exact (prop_ext (fun h1 : (term21 n m) = (m = n) => @lem1012721 m n h1) (fun h1 : (m = n) = (term21 n m) => @lem1012723 n m h1)). Qed.
Lemma lem1012725 (m : nat) : (term22 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem1012724 n m)). Qed.
Lemma lem1012726 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012727 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem1012726) (@lem1012725 m)). Qed.
Lemma lem1012728 : term26 = term27.
Proof. exact (fun_ext (fun m : nat => @lem1012727 m)). Qed.
Lemma lem1012729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012730 : term28 = term29.
Proof. exact (MK_COMB (@lem1012729) (@lem1012728)). Qed.
Lemma lem1012731 : term29.
Proof. exact (EQ_MP (@lem1012730) (@lem92426)). Qed.
Lemma lem1012732 (t1 : Prop) : term30 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem1012733 (t1 : Prop) : (term30 t1) = (term31 t1).
Proof. exact (eq_refl (term30 t1)). Qed.
Lemma lem1012734 (t1 : Prop) : term31 t1.
Proof. exact (EQ_MP (@lem1012733 t1) (@lem1012732 t1)). Qed.
Lemma lem1012735 (t1 : Prop) (t2 : Prop) : term32 t1 t2.
Proof. exact (@lem1012734 t1 t2). Qed.
Lemma lem1012736 (t1 : Prop) (t2 : Prop) : (term32 t1 t2) = (term33 t1 t2).
Proof. exact (eq_refl (term32 t1 t2)). Qed.
Lemma lem1012737 (t1 : Prop) (t2 : Prop) : term33 t1 t2.
Proof. exact (EQ_MP (@lem1012736 t1 t2) (@lem1012735 t1 t2)). Qed.
Lemma lem1012740 (m : nat) : term34 m.
Proof. exact (@lem1012731 m). Qed.
Lemma lem1012741 (m : nat) : (term34 m) = (term25 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1012742 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1012741 m) (@lem1012740 m)). Qed.
Lemma lem1012743 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1012742 m n). Qed.
Lemma lem1012744 (n : nat) (m : nat) : (term35 m n) = ((m = n) = (term21 n m)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1012746 (n : nat) : term36 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1012747 (n : nat) : (term36 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem1012749 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : (term7 m p) = n.
Proof. exact (h1). Qed.
Lemma lem1012750 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : n = (term7 m p).
Proof. exact (SYM (@lem1012749 m p n h1)). Qed.
Lemma lem1012751 (p : nat) : (term37 p) = (term37 p).
Proof. exact (eq_refl (term37 p)). Qed.
Lemma lem1012752 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : (term38 p n) = (term39 m p).
Proof. exact (MK_COMB (@lem1012751 p) (@lem1012750 m p n h1)). Qed.
Lemma lem1012753 (m : nat) (p : nat) : (term39 m p) = (((term40 m p) = (NUMERAL p)) = False).
Proof. exact (eq_refl (term39 m p)). Qed.
Lemma lem1012754 (p : nat) (n : nat) : (term41 p n) = (term41 p n).
Proof. exact (eq_refl (term41 p n)). Qed.
Lemma lem1012755 (n : nat) (m : nat) (p : nat) : ((term38 p n) = (term39 m p)) = ((term38 p n) = (((term40 m p) = (NUMERAL p)) = False)).
Proof. exact (MK_COMB (@lem1012754 p n) (@lem1012753 m p)). Qed.
Lemma lem1012756 (n : nat) (p : nat) : (term38 p n) = (((NUMERAL n) = (NUMERAL p)) = False).
Proof. exact (eq_refl (term38 p n)). Qed.
Lemma lem1012757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1012758 (n : nat) (p : nat) : (term41 p n) = (term42 n p).
Proof. exact (MK_COMB (@lem1012757) (@lem1012756 n p)). Qed.
Lemma lem1012759 (m : nat) (p : nat) : (((term40 m p) = (NUMERAL p)) = False) = (((term40 m p) = (NUMERAL p)) = False).
Proof. exact (eq_refl (((term40 m p) = (NUMERAL p)) = False)). Qed.
Lemma lem1012760 (n : nat) (m : nat) (p : nat) : ((term38 p n) = (((term40 m p) = (NUMERAL p)) = False)) = ((((NUMERAL n) = (NUMERAL p)) = False) = (((term40 m p) = (NUMERAL p)) = False)).
Proof. exact (MK_COMB (@lem1012758 n p) (@lem1012759 m p)). Qed.
Lemma lem1012761 (n : nat) (m : nat) (p : nat) : ((term38 p n) = (term39 m p)) = ((((NUMERAL n) = (NUMERAL p)) = False) = (((term40 m p) = (NUMERAL p)) = False)).
Proof. exact (TRANS (@lem1012755 n m p) (@lem1012760 n m p)). Qed.
Lemma lem1012762 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : (((NUMERAL n) = (NUMERAL p)) = False) = (((term40 m p) = (NUMERAL p)) = False).
Proof. exact (EQ_MP (@lem1012761 n m p) (@lem1012752 m p n h1)). Qed.
Lemma lem1012763 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : (((term40 m p) = (NUMERAL p)) = False) = (((NUMERAL n) = (NUMERAL p)) = False).
Proof. exact (SYM (@lem1012762 m p n h1)). Qed.
Lemma lem1012765 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1012766 (m : nat) (p : nat) : (((term40 m p) = (NUMERAL p)) = False) = (term43 m p).
Proof. exact (@lem1012765 ((term40 m p) = (NUMERAL p))). Qed.
Lemma lem1012770 (n : nat) (m : nat) : (m = n) = (term21 n m).
Proof. exact (EQ_MP (@lem1012744 n m) (@lem1012743 m n)). Qed.
Lemma lem1012771 (m : nat) (p : nat) : ((term40 m p) = (NUMERAL p)) = (term44 m p).
Proof. exact (@lem1012770 (NUMERAL p) (term40 m p)). Qed.
Lemma lem1012775 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012747 n) (@lem1012746 n)). Qed.
Lemma lem1012776 (m : nat) (p : nat) : (term40 m p) = (term7 m p).
Proof. exact (@lem1012775 (term7 m p)). Qed.
Lemma lem1012777 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1012778 (m : nat) (p : nat) : (term45 m p) = (term46 m p).
Proof. exact (MK_COMB (@lem1012777) (@lem1012776 m p)). Qed.
Lemma lem1012780 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012747 n) (@lem1012746 n)). Qed.
Lemma lem1012781 (p : nat) : (NUMERAL p) = p.
Proof. exact (@lem1012780 p). Qed.
Lemma lem1012782 (m : nat) (p : nat) : (term47 m p) = (term48 m p).
Proof. exact (MK_COMB (@lem1012778 m p) (@lem1012781 p)). Qed.
Lemma lem1012783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1012784 (m : nat) (p : nat) : (term49 m p) = (term50 m p).
Proof. exact (MK_COMB (@lem1012783) (@lem1012782 m p)). Qed.
Lemma lem1012786 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012747 n) (@lem1012746 n)). Qed.
Lemma lem1012787 (p : nat) : (NUMERAL p) = p.
Proof. exact (@lem1012786 p). Qed.
Lemma lem1012788 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1012789 (p : nat) : (term51 p) = (Peano.le p).
Proof. exact (MK_COMB (@lem1012788) (@lem1012787 p)). Qed.
Lemma lem1012791 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1012747 n) (@lem1012746 n)). Qed.
Lemma lem1012792 (m : nat) (p : nat) : (term40 m p) = (term7 m p).
Proof. exact (@lem1012791 (term7 m p)). Qed.
Lemma lem1012793 (m : nat) (p : nat) : (term52 m p) = (term53 m p).
Proof. exact (MK_COMB (@lem1012789 p) (@lem1012792 m p)). Qed.
Lemma lem1012794 (m : nat) (p : nat) : (term44 m p) = (term54 m p).
Proof. exact (MK_COMB (@lem1012784 m p) (@lem1012793 m p)). Qed.
Lemma lem1012797 (m : nat) (p : nat) : ((term40 m p) = (NUMERAL p)) = (term54 m p).
Proof. exact (TRANS (@lem1012771 m p) (@lem1012794 m p)). Qed.
Lemma lem1012798 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012799 (m : nat) (p : nat) : (term43 m p) = (term55 m p).
Proof. exact (MK_COMB (@lem1012798) (@lem1012797 m p)). Qed.
Lemma lem1012801 (t1 : Prop) (t2 : Prop) : (term56 t1 t2) = (term57 t1 t2).
Proof. exact (proj1 (@lem1012737 t1 t2)). Qed.
Lemma lem1012802 (m : nat) (p : nat) : (term55 m p) = (term58 m p).
Proof. exact (@lem1012801 (term48 m p) (term53 m p)). Qed.
Lemma lem1012805 (m : nat) (p : nat) : (term43 m p) = (term58 m p).
Proof. exact (TRANS (@lem1012799 m p) (@lem1012802 m p)). Qed.
Lemma lem1012806 (m : nat) (p : nat) : (((term40 m p) = (NUMERAL p)) = False) = (term58 m p).
Proof. exact (TRANS (@lem1012766 m p) (@lem1012805 m p)). Qed.
Lemma lem1012807 (m : nat) (p : nat) : (term58 m p) = (((term40 m p) = (NUMERAL p)) = False).
Proof. exact (SYM (@lem1012806 m p)). Qed.
Lemma lem1012811 (n : nat) (m : nat) : (term20 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1012716 n m) (@lem1012715 m n)). Qed.
Lemma lem1012812 (m : nat) (p : nat) : (term59 m p) = (term60 m p).
Proof. exact (@lem1012811 p (term7 m p)). Qed.
Lemma lem1012814 (n : nat) (m : nat) : (Peano.lt m n) = (term16 n m).
Proof. exact (EQ_MP (@lem1012710 n m) (@lem1012709 m n)). Qed.
Lemma lem1012815 (m : nat) (p : nat) : (term60 m p) = (term61 m p).
Proof. exact (@lem1012814 (term7 m p) p). Qed.
Lemma lem1012820 (m : nat) (p : nat) : (term59 m p) = (term61 m p).
Proof. exact (TRANS (@lem1012812 m p) (@lem1012815 m p)). Qed.
Lemma lem1012824 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1012689 m n) (@lem1012688 m n)). Qed.
Lemma lem1012825 (p : nat) (d : nat) : (term6 p d) = (term7 p d).
Proof. exact (@lem1012824 p d). Qed.
Lemma lem1012826 (m : nat) (p : nat) : (term62 m p) = (term62 m p).
Proof. exact (eq_refl (term62 m p)). Qed.
Lemma lem1012827 (m : nat) (p : nat) (d : nat) : ((term7 m p) = (term6 p d)) = ((term7 m p) = (term7 p d)).
Proof. exact (MK_COMB (@lem1012826 m p) (@lem1012825 p d)). Qed.
Lemma lem1012830 (m : nat) (p : nat) : (term63 m p) = (term64 m p).
Proof. exact (fun_ext (fun d : nat => @lem1012827 m p d)). Qed.
Lemma lem1012831 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012832 (m : nat) (p : nat) : (term61 m p) = (term65 m p).
Proof. exact (MK_COMB (@lem1012831) (@lem1012830 m p)). Qed.
Lemma lem1012837 (m : nat) (p : nat) : (term59 m p) = (term65 m p).
Proof. exact (TRANS (@lem1012820 m p) (@lem1012832 m p)). Qed.
Lemma lem1012838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1012839 (m : nat) (p : nat) : (term66 m p) = (term67 m p).
Proof. exact (MK_COMB (@lem1012838) (@lem1012837 m p)). Qed.
Lemma lem1012841 (n : nat) (m : nat) : (term20 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1012716 n m) (@lem1012715 m n)). Qed.
Lemma lem1012842 (m : nat) (p : nat) : (term68 m p) = (term69 m p).
Proof. exact (@lem1012841 (term7 m p) p). Qed.
Lemma lem1012844 (n : nat) (m : nat) : (Peano.lt m n) = (term16 n m).
Proof. exact (EQ_MP (@lem1012710 n m) (@lem1012709 m n)). Qed.
Lemma lem1012845 (m : nat) (p : nat) : (term69 m p) = (term70 m p).
Proof. exact (@lem1012844 p (term7 m p)). Qed.
Lemma lem1012850 (m : nat) (p : nat) : (term68 m p) = (term70 m p).
Proof. exact (TRANS (@lem1012842 m p) (@lem1012845 m p)). Qed.
Lemma lem1012854 (m : nat) (n : nat) : (term12 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1012696 m n) (@lem1012695 m n)). Qed.
Lemma lem1012855 (m : nat) (p : nat) (d : nat) : (term71 m p d) = (term72 m p d).
Proof. exact (@lem1012854 (Nat.add m p) (S d)). Qed.
Lemma lem1012857 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem1012689 m n) (@lem1012688 m n)). Qed.
Lemma lem1012858 (m : nat) (p : nat) (d : nat) : (term73 m p d) = (term74 m p d).
Proof. exact (@lem1012857 (Nat.add m p) d). Qed.
Lemma lem1012859 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1012860 (m : nat) (p : nat) (d : nat) : (term72 m p d) = (term75 m p d).
Proof. exact (MK_COMB (@lem1012859) (@lem1012858 m p d)). Qed.
Lemma lem1012861 (m : nat) (p : nat) (d : nat) : (term71 m p d) = (term75 m p d).
Proof. exact (TRANS (@lem1012855 m p d) (@lem1012860 m p d)). Qed.
Lemma lem1012862 (p : nat) : (@eq nat p) = (@eq nat p).
Proof. exact (eq_refl (@eq nat p)). Qed.
Lemma lem1012863 (m : nat) (p : nat) (d : nat) : (p = (term71 m p d)) = (p = (term75 m p d)).
Proof. exact (MK_COMB (@lem1012862 p) (@lem1012861 m p d)). Qed.
Lemma lem1012866 (m : nat) (p : nat) : (term76 m p) = (term77 m p).
Proof. exact (fun_ext (fun d : nat => @lem1012863 m p d)). Qed.
Lemma lem1012867 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012868 (m : nat) (p : nat) : (term70 m p) = (term78 m p).
Proof. exact (MK_COMB (@lem1012867) (@lem1012866 m p)). Qed.
Lemma lem1012873 (m : nat) (p : nat) : (term68 m p) = (term78 m p).
Proof. exact (TRANS (@lem1012850 m p) (@lem1012868 m p)). Qed.
Lemma lem1012874 (m : nat) (p : nat) : (term58 m p) = (term79 m p).
Proof. exact (MK_COMB (@lem1012839 m p) (@lem1012873 m p)). Qed.
Lemma lem1012877 (m : nat) (p : nat) : (term79 m p) = (term58 m p).
Proof. exact (SYM (@lem1012874 m p)). Qed.
Lemma lem1012879 (p : Prop) : p = (term80 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1012880 (m : nat) (p : nat) : (term79 m p) = (term81 m p).
Proof. exact (@lem1012879 (term79 m p)). Qed.
Lemma lem1012881 (m : nat) (p : nat) : (term81 m p) = (term79 m p).
Proof. exact (SYM (@lem1012880 m p)). Qed.
Lemma lem1012882 (m : nat) (p : nat) (h1 : term82 m p) : term82 m p.
Proof. exact (h1). Qed.
Lemma lem1012885 (m : nat) (p : nat) (h1 : term83 m p) : term83 m p.
Proof. exact (h1). Qed.
Lemma lem1012886 (m : nat) (p : nat) : term84 m p.
Proof. exact (fun h0 : term83 m p => @lem1012885 m p h0). Qed.
Lemma lem1012887 (m : nat) (p : nat) (h1 : term84 m p) : term84 m p.
Proof. exact (h1). Qed.
Lemma lem1012888 (m : nat) (p : nat) (h1 : term83 m p) : term83 m p.
Proof. exact (h1). Qed.
Lemma lem1012889 (m : nat) (p : nat) (h1 : term83 m p) (h2 : term84 m p) : term83 m p.
Proof. exact (@lem1012887 m p h2 (@lem1012888 m p h1)). Qed.
Lemma lem1012890 (m : nat) (p : nat) (h1 : term83 m p) : term85 m p.
Proof. exact (fun h0 : term84 m p => @lem1012889 m p h1 h0). Qed.
Lemma lem1012891 (m : nat) (p : nat) (h1 : term84 m p) : term84 m p.
Proof. exact (h1). Qed.
Lemma lem1012892 (m : nat) (p : nat) (h1 : term83 m p) (h2 : term84 m p) : term83 m p.
Proof. exact (@lem1012890 m p h1 (@lem1012891 m p h2)). Qed.
Lemma lem1012893 (m : nat) (p : nat) (h1 : term84 m p) : term84 m p.
Proof. exact (fun h0 : term83 m p => @lem1012892 m p h0 h1). Qed.
Lemma lem1012894 (m : nat) (p : nat) : term86 m p.
Proof. exact (fun h0 : term84 m p => @lem1012893 m p h0). Qed.
Lemma lem1012897 (m : nat) (p : nat) : term84 m p.
Proof. exact (@lem1012894 m p (@lem1012886 m p)). Qed.
Lemma lem1012919 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1012920 : term87 = term88.
Proof. exact (@lem1012919 term89). Qed.
Lemma lem1012929 (m : nat) (p : nat) : (term90 m p) = (term90 m p).
Proof. exact (eq_refl (term90 m p)). Qed.
Lemma lem1012930 (m : nat) (p : nat) : (term83 m p) = (term91 m p).
Proof. exact (MK_COMB (@lem1012929 m p) (@lem1012920)). Qed.
Lemma lem1012933 (p : nat) : (term92 p) = (term93 p).
Proof. exact (fun_ext (fun m : nat => @lem1012930 m p)). Qed.
Lemma lem1012934 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012935 (p : nat) : (term94 p) = (term95 p).
Proof. exact (MK_COMB (@lem1012934) (@lem1012933 p)). Qed.
Lemma lem1012940 : term96 = term97.
Proof. exact (fun_ext (fun p : nat => @lem1012935 p)). Qed.
Lemma lem1012941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012950 : term98 = term99.
Proof. exact (MK_COMB (@lem1012941) (@lem1012940)). Qed.
Lemma lem1012951 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1012952 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1012951 n m)). Qed.
Lemma lem1012953 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012954 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1012953) (@lem1012952 m)). Qed.
Lemma lem1012955 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1012954 m)). Qed.
Lemma lem1012956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012957 : term89 = term89.
Proof. exact (MK_COMB (@lem1012956) (@lem1012955)). Qed.
Lemma lem1012958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012959 : term88 = term88.
Proof. exact (MK_COMB (@lem1012958) (@lem1012957)). Qed.
Lemma lem1012960 (m : nat) (p : nat) (d : nat) : (p = (term75 m p d)) = (p = (term75 m p d)).
Proof. exact (eq_refl (p = (term75 m p d))). Qed.
Lemma lem1012961 (m : nat) (p : nat) : (term77 m p) = (term77 m p).
Proof. exact (fun_ext (fun d : nat => @lem1012960 m p d)). Qed.
Lemma lem1012962 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012963 (m : nat) (p : nat) : (term78 m p) = (term78 m p).
Proof. exact (MK_COMB (@lem1012962) (@lem1012961 m p)). Qed.
Lemma lem1012964 (m : nat) (p : nat) (d : nat) : ((term7 m p) = (term7 p d)) = ((term7 m p) = (term7 p d)).
Proof. exact (eq_refl ((term7 m p) = (term7 p d))). Qed.
Lemma lem1012965 (m : nat) (p : nat) : (term64 m p) = (term64 m p).
Proof. exact (fun_ext (fun d : nat => @lem1012964 m p d)). Qed.
Lemma lem1012966 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1012967 (m : nat) (p : nat) : (term65 m p) = (term65 m p).
Proof. exact (MK_COMB (@lem1012966) (@lem1012965 m p)). Qed.
Lemma lem1012968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1012969 (m : nat) (p : nat) : (term67 m p) = (term67 m p).
Proof. exact (MK_COMB (@lem1012968) (@lem1012967 m p)). Qed.
Lemma lem1012970 (m : nat) (p : nat) : (term79 m p) = (term79 m p).
Proof. exact (MK_COMB (@lem1012969 m p) (@lem1012963 m p)). Qed.
Lemma lem1012971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1012972 (m : nat) (p : nat) : (term82 m p) = (term82 m p).
Proof. exact (MK_COMB (@lem1012971) (@lem1012970 m p)). Qed.
Lemma lem1012973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1012974 (m : nat) (p : nat) : (term90 m p) = (term90 m p).
Proof. exact (MK_COMB (@lem1012973) (@lem1012972 m p)). Qed.
Lemma lem1012975 (m : nat) (p : nat) : (term91 m p) = (term91 m p).
Proof. exact (MK_COMB (@lem1012974 m p) (@lem1012959)). Qed.
Lemma lem1012976 (p : nat) : (term93 p) = (term93 p).
Proof. exact (fun_ext (fun m : nat => @lem1012975 m p)). Qed.
Lemma lem1012977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012978 (p : nat) : (term95 p) = (term95 p).
Proof. exact (MK_COMB (@lem1012977) (@lem1012976 p)). Qed.
Lemma lem1012979 : term97 = term97.
Proof. exact (fun_ext (fun p : nat => @lem1012978 p)). Qed.
Lemma lem1012980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1012981 : term99 = term99.
Proof. exact (MK_COMB (@lem1012980) (@lem1012979)). Qed.
Lemma lem1013024 : term98 = term99.
Proof. exact (TRANS (@lem1012950) (@lem1012981)). Qed.
Lemma lem1013025 : term99 = term98.
Proof. exact (SYM (@lem1013024)). Qed.
Lemma lem1013026 (m : nat) (p : nat) (h1 : term82 m p) : term82 m p.
Proof. exact (h1). Qed.
Lemma lem1013027 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1013029 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1013030 (m : nat) (p : nat) : (term105 m p) = (term106 m p).
Proof. exact (@lem1013029 (term64 m p)). Qed.
Lemma lem1013031 (m : nat) (p : nat) (d : nat) : (term107 m p d) = ((term7 m p) = (term7 p d)).
Proof. exact (eq_refl (term107 m p d)). Qed.
Lemma lem1013032 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1013034 (m : nat) (p : nat) (d : nat) : (term108 m p d) = (term109 m p d).
Proof. exact (MK_COMB (@lem1013032) (@lem1013031 m p d)). Qed.
Lemma lem1013035 (m : nat) (p : nat) : (term110 m p) = (term111 m p).
Proof. exact (fun_ext (fun d : nat => @lem1013034 m p d)). Qed.
Lemma lem1013036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013037 (m : nat) (p : nat) : (term106 m p) = (term112 m p).
Proof. exact (MK_COMB (@lem1013036) (@lem1013035 m p)). Qed.
Lemma lem1013038 (m : nat) (p : nat) : (term105 m p) = (term112 m p).
Proof. exact (TRANS (@lem1013030 m p) (@lem1013037 m p)). Qed.
Lemma lem1013040 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1013041 (m : nat) (p : nat) : (term113 m p) = (term114 m p).
Proof. exact (@lem1013040 (term77 m p)). Qed.
Lemma lem1013042 (m : nat) (p : nat) (d : nat) : (term115 m p d) = (p = (term75 m p d)).
Proof. exact (eq_refl (term115 m p d)). Qed.
Lemma lem1013043 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1013045 (m : nat) (p : nat) (d : nat) : (term116 m p d) = (term117 m p d).
Proof. exact (MK_COMB (@lem1013043) (@lem1013042 m p d)). Qed.
Lemma lem1013046 (m : nat) (p : nat) : (term118 m p) = (term119 m p).
Proof. exact (fun_ext (fun d : nat => @lem1013045 m p d)). Qed.
Lemma lem1013047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013048 (m : nat) (p : nat) : (term114 m p) = (term120 m p).
Proof. exact (MK_COMB (@lem1013047) (@lem1013046 m p)). Qed.
Lemma lem1013049 (m : nat) (p : nat) : (term113 m p) = (term120 m p).
Proof. exact (TRANS (@lem1013041 m p) (@lem1013048 m p)). Qed.
Lemma lem1013050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1013051 (m : nat) (p : nat) : (term121 m p) = (term122 m p).
Proof. exact (MK_COMB (@lem1013050) (@lem1013038 m p)). Qed.
Lemma lem1013052 (m : nat) (p : nat) : (term123 m p) = (term124 m p).
Proof. exact (MK_COMB (@lem1013051 m p) (@lem1013049 m p)). Qed.
Lemma lem1013053 (m : nat) (p : nat) : (term82 m p) = (term123 m p).
Proof. exact (@lem17160 (term65 m p) (term78 m p)). Qed.
Lemma lem1013066 (m : nat) (p : nat) : (term82 m p) = (term124 m p).
Proof. exact (TRANS (@lem1013053 m p) (@lem1013052 m p)). Qed.
Lemma lem1013067 (m : nat) (p : nat) (h1 : term82 m p) : term124 m p.
Proof. exact (EQ_MP (@lem1013066 m p) (@lem1013026 m p h1)). Qed.
Lemma lem1013068 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1013069 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1013068 n m)). Qed.
Lemma lem1013070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013071 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1013070) (@lem1013069 m)). Qed.
Lemma lem1013072 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1013071 m)). Qed.
Lemma lem1013073 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013086 : term89 = term89.
Proof. exact (MK_COMB (@lem1013073) (@lem1013072)). Qed.
Lemma lem1013087 (h1 : term89) : term89.
Proof. exact (EQ_MP (@lem1013086) (@lem1013027 h1)). Qed.
Lemma lem1013106 (m : nat) (p : nat) (d : nat) : (term117 m p d) = (term117 m p d).
Proof. exact (eq_refl (term117 m p d)). Qed.
Lemma lem1013107 (m : nat) (p : nat) : (term119 m p) = (term119 m p).
Proof. exact (fun_ext (fun d : nat => @lem1013106 m p d)). Qed.
Lemma lem1013108 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013109 (m : nat) (p : nat) : (term120 m p) = (term120 m p).
Proof. exact (MK_COMB (@lem1013108) (@lem1013107 m p)). Qed.
Lemma lem1013128 (m : nat) (p : nat) (d : nat) : (term109 m p d) = (term109 m p d).
Proof. exact (eq_refl (term109 m p d)). Qed.
Lemma lem1013129 (m : nat) (p : nat) : (term111 m p) = (term111 m p).
Proof. exact (fun_ext (fun d : nat => @lem1013128 m p d)). Qed.
Lemma lem1013130 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013131 (m : nat) (p : nat) : (term112 m p) = (term112 m p).
Proof. exact (MK_COMB (@lem1013130) (@lem1013129 m p)). Qed.
Lemma lem1013132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1013133 (m : nat) (p : nat) : (term122 m p) = (term122 m p).
Proof. exact (MK_COMB (@lem1013132) (@lem1013131 m p)). Qed.
Lemma lem1013134 (m : nat) (p : nat) : (term124 m p) = (term124 m p).
Proof. exact (MK_COMB (@lem1013133 m p) (@lem1013109 m p)). Qed.
Lemma lem1013135 (m : nat) (p : nat) (h1 : term82 m p) : term124 m p.
Proof. exact (EQ_MP (@lem1013134 m p) (@lem1013067 m p h1)). Qed.
Lemma lem1013148 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1013149 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1013148 n m)). Qed.
Lemma lem1013150 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013151 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1013150) (@lem1013149 m)). Qed.
Lemma lem1013152 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1013151 m)). Qed.
Lemma lem1013153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013154 : term89 = term89.
Proof. exact (MK_COMB (@lem1013153) (@lem1013152)). Qed.
Lemma lem1013155 (h1 : term89) : term89.
Proof. exact (EQ_MP (@lem1013154) (@lem1013087 h1)). Qed.
Lemma lem1013157 (m : nat) (p : nat) (h1 : term82 m p) : term112 m p.
Proof. exact (proj1 (@lem1013135 m p h1)). Qed.
Lemma lem1013159 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem1013160 (m : nat) : (term100 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem1013159 n m)). Qed.
Lemma lem1013161 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013162 (m : nat) : (term101 m) = (term101 m).
Proof. exact (MK_COMB (@lem1013161) (@lem1013160 m)). Qed.
Lemma lem1013163 : term102 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1013162 m)). Qed.
Lemma lem1013164 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013166 : term89 = term89.
Proof. exact (MK_COMB (@lem1013164) (@lem1013163)). Qed.
Lemma lem1013167 (h1 : term89) : term89.
Proof. exact (EQ_MP (@lem1013166) (@lem1013155 h1)). Qed.
Lemma lem1013169 (m : nat) (p : nat) (d : nat) : (term109 m p d) = (term109 m p d).
Proof. exact (eq_refl (term109 m p d)). Qed.
Lemma lem1013170 (m : nat) (p : nat) : (term111 m p) = (term111 m p).
Proof. exact (fun_ext (fun d : nat => @lem1013169 m p d)). Qed.
Lemma lem1013171 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1013173 (m : nat) (p : nat) : (term112 m p) = (term112 m p).
Proof. exact (MK_COMB (@lem1013171) (@lem1013170 m p)). Qed.
Lemma lem1013174 (m : nat) (p : nat) (h1 : term82 m p) : term112 m p.
Proof. exact (EQ_MP (@lem1013173 m p) (@lem1013157 m p h1)). Qed.
Lemma lem1013182 (_16461 : nat) (h1 : term89) : term125 _16461.
Proof. exact (@lem1013167 h1 _16461). Qed.
Lemma lem1013183 (_16461 : nat) : (term125 _16461) = (term101 _16461).
Proof. exact (eq_refl (term125 _16461)). Qed.
Lemma lem1013184 (_16461 : nat) (h1 : term89) : term101 _16461.
Proof. exact (EQ_MP (@lem1013183 _16461) (@lem1013182 _16461 h1)). Qed.
Lemma lem1013185 (_16461 : nat) (_16462 : nat) (h1 : term89) : term126 _16461 _16462.
Proof. exact (@lem1013184 _16461 h1 _16462). Qed.
Lemma lem1013186 (_16462 : nat) (_16461 : nat) : (term126 _16461 _16462) = ((Nat.add _16461 _16462) = (Nat.add _16462 _16461)).
Proof. exact (eq_refl (term126 _16461 _16462)). Qed.
Lemma lem1013188 (_16463 : nat) (m : nat) (p : nat) (h1 : term82 m p) : term127 m p _16463.
Proof. exact (@lem1013174 m p h1 _16463). Qed.
Lemma lem1013189 (m : nat) (p : nat) (_16463 : nat) : (term127 m p _16463) = (term109 m p _16463).
Proof. exact (eq_refl (term127 m p _16463)). Qed.
Lemma lem1013197 (_16463 : nat) (m : nat) (p : nat) (h1 : term82 m p) : term109 m p _16463.
Proof. exact (EQ_MP (@lem1013189 m p _16463) (@lem1013188 _16463 m p h1)). Qed.
Lemma lem1013200 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1013201 (_16465 : nat) (_16466 : nat) (h1 : _16465 = _16466) : _16465 = _16466.
Proof. exact (h1). Qed.
Lemma lem1013202 (_16465 : nat) (_16466 : nat) (h1 : _16465 = _16466) : (S _16465) = (S _16466).
Proof. exact (MK_COMB (@lem1013200) (@lem1013201 _16465 _16466 h1)). Qed.
Lemma lem1013203 (_16465 : nat) (_16466 : nat) : term128 _16465 _16466.
Proof. exact (fun h0 : _16465 = _16466 => @lem1013202 _16465 _16466 h0). Qed.
Lemma lem1013205 (a : Prop) (b : Prop) : (a -> b) = (term129 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1013206 (_16465 : nat) (_16466 : nat) : (term128 _16465 _16466) = (term130 _16465 _16466).
Proof. exact (@lem1013205 (_16465 = _16466) ((S _16465) = (S _16466))). Qed.
Lemma lem1013207 (_16465 : nat) (_16466 : nat) : term130 _16465 _16466.
Proof. exact (EQ_MP (@lem1013206 _16465 _16466) (@lem1013203 _16465 _16466)). Qed.
Lemma lem1013226 (_16462 : nat) (_16461 : nat) (h1 : term89) : (Nat.add _16461 _16462) = (Nat.add _16462 _16461).
Proof. exact (EQ_MP (@lem1013186 _16462 _16461) (@lem1013185 _16461 _16462 h1)). Qed.
Lemma lem1013227 (p : nat) (m : nat) (h1 : term89) : (Nat.add m p) = (Nat.add p m).
Proof. exact (@lem1013226 p m h1). Qed.
Lemma lem1013228 (p : nat) (m : nat) (h1 : term89) : term131 p m.
Proof. exact (fun h0 : term132 p m => @lem1013227 p m h1). Qed.
Lemma lem1013230 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1013231 (p : nat) (m : nat) : (term131 p m) = ((Nat.add m p) = (Nat.add p m)).
Proof. exact (@lem1013230 ((Nat.add m p) = (Nat.add p m))). Qed.
Lemma lem1013232 (p : nat) (m : nat) (h1 : term89) : (Nat.add m p) = (Nat.add p m).
Proof. exact (EQ_MP (@lem1013231 p m) (@lem1013228 p m h1)). Qed.
Lemma lem1013238 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1013239 (_16465 : nat) (_16466 : nat) : (term130 _16465 _16466) = (term134 _16465 _16466).
Proof. exact (@lem1013238 ((S _16465) = (S _16466)) (term135 _16465 _16466)). Qed.
Lemma lem1013249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1013250 (_16465 : nat) (_16466 : nat) : (term136 _16465 _16466) = (term137 _16465 _16466).
Proof. exact (MK_COMB (@lem1013249) (@lem1013239 _16465 _16466)). Qed.
Lemma lem1013260 (_16465 : nat) (_16466 : nat) : (term134 _16465 _16466) = (term134 _16465 _16466).
Proof. exact (eq_refl (term134 _16465 _16466)). Qed.
Lemma lem1013261 (_16465 : nat) (_16466 : nat) : ((term130 _16465 _16466) = (term134 _16465 _16466)) = ((term134 _16465 _16466) = (term134 _16465 _16466)).
Proof. exact (MK_COMB (@lem1013250 _16465 _16466) (@lem1013260 _16465 _16466)). Qed.
Lemma lem1013263 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1013264 (x : Prop) : (x = x) = True.
Proof. exact (@lem1013263 Prop x). Qed.
Lemma lem1013265 (_16465 : nat) (_16466 : nat) : ((term134 _16465 _16466) = (term134 _16465 _16466)) = True.
Proof. exact (@lem1013264 (term134 _16465 _16466)). Qed.
Lemma lem1013266 (_16465 : nat) (_16466 : nat) : ((term130 _16465 _16466) = (term134 _16465 _16466)) = True.
Proof. exact (TRANS (@lem1013261 _16465 _16466) (@lem1013265 _16465 _16466)). Qed.
Lemma lem1013267 (_16465 : nat) (_16466 : nat) : True = ((term130 _16465 _16466) = (term134 _16465 _16466)).
Proof. exact (SYM (@lem1013266 _16465 _16466)). Qed.
Lemma lem1013268 (_16465 : nat) (_16466 : nat) : (term130 _16465 _16466) = (term134 _16465 _16466).
Proof. exact (EQ_MP (@lem1013267 _16465 _16466) (@lem0)). Qed.
Lemma lem1013269 (_16465 : nat) (_16466 : nat) : term134 _16465 _16466.
Proof. exact (EQ_MP (@lem1013268 _16465 _16466) (@lem1013207 _16465 _16466)). Qed.
Lemma lem1013271 (b : Prop) (a : Prop) : (a \/ b) = (term138 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1013272 (_16465 : nat) (_16466 : nat) : (term134 _16465 _16466) = (term139 _16465 _16466).
Proof. exact (@lem1013271 (term135 _16465 _16466) ((S _16465) = (S _16466))). Qed.
Lemma lem1013274 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1013275 (_16465 : nat) (_16466 : nat) : (term141 _16465 _16466) = (_16465 = _16466).
Proof. exact (@lem1013274 (_16465 = _16466)). Qed.
Lemma lem1013276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1013277 (_16465 : nat) (_16466 : nat) : (term142 _16465 _16466) = (term143 _16465 _16466).
Proof. exact (MK_COMB (@lem1013276) (@lem1013275 _16465 _16466)). Qed.
Lemma lem1013278 (_16465 : nat) (_16466 : nat) : ((S _16465) = (S _16466)) = ((S _16465) = (S _16466)).
Proof. exact (eq_refl ((S _16465) = (S _16466))). Qed.
Lemma lem1013279 (_16465 : nat) (_16466 : nat) : (term139 _16465 _16466) = (term128 _16465 _16466).
Proof. exact (MK_COMB (@lem1013277 _16465 _16466) (@lem1013278 _16465 _16466)). Qed.
Lemma lem1013280 (_16465 : nat) (_16466 : nat) : (term134 _16465 _16466) = (term128 _16465 _16466).
Proof. exact (TRANS (@lem1013272 _16465 _16466) (@lem1013279 _16465 _16466)). Qed.
Lemma lem1013283 (_16465 : nat) (_16466 : nat) : term128 _16465 _16466.
Proof. exact (EQ_MP (@lem1013280 _16465 _16466) (@lem1013269 _16465 _16466)). Qed.
Lemma lem1013284 (p : nat) (m : nat) : term144 p m.
Proof. exact (@lem1013283 (Nat.add m p) (Nat.add p m)). Qed.
Lemma lem1013287 (p : nat) (m : nat) (h1 : term89) : (term7 m p) = (term7 p m).
Proof. exact (@lem1013284 p m (@lem1013232 p m h1)). Qed.
Lemma lem1013288 (p : nat) (m : nat) (h1 : term89) : term145 p m.
Proof. exact (fun h0 : term146 p m => @lem1013287 p m h1). Qed.
Lemma lem1013290 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1013291 (p : nat) (m : nat) : (term145 p m) = ((term7 m p) = (term7 p m)).
Proof. exact (@lem1013290 ((term7 m p) = (term7 p m))). Qed.
Lemma lem1013292 (p : nat) (m : nat) (h1 : term89) : (term7 m p) = (term7 p m).
Proof. exact (EQ_MP (@lem1013291 p m) (@lem1013288 p m h1)). Qed.
Lemma lem1013295 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1013297 (m : nat) (p : nat) (_16463 : nat) : (term109 m p _16463) = (term147 m p _16463).
Proof. exact (@lem1013295 ((term7 m p) = (term7 p _16463))). Qed.
Lemma lem1013300 (_16463 : nat) (m : nat) (p : nat) (h1 : term82 m p) : term147 m p _16463.
Proof. exact (EQ_MP (@lem1013297 m p _16463) (@lem1013197 _16463 m p h1)). Qed.
Lemma lem1013301 (m : nat) (p : nat) (h1 : term82 m p) : term148 p m.
Proof. exact (@lem1013300 m m p h1). Qed.
Lemma lem1013304 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : False.
Proof. exact (@lem1013301 m p h2 (@lem1013292 p m h1)). Qed.
Lemma lem1013305 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : term149.
Proof. exact (fun h0 : ~ False => @lem1013304 m p h1 h2). Qed.
Lemma lem1013307 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1013308 : term149 = False.
Proof. exact (@lem1013307 False). Qed.
Lemma lem1013309 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : False.
Proof. exact (EQ_MP (@lem1013308) (@lem1013305 m p h1 h2)). Qed.
Lemma lem1013310 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : term89 = False.
Proof. exact (prop_ext (fun h3 : term89 => @lem1013309 m p h1 h2) (fun h3 : False => @lem1013167 h1)). Qed.
Lemma lem1013311 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : False.
Proof. exact (EQ_MP (@lem1013310 m p h1 h2) (@lem1013167 h1)). Qed.
Lemma lem1013312 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : term89 = False.
Proof. exact (prop_ext (fun h3 : term89 => @lem1013311 m p h1 h2) (fun h3 : False => @lem1013155 h1)). Qed.
Lemma lem1013313 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : False.
Proof. exact (EQ_MP (@lem1013312 m p h1 h2) (@lem1013155 h1)). Qed.
Lemma lem1013314 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : term89 = False.
Proof. exact (prop_ext (fun h3 : term89 => @lem1013313 m p h1 h2) (fun h3 : False => @lem1013087 h1)). Qed.
Lemma lem1013315 (m : nat) (p : nat) (h1 : term89) (h2 : term82 m p) : False.
Proof. exact (EQ_MP (@lem1013314 m p h1 h2) (@lem1013087 h1)). Qed.
Lemma lem1013316 (m : nat) (p : nat) (h1 : term82 m p) : term87.
Proof. exact (fun h0 : term89 => @lem1013315 m p h0 h1). Qed.
Lemma lem1013317 : term87 = term88.
Proof. exact (@lem69 term89). Qed.
Lemma lem1013318 (m : nat) (p : nat) (h1 : term82 m p) : term88.
Proof. exact (EQ_MP (@lem1013317) (@lem1013316 m p h1)). Qed.
Lemma lem1013319 (m : nat) (p : nat) : term91 m p.
Proof. exact (fun h0 : term82 m p => @lem1013318 m p h0). Qed.
Lemma lem1013324 (p : nat) : term95 p.
Proof. exact (fun m : nat => @lem1013319 m p). Qed.
Lemma lem1013329 : term99.
Proof. exact (fun p : nat => @lem1013324 p). Qed.
Lemma lem1013330 : term98.
Proof. exact (EQ_MP (@lem1013025) (@lem1013329)). Qed.
Lemma lem1013331 (p : nat) : term150 p.
Proof. exact (@lem1013330 p). Qed.
Lemma lem1013332 (p : nat) : (term150 p) = (term94 p).
Proof. exact (eq_refl (term150 p)). Qed.
Lemma lem1013333 (p : nat) : term94 p.
Proof. exact (EQ_MP (@lem1013332 p) (@lem1013331 p)). Qed.
Lemma lem1013334 (p : nat) (m : nat) : term151 p m.
Proof. exact (@lem1013333 p m). Qed.
Lemma lem1013335 (m : nat) (p : nat) : (term151 p m) = (term83 m p).
Proof. exact (eq_refl (term151 p m)). Qed.
Lemma lem1013336 (m : nat) (p : nat) : term83 m p.
Proof. exact (EQ_MP (@lem1013335 m p) (@lem1013334 p m)). Qed.
Lemma lem1013338 (m : nat) (p : nat) : term83 m p.
Proof. exact (@lem1012897 m p (@lem1013336 m p)). Qed.
Lemma lem1013339 (m : nat) (p : nat) (h1 : term82 m p) : term87.
Proof. exact (@lem1013338 m p (@lem1012882 m p h1)). Qed.
Lemma lem1013340 (m : nat) (p : nat) (h1 : term82 m p) : False.
Proof. exact (@lem1013339 m p h1 (@lem77775)). Qed.
Lemma lem1013341 (m : nat) (p : nat) (h1 : term82 m p) : (term82 m p) = False.
Proof. exact (prop_ext (fun h2 : term82 m p => @lem1013340 m p h1) (fun h2 : False => @lem1012882 m p h1)). Qed.
Lemma lem1013342 (m : nat) (p : nat) (h1 : term82 m p) : False.
Proof. exact (EQ_MP (@lem1013341 m p h1) (@lem1012882 m p h1)). Qed.
Lemma lem1013343 (m : nat) (p : nat) : term81 m p.
Proof. exact (fun h0 : term82 m p => @lem1013342 m p h0). Qed.
Lemma lem1013344 (m : nat) (p : nat) : term79 m p.
Proof. exact (EQ_MP (@lem1012881 m p) (@lem1013343 m p)). Qed.
Lemma lem1013345 (m : nat) (p : nat) : term58 m p.
Proof. exact (EQ_MP (@lem1012877 m p) (@lem1013344 m p)). Qed.
Lemma lem1013346 (m : nat) (p : nat) : ((term40 m p) = (NUMERAL p)) = False.
Proof. exact (EQ_MP (@lem1012807 m p) (@lem1013345 m p)). Qed.
Lemma lem1013347 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : ((NUMERAL n) = (NUMERAL p)) = False.
Proof. exact (EQ_MP (@lem1012763 m p n h1) (@lem1013346 m p)). Qed.
Lemma lem1013350 (m : nat) (n : nat) (p : nat) : term152 m n p.
Proof. exact (fun h0 : (term7 m p) = n => @lem1013347 m p n h0). Qed.
Lemma lem1013351 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : (term7 m p) = n.
Proof. exact (h1). Qed.
Lemma lem1013352 (m : nat) (p : nat) (n : nat) (h1 : (term7 m p) = n) : ((NUMERAL n) = (NUMERAL p)) = False.
Proof. exact (@lem1013350 m n p (@lem1013351 m p n h1)). Qed.
