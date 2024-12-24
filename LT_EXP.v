Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_EXP_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DE_MORGAN_THM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXP_LT_0_spec.
Require Import EXP_ONE_spec.
Require Import LE_EXISTS_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import LTE_TRANS_spec.
Require Import LT_0_spec.
Require Import LT_ADD_spec.
Require Import LT_EXISTS_spec.
Require Import LT_REFL_spec.
Require Import MULT_2_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import NOT_SUC_spec.
Require Import ONE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10568_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80360_spec.
Require Import thm80550_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Require Import thm89994_spec.
Lemma lem146698 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem146699 (m : nat) : term1 m.
Proof. exact (@lem146698 m). Qed.
Lemma lem146700 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem146701 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem146700 m) (@lem146699 m)). Qed.
Lemma lem146702 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem146701 m n). Qed.
Lemma lem146703 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem146705 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem146706 (m : nat) : term7 m.
Proof. exact (@lem146705 m). Qed.
Lemma lem146707 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem146709 (m : nat) : term9 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem146710 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem146711 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem146710 m) (@lem146709 m)). Qed.
Lemma lem146712 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem146711 m n). Qed.
Lemma lem146713 (n : nat) (m : nat) : (term11 m n) = ((term12 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem146715 (m : nat) : term13 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem146716 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem146717 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem146716 m) (@lem146715 m)). Qed.
Lemma lem146718 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem146717 m n). Qed.
Lemma lem146719 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem146720 (m : nat) (n : nat) : term16 m n.
Proof. exact (EQ_MP (@lem146719 m n) (@lem146718 m n)). Qed.
Lemma lem146721 (m : nat) (n : nat) (p : nat) : term17 m n p.
Proof. exact (@lem146720 m n p). Qed.
Lemma lem146722 (m : nat) (n : nat) (p : nat) : (term17 m n p) = ((term18 n m p) = (term19 m n p)).
Proof. exact (eq_refl (term17 m n p)). Qed.
Lemma lem146724 (n : nat) : term20 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem146725 (n : nat) : (term20 n) = (Peano.le n n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem146726 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem146725 n) (@lem146724 n)). Qed.
Lemma lem146727 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem146729 : term21.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem146730 : term22.
Proof. exact (proj2 (@lem146729)). Qed.
Lemma lem146731 : term23.
Proof. exact (proj2 (@lem146730)). Qed.
Lemma lem146747 : term24.
Proof. exact (proj1 (@lem146731)). Qed.
Lemma lem146748 (m : nat) : term25 m.
Proof. exact (@lem146747 m). Qed.
Lemma lem146749 (m : nat) : (term25 m) = ((term26 m) = m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem146763 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem146764 (m : nat) (h1 : term27) : term28 m.
Proof. exact (@lem146763 h1 m). Qed.
Lemma lem146765 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem146766 (m : nat) (h1 : term27) : term29 m.
Proof. exact (EQ_MP (@lem146765 m) (@lem146764 m h1)). Qed.
Lemma lem146767 (m : nat) (n : nat) (h1 : term27) : term30 m n.
Proof. exact (@lem146766 m h1 n). Qed.
Lemma lem146768 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem146769 (n : nat) (m : nat) (h1 : term27) : term31 n m.
Proof. exact (EQ_MP (@lem146768 n m) (@lem146767 m n h1)). Qed.
Lemma lem146770 (n : nat) (m : nat) (p : nat) (h1 : term27) : term32 n m p.
Proof. exact (@lem146769 n m h1 p). Qed.
Lemma lem146771 (n : nat) (m : nat) (p : nat) : (term32 n m p) = (term33 n m p).
Proof. exact (eq_refl (term32 n m p)). Qed.
Lemma lem146772 (n : nat) (m : nat) (p : nat) (h1 : term27) : term33 n m p.
Proof. exact (EQ_MP (@lem146771 n m p) (@lem146770 n m p h1)). Qed.
Lemma lem146773 (m : nat) (n : nat) (p : nat) (h1 : term34 m n p) : term34 m n p.
Proof. exact (h1). Qed.
Lemma lem146774 (m : nat) (n : nat) (p : nat) (h1 : term27) (h2 : term34 m n p) : Peano.le m p.
Proof. exact (@lem146772 n m p h1 (@lem146773 m n p h2)). Qed.
Lemma lem146775 (m : nat) (n : nat) (p : nat) (h1 : term34 m n p) : term35 m p.
Proof. exact (fun h0 : term27 => @lem146774 m n p h0 h1). Qed.
Lemma lem146776 (m : nat) (p : nat) (h1 : term36 m p) : term36 m p.
Proof. exact (h1). Qed.
Lemma lem146777 (m : nat) (p : nat) (h1 : term36 m p) : term35 m p.
Proof. exact (ex_elim (@lem146776 m p h1) (fun n : nat => fun h0 : term37 m p n => @lem146775 m n p h0)). Qed.
Lemma lem146778 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem146779 (m : nat) (p : nat) (h1 : term27) (h2 : term36 m p) : Peano.le m p.
Proof. exact (@lem146777 m p h2 (@lem146778 h1)). Qed.
Lemma lem146780 (m : nat) (p : nat) (h1 : term27) : term38 m p.
Proof. exact (fun h0 : term36 m p => @lem146779 m p h1 h0). Qed.
Lemma lem146781 (m : nat) (h1 : term27) : term39 m.
Proof. exact (fun p : nat => @lem146780 m p h1). Qed.
Lemma lem146782 (h1 : term27) : term40.
Proof. exact (fun m : nat => @lem146781 m h1). Qed.
Lemma lem146783 : term41.
Proof. exact (fun h0 : term27 => @lem146782 h0). Qed.
Lemma lem146784 : term40.
Proof. exact (@lem146783 (@lem93743)). Qed.
Lemma lem146785 (m : nat) : term42 m.
Proof. exact (@lem146784 m). Qed.
Lemma lem146786 (m : nat) : (term42 m) = (term39 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem146787 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem146786 m) (@lem146785 m)). Qed.
Lemma lem146788 (m : nat) (p : nat) : term43 m p.
Proof. exact (@lem146787 m p). Qed.
Lemma lem146789 (m : nat) (p : nat) : (term43 m p) = (term38 m p).
Proof. exact (eq_refl (term43 m p)). Qed.
Lemma lem146791 (m : nat) : term44 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem146792 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem146793 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem146792 m) (@lem146791 m)). Qed.
Lemma lem146794 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem146793 m n). Qed.
Lemma lem146795 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem146796 (m : nat) (n : nat) : term47 m n.
Proof. exact (EQ_MP (@lem146795 m n) (@lem146794 m n)). Qed.
Lemma lem146797 (m : nat) (n : nat) (p : nat) : term48 m n p.
Proof. exact (@lem146796 m n p). Qed.
Lemma lem146798 (m : nat) (n : nat) (p : nat) : (term48 m n p) = ((term49 m n p) = (term50 m n p)).
Proof. exact (eq_refl (term48 m n p)). Qed.
Lemma lem146800 (m : nat) : term51 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem146801 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem146802 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem146801 m) (@lem146800 m)). Qed.
Lemma lem146803 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem146802 m n). Qed.
Lemma lem146804 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem146805 (m : nat) (n : nat) : term54 m n.
Proof. exact (EQ_MP (@lem146804 m n) (@lem146803 m n)). Qed.
Lemma lem146806 (m : nat) (n : nat) (p : nat) : term55 m n p.
Proof. exact (@lem146805 m n p). Qed.
Lemma lem146807 (m : nat) (n : nat) (p : nat) : (term55 m n p) = ((term56 m n p) = (term57 m n p)).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem146809 : term58.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem146810 (m : nat) : term59 m.
Proof. exact (@lem146809 m). Qed.
Lemma lem146811 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem146812 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem146811 m) (@lem146810 m)). Qed.
Lemma lem146813 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem146812 m n). Qed.
Lemma lem146814 (m : nat) (n : nat) : (term61 m n) = ((term62 m n) = (term63 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem146820 : term64.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem146821 : term65.
Proof. exact (proj2 (@lem146820)). Qed.
Lemma lem146822 : term66.
Proof. exact (proj2 (@lem146821)). Qed.
Lemma lem146823 (m : nat) : term67 m.
Proof. exact (@lem146822 m). Qed.
Lemma lem146824 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem146825 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem146824 m) (@lem146823 m)). Qed.
Lemma lem146826 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem146825 m n). Qed.
Lemma lem146827 (m : nat) (n : nat) : (term69 m n) = ((term70 m n) = (term71 m n)).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem146844 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem146845 (m : nat) (h1 : term72) : term73 m.
Proof. exact (@lem146844 h1 m). Qed.
Lemma lem146846 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem146847 (m : nat) (h1 : term72) : term74 m.
Proof. exact (EQ_MP (@lem146846 m) (@lem146845 m h1)). Qed.
Lemma lem146848 (m : nat) (n : nat) (h1 : term72) : term75 m n.
Proof. exact (@lem146847 m h1 n). Qed.
Lemma lem146849 (n : nat) (m : nat) : (term75 m n) = (term76 n m).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem146850 (n : nat) (m : nat) (h1 : term72) : term76 n m.
Proof. exact (EQ_MP (@lem146849 n m) (@lem146848 m n h1)). Qed.
Lemma lem146851 (n : nat) (m : nat) (p : nat) (h1 : term72) : term77 n m p.
Proof. exact (@lem146850 n m h1 p). Qed.
Lemma lem146852 (n : nat) (m : nat) (p : nat) : (term77 n m p) = (term78 n m p).
Proof. exact (eq_refl (term77 n m p)). Qed.
Lemma lem146853 (n : nat) (m : nat) (p : nat) (h1 : term72) : term78 n m p.
Proof. exact (EQ_MP (@lem146852 n m p) (@lem146851 n m p h1)). Qed.
Lemma lem146854 (m : nat) (n : nat) (p : nat) (h1 : term79 m n p) : term79 m n p.
Proof. exact (h1). Qed.
Lemma lem146855 (m : nat) (n : nat) (p : nat) (h1 : term72) (h2 : term79 m n p) : Peano.lt m p.
Proof. exact (@lem146853 n m p h1 (@lem146854 m n p h2)). Qed.
Lemma lem146856 (m : nat) (n : nat) (p : nat) (h1 : term79 m n p) : term80 m p.
Proof. exact (fun h0 : term72 => @lem146855 m n p h0 h1). Qed.
Lemma lem146857 (m : nat) (p : nat) (h1 : term81 m p) : term81 m p.
Proof. exact (h1). Qed.
Lemma lem146858 (m : nat) (p : nat) (h1 : term81 m p) : term80 m p.
Proof. exact (ex_elim (@lem146857 m p h1) (fun n : nat => fun h0 : term82 m p n => @lem146856 m n p h0)). Qed.
Lemma lem146859 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem146860 (m : nat) (p : nat) (h1 : term72) (h2 : term81 m p) : Peano.lt m p.
Proof. exact (@lem146858 m p h2 (@lem146859 h1)). Qed.
Lemma lem146861 (m : nat) (p : nat) (h1 : term72) : term83 m p.
Proof. exact (fun h0 : term81 m p => @lem146860 m p h1 h0). Qed.
Lemma lem146862 (m : nat) (h1 : term72) : term84 m.
Proof. exact (fun p : nat => @lem146861 m p h1). Qed.
Lemma lem146863 (h1 : term72) : term85.
Proof. exact (fun m : nat => @lem146862 m h1). Qed.
Lemma lem146864 : term86.
Proof. exact (fun h0 : term72 => @lem146863 h0). Qed.
Lemma lem146865 : term85.
Proof. exact (@lem146864 (@lem95941)). Qed.
Lemma lem146866 (m : nat) : term87 m.
Proof. exact (@lem146865 m). Qed.
Lemma lem146867 (m : nat) : (term87 m) = (term84 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem146868 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem146867 m) (@lem146866 m)). Qed.
Lemma lem146869 (m : nat) (p : nat) : term88 m p.
Proof. exact (@lem146868 m p). Qed.
Lemma lem146870 (m : nat) (p : nat) : (term88 m p) = (term83 m p).
Proof. exact (eq_refl (term88 m p)). Qed.
Lemma lem146872 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem146873 (m : nat) (h1 : term72) : term73 m.
Proof. exact (@lem146872 h1 m). Qed.
Lemma lem146874 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem146875 (m : nat) (h1 : term72) : term74 m.
Proof. exact (EQ_MP (@lem146874 m) (@lem146873 m h1)). Qed.
Lemma lem146876 (m : nat) (n : nat) (h1 : term72) : term75 m n.
Proof. exact (@lem146875 m h1 n). Qed.
Lemma lem146877 (n : nat) (m : nat) : (term75 m n) = (term76 n m).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem146878 (n : nat) (m : nat) (h1 : term72) : term76 n m.
Proof. exact (EQ_MP (@lem146877 n m) (@lem146876 m n h1)). Qed.
Lemma lem146879 (n : nat) (m : nat) (p : nat) (h1 : term72) : term77 n m p.
Proof. exact (@lem146878 n m h1 p). Qed.
Lemma lem146880 (n : nat) (m : nat) (p : nat) : (term77 n m p) = (term78 n m p).
Proof. exact (eq_refl (term77 n m p)). Qed.
Lemma lem146881 (n : nat) (m : nat) (p : nat) (h1 : term72) : term78 n m p.
Proof. exact (EQ_MP (@lem146880 n m p) (@lem146879 n m p h1)). Qed.
Lemma lem146882 (m : nat) (n : nat) (p : nat) (h1 : term79 m n p) : term79 m n p.
Proof. exact (h1). Qed.
Lemma lem146883 (m : nat) (n : nat) (p : nat) (h1 : term72) (h2 : term79 m n p) : Peano.lt m p.
Proof. exact (@lem146881 n m p h1 (@lem146882 m n p h2)). Qed.
Lemma lem146884 (m : nat) (n : nat) (p : nat) (h1 : term79 m n p) : term80 m p.
Proof. exact (fun h0 : term72 => @lem146883 m n p h0 h1). Qed.
Lemma lem146885 (m : nat) (p : nat) (h1 : term81 m p) : term81 m p.
Proof. exact (h1). Qed.
Lemma lem146886 (m : nat) (p : nat) (h1 : term81 m p) : term80 m p.
Proof. exact (ex_elim (@lem146885 m p h1) (fun n : nat => fun h0 : term82 m p n => @lem146884 m n p h0)). Qed.
Lemma lem146887 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem146888 (m : nat) (p : nat) (h1 : term72) (h2 : term81 m p) : Peano.lt m p.
Proof. exact (@lem146886 m p h2 (@lem146887 h1)). Qed.
Lemma lem146889 (m : nat) (p : nat) (h1 : term72) : term83 m p.
Proof. exact (fun h0 : term81 m p => @lem146888 m p h1 h0). Qed.
Lemma lem146890 (m : nat) (h1 : term72) : term84 m.
Proof. exact (fun p : nat => @lem146889 m p h1). Qed.
Lemma lem146891 (h1 : term72) : term85.
Proof. exact (fun m : nat => @lem146890 m h1). Qed.
Lemma lem146892 : term86.
Proof. exact (fun h0 : term72 => @lem146891 h0). Qed.
Lemma lem146893 : term85.
Proof. exact (@lem146892 (@lem95941)). Qed.
Lemma lem146894 (m : nat) : term87 m.
Proof. exact (@lem146893 m). Qed.
Lemma lem146895 (m : nat) : (term87 m) = (term84 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem146896 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem146895 m) (@lem146894 m)). Qed.
Lemma lem146897 (m : nat) (p : nat) : term88 m p.
Proof. exact (@lem146896 m p). Qed.
Lemma lem146898 (m : nat) (p : nat) : (term88 m p) = (term83 m p).
Proof. exact (eq_refl (term88 m p)). Qed.
Lemma lem146900 : term58.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem146901 (m : nat) : term59 m.
Proof. exact (@lem146900 m). Qed.
Lemma lem146902 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem146903 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem146902 m) (@lem146901 m)). Qed.
Lemma lem146904 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem146903 m n). Qed.
Lemma lem146905 (m : nat) (n : nat) : (term61 m n) = ((term62 m n) = (term63 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem146911 : term64.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem146912 : term65.
Proof. exact (proj2 (@lem146911)). Qed.
Lemma lem146913 : term66.
Proof. exact (proj2 (@lem146912)). Qed.
Lemma lem146914 (m : nat) : term67 m.
Proof. exact (@lem146913 m). Qed.
Lemma lem146915 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem146916 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem146915 m) (@lem146914 m)). Qed.
Lemma lem146917 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem146916 m n). Qed.
Lemma lem146918 (m : nat) (n : nat) : (term69 m n) = ((term70 m n) = (term71 m n)).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem146927 : term89.
Proof. exact (proj1 (@lem146911)). Qed.
Lemma lem146928 (m : nat) : term90 m.
Proof. exact (@lem146927 m). Qed.
Lemma lem146929 (m : nat) : (term90 m) = ((term91 m) = m).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem146935 (m : nat) : term92 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem146936 (m : nat) : (term92 m) = (term93 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem146937 (m : nat) : term93 m.
Proof. exact (EQ_MP (@lem146936 m) (@lem146935 m)). Qed.
Lemma lem146938 (m : nat) (n : nat) : term94 m n.
Proof. exact (@lem146937 m n). Qed.
Lemma lem146939 (n : nat) (m : nat) : (term94 m n) = ((Peano.lt m n) = (term95 n m)).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem146941 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem146942 (m : nat) : term1 m.
Proof. exact (@lem146941 m). Qed.
Lemma lem146943 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem146944 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem146943 m) (@lem146942 m)). Qed.
Lemma lem146945 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem146944 m n). Qed.
Lemma lem146946 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem146948 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem146949 (m : nat) : term7 m.
Proof. exact (@lem146948 m). Qed.
Lemma lem146950 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem146952 (m : nat) : term9 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem146953 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem146954 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem146953 m) (@lem146952 m)). Qed.
Lemma lem146955 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem146954 m n). Qed.
Lemma lem146956 (n : nat) (m : nat) : (term11 m n) = ((term12 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem146958 (m : nat) : term44 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem146959 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem146960 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem146959 m) (@lem146958 m)). Qed.
Lemma lem146961 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem146960 m n). Qed.
Lemma lem146962 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem146963 (m : nat) (n : nat) : term47 m n.
Proof. exact (EQ_MP (@lem146962 m n) (@lem146961 m n)). Qed.
Lemma lem146964 (m : nat) (n : nat) (p : nat) : term48 m n p.
Proof. exact (@lem146963 m n p). Qed.
Lemma lem146965 (m : nat) (n : nat) (p : nat) : (term48 m n p) = ((term49 m n p) = (term50 m n p)).
Proof. exact (eq_refl (term48 m n p)). Qed.
Lemma lem146967 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem146968 (m : nat) (h1 : term27) : term28 m.
Proof. exact (@lem146967 h1 m). Qed.
Lemma lem146969 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem146970 (m : nat) (h1 : term27) : term29 m.
Proof. exact (EQ_MP (@lem146969 m) (@lem146968 m h1)). Qed.
Lemma lem146971 (m : nat) (n : nat) (h1 : term27) : term30 m n.
Proof. exact (@lem146970 m h1 n). Qed.
Lemma lem146972 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem146973 (n : nat) (m : nat) (h1 : term27) : term31 n m.
Proof. exact (EQ_MP (@lem146972 n m) (@lem146971 m n h1)). Qed.
Lemma lem146974 (n : nat) (m : nat) (p : nat) (h1 : term27) : term32 n m p.
Proof. exact (@lem146973 n m h1 p). Qed.
Lemma lem146975 (n : nat) (m : nat) (p : nat) : (term32 n m p) = (term33 n m p).
Proof. exact (eq_refl (term32 n m p)). Qed.
Lemma lem146976 (n : nat) (m : nat) (p : nat) (h1 : term27) : term33 n m p.
Proof. exact (EQ_MP (@lem146975 n m p) (@lem146974 n m p h1)). Qed.
Lemma lem146977 (m : nat) (n : nat) (p : nat) (h1 : term34 m n p) : term34 m n p.
Proof. exact (h1). Qed.
Lemma lem146978 (m : nat) (n : nat) (p : nat) (h1 : term27) (h2 : term34 m n p) : Peano.le m p.
Proof. exact (@lem146976 n m p h1 (@lem146977 m n p h2)). Qed.
Lemma lem146979 (m : nat) (n : nat) (p : nat) (h1 : term34 m n p) : term35 m p.
Proof. exact (fun h0 : term27 => @lem146978 m n p h0 h1). Qed.
Lemma lem146980 (m : nat) (p : nat) (h1 : term36 m p) : term36 m p.
Proof. exact (h1). Qed.
Lemma lem146981 (m : nat) (p : nat) (h1 : term36 m p) : term35 m p.
Proof. exact (ex_elim (@lem146980 m p h1) (fun n : nat => fun h0 : term37 m p n => @lem146979 m n p h0)). Qed.
Lemma lem146982 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem146983 (m : nat) (p : nat) (h1 : term27) (h2 : term36 m p) : Peano.le m p.
Proof. exact (@lem146981 m p h2 (@lem146982 h1)). Qed.
Lemma lem146984 (m : nat) (p : nat) (h1 : term27) : term38 m p.
Proof. exact (fun h0 : term36 m p => @lem146983 m p h1 h0). Qed.
Lemma lem146985 (m : nat) (h1 : term27) : term39 m.
Proof. exact (fun p : nat => @lem146984 m p h1). Qed.
Lemma lem146986 (h1 : term27) : term40.
Proof. exact (fun m : nat => @lem146985 m h1). Qed.
Lemma lem146987 : term41.
Proof. exact (fun h0 : term27 => @lem146986 h0). Qed.
Lemma lem146988 : term40.
Proof. exact (@lem146987 (@lem93743)). Qed.
Lemma lem146989 (m : nat) : term42 m.
Proof. exact (@lem146988 m). Qed.
Lemma lem146990 (m : nat) : (term42 m) = (term39 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem146991 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem146990 m) (@lem146989 m)). Qed.
Lemma lem146992 (m : nat) (p : nat) : term43 m p.
Proof. exact (@lem146991 m p). Qed.
Lemma lem146993 (m : nat) (p : nat) : (term43 m p) = (term38 m p).
Proof. exact (eq_refl (term43 m p)). Qed.
Lemma lem146995 (n : nat) : term20 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem146996 (n : nat) : (term20 n) = (Peano.le n n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem146997 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem146996 n) (@lem146995 n)). Qed.
Lemma lem146998 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem147000 : term58.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem147001 (m : nat) : term59 m.
Proof. exact (@lem147000 m). Qed.
Lemma lem147002 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem147003 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem147002 m) (@lem147001 m)). Qed.
Lemma lem147004 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem147003 m n). Qed.
Lemma lem147005 (m : nat) (n : nat) : (term61 m n) = ((term62 m n) = (term63 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem147011 : term64.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem147012 : term65.
Proof. exact (proj2 (@lem147011)). Qed.
Lemma lem147013 : term66.
Proof. exact (proj2 (@lem147012)). Qed.
Lemma lem147014 (m : nat) : term67 m.
Proof. exact (@lem147013 m). Qed.
Lemma lem147015 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem147016 (m : nat) : term68 m.
Proof. exact (EQ_MP (@lem147015 m) (@lem147014 m)). Qed.
Lemma lem147017 (m : nat) (n : nat) : term69 m n.
Proof. exact (@lem147016 m n). Qed.
Lemma lem147018 (m : nat) (n : nat) : (term69 m n) = ((term70 m n) = (term71 m n)).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem147027 : term89.
Proof. exact (proj1 (@lem147011)). Qed.
Lemma lem147028 (m : nat) : term90 m.
Proof. exact (@lem147027 m). Qed.
Lemma lem147029 (m : nat) : (term90 m) = ((term91 m) = m).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem147035 (m : nat) : term96 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem147036 (m : nat) : (term96 m) = (term97 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem147037 (m : nat) : term97 m.
Proof. exact (EQ_MP (@lem147036 m) (@lem147035 m)). Qed.
Lemma lem147038 (m : nat) (n : nat) : term98 m n.
Proof. exact (@lem147037 m n). Qed.
Lemma lem147039 (n : nat) (m : nat) : (term98 m n) = ((Peano.le m n) = (term99 n m)).
Proof. exact (eq_refl (term98 m n)). Qed.
Lemma lem147042 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem147043 (m : nat) : term1 m.
Proof. exact (@lem147042 m). Qed.
Lemma lem147044 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem147045 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem147044 m) (@lem147043 m)). Qed.
Lemma lem147046 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem147045 m n). Qed.
Lemma lem147047 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem147049 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem147050 (m : nat) : term7 m.
Proof. exact (@lem147049 m). Qed.
Lemma lem147051 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem147053 (m : nat) : term9 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem147054 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem147055 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem147054 m) (@lem147053 m)). Qed.
Lemma lem147056 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem147055 m n). Qed.
Lemma lem147057 (n : nat) (m : nat) : (term11 m n) = ((term12 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem147059 (t1 : Prop) : term100 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem147060 (t1 : Prop) : (term100 t1) = (term101 t1).
Proof. exact (eq_refl (term100 t1)). Qed.
Lemma lem147061 (t1 : Prop) : term101 t1.
Proof. exact (EQ_MP (@lem147060 t1) (@lem147059 t1)). Qed.
Lemma lem147062 (t1 : Prop) (t2 : Prop) : term102 t1 t2.
Proof. exact (@lem147061 t1 t2). Qed.
Lemma lem147063 (t1 : Prop) (t2 : Prop) : (term102 t1 t2) = (term103 t1 t2).
Proof. exact (eq_refl (term102 t1 t2)). Qed.
Lemma lem147064 (t1 : Prop) (t2 : Prop) : term103 t1 t2.
Proof. exact (EQ_MP (@lem147063 t1 t2) (@lem147062 t1 t2)). Qed.
Lemma lem147067 (m : nat) : term104 m.
Proof. exact (@lem98377 m). Qed.
Lemma lem147068 (m : nat) : (term104 m) = (term105 m).
Proof. exact (eq_refl (term104 m)). Qed.
Lemma lem147069 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem147068 m) (@lem147067 m)). Qed.
Lemma lem147070 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem147069 m n). Qed.
Lemma lem147071 (n : nat) (m : nat) : (term106 m n) = ((term107 m n) = (Peano.le n m)).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem147073 (n : nat) : term108 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem147074 (n : nat) : (term108 n) = (term109 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem147075 (n : nat) : term109 n.
Proof. exact (EQ_MP (@lem147074 n) (@lem147073 n)). Qed.
Lemma lem147076 (n : nat) : (term109 n) = ((term109 n) = True).
Proof. exact (@lem7 (term109 n)). Qed.
Lemma lem147089 (n : nat) : term110 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem147090 (n : nat) : (term110 n) = (term111 n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem147091 (n : nat) : term111 n.
Proof. exact (EQ_MP (@lem147090 n) (@lem147089 n)). Qed.
Lemma lem147092 (n : nat) : term112 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem147094 (n : nat) : term113 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem147095 (n : nat) : (term113 n) = (term114 n).
Proof. exact (eq_refl (term113 n)). Qed.
Lemma lem147096 (n : nat) : term114 n.
Proof. exact (EQ_MP (@lem147095 n) (@lem147094 n)). Qed.
Lemma lem147097 (n : nat) : term115 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem147140 : term116.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem147141 (n : nat) : term117 n.
Proof. exact (@lem147140 n). Qed.
Lemma lem147142 (n : nat) : (term117 n) = ((term118 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem147144 : term58.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem147145 (m : nat) : term59 m.
Proof. exact (@lem147144 m). Qed.
Lemma lem147146 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem147147 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem147146 m) (@lem147145 m)). Qed.
Lemma lem147148 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem147147 m n). Qed.
Lemma lem147149 (m : nat) (n : nat) : (term61 m n) = ((term62 m n) = (term63 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem147151 : term119.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem147152 (m : nat) : term120 m.
Proof. exact (@lem147151 m). Qed.
Lemma lem147153 (m : nat) : (term120 m) = ((term121 m) = term122).
Proof. exact (eq_refl (term120 m)). Qed.
Lemma lem147162 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem147163 (m : nat) : term7 m.
Proof. exact (@lem147162 m). Qed.
Lemma lem147164 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem147196 : term116.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem147197 (n : nat) : term117 n.
Proof. exact (@lem147196 n). Qed.
Lemma lem147198 (n : nat) : (term117 n) = ((term118 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem147200 (n : nat) : term113 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem147201 (n : nat) : (term113 n) = (term114 n).
Proof. exact (eq_refl (term113 n)). Qed.
Lemma lem147202 (n : nat) : term114 n.
Proof. exact (EQ_MP (@lem147201 n) (@lem147200 n)). Qed.
Lemma lem147203 (n : nat) : term115 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem147216 : term58.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem147217 (m : nat) : term59 m.
Proof. exact (@lem147216 m). Qed.
Lemma lem147218 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem147219 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem147218 m) (@lem147217 m)). Qed.
Lemma lem147220 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem147219 m n). Qed.
Lemma lem147221 (m : nat) (n : nat) : (term61 m n) = ((term62 m n) = (term63 m n)).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem147223 : term119.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem147224 (m : nat) : term120 m.
Proof. exact (@lem147223 m). Qed.
Lemma lem147225 (m : nat) : (term120 m) = ((term121 m) = term122).
Proof. exact (eq_refl (term120 m)). Qed.
Lemma lem147229 (n : nat) (m : nat) (h1 : (term107 m n) = (Peano.le n m)) : (term107 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem147230 (n : nat) (m : nat) (h1 : (term107 m n) = (Peano.le n m)) : (Peano.le n m) = (term107 m n).
Proof. exact (SYM (@lem147229 n m h1)). Qed.
Lemma lem147231 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term107 m n)) : (Peano.le n m) = (term107 m n).
Proof. exact (h1). Qed.
Lemma lem147232 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term107 m n)) : (term107 m n) = (Peano.le n m).
Proof. exact (SYM (@lem147231 m n h1)). Qed.
Lemma lem147233 (m : nat) (n : nat) : ((term107 m n) = (Peano.le n m)) = ((Peano.le n m) = (term107 m n)).
Proof. exact (prop_ext (fun h1 : (term107 m n) = (Peano.le n m) => @lem147230 n m h1) (fun h1 : (Peano.le n m) = (term107 m n) => @lem147232 m n h1)). Qed.
Lemma lem147234 (m : nat) : (term123 m) = (term124 m).
Proof. exact (fun_ext (fun n : nat => @lem147233 m n)). Qed.
Lemma lem147235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147236 (m : nat) : (term105 m) = (term125 m).
Proof. exact (MK_COMB (@lem147235) (@lem147234 m)). Qed.
Lemma lem147237 : term126 = term127.
Proof. exact (fun_ext (fun m : nat => @lem147236 m)). Qed.
Lemma lem147238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147239 : term128 = term129.
Proof. exact (MK_COMB (@lem147238) (@lem147237)). Qed.
Lemma lem147240 : term129.
Proof. exact (EQ_MP (@lem147239) (@lem98377)). Qed.
Lemma lem147241 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem147242 (m : nat) : term1 m.
Proof. exact (@lem147241 m). Qed.
Lemma lem147243 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem147244 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem147243 m) (@lem147242 m)). Qed.
Lemma lem147245 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem147244 m n). Qed.
Lemma lem147246 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem147248 : term6.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem147249 (m : nat) : term7 m.
Proof. exact (@lem147248 m). Qed.
Lemma lem147250 (m : nat) : (term7 m) = ((term8 m) = False).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem147252 (m : nat) : term130 m.
Proof. exact (@lem147240 m). Qed.
Lemma lem147253 (m : nat) : (term130 m) = (term125 m).
Proof. exact (eq_refl (term130 m)). Qed.
Lemma lem147254 (m : nat) : term125 m.
Proof. exact (EQ_MP (@lem147253 m) (@lem147252 m)). Qed.
Lemma lem147255 (m : nat) (n : nat) : term131 m n.
Proof. exact (@lem147254 m n). Qed.
Lemma lem147256 (m : nat) (n : nat) : (term131 m n) = ((Peano.le n m) = (term107 m n)).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem147258 (x : nat) : term132 x.
Proof. exact (@lem9784 (x = (NUMERAL 0))). Qed.
Lemma lem147259 (x : nat) : (term132 x) = (term133 x).
Proof. exact (eq_refl (term132 x)). Qed.
Lemma lem147260 (x : nat) : term133 x.
Proof. exact (EQ_MP (@lem147259 x) (@lem147258 x)). Qed.
Lemma lem147262 (x : nat) (h1 : term134 x) : term134 x.
Proof. exact (h1). Qed.
Lemma lem147266 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem147267 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem147268 (x : nat) (h1 : x = (NUMERAL 0)) : (Nat.pow x) = term135.
Proof. exact (MK_COMB (@lem147267) (@lem147266 x h1)). Qed.
Lemma lem147269 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem147270 (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (Nat.pow x m) = (term136 m).
Proof. exact (MK_COMB (@lem147268 x h1) (@lem147269 m)). Qed.
Lemma lem147271 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem147272 (m : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term137 x m) = (term138 m).
Proof. exact (MK_COMB (@lem147271) (@lem147270 m x h1)). Qed.
Lemma lem147274 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem147275 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem147276 (x : nat) (h1 : x = (NUMERAL 0)) : (Nat.pow x) = term135.
Proof. exact (MK_COMB (@lem147275) (@lem147274 x h1)). Qed.
Lemma lem147277 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem147278 (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (Nat.pow x n) = (term136 n).
Proof. exact (MK_COMB (@lem147276 x h1) (@lem147277 n)). Qed.
Lemma lem147279 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term139 m x n) = (term140 m n).
Proof. exact (MK_COMB (@lem147272 m x h1) (@lem147278 n x h1)). Qed.
Lemma lem147280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem147281 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term141 m x n) = (term142 m n).
Proof. exact (MK_COMB (@lem147280) (@lem147279 m n x h1)). Qed.
Lemma lem147287 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem147288 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem147289 (x : nat) (h1 : x = (NUMERAL 0)) : (term144 x) = term145.
Proof. exact (MK_COMB (@lem147288) (@lem147287 x h1)). Qed.
Lemma lem147290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147291 (x : nat) (h1 : x = (NUMERAL 0)) : (term146 x) = term147.
Proof. exact (MK_COMB (@lem147290) (@lem147289 x h1)). Qed.
Lemma lem147292 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem147293 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term148 x m n) = (term149 m n).
Proof. exact (MK_COMB (@lem147291 x h1) (@lem147292 m n)). Qed.
Lemma lem147296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147297 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term150 x m n) = (term151 m n).
Proof. exact (MK_COMB (@lem147296) (@lem147293 m n x h1)). Qed.
Lemma lem147303 (x : nat) (h1 : x = (NUMERAL 0)) : x = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem147304 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem147305 (x : nat) (h1 : x = (NUMERAL 0)) : (@eq nat x) = term152.
Proof. exact (MK_COMB (@lem147304) (@lem147303 x h1)). Qed.
Lemma lem147306 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem147307 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem147305 x h1) (@lem147306)). Qed.
Lemma lem147309 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem147310 (x : nat) : (x = x) = True.
Proof. exact (@lem147309 nat x). Qed.
Lemma lem147311 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem147310 (NUMERAL 0)). Qed.
Lemma lem147312 (x : nat) (h1 : x = (NUMERAL 0)) : (x = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem147307 x h1) (@lem147311)). Qed.
Lemma lem147313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147314 (x : nat) (h1 : x = (NUMERAL 0)) : (term153 x) = (and True).
Proof. exact (MK_COMB (@lem147313) (@lem147312 x h1)). Qed.
Lemma lem147321 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem147322 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term155 x m n) = (term156 m n).
Proof. exact (MK_COMB (@lem147314 x h1) (@lem147321 m n)). Qed.
Lemma lem147324 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem147325 (m : nat) (n : nat) : (term156 m n) = (term154 m n).
Proof. exact (@lem147324 (term154 m n)). Qed.
Lemma lem147332 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term155 x m n) = (term154 m n).
Proof. exact (TRANS (@lem147322 m n x h1) (@lem147325 m n)). Qed.
Lemma lem147333 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term157 x m n) = (term158 m n).
Proof. exact (MK_COMB (@lem147297 m n x h1) (@lem147332 m n x h1)). Qed.
Lemma lem147336 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term139 m x n) = (term157 x m n)) = ((term140 m n) = (term158 m n)).
Proof. exact (MK_COMB (@lem147281 m n x h1) (@lem147333 m n x h1)). Qed.
Lemma lem147339 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : ((term140 m n) = (term158 m n)) = ((term139 m x n) = (term157 x m n)).
Proof. exact (SYM (@lem147336 m n x h1)). Qed.
Lemma lem147340 (x : nat) : term159 x.
Proof. exact (@lem82 (x = (NUMERAL 0))). Qed.
Lemma lem147362 (x : nat) (h1 : term134 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem147340 x (@lem147262 x h1)). Qed.
Lemma lem147363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147364 (x : nat) (h1 : term134 x) : (term153 x) = (and False).
Proof. exact (MK_COMB (@lem147363) (@lem147362 x h1)). Qed.
Lemma lem147371 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem147372 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : (term155 x m n) = (term160 m n).
Proof. exact (MK_COMB (@lem147364 x h1) (@lem147371 m n)). Qed.
Lemma lem147374 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem147375 (m : nat) (n : nat) : (term160 m n) = False.
Proof. exact (@lem147374 (term154 m n)). Qed.
Lemma lem147376 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : (term155 x m n) = False.
Proof. exact (TRANS (@lem147372 m n x h1) (@lem147375 m n)). Qed.
Lemma lem147377 (x : nat) (m : nat) (n : nat) : (term150 x m n) = (term150 x m n).
Proof. exact (eq_refl (term150 x m n)). Qed.
Lemma lem147378 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : (term157 x m n) = (term161 x m n).
Proof. exact (MK_COMB (@lem147377 x m n) (@lem147376 m n x h1)). Qed.
Lemma lem147380 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem147381 (x : nat) (m : nat) (n : nat) : (term161 x m n) = (term148 x m n).
Proof. exact (@lem147380 (term148 x m n)). Qed.
Lemma lem147384 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : (term157 x m n) = (term148 x m n).
Proof. exact (TRANS (@lem147378 m n x h1) (@lem147381 x m n)). Qed.
Lemma lem147385 (m : nat) (x : nat) (n : nat) : (term141 m x n) = (term141 m x n).
Proof. exact (eq_refl (term141 m x n)). Qed.
Lemma lem147386 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : ((term139 m x n) = (term157 x m n)) = ((term139 m x n) = (term148 x m n)).
Proof. exact (MK_COMB (@lem147385 m x n) (@lem147384 m n x h1)). Qed.
Lemma lem147389 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : ((term139 m x n) = (term148 x m n)) = ((term139 m x n) = (term157 x m n)).
Proof. exact (SYM (@lem147386 m n x h1)). Qed.
Lemma lem147397 (m : nat) (n : nat) : (Peano.le n m) = (term107 m n).
Proof. exact (EQ_MP (@lem147256 m n) (@lem147255 m n)). Qed.
Lemma lem147398 : term145 = term162.
Proof. exact (@lem147397 (NUMERAL 0) term163). Qed.
Lemma lem147400 : term163 = term164.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem147402 : term122 = term165.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem147403 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem147404 : term164 = term166.
Proof. exact (MK_COMB (@lem147403) (@lem147402)). Qed.
Lemma lem147405 : term163 = term166.
Proof. exact (TRANS (@lem147400) (@lem147404)). Qed.
Lemma lem147406 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem147407 : term168 = term169.
Proof. exact (MK_COMB (@lem147406) (@lem147405)). Qed.
Lemma lem147409 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem147246 m n) (@lem147245 m n)). Qed.
Lemma lem147410 : term169 = term170.
Proof. exact (@lem147409 (NUMERAL 0) term165). Qed.
Lemma lem147416 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem147246 m n) (@lem147245 m n)). Qed.
Lemma lem147417 : term171 = term172.
Proof. exact (@lem147416 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem147421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem147422 (x : nat) : (x = x) = True.
Proof. exact (@lem147421 nat x). Qed.
Lemma lem147423 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem147422 (NUMERAL 0)). Qed.
Lemma lem147424 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147425 : term173 = (or True).
Proof. exact (MK_COMB (@lem147424) (@lem147423)). Qed.
Lemma lem147427 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem147250 m) (@lem147249 m)). Qed.
Lemma lem147428 : term174 = False.
Proof. exact (@lem147427 (NUMERAL 0)). Qed.
Lemma lem147429 : term172 = (True \/ False).
Proof. exact (MK_COMB (@lem147425) (@lem147428)). Qed.
Lemma lem147431 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem147432 : (True \/ False) = True.
Proof. exact (@lem147431 False). Qed.
Lemma lem147433 : term172 = True.
Proof. exact (TRANS (@lem147429) (@lem147432)). Qed.
Lemma lem147434 : term171 = True.
Proof. exact (TRANS (@lem147417) (@lem147433)). Qed.
Lemma lem147435 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem147436 : term170 = term176.
Proof. exact (MK_COMB (@lem147435) (@lem147434)). Qed.
Lemma lem147438 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem147439 : term176 = True.
Proof. exact (@lem147438 ((NUMERAL 0) = term165)). Qed.
Lemma lem147440 : term170 = True.
Proof. exact (TRANS (@lem147436) (@lem147439)). Qed.
Lemma lem147441 : term169 = True.
Proof. exact (TRANS (@lem147410) (@lem147440)). Qed.
Lemma lem147442 : term168 = True.
Proof. exact (TRANS (@lem147407) (@lem147441)). Qed.
Lemma lem147443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem147444 : term162 = (~ True).
Proof. exact (MK_COMB (@lem147443) (@lem147442)). Qed.
Lemma lem147446 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem147447 : term162 = False.
Proof. exact (TRANS (@lem147444) (@lem147446)). Qed.
Lemma lem147448 : term145 = False.
Proof. exact (TRANS (@lem147398) (@lem147447)). Qed.
Lemma lem147449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147450 : term147 = (and False).
Proof. exact (MK_COMB (@lem147449) (@lem147448)). Qed.
Lemma lem147451 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem147452 (m : nat) (n : nat) : (term149 m n) = (term177 m n).
Proof. exact (MK_COMB (@lem147450) (@lem147451 m n)). Qed.
Lemma lem147454 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem147455 (m : nat) (n : nat) : (term177 m n) = False.
Proof. exact (@lem147454 (Peano.lt m n)). Qed.
Lemma lem147456 (m : nat) (n : nat) : (term149 m n) = False.
Proof. exact (TRANS (@lem147452 m n) (@lem147455 m n)). Qed.
Lemma lem147457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147458 (m : nat) (n : nat) : (term151 m n) = (or False).
Proof. exact (MK_COMB (@lem147457) (@lem147456 m n)). Qed.
Lemma lem147465 (m : nat) (n : nat) : (term154 m n) = (term154 m n).
Proof. exact (eq_refl (term154 m n)). Qed.
Lemma lem147466 (m : nat) (n : nat) : (term158 m n) = (term178 m n).
Proof. exact (MK_COMB (@lem147458 m n) (@lem147465 m n)). Qed.
Lemma lem147468 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem147469 (m : nat) (n : nat) : (term178 m n) = (term154 m n).
Proof. exact (@lem147468 (term154 m n)). Qed.
Lemma lem147476 (m : nat) (n : nat) : (term158 m n) = (term154 m n).
Proof. exact (TRANS (@lem147466 m n) (@lem147469 m n)). Qed.
Lemma lem147477 (m : nat) (n : nat) : (term142 m n) = (term142 m n).
Proof. exact (eq_refl (term142 m n)). Qed.
Lemma lem147478 (m : nat) (n : nat) : ((term140 m n) = (term158 m n)) = ((term140 m n) = (term154 m n)).
Proof. exact (MK_COMB (@lem147477 m n) (@lem147476 m n)). Qed.
Lemma lem147481 (m : nat) (n : nat) : ((term140 m n) = (term154 m n)) = ((term140 m n) = (term158 m n)).
Proof. exact (SYM (@lem147478 m n)). Qed.
Lemma lem147483 (P : nat -> Prop) : term179 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem147484 (m : nat) : term180 m.
Proof. exact (@lem147483 (term181 m)). Qed.
Lemma lem147485 (m : nat) : (term182 m) = ((term183 m) = (term184 m)).
Proof. exact (eq_refl (term182 m)). Qed.
Lemma lem147486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147487 (m : nat) : (term185 m) = (term186 m).
Proof. exact (MK_COMB (@lem147486) (@lem147485 m)). Qed.
Lemma lem147488 (m : nat) (n : nat) : (term187 m n) = ((term140 m n) = (term154 m n)).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem147489 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147490 (m : nat) (n : nat) : (term188 m n) = (term189 m n).
Proof. exact (MK_COMB (@lem147489) (@lem147488 m n)). Qed.
Lemma lem147491 (m : nat) (n : nat) : (term190 m n) = ((term191 m n) = (term192 m n)).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem147492 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (MK_COMB (@lem147490 m n) (@lem147491 m n)). Qed.
Lemma lem147493 (m : nat) : (term195 m) = (term196 m).
Proof. exact (fun_ext (fun n : nat => @lem147492 m n)). Qed.
Lemma lem147494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147495 (m : nat) : (term197 m) = (term198 m).
Proof. exact (MK_COMB (@lem147494) (@lem147493 m)). Qed.
Lemma lem147496 (m : nat) : (term199 m) = (term200 m).
Proof. exact (MK_COMB (@lem147487 m) (@lem147495 m)). Qed.
Lemma lem147497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147498 (m : nat) : (term201 m) = (term202 m).
Proof. exact (MK_COMB (@lem147497) (@lem147496 m)). Qed.
Lemma lem147499 (m : nat) (n : nat) : (term187 m n) = ((term140 m n) = (term154 m n)).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem147500 (m : nat) : (term203 m) = (term181 m).
Proof. exact (fun_ext (fun n : nat => @lem147499 m n)). Qed.
Lemma lem147501 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147502 (m : nat) : (term204 m) = (term205 m).
Proof. exact (MK_COMB (@lem147501) (@lem147500 m)). Qed.
Lemma lem147503 (m : nat) : (term180 m) = (term206 m).
Proof. exact (MK_COMB (@lem147498 m) (@lem147502 m)). Qed.
Lemma lem147504 (m : nat) : term206 m.
Proof. exact (EQ_MP (@lem147503 m) (@lem147484 m)). Qed.
Lemma lem147509 (m : nat) : (term121 m) = term122.
Proof. exact (EQ_MP (@lem147225 m) (@lem147224 m)). Qed.
Lemma lem147510 : term207 = term122.
Proof. exact (@lem147509 (NUMERAL 0)). Qed.
Lemma lem147511 (m : nat) : (term138 m) = (term138 m).
Proof. exact (eq_refl (term138 m)). Qed.
Lemma lem147512 (m : nat) : (term183 m) = (term208 m).
Proof. exact (MK_COMB (@lem147511 m) (@lem147510)). Qed.
Lemma lem147513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem147514 (m : nat) : (term209 m) = (term210 m).
Proof. exact (MK_COMB (@lem147513) (@lem147512 m)). Qed.
Lemma lem147520 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem147521 (x : nat) : (x = x) = True.
Proof. exact (@lem147520 nat x). Qed.
Lemma lem147522 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem147521 (NUMERAL 0)). Qed.
Lemma lem147523 (m : nat) : (term211 m) = (term211 m).
Proof. exact (eq_refl (term211 m)). Qed.
Lemma lem147524 (m : nat) : (term184 m) = (term212 m).
Proof. exact (MK_COMB (@lem147523 m) (@lem147522)). Qed.
Lemma lem147526 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem147527 (m : nat) : (term212 m) = (term134 m).
Proof. exact (@lem147526 (term134 m)). Qed.
Lemma lem147530 (m : nat) : (term184 m) = (term134 m).
Proof. exact (TRANS (@lem147524 m) (@lem147527 m)). Qed.
Lemma lem147531 (m : nat) : ((term183 m) = (term184 m)) = ((term208 m) = (term134 m)).
Proof. exact (MK_COMB (@lem147514 m) (@lem147530 m)). Qed.
Lemma lem147534 (m : nat) : ((term208 m) = (term134 m)) = ((term183 m) = (term184 m)).
Proof. exact (SYM (@lem147531 m)). Qed.
Lemma lem147538 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem147221 m n) (@lem147220 m n)). Qed.
Lemma lem147539 (n : nat) : (term213 n) = (term214 n).
Proof. exact (@lem147538 (NUMERAL 0) n). Qed.
Lemma lem147541 (n : nat) : (term118 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem147198 n) (@lem147197 n)). Qed.
Lemma lem147542 (n : nat) : (term214 n) = (NUMERAL 0).
Proof. exact (@lem147541 (term136 n)). Qed.
Lemma lem147543 (n : nat) : (term213 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem147539 n) (@lem147542 n)). Qed.
Lemma lem147544 (m : nat) : (term138 m) = (term138 m).
Proof. exact (eq_refl (term138 m)). Qed.
Lemma lem147545 (n : nat) (m : nat) : (term191 m n) = (term215 m).
Proof. exact (MK_COMB (@lem147544 m) (@lem147543 n)). Qed.
Lemma lem147547 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem147164 m) (@lem147163 m)). Qed.
Lemma lem147548 (m : nat) : (term215 m) = False.
Proof. exact (@lem147547 (term136 m)). Qed.
Lemma lem147549 (m : nat) (n : nat) : (term191 m n) = False.
Proof. exact (TRANS (@lem147545 n m) (@lem147548 m)). Qed.
Lemma lem147550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem147551 (m : nat) (n : nat) : (term216 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem147550) (@lem147549 m n)). Qed.
Lemma lem147557 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem147203 n (@lem147202 n)). Qed.
Lemma lem147558 (m : nat) : (term211 m) = (term211 m).
Proof. exact (eq_refl (term211 m)). Qed.
Lemma lem147559 (n : nat) (m : nat) : (term192 m n) = (term217 m).
Proof. exact (MK_COMB (@lem147558 m) (@lem147557 n)). Qed.
Lemma lem147561 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem147562 (m : nat) : (term217 m) = False.
Proof. exact (@lem147561 (term134 m)). Qed.
Lemma lem147563 (m : nat) (n : nat) : (term192 m n) = False.
Proof. exact (TRANS (@lem147559 n m) (@lem147562 m)). Qed.
Lemma lem147564 (m : nat) (n : nat) : ((term191 m n) = (term192 m n)) = (False = False).
Proof. exact (MK_COMB (@lem147551 m n) (@lem147563 m n)). Qed.
Lemma lem147566 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem147567 : (False = False) = (~ False).
Proof. exact (@lem147566 False). Qed.
Lemma lem147569 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem147570 : (False = False) = True.
Proof. exact (TRANS (@lem147567) (@lem147569)). Qed.
Lemma lem147571 (m : nat) (n : nat) : ((term191 m n) = (term192 m n)) = True.
Proof. exact (TRANS (@lem147564 m n) (@lem147570)). Qed.
Lemma lem147572 (m : nat) (n : nat) : True = ((term191 m n) = (term192 m n)).
Proof. exact (SYM (@lem147571 m n)). Qed.
Lemma lem147573 (m : nat) (n : nat) : (term191 m n) = (term192 m n).
Proof. exact (EQ_MP (@lem147572 m n) (@lem0)). Qed.
Lemma lem147575 (P : nat -> Prop) : term179 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem147576 : term218.
Proof. exact (@lem147575 term219). Qed.
Lemma lem147577 : term220 = (term221 = term222).
Proof. exact (eq_refl term220). Qed.
Lemma lem147578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147579 : term223 = term224.
Proof. exact (MK_COMB (@lem147578) (@lem147577)). Qed.
Lemma lem147580 (m : nat) : (term225 m) = ((term208 m) = (term134 m)).
Proof. exact (eq_refl (term225 m)). Qed.
Lemma lem147581 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147582 (m : nat) : (term226 m) = (term227 m).
Proof. exact (MK_COMB (@lem147581) (@lem147580 m)). Qed.
Lemma lem147583 (m : nat) : (term228 m) = ((term229 m) = (term114 m)).
Proof. exact (eq_refl (term228 m)). Qed.
Lemma lem147584 (m : nat) : (term230 m) = (term231 m).
Proof. exact (MK_COMB (@lem147582 m) (@lem147583 m)). Qed.
Lemma lem147585 : term232 = term233.
Proof. exact (fun_ext (fun m : nat => @lem147584 m)). Qed.
Lemma lem147586 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147587 : term234 = term235.
Proof. exact (MK_COMB (@lem147586) (@lem147585)). Qed.
Lemma lem147588 : term236 = term237.
Proof. exact (MK_COMB (@lem147579) (@lem147587)). Qed.
Lemma lem147589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147590 : term238 = term239.
Proof. exact (MK_COMB (@lem147589) (@lem147588)). Qed.
Lemma lem147591 (m : nat) : (term225 m) = ((term208 m) = (term134 m)).
Proof. exact (eq_refl (term225 m)). Qed.
Lemma lem147592 : term240 = term219.
Proof. exact (fun_ext (fun m : nat => @lem147591 m)). Qed.
Lemma lem147593 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147594 : term241 = term242.
Proof. exact (MK_COMB (@lem147593) (@lem147592)). Qed.
Lemma lem147595 : term218 = term243.
Proof. exact (MK_COMB (@lem147590) (@lem147594)). Qed.
Lemma lem147596 : term243.
Proof. exact (EQ_MP (@lem147595) (@lem147576)). Qed.
Lemma lem147603 (m : nat) : (term121 m) = term122.
Proof. exact (EQ_MP (@lem147153 m) (@lem147152 m)). Qed.
Lemma lem147604 : term207 = term122.
Proof. exact (@lem147603 (NUMERAL 0)). Qed.
Lemma lem147605 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem147606 : term244 = term245.
Proof. exact (MK_COMB (@lem147605) (@lem147604)). Qed.
Lemma lem147607 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem147608 : term221 = term246.
Proof. exact (MK_COMB (@lem147606) (@lem147607)). Qed.
Lemma lem147610 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem147092 n (@lem147091 n)). Qed.
Lemma lem147611 : term246 = False.
Proof. exact (@lem147610 term122). Qed.
Lemma lem147612 : term221 = False.
Proof. exact (TRANS (@lem147608) (@lem147611)). Qed.
Lemma lem147613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem147614 : term247 = (@eq Prop False).
Proof. exact (MK_COMB (@lem147613) (@lem147612)). Qed.
Lemma lem147616 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem147617 (x : nat) : (x = x) = True.
Proof. exact (@lem147616 nat x). Qed.
Lemma lem147618 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem147617 (NUMERAL 0)). Qed.
Lemma lem147619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem147620 : term222 = (~ True).
Proof. exact (MK_COMB (@lem147619) (@lem147618)). Qed.
Lemma lem147622 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem147623 : term222 = False.
Proof. exact (TRANS (@lem147620) (@lem147622)). Qed.
Lemma lem147624 : (term221 = term222) = (False = False).
Proof. exact (MK_COMB (@lem147614) (@lem147623)). Qed.
Lemma lem147626 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem147627 : (False = False) = (~ False).
Proof. exact (@lem147626 False). Qed.
Lemma lem147629 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem147630 : (False = False) = True.
Proof. exact (TRANS (@lem147627) (@lem147629)). Qed.
Lemma lem147631 : (term221 = term222) = True.
Proof. exact (TRANS (@lem147624) (@lem147630)). Qed.
Lemma lem147632 : True = (term221 = term222).
Proof. exact (SYM (@lem147631)). Qed.
Lemma lem147633 : term221 = term222.
Proof. exact (EQ_MP (@lem147632) (@lem0)). Qed.
Lemma lem147639 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem147149 m n) (@lem147148 m n)). Qed.
Lemma lem147640 (m : nat) : (term213 m) = (term214 m).
Proof. exact (@lem147639 (NUMERAL 0) m). Qed.
Lemma lem147642 (n : nat) : (term118 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem147142 n) (@lem147141 n)). Qed.
Lemma lem147643 (m : nat) : (term214 m) = (NUMERAL 0).
Proof. exact (@lem147642 (term136 m)). Qed.
Lemma lem147644 (m : nat) : (term213 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem147640 m) (@lem147643 m)). Qed.
Lemma lem147645 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem147646 (m : nat) : (term248 m) = term167.
Proof. exact (MK_COMB (@lem147645) (@lem147644 m)). Qed.
Lemma lem147647 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem147648 (m : nat) : (term229 m) = term249.
Proof. exact (MK_COMB (@lem147646 m) (@lem147647)). Qed.
Lemma lem147651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem147652 (m : nat) : (term250 m) = term251.
Proof. exact (MK_COMB (@lem147651) (@lem147648 m)). Qed.
Lemma lem147654 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem147097 n (@lem147096 n)). Qed.
Lemma lem147655 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem147654 m). Qed.
Lemma lem147656 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem147657 (m : nat) : (term114 m) = (~ False).
Proof. exact (MK_COMB (@lem147656) (@lem147655 m)). Qed.
Lemma lem147659 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem147660 (m : nat) : (term114 m) = True.
Proof. exact (TRANS (@lem147657 m) (@lem147659)). Qed.
Lemma lem147661 (m : nat) : ((term229 m) = (term114 m)) = (term249 = True).
Proof. exact (MK_COMB (@lem147652 m) (@lem147660 m)). Qed.
Lemma lem147663 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem147664 : (term249 = True) = term249.
Proof. exact (@lem147663 term249). Qed.
Lemma lem147667 (m : nat) : ((term229 m) = (term114 m)) = term249.
Proof. exact (TRANS (@lem147661 m) (@lem147664)). Qed.
Lemma lem147668 (m : nat) : term249 = ((term229 m) = (term114 m)).
Proof. exact (SYM (@lem147667 m)). Qed.
Lemma lem147670 : term122 = term165.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem147671 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem147672 : term249 = term171.
Proof. exact (MK_COMB (@lem147671) (@lem147670)). Qed.
Lemma lem147674 (n : nat) : (term109 n) = True.
Proof. exact (EQ_MP (@lem147076 n) (@lem147075 n)). Qed.
Lemma lem147675 : term171 = True.
Proof. exact (@lem147674 (NUMERAL 0)). Qed.
Lemma lem147676 : term249 = True.
Proof. exact (TRANS (@lem147672) (@lem147675)). Qed.
Lemma lem147677 : True = term249.
Proof. exact (SYM (@lem147676)). Qed.
Lemma lem147678 : term249.
Proof. exact (EQ_MP (@lem147677) (@lem0)). Qed.
Lemma lem147679 (m : nat) : (term229 m) = (term114 m).
Proof. exact (EQ_MP (@lem147668 m) (@lem147678)). Qed.
Lemma lem147680 (m : nat) : term231 m.
Proof. exact (fun h0 : (term208 m) = (term134 m) => @lem147679 m). Qed.
Lemma lem147685 : term235.
Proof. exact (fun m : nat => @lem147680 m). Qed.
Lemma lem147686 : term237.
Proof. exact (conj (@lem147633) (@lem147685)). Qed.
Lemma lem147687 : term242.
Proof. exact (@lem147596 (@lem147686)). Qed.
Lemma lem147688 (m : nat) : term225 m.
Proof. exact (@lem147687 m). Qed.
Lemma lem147689 (m : nat) : (term225 m) = ((term208 m) = (term134 m)).
Proof. exact (eq_refl (term225 m)). Qed.
Lemma lem147690 (m : nat) : (term208 m) = (term134 m).
Proof. exact (EQ_MP (@lem147689 m) (@lem147688 m)). Qed.
Lemma lem147691 (m : nat) : (term183 m) = (term184 m).
Proof. exact (EQ_MP (@lem147534 m) (@lem147690 m)). Qed.
Lemma lem147692 (m : nat) (n : nat) : term194 m n.
Proof. exact (fun h0 : (term140 m n) = (term154 m n) => @lem147573 m n). Qed.
Lemma lem147697 (m : nat) : term198 m.
Proof. exact (fun n : nat => @lem147692 m n). Qed.
Lemma lem147698 (m : nat) : term200 m.
Proof. exact (conj (@lem147691 m) (@lem147697 m)). Qed.
Lemma lem147699 (m : nat) : term205 m.
Proof. exact (@lem147504 m (@lem147698 m)). Qed.
Lemma lem147700 (m : nat) (n : nat) : term187 m n.
Proof. exact (@lem147699 m n). Qed.
Lemma lem147701 (m : nat) (n : nat) : (term187 m n) = ((term140 m n) = (term154 m n)).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem147702 (m : nat) (n : nat) : (term140 m n) = (term154 m n).
Proof. exact (EQ_MP (@lem147701 m n) (@lem147700 m n)). Qed.
Lemma lem147703 (m : nat) (n : nat) : (term140 m n) = (term158 m n).
Proof. exact (EQ_MP (@lem147481 m n) (@lem147702 m n)). Qed.
Lemma lem147704 (m : nat) (x : nat) (n : nat) : (term252 x m n) = (term253 m x n).
Proof. exact (@lem10568 (term148 x m n) (term139 m x n)). Qed.
Lemma lem147705 (x : nat) (m : nat) (n : nat) : (term253 m x n) = (term252 x m n).
Proof. exact (SYM (@lem147704 m x n)). Qed.
Lemma lem147709 (t1 : Prop) (t2 : Prop) : (term254 t1 t2) = (term255 t1 t2).
Proof. exact (proj1 (@lem147064 t1 t2)). Qed.
Lemma lem147710 (x : nat) (m : nat) (n : nat) : (term256 x m n) = (term257 x m n).
Proof. exact (@lem147709 (term144 x) (Peano.lt m n)). Qed.
Lemma lem147714 (n : nat) (m : nat) : (term12 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem147057 n m) (@lem147056 m n)). Qed.
Lemma lem147715 (x : nat) : (term258 x) = (term259 x).
Proof. exact (@lem147714 x term163). Qed.
Lemma lem147716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147717 (x : nat) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem147716) (@lem147715 x)). Qed.
Lemma lem147719 (n : nat) (m : nat) : (term107 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem147071 n m) (@lem147070 m n)). Qed.
Lemma lem147720 (x : nat) (n : nat) (m : nat) : (term257 x m n) = (term262 x n m).
Proof. exact (MK_COMB (@lem147717 x) (@lem147719 n m)). Qed.
Lemma lem147723 (x : nat) (n : nat) (m : nat) : (term256 x m n) = (term262 x n m).
Proof. exact (TRANS (@lem147710 x m n) (@lem147720 x n m)). Qed.
Lemma lem147724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147725 (x : nat) (n : nat) (m : nat) : (term263 x m n) = (term264 x n m).
Proof. exact (MK_COMB (@lem147724) (@lem147723 x n m)). Qed.
Lemma lem147727 (n : nat) (m : nat) : (term107 m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem147071 n m) (@lem147070 m n)). Qed.
Lemma lem147728 (n : nat) (x : nat) (m : nat) : (term265 m x n) = (term266 n x m).
Proof. exact (@lem147727 (Nat.pow x n) (Nat.pow x m)). Qed.
Lemma lem147729 (n : nat) (x : nat) (m : nat) : (term253 m x n) = (term267 n x m).
Proof. exact (MK_COMB (@lem147725 x n m) (@lem147728 n x m)). Qed.
Lemma lem147732 (m : nat) (x : nat) (n : nat) : (term267 n x m) = (term253 m x n).
Proof. exact (SYM (@lem147729 n x m)). Qed.
Lemma lem147738 : term163 = term164.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem147740 : term122 = term165.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem147741 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem147742 : term164 = term166.
Proof. exact (MK_COMB (@lem147741) (@lem147740)). Qed.
Lemma lem147743 : term163 = term166.
Proof. exact (TRANS (@lem147738) (@lem147742)). Qed.
Lemma lem147744 (x : nat) : (Peano.lt x) = (Peano.lt x).
Proof. exact (eq_refl (Peano.lt x)). Qed.
Lemma lem147745 (x : nat) : (term259 x) = (term268 x).
Proof. exact (MK_COMB (@lem147744 x) (@lem147743)). Qed.
Lemma lem147747 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem147047 m n) (@lem147046 m n)). Qed.
Lemma lem147748 (x : nat) : (term268 x) = (term269 x).
Proof. exact (@lem147747 x term165). Qed.
Lemma lem147754 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem147047 m n) (@lem147046 m n)). Qed.
Lemma lem147755 (x : nat) : (term270 x) = (term271 x).
Proof. exact (@lem147754 x (NUMERAL 0)). Qed.
Lemma lem147761 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem147051 m) (@lem147050 m)). Qed.
Lemma lem147762 (x : nat) : (term8 x) = False.
Proof. exact (@lem147761 x). Qed.
Lemma lem147763 (x : nat) : (term272 x) = (term272 x).
Proof. exact (eq_refl (term272 x)). Qed.
Lemma lem147764 (x : nat) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem147763 x) (@lem147762 x)). Qed.
Lemma lem147766 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem147767 (x : nat) : (term273 x) = (x = (NUMERAL 0)).
Proof. exact (@lem147766 (x = (NUMERAL 0))). Qed.
Lemma lem147770 (x : nat) : (term271 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem147764 x) (@lem147767 x)). Qed.
Lemma lem147771 (x : nat) : (term270 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem147755 x) (@lem147770 x)). Qed.
Lemma lem147772 (x : nat) : (term274 x) = (term274 x).
Proof. exact (eq_refl (term274 x)). Qed.
Lemma lem147773 (x : nat) : (term269 x) = (term275 x).
Proof. exact (MK_COMB (@lem147772 x) (@lem147771 x)). Qed.
Lemma lem147776 (x : nat) : (term268 x) = (term275 x).
Proof. exact (TRANS (@lem147748 x) (@lem147773 x)). Qed.
Lemma lem147777 (x : nat) : (term259 x) = (term275 x).
Proof. exact (TRANS (@lem147745 x) (@lem147776 x)). Qed.
Lemma lem147778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147779 (x : nat) : (term261 x) = (term276 x).
Proof. exact (MK_COMB (@lem147778) (@lem147777 x)). Qed.
Lemma lem147780 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem147781 (x : nat) (n : nat) (m : nat) : (term262 x n m) = (term277 x n m).
Proof. exact (MK_COMB (@lem147779 x) (@lem147780 n m)). Qed.
Lemma lem147784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147785 (x : nat) (n : nat) (m : nat) : (term264 x n m) = (term278 x n m).
Proof. exact (MK_COMB (@lem147784) (@lem147781 x n m)). Qed.
Lemma lem147786 (n : nat) (x : nat) (m : nat) : (term266 n x m) = (term266 n x m).
Proof. exact (eq_refl (term266 n x m)). Qed.
Lemma lem147787 (n : nat) (x : nat) (m : nat) : (term267 n x m) = (term279 n x m).
Proof. exact (MK_COMB (@lem147785 x n m) (@lem147786 n x m)). Qed.
Lemma lem147790 (n : nat) (x : nat) (m : nat) : (term279 n x m) = (term267 n x m).
Proof. exact (SYM (@lem147787 n x m)). Qed.
Lemma lem147791 (x : nat) : term159 x.
Proof. exact (@lem82 (x = (NUMERAL 0))). Qed.
Lemma lem147813 : term165 = term122.
Proof. exact (SYM (@lem80361)). Qed.
Lemma lem147814 (x : nat) : (@eq nat x) = (@eq nat x).
Proof. exact (eq_refl (@eq nat x)). Qed.
Lemma lem147815 (x : nat) : (x = term165) = (x = term122).
Proof. exact (MK_COMB (@lem147814 x) (@lem147813)). Qed.
Lemma lem147818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147819 (x : nat) : (term274 x) = (term280 x).
Proof. exact (MK_COMB (@lem147818) (@lem147815 x)). Qed.
Lemma lem147821 (x : nat) (h1 : term134 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem147791 x (@lem147262 x h1)). Qed.
Lemma lem147822 (x : nat) (h1 : term134 x) : (term275 x) = (term281 x).
Proof. exact (MK_COMB (@lem147819 x) (@lem147821 x h1)). Qed.
Lemma lem147824 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem147825 (x : nat) : (term281 x) = (x = term122).
Proof. exact (@lem147824 (x = term122)). Qed.
Lemma lem147828 (x : nat) (h1 : term134 x) : (term275 x) = (x = term122).
Proof. exact (TRANS (@lem147822 x h1) (@lem147825 x)). Qed.
Lemma lem147829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem147830 (x : nat) (h1 : term134 x) : (term276 x) = (term280 x).
Proof. exact (MK_COMB (@lem147829) (@lem147828 x h1)). Qed.
Lemma lem147831 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem147832 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : (term277 x n m) = (term282 x n m).
Proof. exact (MK_COMB (@lem147830 x h1) (@lem147831 n m)). Qed.
Lemma lem147835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147836 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : (term278 x n m) = (term283 x n m).
Proof. exact (MK_COMB (@lem147835) (@lem147832 n m x h1)). Qed.
Lemma lem147837 (n : nat) (x : nat) (m : nat) : (term266 n x m) = (term266 n x m).
Proof. exact (eq_refl (term266 n x m)). Qed.
Lemma lem147838 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : (term279 n x m) = (term284 n x m).
Proof. exact (MK_COMB (@lem147836 n m x h1) (@lem147837 n x m)). Qed.
Lemma lem147841 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : (term284 n x m) = (term279 n x m).
Proof. exact (SYM (@lem147838 n m x h1)). Qed.
Lemma lem147842 (x : nat) (n : nat) (m : nat) (h1 : term282 x n m) : term282 x n m.
Proof. exact (h1). Qed.
Lemma lem147843 (x : nat) (h1 : x = term122) : x = term122.
Proof. exact (h1). Qed.
Lemma lem147844 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem147845 (n : nat) : term20 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem147846 (n : nat) : (term20 n) = (Peano.le n n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem147847 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem147846 n) (@lem147845 n)). Qed.
Lemma lem147848 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem147850 (n : nat) : term285 n.
Proof. exact (@lem87885 n). Qed.
Lemma lem147851 (n : nat) : (term285 n) = ((term286 n) = term122).
Proof. exact (eq_refl (term285 n)). Qed.
Lemma lem147869 (x : nat) (h1 : x = term122) : x = term122.
Proof. exact (h1). Qed.
Lemma lem147870 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem147871 (x : nat) (h1 : x = term122) : (Nat.pow x) = term287.
Proof. exact (MK_COMB (@lem147870) (@lem147869 x h1)). Qed.
Lemma lem147872 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem147873 (n : nat) (x : nat) (h1 : x = term122) : (Nat.pow x n) = (term286 n).
Proof. exact (MK_COMB (@lem147871 x h1) (@lem147872 n)). Qed.
Lemma lem147875 (n : nat) : (term286 n) = term122.
Proof. exact (EQ_MP (@lem147851 n) (@lem147850 n)). Qed.
Lemma lem147876 (n : nat) (x : nat) (h1 : x = term122) : (Nat.pow x n) = term122.
Proof. exact (TRANS (@lem147873 n x h1) (@lem147875 n)). Qed.
Lemma lem147877 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem147878 (n : nat) (x : nat) (h1 : x = term122) : (term288 x n) = term289.
Proof. exact (MK_COMB (@lem147877) (@lem147876 n x h1)). Qed.
Lemma lem147880 (x : nat) (h1 : x = term122) : x = term122.
Proof. exact (h1). Qed.
Lemma lem147881 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem147882 (x : nat) (h1 : x = term122) : (Nat.pow x) = term287.
Proof. exact (MK_COMB (@lem147881) (@lem147880 x h1)). Qed.
Lemma lem147883 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem147884 (m : nat) (x : nat) (h1 : x = term122) : (Nat.pow x m) = (term286 m).
Proof. exact (MK_COMB (@lem147882 x h1) (@lem147883 m)). Qed.
Lemma lem147886 (n : nat) : (term286 n) = term122.
Proof. exact (EQ_MP (@lem147851 n) (@lem147850 n)). Qed.
Lemma lem147887 (m : nat) : (term286 m) = term122.
Proof. exact (@lem147886 m). Qed.
Lemma lem147888 (m : nat) (x : nat) (h1 : x = term122) : (Nat.pow x m) = term122.
Proof. exact (TRANS (@lem147884 m x h1) (@lem147887 m)). Qed.
Lemma lem147889 (n : nat) (m : nat) (x : nat) (h1 : x = term122) : (term266 n x m) = term290.
Proof. exact (MK_COMB (@lem147878 n x h1) (@lem147888 m x h1)). Qed.
Lemma lem147891 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem147848 n) (@lem147847 n)). Qed.
Lemma lem147892 : term290 = True.
Proof. exact (@lem147891 term122). Qed.
Lemma lem147893 (n : nat) (m : nat) (x : nat) (h1 : x = term122) : (term266 n x m) = True.
Proof. exact (TRANS (@lem147889 n m x h1) (@lem147892)). Qed.
Lemma lem147894 (n : nat) (m : nat) (x : nat) (h1 : x = term122) : True = (term266 n x m).
Proof. exact (SYM (@lem147893 n m x h1)). Qed.
Lemma lem147895 (n : nat) (m : nat) (x : nat) (h1 : x = term122) : term266 n x m.
Proof. exact (EQ_MP (@lem147894 n m x h1) (@lem0)). Qed.
Lemma lem147924 (n : nat) (m : nat) : (Peano.le m n) = (term99 n m).
Proof. exact (EQ_MP (@lem147039 n m) (@lem147038 m n)). Qed.
Lemma lem147925 (m : nat) (n : nat) : (Peano.le n m) = (term99 m n).
Proof. exact (@lem147924 m n). Qed.
Lemma lem147932 (n : nat) (m : nat) (h1 : Peano.le n m) : term99 m n.
Proof. exact (EQ_MP (@lem147925 m n) (@lem147844 n m h1)). Qed.
Lemma lem147933 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem147934 (n : nat) (x : nat) : (term291 n x) = (term291 n x).
Proof. exact (eq_refl (term291 n x)). Qed.
Lemma lem147935 (x : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term292 n x m) = (term293 x n d).
Proof. exact (MK_COMB (@lem147934 n x) (@lem147933 m n d h1)). Qed.
Lemma lem147936 (x : nat) (n : nat) (d : nat) : (term293 x n d) = (term294 x n d).
Proof. exact (eq_refl (term293 x n d)). Qed.
Lemma lem147937 (n : nat) (x : nat) (m : nat) : (term295 n x m) = (term295 n x m).
Proof. exact (eq_refl (term295 n x m)). Qed.
Lemma lem147938 (m : nat) (x : nat) (n : nat) (d : nat) : ((term292 n x m) = (term293 x n d)) = ((term292 n x m) = (term294 x n d)).
Proof. exact (MK_COMB (@lem147937 n x m) (@lem147936 x n d)). Qed.
Lemma lem147939 (n : nat) (x : nat) (m : nat) : (term292 n x m) = (term266 n x m).
Proof. exact (eq_refl (term292 n x m)). Qed.
Lemma lem147940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem147941 (n : nat) (x : nat) (m : nat) : (term295 n x m) = (term296 n x m).
Proof. exact (MK_COMB (@lem147940) (@lem147939 n x m)). Qed.
Lemma lem147942 (x : nat) (n : nat) (d : nat) : (term294 x n d) = (term294 x n d).
Proof. exact (eq_refl (term294 x n d)). Qed.
Lemma lem147943 (m : nat) (x : nat) (n : nat) (d : nat) : ((term292 n x m) = (term294 x n d)) = ((term266 n x m) = (term294 x n d)).
Proof. exact (MK_COMB (@lem147941 n x m) (@lem147942 x n d)). Qed.
Lemma lem147944 (m : nat) (x : nat) (n : nat) (d : nat) : ((term292 n x m) = (term293 x n d)) = ((term266 n x m) = (term294 x n d)).
Proof. exact (TRANS (@lem147938 m x n d) (@lem147943 m x n d)). Qed.
Lemma lem147945 (x : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term266 n x m) = (term294 x n d).
Proof. exact (EQ_MP (@lem147944 m x n d) (@lem147935 x m n d h1)). Qed.
Lemma lem147946 (x : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term294 x n d) = (term266 n x m).
Proof. exact (SYM (@lem147945 x m n d h1)). Qed.
Lemma lem147948 (P : nat -> Prop) : term179 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem147949 (x : nat) (n : nat) : term297 x n.
Proof. exact (@lem147948 (term298 x n)). Qed.
Lemma lem147950 (x : nat) (n : nat) : (term299 x n) = (term300 x n).
Proof. exact (eq_refl (term299 x n)). Qed.
Lemma lem147951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem147952 (x : nat) (n : nat) : (term301 x n) = (term302 x n).
Proof. exact (MK_COMB (@lem147951) (@lem147950 x n)). Qed.
Lemma lem147953 (x : nat) (n : nat) (d : nat) : (term303 x n d) = (term294 x n d).
Proof. exact (eq_refl (term303 x n d)). Qed.
Lemma lem147954 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147955 (x : nat) (n : nat) (d : nat) : (term304 x n d) = (term305 x n d).
Proof. exact (MK_COMB (@lem147954) (@lem147953 x n d)). Qed.
Lemma lem147956 (x : nat) (n : nat) (d : nat) : (term306 x n d) = (term307 x n d).
Proof. exact (eq_refl (term306 x n d)). Qed.
Lemma lem147957 (x : nat) (n : nat) (d : nat) : (term308 x n d) = (term309 x n d).
Proof. exact (MK_COMB (@lem147955 x n d) (@lem147956 x n d)). Qed.
Lemma lem147958 (x : nat) (n : nat) : (term310 x n) = (term311 x n).
Proof. exact (fun_ext (fun d : nat => @lem147957 x n d)). Qed.
Lemma lem147959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147960 (x : nat) (n : nat) : (term312 x n) = (term313 x n).
Proof. exact (MK_COMB (@lem147959) (@lem147958 x n)). Qed.
Lemma lem147961 (x : nat) (n : nat) : (term314 x n) = (term315 x n).
Proof. exact (MK_COMB (@lem147952 x n) (@lem147960 x n)). Qed.
Lemma lem147962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem147963 (x : nat) (n : nat) : (term316 x n) = (term317 x n).
Proof. exact (MK_COMB (@lem147962) (@lem147961 x n)). Qed.
Lemma lem147964 (x : nat) (n : nat) (d : nat) : (term303 x n d) = (term294 x n d).
Proof. exact (eq_refl (term303 x n d)). Qed.
Lemma lem147965 (x : nat) (n : nat) : (term318 x n) = (term298 x n).
Proof. exact (fun_ext (fun d : nat => @lem147964 x n d)). Qed.
Lemma lem147966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem147967 (x : nat) (n : nat) : (term319 x n) = (term320 x n).
Proof. exact (MK_COMB (@lem147966) (@lem147965 x n)). Qed.
Lemma lem147968 (x : nat) (n : nat) : (term297 x n) = (term321 x n).
Proof. exact (MK_COMB (@lem147963 x n) (@lem147967 x n)). Qed.
Lemma lem147969 (x : nat) (n : nat) : term321 x n.
Proof. exact (EQ_MP (@lem147968 x n) (@lem147949 x n)). Qed.
Lemma lem147970 (x : nat) (n : nat) (d : nat) (h1 : term294 x n d) : term294 x n d.
Proof. exact (h1). Qed.
Lemma lem147974 (m : nat) : (term91 m) = m.
Proof. exact (EQ_MP (@lem147029 m) (@lem147028 m)). Qed.
Lemma lem147975 (n : nat) : (term91 n) = n.
Proof. exact (@lem147974 n). Qed.
Lemma lem147976 (x : nat) : (Nat.pow x) = (Nat.pow x).
Proof. exact (eq_refl (Nat.pow x)). Qed.
Lemma lem147977 (x : nat) (n : nat) : (term322 x n) = (Nat.pow x n).
Proof. exact (MK_COMB (@lem147976 x) (@lem147975 n)). Qed.
Lemma lem147978 (x : nat) (n : nat) : (term288 x n) = (term288 x n).
Proof. exact (eq_refl (term288 x n)). Qed.
Lemma lem147979 (x : nat) (n : nat) : (term300 x n) = (term323 x n).
Proof. exact (MK_COMB (@lem147978 x n) (@lem147977 x n)). Qed.
Lemma lem147981 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem146998 n) (@lem146997 n)). Qed.
Lemma lem147982 (x : nat) (n : nat) : (term323 x n) = True.
Proof. exact (@lem147981 (Nat.pow x n)). Qed.
Lemma lem147983 (x : nat) (n : nat) : (term300 x n) = True.
Proof. exact (TRANS (@lem147979 x n) (@lem147982 x n)). Qed.
Lemma lem147984 (x : nat) (n : nat) : True = (term300 x n).
Proof. exact (SYM (@lem147983 x n)). Qed.
Lemma lem147985 (x : nat) (n : nat) : term300 x n.
Proof. exact (EQ_MP (@lem147984 x n) (@lem0)). Qed.
Lemma lem147989 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (EQ_MP (@lem147018 m n) (@lem147017 m n)). Qed.
Lemma lem147990 (n : nat) (d : nat) : (term70 n d) = (term71 n d).
Proof. exact (@lem147989 n d). Qed.
Lemma lem147991 (x : nat) : (Nat.pow x) = (Nat.pow x).
Proof. exact (eq_refl (Nat.pow x)). Qed.
Lemma lem147992 (x : nat) (n : nat) (d : nat) : (term324 x n d) = (term325 x n d).
Proof. exact (MK_COMB (@lem147991 x) (@lem147990 n d)). Qed.
Lemma lem147994 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem147005 m n) (@lem147004 m n)). Qed.
Lemma lem147995 (x : nat) (n : nat) (d : nat) : (term325 x n d) = (term326 x n d).
Proof. exact (@lem147994 x (Nat.add n d)). Qed.
Lemma lem147996 (x : nat) (n : nat) (d : nat) : (term324 x n d) = (term326 x n d).
Proof. exact (TRANS (@lem147992 x n d) (@lem147995 x n d)). Qed.
Lemma lem147997 (x : nat) (n : nat) : (term288 x n) = (term288 x n).
Proof. exact (eq_refl (term288 x n)). Qed.
Lemma lem147998 (x : nat) (n : nat) (d : nat) : (term307 x n d) = (term327 x n d).
Proof. exact (MK_COMB (@lem147997 x n) (@lem147996 x n d)). Qed.
Lemma lem148001 (x : nat) (n : nat) (d : nat) : (term327 x n d) = (term307 x n d).
Proof. exact (SYM (@lem147998 x n d)). Qed.
Lemma lem148003 (m : nat) (p : nat) : term38 m p.
Proof. exact (EQ_MP (@lem146993 m p) (@lem146992 m p)). Qed.
Lemma lem148004 (x : nat) (n : nat) (d : nat) : term328 x n d.
Proof. exact (@lem148003 (Nat.pow x n) (term326 x n d)). Qed.
Lemma lem148005 : term21.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem148006 : term22.
Proof. exact (proj2 (@lem148005)). Qed.
Lemma lem148027 : term329.
Proof. exact (proj1 (@lem148006)). Qed.
Lemma lem148028 (n : nat) : term330 n.
Proof. exact (@lem148027 n). Qed.
Lemma lem148029 (n : nat) : (term330 n) = ((term331 n) = n).
Proof. exact (eq_refl (term330 n)). Qed.
Lemma lem148054 (x : nat) (n : nat) (d : nat) : (term294 x n d) = ((term294 x n d) = True).
Proof. exact (@lem7 (term294 x n d)). Qed.
Lemma lem148057 (n : nat) : (term331 n) = n.
Proof. exact (EQ_MP (@lem148029 n) (@lem148028 n)). Qed.
Lemma lem148058 (x : nat) (n : nat) (d : nat) : (term332 x n d) = (term333 x n d).
Proof. exact (@lem148057 (term333 x n d)). Qed.
Lemma lem148059 (x : nat) (n : nat) : (term288 x n) = (term288 x n).
Proof. exact (eq_refl (term288 x n)). Qed.
Lemma lem148060 (x : nat) (n : nat) (d : nat) : (term334 x n d) = (term294 x n d).
Proof. exact (MK_COMB (@lem148059 x n) (@lem148058 x n d)). Qed.
Lemma lem148062 (x : nat) (n : nat) (d : nat) (h1 : term294 x n d) : (term294 x n d) = True.
Proof. exact (EQ_MP (@lem148054 x n d) (@lem147970 x n d h1)). Qed.
Lemma lem148063 (x : nat) (n : nat) (d : nat) (h1 : term294 x n d) : (term334 x n d) = True.
Proof. exact (TRANS (@lem148060 x n d) (@lem148062 x n d h1)). Qed.
Lemma lem148064 (x : nat) (n : nat) (d : nat) (h1 : term294 x n d) : True = (term334 x n d).
Proof. exact (SYM (@lem148063 x n d h1)). Qed.
Lemma lem148065 (x : nat) (n : nat) (d : nat) (h1 : term294 x n d) : term334 x n d.
Proof. exact (EQ_MP (@lem148064 x n d h1) (@lem0)). Qed.
Lemma lem148067 (m : nat) (n : nat) (p : nat) : (term49 m n p) = (term50 m n p).
Proof. exact (EQ_MP (@lem146965 m n p) (@lem146964 m n p)). Qed.
Lemma lem148068 (x : nat) (n : nat) (d : nat) : (term335 x n d) = (term336 x n d).
Proof. exact (@lem148067 term122 x (term333 x n d)). Qed.
Lemma lem148073 (x : nat) (n : nat) (d : nat) : (term336 x n d) = (term335 x n d).
Proof. exact (SYM (@lem148068 x n d)). Qed.
Lemma lem148074 (x : nat) : (term337 x) = (term338 x).
Proof. exact (@lem10568 (term339 x) (term134 x)). Qed.
Lemma lem148075 (x : nat) : (term338 x) = (term337 x).
Proof. exact (SYM (@lem148074 x)). Qed.
Lemma lem148079 (n : nat) (m : nat) : (term12 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem146956 n m) (@lem146955 m n)). Qed.
Lemma lem148080 (x : nat) : (term340 x) = (term341 x).
Proof. exact (@lem148079 x term122). Qed.
Lemma lem148081 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem148082 (x : nat) : (term342 x) = (term343 x).
Proof. exact (MK_COMB (@lem148081) (@lem148080 x)). Qed.
Lemma lem148084 (t : Prop) : (term344 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem148085 (x : nat) : (term345 x) = (x = (NUMERAL 0)).
Proof. exact (@lem148084 (x = (NUMERAL 0))). Qed.
Lemma lem148088 (x : nat) : (term338 x) = (term346 x).
Proof. exact (MK_COMB (@lem148082 x) (@lem148085 x)). Qed.
Lemma lem148091 (x : nat) : (term346 x) = (term338 x).
Proof. exact (SYM (@lem148088 x)). Qed.
Lemma lem148095 : term122 = term165.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem148096 (x : nat) : (Peano.lt x) = (Peano.lt x).
Proof. exact (eq_refl (Peano.lt x)). Qed.
Lemma lem148097 (x : nat) : (term341 x) = (term270 x).
Proof. exact (MK_COMB (@lem148096 x) (@lem148095)). Qed.
Lemma lem148099 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem146946 m n) (@lem146945 m n)). Qed.
Lemma lem148100 (x : nat) : (term270 x) = (term271 x).
Proof. exact (@lem148099 x (NUMERAL 0)). Qed.
Lemma lem148106 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem146950 m) (@lem146949 m)). Qed.
Lemma lem148107 (x : nat) : (term8 x) = False.
Proof. exact (@lem148106 x). Qed.
Lemma lem148108 (x : nat) : (term272 x) = (term272 x).
Proof. exact (eq_refl (term272 x)). Qed.
Lemma lem148109 (x : nat) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem148108 x) (@lem148107 x)). Qed.
Lemma lem148111 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem148112 (x : nat) : (term273 x) = (x = (NUMERAL 0)).
Proof. exact (@lem148111 (x = (NUMERAL 0))). Qed.
Lemma lem148115 (x : nat) : (term271 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem148109 x) (@lem148112 x)). Qed.
Lemma lem148116 (x : nat) : (term270 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem148100 x) (@lem148115 x)). Qed.
Lemma lem148117 (x : nat) : (term341 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem148097 x) (@lem148116 x)). Qed.
Lemma lem148118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem148119 (x : nat) : (term343 x) = (term347 x).
Proof. exact (MK_COMB (@lem148118) (@lem148117 x)). Qed.
Lemma lem148122 (x : nat) : (x = (NUMERAL 0)) = (x = (NUMERAL 0)).
Proof. exact (eq_refl (x = (NUMERAL 0))). Qed.
Lemma lem148123 (x : nat) : (term346 x) = (term348 x).
Proof. exact (MK_COMB (@lem148119 x) (@lem148122 x)). Qed.
Lemma lem148127 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem148128 (x : nat) : (term348 x) = True.
Proof. exact (@lem148127 (x = (NUMERAL 0))). Qed.
Lemma lem148129 (x : nat) : (term346 x) = True.
Proof. exact (TRANS (@lem148123 x) (@lem148128 x)). Qed.
Lemma lem148130 (x : nat) : True = (term346 x).
Proof. exact (SYM (@lem148129 x)). Qed.
Lemma lem148131 (x : nat) : term346 x.
Proof. exact (EQ_MP (@lem148130 x) (@lem0)). Qed.
Lemma lem148132 (x : nat) : term338 x.
Proof. exact (EQ_MP (@lem148091 x) (@lem148131 x)). Qed.
Lemma lem148133 (x : nat) : term337 x.
Proof. exact (EQ_MP (@lem148075 x) (@lem148132 x)). Qed.
Lemma lem148134 (x : nat) (h1 : term134 x) : term339 x.
Proof. exact (@lem148133 x (@lem147262 x h1)). Qed.
Lemma lem148135 (n : nat) (d : nat) (x : nat) (h1 : term134 x) : term336 x n d.
Proof. exact (or_intro1 (@lem148134 x h1) ((term333 x n d) = (NUMERAL 0))). Qed.
Lemma lem148136 (n : nat) (d : nat) (x : nat) (h1 : term134 x) : term335 x n d.
Proof. exact (EQ_MP (@lem148073 x n d) (@lem148135 n d x h1)). Qed.
Lemma lem148137 (x : nat) (n : nat) (d : nat) (h1 : term134 x) (h2 : term294 x n d) : term349 x n d.
Proof. exact (conj (@lem148065 x n d h2) (@lem148136 n d x h1)). Qed.
Lemma lem148138 (x : nat) (n : nat) (d : nat) (h1 : term134 x) (h2 : term294 x n d) : term350 x n d.
Proof. exact (ex_intro (term351 x n d) (term332 x n d) (@lem148137 x n d h1 h2)). Qed.
Lemma lem148139 (x : nat) (n : nat) (d : nat) (h1 : term134 x) (h2 : term294 x n d) : term327 x n d.
Proof. exact (@lem148004 x n d (@lem148138 x n d h1 h2)). Qed.
Lemma lem148140 (x : nat) (n : nat) (d : nat) (h1 : term134 x) (h2 : term294 x n d) : term307 x n d.
Proof. exact (EQ_MP (@lem148001 x n d) (@lem148139 x n d h1 h2)). Qed.
Lemma lem148141 (n : nat) (d : nat) (x : nat) (h1 : term134 x) : term309 x n d.
Proof. exact (fun h0 : term294 x n d => @lem148140 x n d h1 h0). Qed.
Lemma lem148146 (n : nat) (x : nat) (h1 : term134 x) : term313 x n.
Proof. exact (fun d : nat => @lem148141 n d x h1). Qed.
Lemma lem148147 (n : nat) (x : nat) (h1 : term134 x) : term315 x n.
Proof. exact (conj (@lem147985 x n) (@lem148146 n x h1)). Qed.
Lemma lem148148 (n : nat) (x : nat) (h1 : term134 x) : term320 x n.
Proof. exact (@lem147969 x n (@lem148147 n x h1)). Qed.
Lemma lem148149 (n : nat) (d : nat) (x : nat) (h1 : term134 x) : term303 x n d.
Proof. exact (@lem148148 n x h1 d). Qed.
Lemma lem148150 (x : nat) (n : nat) (d : nat) : (term303 x n d) = (term294 x n d).
Proof. exact (eq_refl (term303 x n d)). Qed.
Lemma lem148151 (n : nat) (d : nat) (x : nat) (h1 : term134 x) : term294 x n d.
Proof. exact (EQ_MP (@lem148150 x n d) (@lem148149 n d x h1)). Qed.
Lemma lem148152 (x : nat) (m : nat) (n : nat) (d : nat) (h1 : term134 x) (h2 : m = (Nat.add n d)) : term266 n x m.
Proof. exact (EQ_MP (@lem147946 x m n d h2) (@lem148151 n d x h1)). Qed.
Lemma lem148154 (x : nat) (n : nat) (m : nat) (h1 : term134 x) (h2 : Peano.le n m) : term266 n x m.
Proof. exact (ex_elim (@lem147932 n m h2) (fun d : nat => fun h0 : term352 m n d => @lem148152 x m n d h1 h0)). Qed.
Lemma lem148155 (x : nat) (n : nat) (m : nat) (h1 : term134 x) (h2 : Peano.le n m) : (Peano.le n m) = (term266 n x m).
Proof. exact (prop_ext (fun h3 : Peano.le n m => @lem148154 x n m h1 h2) (fun h3 : term266 n x m => @lem147844 n m h2)). Qed.
Lemma lem148156 (x : nat) (n : nat) (m : nat) (h1 : term134 x) (h2 : Peano.le n m) : term266 n x m.
Proof. exact (EQ_MP (@lem148155 x n m h1 h2) (@lem147844 n m h2)). Qed.
Lemma lem148157 (n : nat) (m : nat) (x : nat) (h1 : x = term122) : (x = term122) = (term266 n x m).
Proof. exact (prop_ext (fun h2 : x = term122 => @lem147895 n m x h1) (fun h2 : term266 n x m => @lem147843 x h1)). Qed.
Lemma lem148158 (n : nat) (m : nat) (x : nat) (h1 : x = term122) : term266 n x m.
Proof. exact (EQ_MP (@lem148157 n m x h1) (@lem147843 x h1)). Qed.
Lemma lem148159 (x : nat) (n : nat) (m : nat) (h1 : term134 x) (h2 : term282 x n m) : term266 n x m.
Proof. exact (or_elim (@lem147842 x n m h2) (fun h0 : x = term122 => @lem148158 n m x h0) (fun h0 : Peano.le n m => @lem148156 x n m h1 h0)). Qed.
Lemma lem148160 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : term284 n x m.
Proof. exact (fun h0 : term282 x n m => @lem148159 x n m h1 h0). Qed.
Lemma lem148161 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : term279 n x m.
Proof. exact (EQ_MP (@lem147841 n m x h1) (@lem148160 n m x h1)). Qed.
Lemma lem148162 (n : nat) (m : nat) (x : nat) (h1 : term134 x) : term267 n x m.
Proof. exact (EQ_MP (@lem147790 n x m) (@lem148161 n m x h1)). Qed.
Lemma lem148163 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : term253 m x n.
Proof. exact (EQ_MP (@lem147732 m x n) (@lem148162 n m x h1)). Qed.
Lemma lem148164 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : term252 x m n.
Proof. exact (EQ_MP (@lem147705 x m n) (@lem148163 m n x h1)). Qed.
Lemma lem148165 (x : nat) (m : nat) (n : nat) (h1 : term148 x m n) : term148 x m n.
Proof. exact (h1). Qed.
Lemma lem148166 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem148167 (x : nat) (h1 : term144 x) : term144 x.
Proof. exact (h1). Qed.
Lemma lem148169 (n : nat) (m : nat) : (Peano.lt m n) = (term95 n m).
Proof. exact (EQ_MP (@lem146939 n m) (@lem146938 m n)). Qed.
Lemma lem148176 (m : nat) (n : nat) (h1 : Peano.lt m n) : term95 n m.
Proof. exact (EQ_MP (@lem148169 n m) (@lem148166 m n h1)). Qed.
Lemma lem148177 (n : nat) (m : nat) (d : nat) (h1 : n = (term70 m d)) : n = (term70 m d).
Proof. exact (h1). Qed.
Lemma lem148178 (m : nat) (x : nat) : (term353 m x) = (term353 m x).
Proof. exact (eq_refl (term353 m x)). Qed.
Lemma lem148179 (x : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (term70 m d)) : (term354 m x n) = (term355 x m d).
Proof. exact (MK_COMB (@lem148178 m x) (@lem148177 n m d h1)). Qed.
Lemma lem148180 (x : nat) (m : nat) (d : nat) : (term355 x m d) = (term356 x m d).
Proof. exact (eq_refl (term355 x m d)). Qed.
Lemma lem148181 (m : nat) (x : nat) (n : nat) : (term357 m x n) = (term357 m x n).
Proof. exact (eq_refl (term357 m x n)). Qed.
Lemma lem148182 (n : nat) (x : nat) (m : nat) (d : nat) : ((term354 m x n) = (term355 x m d)) = ((term354 m x n) = (term356 x m d)).
Proof. exact (MK_COMB (@lem148181 m x n) (@lem148180 x m d)). Qed.
Lemma lem148183 (m : nat) (x : nat) (n : nat) : (term354 m x n) = (term139 m x n).
Proof. exact (eq_refl (term354 m x n)). Qed.
Lemma lem148184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem148185 (m : nat) (x : nat) (n : nat) : (term357 m x n) = (term141 m x n).
Proof. exact (MK_COMB (@lem148184) (@lem148183 m x n)). Qed.
Lemma lem148186 (x : nat) (m : nat) (d : nat) : (term356 x m d) = (term356 x m d).
Proof. exact (eq_refl (term356 x m d)). Qed.
Lemma lem148187 (n : nat) (x : nat) (m : nat) (d : nat) : ((term354 m x n) = (term356 x m d)) = ((term139 m x n) = (term356 x m d)).
Proof. exact (MK_COMB (@lem148185 m x n) (@lem148186 x m d)). Qed.
Lemma lem148188 (n : nat) (x : nat) (m : nat) (d : nat) : ((term354 m x n) = (term355 x m d)) = ((term139 m x n) = (term356 x m d)).
Proof. exact (TRANS (@lem148182 n x m d) (@lem148187 n x m d)). Qed.
Lemma lem148189 (x : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (term70 m d)) : (term139 m x n) = (term356 x m d).
Proof. exact (EQ_MP (@lem148188 n x m d) (@lem148179 x n m d h1)). Qed.
Lemma lem148190 (x : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (term70 m d)) : (term356 x m d) = (term139 m x n).
Proof. exact (SYM (@lem148189 x n m d h1)). Qed.
Lemma lem148192 (P : nat -> Prop) : term179 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem148193 (x : nat) (m : nat) : term358 x m.
Proof. exact (@lem148192 (term359 x m)). Qed.
Lemma lem148194 (x : nat) (m : nat) : (term360 x m) = (term361 x m).
Proof. exact (eq_refl (term360 x m)). Qed.
Lemma lem148195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem148196 (x : nat) (m : nat) : (term362 x m) = (term363 x m).
Proof. exact (MK_COMB (@lem148195) (@lem148194 x m)). Qed.
Lemma lem148197 (x : nat) (m : nat) (d : nat) : (term364 x m d) = (term356 x m d).
Proof. exact (eq_refl (term364 x m d)). Qed.
Lemma lem148198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem148199 (x : nat) (m : nat) (d : nat) : (term365 x m d) = (term366 x m d).
Proof. exact (MK_COMB (@lem148198) (@lem148197 x m d)). Qed.
Lemma lem148200 (x : nat) (m : nat) (d : nat) : (term367 x m d) = (term368 x m d).
Proof. exact (eq_refl (term367 x m d)). Qed.
Lemma lem148201 (x : nat) (m : nat) (d : nat) : (term369 x m d) = (term370 x m d).
Proof. exact (MK_COMB (@lem148199 x m d) (@lem148200 x m d)). Qed.
Lemma lem148202 (x : nat) (m : nat) : (term371 x m) = (term372 x m).
Proof. exact (fun_ext (fun d : nat => @lem148201 x m d)). Qed.
Lemma lem148203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem148204 (x : nat) (m : nat) : (term373 x m) = (term374 x m).
Proof. exact (MK_COMB (@lem148203) (@lem148202 x m)). Qed.
Lemma lem148205 (x : nat) (m : nat) : (term375 x m) = (term376 x m).
Proof. exact (MK_COMB (@lem148196 x m) (@lem148204 x m)). Qed.
Lemma lem148206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem148207 (x : nat) (m : nat) : (term377 x m) = (term378 x m).
Proof. exact (MK_COMB (@lem148206) (@lem148205 x m)). Qed.
Lemma lem148208 (x : nat) (m : nat) (d : nat) : (term364 x m d) = (term356 x m d).
Proof. exact (eq_refl (term364 x m d)). Qed.
Lemma lem148209 (x : nat) (m : nat) : (term379 x m) = (term359 x m).
Proof. exact (fun_ext (fun d : nat => @lem148208 x m d)). Qed.
Lemma lem148210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem148211 (x : nat) (m : nat) : (term380 x m) = (term381 x m).
Proof. exact (MK_COMB (@lem148210) (@lem148209 x m)). Qed.
Lemma lem148212 (x : nat) (m : nat) : (term358 x m) = (term382 x m).
Proof. exact (MK_COMB (@lem148207 x m) (@lem148211 x m)). Qed.
Lemma lem148213 (x : nat) (m : nat) : term382 x m.
Proof. exact (EQ_MP (@lem148212 x m) (@lem148193 x m)). Qed.
Lemma lem148214 (x : nat) (m : nat) (d : nat) (h1 : term356 x m d) : term356 x m d.
Proof. exact (h1). Qed.
Lemma lem148216 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (EQ_MP (@lem146918 m n) (@lem146917 m n)). Qed.
Lemma lem148217 (m : nat) : (term383 m) = (term384 m).
Proof. exact (@lem148216 m (NUMERAL 0)). Qed.
Lemma lem148219 (m : nat) : (term91 m) = m.
Proof. exact (EQ_MP (@lem146929 m) (@lem146928 m)). Qed.
Lemma lem148220 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem148221 (m : nat) : (term384 m) = (S m).
Proof. exact (MK_COMB (@lem148220) (@lem148219 m)). Qed.
Lemma lem148222 (m : nat) : (term383 m) = (S m).
Proof. exact (TRANS (@lem148217 m) (@lem148221 m)). Qed.
Lemma lem148223 (x : nat) : (Nat.pow x) = (Nat.pow x).
Proof. exact (eq_refl (Nat.pow x)). Qed.
Lemma lem148224 (x : nat) (m : nat) : (term385 x m) = (term62 x m).
Proof. exact (MK_COMB (@lem148223 x) (@lem148222 m)). Qed.
Lemma lem148226 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem146905 m n) (@lem146904 m n)). Qed.
Lemma lem148227 (x : nat) (m : nat) : (term62 x m) = (term63 x m).
Proof. exact (@lem148226 x m). Qed.
Lemma lem148228 (x : nat) (m : nat) : (term385 x m) = (term63 x m).
Proof. exact (TRANS (@lem148224 x m) (@lem148227 x m)). Qed.
Lemma lem148229 (x : nat) (m : nat) : (term137 x m) = (term137 x m).
Proof. exact (eq_refl (term137 x m)). Qed.
Lemma lem148230 (x : nat) (m : nat) : (term361 x m) = (term386 x m).
Proof. exact (MK_COMB (@lem148229 x m) (@lem148228 x m)). Qed.
Lemma lem148231 (x : nat) (m : nat) : (term386 x m) = (term361 x m).
Proof. exact (SYM (@lem148230 x m)). Qed.
Lemma lem148233 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (EQ_MP (@lem146918 m n) (@lem146917 m n)). Qed.
Lemma lem148234 (m : nat) (d : nat) : (term387 m d) = (term388 m d).
Proof. exact (@lem148233 m (S d)). Qed.
Lemma lem148236 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (EQ_MP (@lem146918 m n) (@lem146917 m n)). Qed.
Lemma lem148237 (m : nat) (d : nat) : (term70 m d) = (term71 m d).
Proof. exact (@lem148236 m d). Qed.
Lemma lem148238 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem148239 (m : nat) (d : nat) : (term388 m d) = (term389 m d).
Proof. exact (MK_COMB (@lem148238) (@lem148237 m d)). Qed.
Lemma lem148240 (m : nat) (d : nat) : (term387 m d) = (term389 m d).
Proof. exact (TRANS (@lem148234 m d) (@lem148239 m d)). Qed.
Lemma lem148241 (x : nat) : (Nat.pow x) = (Nat.pow x).
Proof. exact (eq_refl (Nat.pow x)). Qed.
Lemma lem148242 (x : nat) (m : nat) (d : nat) : (term390 x m d) = (term391 x m d).
Proof. exact (MK_COMB (@lem148241 x) (@lem148240 m d)). Qed.
Lemma lem148244 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem146905 m n) (@lem146904 m n)). Qed.
Lemma lem148245 (x : nat) (m : nat) (d : nat) : (term391 x m d) = (term392 x m d).
Proof. exact (@lem148244 x (term71 m d)). Qed.
Lemma lem148247 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem146905 m n) (@lem146904 m n)). Qed.
Lemma lem148248 (x : nat) (m : nat) (d : nat) : (term325 x m d) = (term326 x m d).
Proof. exact (@lem148247 x (Nat.add m d)). Qed.
Lemma lem148249 (x : nat) : (Nat.mul x) = (Nat.mul x).
Proof. exact (eq_refl (Nat.mul x)). Qed.
Lemma lem148250 (x : nat) (m : nat) (d : nat) : (term392 x m d) = (term393 x m d).
Proof. exact (MK_COMB (@lem148249 x) (@lem148248 x m d)). Qed.
Lemma lem148251 (x : nat) (m : nat) (d : nat) : (term391 x m d) = (term393 x m d).
Proof. exact (TRANS (@lem148245 x m d) (@lem148250 x m d)). Qed.
Lemma lem148252 (x : nat) (m : nat) (d : nat) : (term390 x m d) = (term393 x m d).
Proof. exact (TRANS (@lem148242 x m d) (@lem148251 x m d)). Qed.
Lemma lem148253 (x : nat) (m : nat) : (term137 x m) = (term137 x m).
Proof. exact (eq_refl (term137 x m)). Qed.
Lemma lem148254 (x : nat) (m : nat) (d : nat) : (term368 x m d) = (term394 x m d).
Proof. exact (MK_COMB (@lem148253 x m) (@lem148252 x m d)). Qed.
Lemma lem148255 (x : nat) (m : nat) (d : nat) : (term394 x m d) = (term368 x m d).
Proof. exact (SYM (@lem148254 x m d)). Qed.
Lemma lem148257 (m : nat) (p : nat) : term83 m p.
Proof. exact (EQ_MP (@lem146898 m p) (@lem146897 m p)). Qed.
Lemma lem148258 (x : nat) (m : nat) : term395 x m.
Proof. exact (@lem148257 (Nat.pow x m) (term63 x m)). Qed.
Lemma lem148259 (n : nat) : term396 n.
Proof. exact (@lem146697 n). Qed.
Lemma lem148260 (n : nat) : (term396 n) = (term397 n).
Proof. exact (eq_refl (term396 n)). Qed.
Lemma lem148261 (n : nat) : term397 n.
Proof. exact (EQ_MP (@lem148260 n) (@lem148259 n)). Qed.
Lemma lem148262 (n : nat) (x : nat) : term398 n x.
Proof. exact (@lem148261 n x). Qed.
Lemma lem148263 (x : nat) (n : nat) : (term398 n x) = ((term399 x n) = (term400 x n)).
Proof. exact (eq_refl (term398 n x)). Qed.
Lemma lem148265 (m : nat) : term401 m.
Proof. exact (@lem100722 m). Qed.
Lemma lem148266 (m : nat) : (term401 m) = (term402 m).
Proof. exact (eq_refl (term401 m)). Qed.
Lemma lem148267 (m : nat) : term402 m.
Proof. exact (EQ_MP (@lem148266 m) (@lem148265 m)). Qed.
Lemma lem148268 (m : nat) (n : nat) : term403 m n.
Proof. exact (@lem148267 m n). Qed.
Lemma lem148269 (m : nat) (n : nat) : (term403 m n) = ((term404 m n) = (term405 n)).
Proof. exact (eq_refl (term403 m n)). Qed.
Lemma lem148271 (n : nat) : term406 n.
Proof. exact (@lem84996 n). Qed.
Lemma lem148272 (n : nat) : (term406 n) = ((term407 n) = (Nat.add n n)).
Proof. exact (eq_refl (term406 n)). Qed.
Lemma lem148274 (x : nat) : term159 x.
Proof. exact (@lem82 (x = (NUMERAL 0))). Qed.
Lemma lem148292 (n : nat) : (term407 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem148272 n) (@lem148271 n)). Qed.
Lemma lem148293 (x : nat) (m : nat) : (term408 x m) = (term409 x m).
Proof. exact (@lem148292 (Nat.pow x m)). Qed.
Lemma lem148294 (x : nat) (m : nat) : (term137 x m) = (term137 x m).
Proof. exact (eq_refl (term137 x m)). Qed.
Lemma lem148295 (x : nat) (m : nat) : (term410 x m) = (term411 x m).
Proof. exact (MK_COMB (@lem148294 x m) (@lem148293 x m)). Qed.
Lemma lem148297 (m : nat) (n : nat) : (term404 m n) = (term405 n).
Proof. exact (EQ_MP (@lem148269 m n) (@lem148268 m n)). Qed.
Lemma lem148298 (x : nat) (m : nat) : (term411 x m) = (term399 x m).
Proof. exact (@lem148297 (Nat.pow x m) (Nat.pow x m)). Qed.
Lemma lem148300 (x : nat) (n : nat) : (term399 x n) = (term400 x n).
Proof. exact (EQ_MP (@lem148263 x n) (@lem148262 n x)). Qed.
Lemma lem148301 (x : nat) (m : nat) : (term399 x m) = (term400 x m).
Proof. exact (@lem148300 x m). Qed.
Lemma lem148305 (x : nat) (h1 : term134 x) : (x = (NUMERAL 0)) = False.
Proof. exact (@lem148274 x (@lem147262 x h1)). Qed.
Lemma lem148306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem148307 (x : nat) (h1 : term134 x) : (term134 x) = (~ False).
Proof. exact (MK_COMB (@lem148306) (@lem148305 x h1)). Qed.
Lemma lem148309 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem148310 (x : nat) (h1 : term134 x) : (term134 x) = True.
Proof. exact (TRANS (@lem148307 x h1) (@lem148309)). Qed.
Lemma lem148311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148312 (x : nat) (h1 : term134 x) : (term412 x) = (or True).
Proof. exact (MK_COMB (@lem148311) (@lem148310 x h1)). Qed.
Lemma lem148315 (m : nat) : (m = (NUMERAL 0)) = (m = (NUMERAL 0)).
Proof. exact (eq_refl (m = (NUMERAL 0))). Qed.
Lemma lem148316 (m : nat) (x : nat) (h1 : term134 x) : (term400 x m) = (term413 m).
Proof. exact (MK_COMB (@lem148312 x h1) (@lem148315 m)). Qed.
Lemma lem148318 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem148319 (m : nat) : (term413 m) = True.
Proof. exact (@lem148318 (m = (NUMERAL 0))). Qed.
Lemma lem148320 (m : nat) (x : nat) (h1 : term134 x) : (term400 x m) = True.
Proof. exact (TRANS (@lem148316 m x h1) (@lem148319 m)). Qed.
Lemma lem148321 (m : nat) (x : nat) (h1 : term134 x) : (term399 x m) = True.
Proof. exact (TRANS (@lem148301 x m) (@lem148320 m x h1)). Qed.
Lemma lem148322 (m : nat) (x : nat) (h1 : term134 x) : (term411 x m) = True.
Proof. exact (TRANS (@lem148298 x m) (@lem148321 m x h1)). Qed.
Lemma lem148323 (m : nat) (x : nat) (h1 : term134 x) : (term410 x m) = True.
Proof. exact (TRANS (@lem148295 x m) (@lem148322 m x h1)). Qed.
Lemma lem148324 (m : nat) (x : nat) (h1 : term134 x) : True = (term410 x m).
Proof. exact (SYM (@lem148323 m x h1)). Qed.
Lemma lem148325 (m : nat) (x : nat) (h1 : term134 x) : term410 x m.
Proof. exact (EQ_MP (@lem148324 m x h1) (@lem0)). Qed.
Lemma lem148326 (m : nat) : term44 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem148327 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem148328 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem148327 m) (@lem148326 m)). Qed.
Lemma lem148329 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem148328 m n). Qed.
Lemma lem148330 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem148331 (m : nat) (n : nat) : term47 m n.
Proof. exact (EQ_MP (@lem148330 m n) (@lem148329 m n)). Qed.
Lemma lem148332 (m : nat) (n : nat) (p : nat) : term48 m n p.
Proof. exact (@lem148331 m n p). Qed.
Lemma lem148333 (m : nat) (n : nat) (p : nat) : (term48 m n p) = ((term49 m n p) = (term50 m n p)).
Proof. exact (eq_refl (term48 m n p)). Qed.
Lemma lem148348 (x : nat) : (term144 x) = ((term144 x) = True).
Proof. exact (@lem7 (term144 x)). Qed.
Lemma lem148353 (m : nat) (n : nat) (p : nat) : (term49 m n p) = (term50 m n p).
Proof. exact (EQ_MP (@lem148333 m n p) (@lem148332 m n p)). Qed.
Lemma lem148354 (x : nat) (m : nat) : (term414 x m) = (term415 x m).
Proof. exact (@lem148353 term163 x (Nat.pow x m)). Qed.
Lemma lem148358 (x : nat) (h1 : term144 x) : (term144 x) = True.
Proof. exact (EQ_MP (@lem148348 x) (@lem148167 x h1)). Qed.
Lemma lem148359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem148360 (x : nat) (h1 : term144 x) : (term416 x) = (or True).
Proof. exact (MK_COMB (@lem148359) (@lem148358 x h1)). Qed.
Lemma lem148363 (x : nat) (m : nat) : ((Nat.pow x m) = (NUMERAL 0)) = ((Nat.pow x m) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.pow x m) = (NUMERAL 0))). Qed.
Lemma lem148364 (m : nat) (x : nat) (h1 : term144 x) : (term415 x m) = (term417 x m).
Proof. exact (MK_COMB (@lem148360 x h1) (@lem148363 x m)). Qed.
Lemma lem148366 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem148367 (x : nat) (m : nat) : (term417 x m) = True.
Proof. exact (@lem148366 ((Nat.pow x m) = (NUMERAL 0))). Qed.
Lemma lem148368 (m : nat) (x : nat) (h1 : term144 x) : (term415 x m) = True.
Proof. exact (TRANS (@lem148364 m x h1) (@lem148367 x m)). Qed.
Lemma lem148369 (m : nat) (x : nat) (h1 : term144 x) : (term414 x m) = True.
Proof. exact (TRANS (@lem148354 x m) (@lem148368 m x h1)). Qed.
Lemma lem148370 (m : nat) (x : nat) (h1 : term144 x) : True = (term414 x m).
Proof. exact (SYM (@lem148369 m x h1)). Qed.
Lemma lem148371 (m : nat) (x : nat) (h1 : term144 x) : term414 x m.
Proof. exact (EQ_MP (@lem148370 m x h1) (@lem0)). Qed.
Lemma lem148372 (m : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term418 x m.
Proof. exact (conj (@lem148325 m x h1) (@lem148371 m x h2)). Qed.
Lemma lem148373 (m : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term419 x m.
Proof. exact (ex_intro (term420 x m) (term408 x m) (@lem148372 m x h1 h2)). Qed.
Lemma lem148374 (m : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term386 x m.
Proof. exact (@lem148258 x m (@lem148373 m x h1 h2)). Qed.
Lemma lem148376 (m : nat) (p : nat) : term83 m p.
Proof. exact (EQ_MP (@lem146870 m p) (@lem146869 m p)). Qed.
Lemma lem148377 (x : nat) (m : nat) (d : nat) : term421 x m d.
Proof. exact (@lem148376 (Nat.pow x m) (term393 x m d)). Qed.
Lemma lem148395 (x : nat) (m : nat) (d : nat) : (term356 x m d) = ((term356 x m d) = True).
Proof. exact (@lem7 (term356 x m d)). Qed.
Lemma lem148400 (x : nat) (m : nat) (d : nat) (h1 : term356 x m d) : (term356 x m d) = True.
Proof. exact (EQ_MP (@lem148395 x m d) (@lem148214 x m d h1)). Qed.
Lemma lem148401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem148402 (x : nat) (m : nat) (d : nat) (h1 : term356 x m d) : (term422 x m d) = (and True).
Proof. exact (MK_COMB (@lem148401) (@lem148400 x m d h1)). Qed.
Lemma lem148403 (x : nat) (m : nat) (d : nat) : (term423 x m d) = (term423 x m d).
Proof. exact (eq_refl (term423 x m d)). Qed.
Lemma lem148404 (x : nat) (m : nat) (d : nat) (h1 : term356 x m d) : (term424 x m d) = (term425 x m d).
Proof. exact (MK_COMB (@lem148402 x m d h1) (@lem148403 x m d)). Qed.
Lemma lem148406 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem148407 (x : nat) (m : nat) (d : nat) : (term425 x m d) = (term423 x m d).
Proof. exact (@lem148406 (term423 x m d)). Qed.
Lemma lem148408 (x : nat) (m : nat) (d : nat) (h1 : term356 x m d) : (term424 x m d) = (term423 x m d).
Proof. exact (TRANS (@lem148404 x m d h1) (@lem148407 x m d)). Qed.
Lemma lem148409 (x : nat) (m : nat) (d : nat) (h1 : term356 x m d) : (term423 x m d) = (term424 x m d).
Proof. exact (SYM (@lem148408 x m d h1)). Qed.
Lemma lem148411 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (EQ_MP (@lem146827 m n) (@lem146826 m n)). Qed.
Lemma lem148412 (m : nat) (d : nat) : (term70 m d) = (term71 m d).
Proof. exact (@lem148411 m d). Qed.
Lemma lem148413 (x : nat) : (Nat.pow x) = (Nat.pow x).
Proof. exact (eq_refl (Nat.pow x)). Qed.
Lemma lem148414 (x : nat) (m : nat) (d : nat) : (term324 x m d) = (term325 x m d).
Proof. exact (MK_COMB (@lem148413 x) (@lem148412 m d)). Qed.
Lemma lem148416 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (EQ_MP (@lem146814 m n) (@lem146813 m n)). Qed.
Lemma lem148417 (x : nat) (m : nat) (d : nat) : (term325 x m d) = (term326 x m d).
Proof. exact (@lem148416 x (Nat.add m d)). Qed.
Lemma lem148418 (x : nat) (m : nat) (d : nat) : (term324 x m d) = (term326 x m d).
Proof. exact (TRANS (@lem148414 x m d) (@lem148417 x m d)). Qed.
Lemma lem148419 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem148420 (x : nat) (m : nat) (d : nat) : (term426 x m d) = (term427 x m d).
Proof. exact (MK_COMB (@lem148419) (@lem148418 x m d)). Qed.
Lemma lem148422 (m : nat) (n : nat) (p : nat) : (term56 m n p) = (term57 m n p).
Proof. exact (EQ_MP (@lem146807 m n p) (@lem146806 m n p)). Qed.
Lemma lem148423 (x : nat) (m : nat) (d : nat) : (term393 x m d) = (term428 x m d).
Proof. exact (@lem148422 x x (term333 x m d)). Qed.
Lemma lem148424 (x : nat) (m : nat) (d : nat) : (term423 x m d) = (term429 x m d).
Proof. exact (MK_COMB (@lem148420 x m d) (@lem148423 x m d)). Qed.
Lemma lem148426 (m : nat) (n : nat) (p : nat) : (term49 m n p) = (term50 m n p).
Proof. exact (EQ_MP (@lem146798 m n p) (@lem146797 m n p)). Qed.
Lemma lem148427 (x : nat) (m : nat) (d : nat) : (term429 x m d) = (term430 x m d).
Proof. exact (@lem148426 x (Nat.mul x x) (term333 x m d)). Qed.
Lemma lem148432 (x : nat) (m : nat) (d : nat) : (term423 x m d) = (term430 x m d).
Proof. exact (TRANS (@lem148424 x m d) (@lem148427 x m d)). Qed.
Lemma lem148433 (x : nat) (m : nat) (d : nat) : (term430 x m d) = (term423 x m d).
Proof. exact (SYM (@lem148432 x m d)). Qed.
Lemma lem148435 (m : nat) (p : nat) : term38 m p.
Proof. exact (EQ_MP (@lem146789 m p) (@lem146788 m p)). Qed.
Lemma lem148436 (x : nat) : term431 x.
Proof. exact (@lem148435 x (Nat.mul x x)). Qed.
Lemma lem148440 (m : nat) : (term26 m) = m.
Proof. exact (EQ_MP (@lem146749 m) (@lem146748 m)). Qed.
Lemma lem148441 (x : nat) : (term26 x) = x.
Proof. exact (@lem148440 x). Qed.
Lemma lem148442 (x : nat) : (Peano.le x) = (Peano.le x).
Proof. exact (eq_refl (Peano.le x)). Qed.
Lemma lem148443 (x : nat) : (term432 x) = (Peano.le x x).
Proof. exact (MK_COMB (@lem148442 x) (@lem148441 x)). Qed.
Lemma lem148445 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem146727 n) (@lem146726 n)). Qed.
Lemma lem148446 (x : nat) : (Peano.le x x) = True.
Proof. exact (@lem148445 x). Qed.
Lemma lem148447 (x : nat) : (term432 x) = True.
Proof. exact (TRANS (@lem148443 x) (@lem148446 x)). Qed.
Lemma lem148448 (x : nat) : True = (term432 x).
Proof. exact (SYM (@lem148447 x)). Qed.
Lemma lem148449 (x : nat) : term432 x.
Proof. exact (EQ_MP (@lem148448 x) (@lem0)). Qed.
Lemma lem148451 (m : nat) (n : nat) (p : nat) : (term18 n m p) = (term19 m n p).
Proof. exact (EQ_MP (@lem146722 m n p) (@lem146721 m n p)). Qed.
Lemma lem148452 (x : nat) : (term433 x) = (term434 x).
Proof. exact (@lem148451 x term122 x). Qed.
Lemma lem148457 (x : nat) : (term434 x) = (term433 x).
Proof. exact (SYM (@lem148452 x)). Qed.
Lemma lem148458 (x : nat) : (term337 x) = (term338 x).
Proof. exact (@lem10568 (term339 x) (term134 x)). Qed.
Lemma lem148459 (x : nat) : (term338 x) = (term337 x).
Proof. exact (SYM (@lem148458 x)). Qed.
Lemma lem148463 (n : nat) (m : nat) : (term12 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem146713 n m) (@lem146712 m n)). Qed.
Lemma lem148464 (x : nat) : (term340 x) = (term341 x).
Proof. exact (@lem148463 x term122). Qed.
Lemma lem148465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem148466 (x : nat) : (term342 x) = (term343 x).
Proof. exact (MK_COMB (@lem148465) (@lem148464 x)). Qed.
Lemma lem148468 (t : Prop) : (term344 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem148469 (x : nat) : (term345 x) = (x = (NUMERAL 0)).
Proof. exact (@lem148468 (x = (NUMERAL 0))). Qed.
Lemma lem148472 (x : nat) : (term338 x) = (term346 x).
Proof. exact (MK_COMB (@lem148466 x) (@lem148469 x)). Qed.
Lemma lem148475 (x : nat) : (term346 x) = (term338 x).
Proof. exact (SYM (@lem148472 x)). Qed.
Lemma lem148479 : term122 = term165.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem148480 (x : nat) : (Peano.lt x) = (Peano.lt x).
Proof. exact (eq_refl (Peano.lt x)). Qed.
Lemma lem148481 (x : nat) : (term341 x) = (term270 x).
Proof. exact (MK_COMB (@lem148480 x) (@lem148479)). Qed.
Lemma lem148483 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem146703 m n) (@lem146702 m n)). Qed.
Lemma lem148484 (x : nat) : (term270 x) = (term271 x).
Proof. exact (@lem148483 x (NUMERAL 0)). Qed.
Lemma lem148490 (m : nat) : (term8 m) = False.
Proof. exact (EQ_MP (@lem146707 m) (@lem146706 m)). Qed.
Lemma lem148491 (x : nat) : (term8 x) = False.
Proof. exact (@lem148490 x). Qed.
Lemma lem148492 (x : nat) : (term272 x) = (term272 x).
Proof. exact (eq_refl (term272 x)). Qed.
Lemma lem148493 (x : nat) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem148492 x) (@lem148491 x)). Qed.
Lemma lem148495 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem148496 (x : nat) : (term273 x) = (x = (NUMERAL 0)).
Proof. exact (@lem148495 (x = (NUMERAL 0))). Qed.
Lemma lem148499 (x : nat) : (term271 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem148493 x) (@lem148496 x)). Qed.
Lemma lem148500 (x : nat) : (term270 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem148484 x) (@lem148499 x)). Qed.
Lemma lem148501 (x : nat) : (term341 x) = (x = (NUMERAL 0)).
Proof. exact (TRANS (@lem148481 x) (@lem148500 x)). Qed.
Lemma lem148502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem148503 (x : nat) : (term343 x) = (term347 x).
Proof. exact (MK_COMB (@lem148502) (@lem148501 x)). Qed.
Lemma lem148506 (x : nat) : (x = (NUMERAL 0)) = (x = (NUMERAL 0)).
Proof. exact (eq_refl (x = (NUMERAL 0))). Qed.
Lemma lem148507 (x : nat) : (term346 x) = (term348 x).
Proof. exact (MK_COMB (@lem148503 x) (@lem148506 x)). Qed.
Lemma lem148511 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem148512 (x : nat) : (term348 x) = True.
Proof. exact (@lem148511 (x = (NUMERAL 0))). Qed.
Lemma lem148513 (x : nat) : (term346 x) = True.
Proof. exact (TRANS (@lem148507 x) (@lem148512 x)). Qed.
Lemma lem148514 (x : nat) : True = (term346 x).
Proof. exact (SYM (@lem148513 x)). Qed.
Lemma lem148515 (x : nat) : term346 x.
Proof. exact (EQ_MP (@lem148514 x) (@lem0)). Qed.
Lemma lem148516 (x : nat) : term338 x.
Proof. exact (EQ_MP (@lem148475 x) (@lem148515 x)). Qed.
Lemma lem148517 (x : nat) : term337 x.
Proof. exact (EQ_MP (@lem148459 x) (@lem148516 x)). Qed.
Lemma lem148518 (x : nat) (h1 : term134 x) : term339 x.
Proof. exact (@lem148517 x (@lem147262 x h1)). Qed.
Lemma lem148519 (x : nat) (h1 : term134 x) : term434 x.
Proof. exact (or_intro2 (x = (NUMERAL 0)) (@lem148518 x h1)). Qed.
Lemma lem148520 (x : nat) (h1 : term134 x) : term433 x.
Proof. exact (EQ_MP (@lem148457 x) (@lem148519 x h1)). Qed.
Lemma lem148521 (x : nat) (h1 : term134 x) : term435 x.
Proof. exact (conj (@lem148449 x) (@lem148520 x h1)). Qed.
Lemma lem148522 (x : nat) (h1 : term134 x) : term436 x.
Proof. exact (ex_intro (term437 x) (term26 x) (@lem148521 x h1)). Qed.
Lemma lem148523 (x : nat) (h1 : term134 x) : term438 x.
Proof. exact (@lem148436 x (@lem148522 x h1)). Qed.
Lemma lem148524 (m : nat) (d : nat) (x : nat) (h1 : term134 x) : term430 x m d.
Proof. exact (or_intro1 (@lem148523 x h1) ((term333 x m d) = (NUMERAL 0))). Qed.
Lemma lem148525 (m : nat) (d : nat) (x : nat) (h1 : term134 x) : term423 x m d.
Proof. exact (EQ_MP (@lem148433 x m d) (@lem148524 m d x h1)). Qed.
Lemma lem148526 (x : nat) (m : nat) (d : nat) (h1 : term134 x) (h2 : term356 x m d) : term424 x m d.
Proof. exact (EQ_MP (@lem148409 x m d h2) (@lem148525 m d x h1)). Qed.
Lemma lem148527 (x : nat) (m : nat) (d : nat) (h1 : term134 x) (h2 : term356 x m d) : term439 x m d.
Proof. exact (ex_intro (term440 x m d) (term324 x m d) (@lem148526 x m d h1 h2)). Qed.
Lemma lem148528 (x : nat) (m : nat) (d : nat) (h1 : term134 x) (h2 : term356 x m d) : term394 x m d.
Proof. exact (@lem148377 x m d (@lem148527 x m d h1 h2)). Qed.
Lemma lem148529 (x : nat) (m : nat) (d : nat) (h1 : term134 x) (h2 : term356 x m d) : term368 x m d.
Proof. exact (EQ_MP (@lem148255 x m d) (@lem148528 x m d h1 h2)). Qed.
Lemma lem148530 (m : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term361 x m.
Proof. exact (EQ_MP (@lem148231 x m) (@lem148374 m x h1 h2)). Qed.
Lemma lem148531 (m : nat) (d : nat) (x : nat) (h1 : term134 x) : term370 x m d.
Proof. exact (fun h0 : term356 x m d => @lem148529 x m d h1 h0). Qed.
Lemma lem148536 (m : nat) (x : nat) (h1 : term134 x) : term374 x m.
Proof. exact (fun d : nat => @lem148531 m d x h1). Qed.
Lemma lem148537 (m : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term376 x m.
Proof. exact (conj (@lem148530 m x h1 h2) (@lem148536 m x h1)). Qed.
Lemma lem148538 (m : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term381 x m.
Proof. exact (@lem148213 x m (@lem148537 m x h1 h2)). Qed.
Lemma lem148539 (m : nat) (d : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term364 x m d.
Proof. exact (@lem148538 m x h1 h2 d). Qed.
Lemma lem148540 (x : nat) (m : nat) (d : nat) : (term364 x m d) = (term356 x m d).
Proof. exact (eq_refl (term364 x m d)). Qed.
Lemma lem148541 (m : nat) (d : nat) (x : nat) (h1 : term134 x) (h2 : term144 x) : term356 x m d.
Proof. exact (EQ_MP (@lem148540 x m d) (@lem148539 m d x h1 h2)). Qed.
Lemma lem148542 (x : nat) (n : nat) (m : nat) (d : nat) (h1 : term134 x) (h2 : term144 x) (h3 : n = (term70 m d)) : term139 m x n.
Proof. exact (EQ_MP (@lem148190 x n m d h3) (@lem148541 m d x h1 h2)). Qed.
Lemma lem148543 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : Peano.lt m n) (h3 : term144 x) : term139 m x n.
Proof. exact (ex_elim (@lem148176 m n h2) (fun d : nat => fun h0 : term441 n m d => @lem148542 x n m d h1 h3 h0)). Qed.
Lemma lem148544 (x : nat) (m : nat) (n : nat) (h1 : term148 x m n) : Peano.lt m n.
Proof. exact (proj2 (@lem148165 x m n h1)). Qed.
Lemma lem148545 (x : nat) (m : nat) (n : nat) (h1 : term148 x m n) : term144 x.
Proof. exact (proj1 (@lem148165 x m n h1)). Qed.
Lemma lem148546 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : Peano.lt m n) (h3 : term144 x) : (Peano.lt m n) = (term139 m x n).
Proof. exact (prop_ext (fun h4 : Peano.lt m n => @lem148543 m n x h1 h2 h3) (fun h4 : term139 m x n => @lem148166 m n h2)). Qed.
Lemma lem148547 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : Peano.lt m n) (h3 : term144 x) : term139 m x n.
Proof. exact (EQ_MP (@lem148546 m n x h1 h2 h3) (@lem148166 m n h2)). Qed.
Lemma lem148548 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : Peano.lt m n) (h3 : term144 x) : (term144 x) = (term139 m x n).
Proof. exact (prop_ext (fun h4 : term144 x => @lem148547 m n x h1 h2 h3) (fun h4 : term139 m x n => @lem148167 x h3)). Qed.
Lemma lem148549 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : Peano.lt m n) (h3 : term144 x) : term139 m x n.
Proof. exact (EQ_MP (@lem148548 m n x h1 h2 h3) (@lem148167 x h3)). Qed.
Lemma lem148550 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : term148 x m n) (h3 : term144 x) : (Peano.lt m n) = (term139 m x n).
Proof. exact (prop_ext (fun h4 : Peano.lt m n => @lem148549 m n x h1 h4 h3) (fun h4 : term139 m x n => @lem148544 x m n h2)). Qed.
Lemma lem148551 (m : nat) (n : nat) (x : nat) (h1 : term134 x) (h2 : term148 x m n) (h3 : term144 x) : term139 m x n.
Proof. exact (EQ_MP (@lem148550 m n x h1 h2 h3) (@lem148544 x m n h2)). Qed.
Lemma lem148552 (x : nat) (m : nat) (n : nat) (h1 : term134 x) (h2 : term148 x m n) : (term144 x) = (term139 m x n).
Proof. exact (prop_ext (fun h3 : term144 x => @lem148551 m n x h1 h2 h3) (fun h3 : term139 m x n => @lem148545 x m n h2)). Qed.
Lemma lem148553 (x : nat) (m : nat) (n : nat) (h1 : term134 x) (h2 : term148 x m n) : term139 m x n.
Proof. exact (EQ_MP (@lem148552 x m n h1 h2) (@lem148545 x m n h2)). Qed.
Lemma lem148554 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : term442 m x n.
Proof. exact (fun h0 : term148 x m n => @lem148553 x m n h1 h0). Qed.
Lemma lem148555 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : term443 m x n.
Proof. exact (conj (@lem148164 m n x h1) (@lem148554 m n x h1)). Qed.
Lemma lem148556 (x : nat) (m : nat) (n : nat) : (term443 m x n) = ((term139 m x n) = (term148 x m n)).
Proof. exact (@lem32 (term139 m x n) (term148 x m n)). Qed.
Lemma lem148557 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : (term139 m x n) = (term148 x m n).
Proof. exact (EQ_MP (@lem148556 x m n) (@lem148555 m n x h1)). Qed.
Lemma lem148558 (m : nat) (n : nat) (x : nat) (h1 : term134 x) : (term139 m x n) = (term157 x m n).
Proof. exact (EQ_MP (@lem147389 m n x h1) (@lem148557 m n x h1)). Qed.
Lemma lem148559 (m : nat) (n : nat) (x : nat) (h1 : x = (NUMERAL 0)) : (term139 m x n) = (term157 x m n).
Proof. exact (EQ_MP (@lem147339 m n x h1) (@lem147703 m n)). Qed.
Lemma lem148560 (x : nat) (m : nat) (n : nat) : (term139 m x n) = (term157 x m n).
Proof. exact (or_elim (@lem147260 x) (fun h0 : x = (NUMERAL 0) => @lem148559 m n x h0) (fun h0 : term134 x => @lem148558 m n x h0)). Qed.
Lemma lem148565 (x : nat) (m : nat) : term444 x m.
Proof. exact (fun n : nat => @lem148560 x m n). Qed.
Lemma lem148570 (x : nat) : term445 x.
Proof. exact (fun m : nat => @lem148565 x m). Qed.
Lemma lem148575 : term446.
Proof. exact (fun x : nat => @lem148570 x). Qed.
