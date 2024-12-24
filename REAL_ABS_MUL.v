Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_MUL_term_abbrevs.
Require Import REAL_ABS_NEG_spec.
Require Import REAL_LE_NEGTOTAL_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1340049_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1581690 (x : real) (h1 : (term0 x) = (real_abs x)) : (term0 x) = (real_abs x).
Proof. exact (h1). Qed.
Lemma lem1581691 (x : real) (h1 : (term0 x) = (real_abs x)) : (real_abs x) = (term0 x).
Proof. exact (SYM (@lem1581690 x h1)). Qed.
Lemma lem1581692 (x : real) (h1 : (real_abs x) = (term0 x)) : (real_abs x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1581693 (x : real) (h1 : (real_abs x) = (term0 x)) : (term0 x) = (real_abs x).
Proof. exact (SYM (@lem1581692 x h1)). Qed.
Lemma lem1581694 (x : real) : ((term0 x) = (real_abs x)) = ((real_abs x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (real_abs x) => @lem1581691 x h1) (fun h1 : (real_abs x) = (term0 x) => @lem1581693 x h1)). Qed.
Lemma lem1581695 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1581694 x)). Qed.
Lemma lem1581696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1581697 : term3 = term4.
Proof. exact (MK_COMB (@lem1581696) (@lem1581695)). Qed.
Lemma lem1581698 : term4.
Proof. exact (EQ_MP (@lem1581697) (@lem1365032)). Qed.
Lemma lem1581699 (x : real) : term5 x.
Proof. exact (@lem1581698 x). Qed.
Lemma lem1581700 (x : real) : (term5 x) = ((real_abs x) = (term0 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1581703 (x : real) (h1 : (term0 x) = (real_abs x)) : (term0 x) = (real_abs x).
Proof. exact (h1). Qed.
Lemma lem1581704 (x : real) (h1 : (term0 x) = (real_abs x)) : (real_abs x) = (term0 x).
Proof. exact (SYM (@lem1581703 x h1)). Qed.
Lemma lem1581705 (x : real) (h1 : (real_abs x) = (term0 x)) : (real_abs x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1581706 (x : real) (h1 : (real_abs x) = (term0 x)) : (term0 x) = (real_abs x).
Proof. exact (SYM (@lem1581705 x h1)). Qed.
Lemma lem1581707 (x : real) : ((term0 x) = (real_abs x)) = ((real_abs x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (real_abs x) => @lem1581704 x h1) (fun h1 : (real_abs x) = (term0 x) => @lem1581706 x h1)). Qed.
Lemma lem1581708 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1581707 x)). Qed.
Lemma lem1581709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1581710 : term3 = term4.
Proof. exact (MK_COMB (@lem1581709) (@lem1581708)). Qed.
Lemma lem1581711 : term4.
Proof. exact (EQ_MP (@lem1581710) (@lem1365032)). Qed.
Lemma lem1581712 (x : real) : term5 x.
Proof. exact (@lem1581711 x). Qed.
Lemma lem1581713 (x : real) : (term5 x) = ((real_abs x) = (term0 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1581715 (x : real) : term6 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1581716 (x : real) : (term6 x) = ((term7 x) = x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1581718 (x : real) : term8 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1581719 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1581720 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1581719 x) (@lem1581718 x)). Qed.
Lemma lem1581721 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1581720 x y). Qed.
Lemma lem1581722 (x : real) (y : real) : (term10 x y) = ((term11 x y) = (term12 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1581724 (x : real) : term13 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1581725 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1581726 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1581725 x) (@lem1581724 x)). Qed.
Lemma lem1581727 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1581726 x y). Qed.
Lemma lem1581728 (x : real) (y : real) : (term15 x y) = ((term16 x y) = (term12 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1581730 (x : real) : term17 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1581731 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1581732 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem1581731 x) (@lem1581730 x)). Qed.
Lemma lem1581733 (x : real) (y : real) : term19 x y.
Proof. exact (@lem1581732 x y). Qed.
Lemma lem1581734 (x : real) (y : real) : (term19 x y) = (term20 x y).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1581737 (x : real) (h1 : (term0 x) = (real_abs x)) : (term0 x) = (real_abs x).
Proof. exact (h1). Qed.
Lemma lem1581738 (x : real) (h1 : (term0 x) = (real_abs x)) : (real_abs x) = (term0 x).
Proof. exact (SYM (@lem1581737 x h1)). Qed.
Lemma lem1581739 (x : real) (h1 : (real_abs x) = (term0 x)) : (real_abs x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1581740 (x : real) (h1 : (real_abs x) = (term0 x)) : (term0 x) = (real_abs x).
Proof. exact (SYM (@lem1581739 x h1)). Qed.
Lemma lem1581741 (x : real) : ((term0 x) = (real_abs x)) = ((real_abs x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (real_abs x) => @lem1581738 x h1) (fun h1 : (real_abs x) = (term0 x) => @lem1581740 x h1)). Qed.
Lemma lem1581742 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1581741 x)). Qed.
Lemma lem1581743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1581744 : term3 = term4.
Proof. exact (MK_COMB (@lem1581743) (@lem1581742)). Qed.
Lemma lem1581745 : term4.
Proof. exact (EQ_MP (@lem1581744) (@lem1365032)). Qed.
Lemma lem1581746 (x : real) : term5 x.
Proof. exact (@lem1581745 x). Qed.
Lemma lem1581747 (x : real) : (term5 x) = ((real_abs x) = (term0 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1581749 (y : real) : term21 y.
Proof. exact (@lem1382820 y). Qed.
Lemma lem1581750 (y : real) : (term21 y) = (term22 y).
Proof. exact (eq_refl (term21 y)). Qed.
Lemma lem1581751 (y : real) : term22 y.
Proof. exact (EQ_MP (@lem1581750 y) (@lem1581749 y)). Qed.
Lemma lem1581752 (y : real) (h1 : term23 y) : term23 y.
Proof. exact (h1). Qed.
Lemma lem1581753 (y : real) (h1 : term24 y) : term24 y.
Proof. exact (h1). Qed.
Lemma lem1581755 (x : real) (h1 : (term0 x) = (real_abs x)) : (term0 x) = (real_abs x).
Proof. exact (h1). Qed.
Lemma lem1581756 (x : real) (h1 : (term0 x) = (real_abs x)) : (real_abs x) = (term0 x).
Proof. exact (SYM (@lem1581755 x h1)). Qed.
Lemma lem1581757 (x : real) (h1 : (real_abs x) = (term0 x)) : (real_abs x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem1581758 (x : real) (h1 : (real_abs x) = (term0 x)) : (term0 x) = (real_abs x).
Proof. exact (SYM (@lem1581757 x h1)). Qed.
Lemma lem1581759 (x : real) : ((term0 x) = (real_abs x)) = ((real_abs x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (real_abs x) => @lem1581756 x h1) (fun h1 : (real_abs x) = (term0 x) => @lem1581758 x h1)). Qed.
Lemma lem1581760 : term1 = term2.
Proof. exact (fun_ext (fun x : real => @lem1581759 x)). Qed.
Lemma lem1581761 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1581762 : term3 = term4.
Proof. exact (MK_COMB (@lem1581761) (@lem1581760)). Qed.
Lemma lem1581763 : term4.
Proof. exact (EQ_MP (@lem1581762) (@lem1365032)). Qed.
Lemma lem1581764 (x : real) : term5 x.
Proof. exact (@lem1581763 x). Qed.
Lemma lem1581765 (x : real) : (term5 x) = ((real_abs x) = (term0 x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1581767 (x : real) : term21 x.
Proof. exact (@lem1382820 x). Qed.
Lemma lem1581768 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1581769 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1581768 x) (@lem1581767 x)). Qed.
Lemma lem1581770 (x : real) (h1 : term23 x) : term23 x.
Proof. exact (h1). Qed.
Lemma lem1581771 (x : real) (h1 : term24 x) : term24 x.
Proof. exact (h1). Qed.
Lemma lem1581773 (x : real) : (real_abs x) = (term0 x).
Proof. exact (EQ_MP (@lem1581765 x) (@lem1581764 x)). Qed.
Lemma lem1581774 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1581775 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1581774) (@lem1581773 x)). Qed.
Lemma lem1581776 (y : real) : (real_abs y) = (real_abs y).
Proof. exact (eq_refl (real_abs y)). Qed.
Lemma lem1581777 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1581775 x) (@lem1581776 y)). Qed.
Lemma lem1581778 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1581779 (x : real) (y : real) : ((term30 x y) = (term27 x y)) = ((term30 x y) = (term28 x y)).
Proof. exact (MK_COMB (@lem1581778 x y) (@lem1581777 x y)). Qed.
Lemma lem1581780 (x : real) (y : real) : ((term30 x y) = (term28 x y)) = ((term30 x y) = (term27 x y)).
Proof. exact (SYM (@lem1581779 x y)). Qed.
Lemma lem1581782 (x : real) : (real_abs x) = (term0 x).
Proof. exact (EQ_MP (@lem1581747 x) (@lem1581746 x)). Qed.
Lemma lem1581783 (y : real) : (real_abs y) = (term0 y).
Proof. exact (@lem1581782 y). Qed.
Lemma lem1581784 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1581785 (x : real) (y : real) : (term27 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1581784 x) (@lem1581783 y)). Qed.
Lemma lem1581786 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1581787 (x : real) (y : real) : ((term30 x y) = (term27 x y)) = ((term30 x y) = (term31 x y)).
Proof. exact (MK_COMB (@lem1581786 x y) (@lem1581785 x y)). Qed.
Lemma lem1581788 (x : real) (y : real) : ((term30 x y) = (term31 x y)) = ((term30 x y) = (term27 x y)).
Proof. exact (SYM (@lem1581787 x y)). Qed.
Lemma lem1581790 (x : real) : (real_abs x) = (term0 x).
Proof. exact (EQ_MP (@lem1581747 x) (@lem1581746 x)). Qed.
Lemma lem1581791 (y : real) : (real_abs y) = (term0 y).
Proof. exact (@lem1581790 y). Qed.
Lemma lem1581792 (x : real) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1581793 (x : real) (y : real) : (term28 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1581792 x) (@lem1581791 y)). Qed.
Lemma lem1581794 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1581795 (x : real) (y : real) : ((term30 x y) = (term28 x y)) = ((term30 x y) = (term32 x y)).
Proof. exact (MK_COMB (@lem1581794 x y) (@lem1581793 x y)). Qed.
Lemma lem1581796 (x : real) (y : real) : ((term30 x y) = (term32 x y)) = ((term30 x y) = (term28 x y)).
Proof. exact (SYM (@lem1581795 x y)). Qed.
Lemma lem1581797 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) : term33 x y.
Proof. exact (conj (@lem1581770 x h1) (@lem1581752 y h2)). Qed.
Lemma lem1581799 (x : real) (y : real) : term20 x y.
Proof. exact (EQ_MP (@lem1581734 x y) (@lem1581733 x y)). Qed.
Lemma lem1581800 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) : term34 x y.
Proof. exact (@lem1581799 x y (@lem1581797 x y h1 h2)). Qed.
Lemma lem1581801 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : term35 x y.
Proof. exact (conj (@lem1581770 x h1) (@lem1581753 y h2)). Qed.
Lemma lem1581803 (x : real) (y : real) : term20 x y.
Proof. exact (EQ_MP (@lem1581734 x y) (@lem1581733 x y)). Qed.
Lemma lem1581804 (x : real) (y : real) : term36 x y.
Proof. exact (@lem1581803 x (real_neg y)). Qed.
Lemma lem1581805 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : term37 x y.
Proof. exact (@lem1581804 x y (@lem1581801 x y h1 h2)). Qed.
Lemma lem1581806 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : term38 x y.
Proof. exact (conj (@lem1581771 x h2) (@lem1581752 y h1)). Qed.
Lemma lem1581808 (x : real) (y : real) : term20 x y.
Proof. exact (EQ_MP (@lem1581734 x y) (@lem1581733 x y)). Qed.
Lemma lem1581809 (x : real) (y : real) : term39 x y.
Proof. exact (@lem1581808 (real_neg x) y). Qed.
Lemma lem1581810 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : term40 x y.
Proof. exact (@lem1581809 x y (@lem1581806 y x h1 h2)). Qed.
Lemma lem1581811 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : term41 x y.
Proof. exact (conj (@lem1581771 x h1) (@lem1581753 y h2)). Qed.
Lemma lem1581813 (x : real) (y : real) : term20 x y.
Proof. exact (EQ_MP (@lem1581734 x y) (@lem1581733 x y)). Qed.
Lemma lem1581814 (x : real) (y : real) : term42 x y.
Proof. exact (@lem1581813 (real_neg x) (real_neg y)). Qed.
Lemma lem1581815 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : term43 x y.
Proof. exact (@lem1581814 x y (@lem1581811 x y h1 h2)). Qed.
Lemma lem1581825 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1581722 x y) (@lem1581721 x y)). Qed.
Lemma lem1581826 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1581827 (x : real) (y : real) : (term37 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1581826) (@lem1581825 x y)). Qed.
Lemma lem1581828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1581829 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1581828) (@lem1581827 x y)). Qed.
Lemma lem1581832 (x : real) (y : real) : ((term30 x y) = (term31 x y)) = ((term30 x y) = (term31 x y)).
Proof. exact (eq_refl ((term30 x y) = (term31 x y))). Qed.
Lemma lem1581833 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1581829 x y) (@lem1581832 x y)). Qed.
Lemma lem1581836 (x : real) (y : real) : (term49 x y) = (term48 x y).
Proof. exact (SYM (@lem1581833 x y)). Qed.
Lemma lem1581840 (x : real) (y : real) : (term16 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1581728 x y) (@lem1581727 x y)). Qed.
Lemma lem1581841 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1581842 (x : real) (y : real) : (term40 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1581841) (@lem1581840 x y)). Qed.
Lemma lem1581843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1581844 (x : real) (y : real) : (term50 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1581843) (@lem1581842 x y)). Qed.
Lemma lem1581847 (x : real) (y : real) : ((term30 x y) = (term28 x y)) = ((term30 x y) = (term28 x y)).
Proof. exact (eq_refl ((term30 x y) = (term28 x y))). Qed.
Lemma lem1581848 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1581844 x y) (@lem1581847 x y)). Qed.
Lemma lem1581851 (x : real) (y : real) : (term52 x y) = (term51 x y).
Proof. exact (SYM (@lem1581848 x y)). Qed.
Lemma lem1581855 (x : real) (y : real) : (term16 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1581728 x y) (@lem1581727 x y)). Qed.
Lemma lem1581856 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem1581855 x (real_neg y)). Qed.
Lemma lem1581858 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1581722 x y) (@lem1581721 x y)). Qed.
Lemma lem1581859 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1581860 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1581859) (@lem1581858 x y)). Qed.
Lemma lem1581862 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1581716 x) (@lem1581715 x)). Qed.
Lemma lem1581863 (x : real) (y : real) : (term55 x y) = (real_mul x y).
Proof. exact (@lem1581862 (real_mul x y)). Qed.
Lemma lem1581864 (x : real) (y : real) : (term54 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1581860 x y) (@lem1581863 x y)). Qed.
Lemma lem1581865 (x : real) (y : real) : (term53 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1581856 x y) (@lem1581864 x y)). Qed.
Lemma lem1581866 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1581867 (x : real) (y : real) : (term43 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1581866) (@lem1581865 x y)). Qed.
Lemma lem1581868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1581869 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1581868) (@lem1581867 x y)). Qed.
Lemma lem1581872 (x : real) (y : real) : ((term30 x y) = (term32 x y)) = ((term30 x y) = (term32 x y)).
Proof. exact (eq_refl ((term30 x y) = (term32 x y))). Qed.
Lemma lem1581873 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1581869 x y) (@lem1581872 x y)). Qed.
Lemma lem1581876 (x : real) (y : real) : (term59 x y) = (term58 x y).
Proof. exact (SYM (@lem1581873 x y)). Qed.
Lemma lem1581877 (x : real) (y : real) (h1 : term34 x y) : term34 x y.
Proof. exact (h1). Qed.
Lemma lem1581878 (x : real) (y : real) (h1 : term45 x y) : term45 x y.
Proof. exact (h1). Qed.
Lemma lem1581879 (x : real) (y : real) (h1 : term45 x y) : term45 x y.
Proof. exact (h1). Qed.
Lemma lem1581880 (x : real) (y : real) (h1 : term34 x y) : term34 x y.
Proof. exact (h1). Qed.
Lemma lem1581882 (x : real) : (real_abs x) = (term0 x).
Proof. exact (EQ_MP (@lem1581713 x) (@lem1581712 x)). Qed.
Lemma lem1581883 (x : real) (y : real) : (term30 x y) = (term60 x y).
Proof. exact (@lem1581882 (real_mul x y)). Qed.
Lemma lem1581884 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1581885 (x : real) (y : real) : (term29 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1581884) (@lem1581883 x y)). Qed.
Lemma lem1581886 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1581887 (x : real) (y : real) : ((term30 x y) = (term31 x y)) = ((term60 x y) = (term31 x y)).
Proof. exact (MK_COMB (@lem1581885 x y) (@lem1581886 x y)). Qed.
Lemma lem1581888 (x : real) (y : real) : ((term60 x y) = (term31 x y)) = ((term30 x y) = (term31 x y)).
Proof. exact (SYM (@lem1581887 x y)). Qed.
Lemma lem1581890 (x : real) : (real_abs x) = (term0 x).
Proof. exact (EQ_MP (@lem1581700 x) (@lem1581699 x)). Qed.
Lemma lem1581891 (x : real) (y : real) : (term30 x y) = (term60 x y).
Proof. exact (@lem1581890 (real_mul x y)). Qed.
Lemma lem1581892 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1581893 (x : real) (y : real) : (term29 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1581892) (@lem1581891 x y)). Qed.
Lemma lem1581894 (x : real) (y : real) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1581895 (x : real) (y : real) : ((term30 x y) = (term28 x y)) = ((term60 x y) = (term28 x y)).
Proof. exact (MK_COMB (@lem1581893 x y) (@lem1581894 x y)). Qed.
Lemma lem1581896 (x : real) (y : real) : ((term60 x y) = (term28 x y)) = ((term30 x y) = (term28 x y)).
Proof. exact (SYM (@lem1581895 x y)). Qed.
Lemma lem1581912 (x : real) : term62 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1581913 (x : real) : (term62 x) = ((real_abs x) = (term63 x)).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1581915 (x : real) : (term23 x) = ((term23 x) = True).
Proof. exact (@lem7 (term23 x)). Qed.
Lemma lem1581917 (y : real) : (term23 y) = ((term23 y) = True).
Proof. exact (@lem7 (term23 y)). Qed.
Lemma lem1581919 (x : real) (y : real) : (term34 x y) = ((term34 x y) = True).
Proof. exact (@lem7 (term34 x y)). Qed.
Lemma lem1581924 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1581913 x) (@lem1581912 x)). Qed.
Lemma lem1581925 (x : real) (y : real) : (term30 x y) = (term64 x y).
Proof. exact (@lem1581924 (real_mul x y)). Qed.
Lemma lem1581927 (x : real) (y : real) (h1 : term34 x y) : (term34 x y) = True.
Proof. exact (EQ_MP (@lem1581919 x y) (@lem1581877 x y h1)). Qed.
Lemma lem1581928 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1581929 (x : real) (y : real) (h1 : term34 x y) : (term65 x y) = (@COND real True).
Proof. exact (MK_COMB (@lem1581928) (@lem1581927 x y h1)). Qed.
Lemma lem1581930 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1581931 (x : real) (y : real) (h1 : term34 x y) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1581929 x y h1) (@lem1581930 x y)). Qed.
Lemma lem1581932 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1581933 (x : real) (y : real) (h1 : term34 x y) : (term64 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1581931 x y h1) (@lem1581932 x y)). Qed.
Lemma lem1581935 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1581936 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1581935 real t2 t1). Qed.
Lemma lem1581937 (x : real) (y : real) : (term68 x y) = (real_mul x y).
Proof. exact (@lem1581936 (term12 x y) (real_mul x y)). Qed.
Lemma lem1581938 (x : real) (y : real) (h1 : term34 x y) : (term64 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1581933 x y h1) (@lem1581937 x y)). Qed.
Lemma lem1581939 (x : real) (y : real) (h1 : term34 x y) : (term30 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1581925 x y) (@lem1581938 x y h1)). Qed.
Lemma lem1581940 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1581941 (x : real) (y : real) (h1 : term34 x y) : (term29 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1581940) (@lem1581939 x y h1)). Qed.
Lemma lem1581943 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1581913 x) (@lem1581912 x)). Qed.
Lemma lem1581945 (x : real) (h1 : term23 x) : (term23 x) = True.
Proof. exact (EQ_MP (@lem1581915 x) (@lem1581770 x h1)). Qed.
Lemma lem1581946 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1581947 (x : real) (h1 : term23 x) : (term70 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1581946) (@lem1581945 x h1)). Qed.
Lemma lem1581948 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1581949 (x : real) (h1 : term23 x) : (term71 x) = (@COND real True x).
Proof. exact (MK_COMB (@lem1581947 x h1) (@lem1581948 x)). Qed.
Lemma lem1581950 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1581951 (x : real) (h1 : term23 x) : (term63 x) = (term72 x).
Proof. exact (MK_COMB (@lem1581949 x h1) (@lem1581950 x)). Qed.
Lemma lem1581953 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1581954 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1581953 real t2 t1). Qed.
Lemma lem1581955 (x : real) : (term72 x) = x.
Proof. exact (@lem1581954 (real_neg x) x). Qed.
Lemma lem1581956 (x : real) (h1 : term23 x) : (term63 x) = x.
Proof. exact (TRANS (@lem1581951 x h1) (@lem1581955 x)). Qed.
Lemma lem1581957 (x : real) (h1 : term23 x) : (real_abs x) = x.
Proof. exact (TRANS (@lem1581943 x) (@lem1581956 x h1)). Qed.
Lemma lem1581958 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1581959 (x : real) (h1 : term23 x) : (term25 x) = (real_mul x).
Proof. exact (MK_COMB (@lem1581958) (@lem1581957 x h1)). Qed.
Lemma lem1581961 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1581913 x) (@lem1581912 x)). Qed.
Lemma lem1581962 (y : real) : (real_abs y) = (term63 y).
Proof. exact (@lem1581961 y). Qed.
Lemma lem1581964 (y : real) (h1 : term23 y) : (term23 y) = True.
Proof. exact (EQ_MP (@lem1581917 y) (@lem1581752 y h1)). Qed.
Lemma lem1581965 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1581966 (y : real) (h1 : term23 y) : (term70 y) = (@COND real True).
Proof. exact (MK_COMB (@lem1581965) (@lem1581964 y h1)). Qed.
Lemma lem1581967 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1581968 (y : real) (h1 : term23 y) : (term71 y) = (@COND real True y).
Proof. exact (MK_COMB (@lem1581966 y h1) (@lem1581967 y)). Qed.
Lemma lem1581969 (y : real) : (real_neg y) = (real_neg y).
Proof. exact (eq_refl (real_neg y)). Qed.
Lemma lem1581970 (y : real) (h1 : term23 y) : (term63 y) = (term72 y).
Proof. exact (MK_COMB (@lem1581968 y h1) (@lem1581969 y)). Qed.
Lemma lem1581972 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1581973 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1581972 real t2 t1). Qed.
Lemma lem1581974 (y : real) : (term72 y) = y.
Proof. exact (@lem1581973 (real_neg y) y). Qed.
Lemma lem1581975 (y : real) (h1 : term23 y) : (term63 y) = y.
Proof. exact (TRANS (@lem1581970 y h1) (@lem1581974 y)). Qed.
Lemma lem1581976 (y : real) (h1 : term23 y) : (real_abs y) = y.
Proof. exact (TRANS (@lem1581962 y) (@lem1581975 y h1)). Qed.
Lemma lem1581977 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) : (term27 x y) = (real_mul x y).
Proof. exact (MK_COMB (@lem1581959 x h1) (@lem1581976 y h2)). Qed.
Lemma lem1581978 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) (h3 : term34 x y) : ((term30 x y) = (term27 x y)) = ((real_mul x y) = (real_mul x y)).
Proof. exact (MK_COMB (@lem1581941 x y h3) (@lem1581977 x y h1 h2)). Qed.
Lemma lem1581980 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1581981 (x : real) : (x = x) = True.
Proof. exact (@lem1581980 real x). Qed.
Lemma lem1581982 (x : real) (y : real) : ((real_mul x y) = (real_mul x y)) = True.
Proof. exact (@lem1581981 (real_mul x y)). Qed.
Lemma lem1581983 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) (h3 : term34 x y) : ((term30 x y) = (term27 x y)) = True.
Proof. exact (TRANS (@lem1581978 x y h1 h2 h3) (@lem1581982 x y)). Qed.
Lemma lem1581984 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) (h3 : term34 x y) : True = ((term30 x y) = (term27 x y)).
Proof. exact (SYM (@lem1581983 x y h1 h2 h3)). Qed.
Lemma lem1581985 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) (h3 : term34 x y) : (term30 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1581984 x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1581986 (x : real) : term6 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1581987 (x : real) : (term6 x) = ((term7 x) = x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1581989 (x : real) : term8 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1581990 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1581991 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1581990 x) (@lem1581989 x)). Qed.
Lemma lem1581992 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1581991 x y). Qed.
Lemma lem1581993 (x : real) (y : real) : (term10 x y) = ((term11 x y) = (term12 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1582001 (x : real) : term62 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1582002 (x : real) : (term62 x) = ((real_abs x) = (term63 x)).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1582004 (x : real) : (term23 x) = ((term23 x) = True).
Proof. exact (@lem7 (term23 x)). Qed.
Lemma lem1582006 (y : real) : (term24 y) = ((term24 y) = True).
Proof. exact (@lem7 (term24 y)). Qed.
Lemma lem1582008 (x : real) (y : real) : (term45 x y) = ((term45 x y) = True).
Proof. exact (@lem7 (term45 x y)). Qed.
Lemma lem1582013 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582002 x) (@lem1582001 x)). Qed.
Lemma lem1582014 (x : real) (y : real) : (term60 x y) = (term73 x y).
Proof. exact (@lem1582013 (term12 x y)). Qed.
Lemma lem1582016 (x : real) (y : real) (h1 : term45 x y) : (term45 x y) = True.
Proof. exact (EQ_MP (@lem1582008 x y) (@lem1581878 x y h1)). Qed.
Lemma lem1582017 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582018 (x : real) (y : real) (h1 : term45 x y) : (term74 x y) = (@COND real True).
Proof. exact (MK_COMB (@lem1582017) (@lem1582016 x y h1)). Qed.
Lemma lem1582019 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1582020 (x : real) (y : real) (h1 : term45 x y) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1582018 x y h1) (@lem1582019 x y)). Qed.
Lemma lem1582022 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1581987 x) (@lem1581986 x)). Qed.
Lemma lem1582023 (x : real) (y : real) : (term55 x y) = (real_mul x y).
Proof. exact (@lem1582022 (real_mul x y)). Qed.
Lemma lem1582024 (x : real) (y : real) (h1 : term45 x y) : (term73 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1582020 x y h1) (@lem1582023 x y)). Qed.
Lemma lem1582026 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582027 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582026 real t2 t1). Qed.
Lemma lem1582028 (x : real) (y : real) : (term77 x y) = (term12 x y).
Proof. exact (@lem1582027 (real_mul x y) (term12 x y)). Qed.
Lemma lem1582029 (x : real) (y : real) (h1 : term45 x y) : (term73 x y) = (term12 x y).
Proof. exact (TRANS (@lem1582024 x y h1) (@lem1582028 x y)). Qed.
Lemma lem1582030 (x : real) (y : real) (h1 : term45 x y) : (term60 x y) = (term12 x y).
Proof. exact (TRANS (@lem1582014 x y) (@lem1582029 x y h1)). Qed.
Lemma lem1582031 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1582032 (x : real) (y : real) (h1 : term45 x y) : (term61 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1582031) (@lem1582030 x y h1)). Qed.
Lemma lem1582034 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582002 x) (@lem1582001 x)). Qed.
Lemma lem1582036 (x : real) (h1 : term23 x) : (term23 x) = True.
Proof. exact (EQ_MP (@lem1582004 x) (@lem1581770 x h1)). Qed.
Lemma lem1582037 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582038 (x : real) (h1 : term23 x) : (term70 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1582037) (@lem1582036 x h1)). Qed.
Lemma lem1582039 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1582040 (x : real) (h1 : term23 x) : (term71 x) = (@COND real True x).
Proof. exact (MK_COMB (@lem1582038 x h1) (@lem1582039 x)). Qed.
Lemma lem1582041 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1582042 (x : real) (h1 : term23 x) : (term63 x) = (term72 x).
Proof. exact (MK_COMB (@lem1582040 x h1) (@lem1582041 x)). Qed.
Lemma lem1582044 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582045 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582044 real t2 t1). Qed.
Lemma lem1582046 (x : real) : (term72 x) = x.
Proof. exact (@lem1582045 (real_neg x) x). Qed.
Lemma lem1582047 (x : real) (h1 : term23 x) : (term63 x) = x.
Proof. exact (TRANS (@lem1582042 x h1) (@lem1582046 x)). Qed.
Lemma lem1582048 (x : real) (h1 : term23 x) : (real_abs x) = x.
Proof. exact (TRANS (@lem1582034 x) (@lem1582047 x h1)). Qed.
Lemma lem1582049 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1582050 (x : real) (h1 : term23 x) : (term25 x) = (real_mul x).
Proof. exact (MK_COMB (@lem1582049) (@lem1582048 x h1)). Qed.
Lemma lem1582052 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582002 x) (@lem1582001 x)). Qed.
Lemma lem1582053 (y : real) : (term0 y) = (term79 y).
Proof. exact (@lem1582052 (real_neg y)). Qed.
Lemma lem1582055 (y : real) (h1 : term24 y) : (term24 y) = True.
Proof. exact (EQ_MP (@lem1582006 y) (@lem1581753 y h1)). Qed.
Lemma lem1582056 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582057 (y : real) (h1 : term24 y) : (term80 y) = (@COND real True).
Proof. exact (MK_COMB (@lem1582056) (@lem1582055 y h1)). Qed.
Lemma lem1582058 (y : real) : (real_neg y) = (real_neg y).
Proof. exact (eq_refl (real_neg y)). Qed.
Lemma lem1582059 (y : real) (h1 : term24 y) : (term81 y) = (term82 y).
Proof. exact (MK_COMB (@lem1582057 y h1) (@lem1582058 y)). Qed.
Lemma lem1582061 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1581987 x) (@lem1581986 x)). Qed.
Lemma lem1582062 (y : real) : (term7 y) = y.
Proof. exact (@lem1582061 y). Qed.
Lemma lem1582063 (y : real) (h1 : term24 y) : (term79 y) = (term83 y).
Proof. exact (MK_COMB (@lem1582059 y h1) (@lem1582062 y)). Qed.
Lemma lem1582065 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582066 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582065 real t2 t1). Qed.
Lemma lem1582067 (y : real) : (term83 y) = (real_neg y).
Proof. exact (@lem1582066 y (real_neg y)). Qed.
Lemma lem1582068 (y : real) (h1 : term24 y) : (term79 y) = (real_neg y).
Proof. exact (TRANS (@lem1582063 y h1) (@lem1582067 y)). Qed.
Lemma lem1582069 (y : real) (h1 : term24 y) : (term0 y) = (real_neg y).
Proof. exact (TRANS (@lem1582053 y) (@lem1582068 y h1)). Qed.
Lemma lem1582070 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : (term31 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem1582050 x h1) (@lem1582069 y h2)). Qed.
Lemma lem1582072 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1581993 x y) (@lem1581992 x y)). Qed.
Lemma lem1582073 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : (term31 x y) = (term12 x y).
Proof. exact (TRANS (@lem1582070 x y h1 h2) (@lem1582072 x y)). Qed.
Lemma lem1582074 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) (h3 : term45 x y) : ((term60 x y) = (term31 x y)) = ((term12 x y) = (term12 x y)).
Proof. exact (MK_COMB (@lem1582032 x y h3) (@lem1582073 x y h1 h2)). Qed.
Lemma lem1582076 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1582077 (x : real) : (x = x) = True.
Proof. exact (@lem1582076 real x). Qed.
Lemma lem1582078 (x : real) (y : real) : ((term12 x y) = (term12 x y)) = True.
Proof. exact (@lem1582077 (term12 x y)). Qed.
Lemma lem1582079 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) (h3 : term45 x y) : ((term60 x y) = (term31 x y)) = True.
Proof. exact (TRANS (@lem1582074 x y h1 h2 h3) (@lem1582078 x y)). Qed.
Lemma lem1582080 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) (h3 : term45 x y) : True = ((term60 x y) = (term31 x y)).
Proof. exact (SYM (@lem1582079 x y h1 h2 h3)). Qed.
Lemma lem1582081 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) (h3 : term45 x y) : (term60 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1582080 x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1582082 (x : real) : term6 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1582083 (x : real) : (term6 x) = ((term7 x) = x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1582091 (x : real) : term13 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1582092 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1582093 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1582092 x) (@lem1582091 x)). Qed.
Lemma lem1582094 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1582093 x y). Qed.
Lemma lem1582095 (x : real) (y : real) : (term15 x y) = ((term16 x y) = (term12 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1582097 (x : real) : term62 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1582098 (x : real) : (term62 x) = ((real_abs x) = (term63 x)).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1582100 (x : real) : (term24 x) = ((term24 x) = True).
Proof. exact (@lem7 (term24 x)). Qed.
Lemma lem1582102 (y : real) : (term23 y) = ((term23 y) = True).
Proof. exact (@lem7 (term23 y)). Qed.
Lemma lem1582104 (x : real) (y : real) : (term45 x y) = ((term45 x y) = True).
Proof. exact (@lem7 (term45 x y)). Qed.
Lemma lem1582109 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582098 x) (@lem1582097 x)). Qed.
Lemma lem1582110 (x : real) (y : real) : (term60 x y) = (term73 x y).
Proof. exact (@lem1582109 (term12 x y)). Qed.
Lemma lem1582112 (x : real) (y : real) (h1 : term45 x y) : (term45 x y) = True.
Proof. exact (EQ_MP (@lem1582104 x y) (@lem1581879 x y h1)). Qed.
Lemma lem1582113 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582114 (x : real) (y : real) (h1 : term45 x y) : (term74 x y) = (@COND real True).
Proof. exact (MK_COMB (@lem1582113) (@lem1582112 x y h1)). Qed.
Lemma lem1582115 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1582116 (x : real) (y : real) (h1 : term45 x y) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1582114 x y h1) (@lem1582115 x y)). Qed.
Lemma lem1582118 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1582083 x) (@lem1582082 x)). Qed.
Lemma lem1582119 (x : real) (y : real) : (term55 x y) = (real_mul x y).
Proof. exact (@lem1582118 (real_mul x y)). Qed.
Lemma lem1582120 (x : real) (y : real) (h1 : term45 x y) : (term73 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1582116 x y h1) (@lem1582119 x y)). Qed.
Lemma lem1582122 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582123 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582122 real t2 t1). Qed.
Lemma lem1582124 (x : real) (y : real) : (term77 x y) = (term12 x y).
Proof. exact (@lem1582123 (real_mul x y) (term12 x y)). Qed.
Lemma lem1582125 (x : real) (y : real) (h1 : term45 x y) : (term73 x y) = (term12 x y).
Proof. exact (TRANS (@lem1582120 x y h1) (@lem1582124 x y)). Qed.
Lemma lem1582126 (x : real) (y : real) (h1 : term45 x y) : (term60 x y) = (term12 x y).
Proof. exact (TRANS (@lem1582110 x y) (@lem1582125 x y h1)). Qed.
Lemma lem1582127 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1582128 (x : real) (y : real) (h1 : term45 x y) : (term61 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1582127) (@lem1582126 x y h1)). Qed.
Lemma lem1582130 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582098 x) (@lem1582097 x)). Qed.
Lemma lem1582131 (x : real) : (term0 x) = (term79 x).
Proof. exact (@lem1582130 (real_neg x)). Qed.
Lemma lem1582133 (x : real) (h1 : term24 x) : (term24 x) = True.
Proof. exact (EQ_MP (@lem1582100 x) (@lem1581771 x h1)). Qed.
Lemma lem1582134 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582135 (x : real) (h1 : term24 x) : (term80 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1582134) (@lem1582133 x h1)). Qed.
Lemma lem1582136 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1582137 (x : real) (h1 : term24 x) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1582135 x h1) (@lem1582136 x)). Qed.
Lemma lem1582139 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1582083 x) (@lem1582082 x)). Qed.
Lemma lem1582140 (x : real) (h1 : term24 x) : (term79 x) = (term83 x).
Proof. exact (MK_COMB (@lem1582137 x h1) (@lem1582139 x)). Qed.
Lemma lem1582142 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582143 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582142 real t2 t1). Qed.
Lemma lem1582144 (x : real) : (term83 x) = (real_neg x).
Proof. exact (@lem1582143 x (real_neg x)). Qed.
Lemma lem1582145 (x : real) (h1 : term24 x) : (term79 x) = (real_neg x).
Proof. exact (TRANS (@lem1582140 x h1) (@lem1582144 x)). Qed.
Lemma lem1582146 (x : real) (h1 : term24 x) : (term0 x) = (real_neg x).
Proof. exact (TRANS (@lem1582131 x) (@lem1582145 x h1)). Qed.
Lemma lem1582147 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1582148 (x : real) (h1 : term24 x) : (term26 x) = (term84 x).
Proof. exact (MK_COMB (@lem1582147) (@lem1582146 x h1)). Qed.
Lemma lem1582150 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582098 x) (@lem1582097 x)). Qed.
Lemma lem1582151 (y : real) : (real_abs y) = (term63 y).
Proof. exact (@lem1582150 y). Qed.
Lemma lem1582153 (y : real) (h1 : term23 y) : (term23 y) = True.
Proof. exact (EQ_MP (@lem1582102 y) (@lem1581752 y h1)). Qed.
Lemma lem1582154 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582155 (y : real) (h1 : term23 y) : (term70 y) = (@COND real True).
Proof. exact (MK_COMB (@lem1582154) (@lem1582153 y h1)). Qed.
Lemma lem1582156 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1582157 (y : real) (h1 : term23 y) : (term71 y) = (@COND real True y).
Proof. exact (MK_COMB (@lem1582155 y h1) (@lem1582156 y)). Qed.
Lemma lem1582158 (y : real) : (real_neg y) = (real_neg y).
Proof. exact (eq_refl (real_neg y)). Qed.
Lemma lem1582159 (y : real) (h1 : term23 y) : (term63 y) = (term72 y).
Proof. exact (MK_COMB (@lem1582157 y h1) (@lem1582158 y)). Qed.
Lemma lem1582161 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582162 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582161 real t2 t1). Qed.
Lemma lem1582163 (y : real) : (term72 y) = y.
Proof. exact (@lem1582162 (real_neg y) y). Qed.
Lemma lem1582164 (y : real) (h1 : term23 y) : (term63 y) = y.
Proof. exact (TRANS (@lem1582159 y h1) (@lem1582163 y)). Qed.
Lemma lem1582165 (y : real) (h1 : term23 y) : (real_abs y) = y.
Proof. exact (TRANS (@lem1582151 y) (@lem1582164 y h1)). Qed.
Lemma lem1582166 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : (term28 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1582148 x h2) (@lem1582165 y h1)). Qed.
Lemma lem1582168 (x : real) (y : real) : (term16 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1582095 x y) (@lem1582094 x y)). Qed.
Lemma lem1582169 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : (term28 x y) = (term12 x y).
Proof. exact (TRANS (@lem1582166 y x h1 h2) (@lem1582168 x y)). Qed.
Lemma lem1582170 (x : real) (y : real) (h1 : term23 y) (h2 : term24 x) (h3 : term45 x y) : ((term60 x y) = (term28 x y)) = ((term12 x y) = (term12 x y)).
Proof. exact (MK_COMB (@lem1582128 x y h3) (@lem1582169 y x h1 h2)). Qed.
Lemma lem1582172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1582173 (x : real) : (x = x) = True.
Proof. exact (@lem1582172 real x). Qed.
Lemma lem1582174 (x : real) (y : real) : ((term12 x y) = (term12 x y)) = True.
Proof. exact (@lem1582173 (term12 x y)). Qed.
Lemma lem1582175 (x : real) (y : real) (h1 : term23 y) (h2 : term24 x) (h3 : term45 x y) : ((term60 x y) = (term28 x y)) = True.
Proof. exact (TRANS (@lem1582170 x y h1 h2 h3) (@lem1582174 x y)). Qed.
Lemma lem1582176 (x : real) (y : real) (h1 : term23 y) (h2 : term24 x) (h3 : term45 x y) : True = ((term60 x y) = (term28 x y)).
Proof. exact (SYM (@lem1582175 x y h1 h2 h3)). Qed.
Lemma lem1582177 (x : real) (y : real) (h1 : term23 y) (h2 : term24 x) (h3 : term45 x y) : (term60 x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1582176 x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1582178 (x : real) : term6 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1582179 (x : real) : (term6 x) = ((term7 x) = x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1582181 (x : real) : term8 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1582182 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1582183 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1582182 x) (@lem1582181 x)). Qed.
Lemma lem1582184 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1582183 x y). Qed.
Lemma lem1582185 (x : real) (y : real) : (term10 x y) = ((term11 x y) = (term12 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1582187 (x : real) : term13 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1582188 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1582189 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1582188 x) (@lem1582187 x)). Qed.
Lemma lem1582190 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1582189 x y). Qed.
Lemma lem1582191 (x : real) (y : real) : (term15 x y) = ((term16 x y) = (term12 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1582193 (x : real) : term62 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1582194 (x : real) : (term62 x) = ((real_abs x) = (term63 x)).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem1582196 (x : real) : (term24 x) = ((term24 x) = True).
Proof. exact (@lem7 (term24 x)). Qed.
Lemma lem1582198 (y : real) : (term24 y) = ((term24 y) = True).
Proof. exact (@lem7 (term24 y)). Qed.
Lemma lem1582200 (x : real) (y : real) : (term34 x y) = ((term34 x y) = True).
Proof. exact (@lem7 (term34 x y)). Qed.
Lemma lem1582205 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582194 x) (@lem1582193 x)). Qed.
Lemma lem1582206 (x : real) (y : real) : (term30 x y) = (term64 x y).
Proof. exact (@lem1582205 (real_mul x y)). Qed.
Lemma lem1582208 (x : real) (y : real) (h1 : term34 x y) : (term34 x y) = True.
Proof. exact (EQ_MP (@lem1582200 x y) (@lem1581880 x y h1)). Qed.
Lemma lem1582209 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582210 (x : real) (y : real) (h1 : term34 x y) : (term65 x y) = (@COND real True).
Proof. exact (MK_COMB (@lem1582209) (@lem1582208 x y h1)). Qed.
Lemma lem1582211 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1582212 (x : real) (y : real) (h1 : term34 x y) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1582210 x y h1) (@lem1582211 x y)). Qed.
Lemma lem1582213 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1582214 (x : real) (y : real) (h1 : term34 x y) : (term64 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1582212 x y h1) (@lem1582213 x y)). Qed.
Lemma lem1582216 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582217 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582216 real t2 t1). Qed.
Lemma lem1582218 (x : real) (y : real) : (term68 x y) = (real_mul x y).
Proof. exact (@lem1582217 (term12 x y) (real_mul x y)). Qed.
Lemma lem1582219 (x : real) (y : real) (h1 : term34 x y) : (term64 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1582214 x y h1) (@lem1582218 x y)). Qed.
Lemma lem1582220 (x : real) (y : real) (h1 : term34 x y) : (term30 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1582206 x y) (@lem1582219 x y h1)). Qed.
Lemma lem1582221 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1582222 (x : real) (y : real) (h1 : term34 x y) : (term29 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1582221) (@lem1582220 x y h1)). Qed.
Lemma lem1582224 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582194 x) (@lem1582193 x)). Qed.
Lemma lem1582225 (x : real) : (term0 x) = (term79 x).
Proof. exact (@lem1582224 (real_neg x)). Qed.
Lemma lem1582227 (x : real) (h1 : term24 x) : (term24 x) = True.
Proof. exact (EQ_MP (@lem1582196 x) (@lem1581771 x h1)). Qed.
Lemma lem1582228 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582229 (x : real) (h1 : term24 x) : (term80 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1582228) (@lem1582227 x h1)). Qed.
Lemma lem1582230 (x : real) : (real_neg x) = (real_neg x).
Proof. exact (eq_refl (real_neg x)). Qed.
Lemma lem1582231 (x : real) (h1 : term24 x) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1582229 x h1) (@lem1582230 x)). Qed.
Lemma lem1582233 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1582179 x) (@lem1582178 x)). Qed.
Lemma lem1582234 (x : real) (h1 : term24 x) : (term79 x) = (term83 x).
Proof. exact (MK_COMB (@lem1582231 x h1) (@lem1582233 x)). Qed.
Lemma lem1582236 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582237 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582236 real t2 t1). Qed.
Lemma lem1582238 (x : real) : (term83 x) = (real_neg x).
Proof. exact (@lem1582237 x (real_neg x)). Qed.
Lemma lem1582239 (x : real) (h1 : term24 x) : (term79 x) = (real_neg x).
Proof. exact (TRANS (@lem1582234 x h1) (@lem1582238 x)). Qed.
Lemma lem1582240 (x : real) (h1 : term24 x) : (term0 x) = (real_neg x).
Proof. exact (TRANS (@lem1582225 x) (@lem1582239 x h1)). Qed.
Lemma lem1582241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1582242 (x : real) (h1 : term24 x) : (term26 x) = (term84 x).
Proof. exact (MK_COMB (@lem1582241) (@lem1582240 x h1)). Qed.
Lemma lem1582244 (x : real) : (real_abs x) = (term63 x).
Proof. exact (EQ_MP (@lem1582194 x) (@lem1582193 x)). Qed.
Lemma lem1582245 (y : real) : (term0 y) = (term79 y).
Proof. exact (@lem1582244 (real_neg y)). Qed.
Lemma lem1582247 (y : real) (h1 : term24 y) : (term24 y) = True.
Proof. exact (EQ_MP (@lem1582198 y) (@lem1581753 y h1)). Qed.
Lemma lem1582248 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1582249 (y : real) (h1 : term24 y) : (term80 y) = (@COND real True).
Proof. exact (MK_COMB (@lem1582248) (@lem1582247 y h1)). Qed.
Lemma lem1582250 (y : real) : (real_neg y) = (real_neg y).
Proof. exact (eq_refl (real_neg y)). Qed.
Lemma lem1582251 (y : real) (h1 : term24 y) : (term81 y) = (term82 y).
Proof. exact (MK_COMB (@lem1582249 y h1) (@lem1582250 y)). Qed.
Lemma lem1582253 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1582179 x) (@lem1582178 x)). Qed.
Lemma lem1582254 (y : real) : (term7 y) = y.
Proof. exact (@lem1582253 y). Qed.
Lemma lem1582255 (y : real) (h1 : term24 y) : (term79 y) = (term83 y).
Proof. exact (MK_COMB (@lem1582251 y h1) (@lem1582254 y)). Qed.
Lemma lem1582257 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1582258 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1582257 real t2 t1). Qed.
Lemma lem1582259 (y : real) : (term83 y) = (real_neg y).
Proof. exact (@lem1582258 y (real_neg y)). Qed.
Lemma lem1582260 (y : real) (h1 : term24 y) : (term79 y) = (real_neg y).
Proof. exact (TRANS (@lem1582255 y h1) (@lem1582259 y)). Qed.
Lemma lem1582261 (y : real) (h1 : term24 y) : (term0 y) = (real_neg y).
Proof. exact (TRANS (@lem1582245 y) (@lem1582260 y h1)). Qed.
Lemma lem1582262 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : (term32 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1582242 x h1) (@lem1582261 y h2)). Qed.
Lemma lem1582264 (x : real) (y : real) : (term16 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1582191 x y) (@lem1582190 x y)). Qed.
Lemma lem1582265 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem1582264 x (real_neg y)). Qed.
Lemma lem1582267 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1582185 x y) (@lem1582184 x y)). Qed.
Lemma lem1582268 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1582269 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1582268) (@lem1582267 x y)). Qed.
Lemma lem1582271 (x : real) : (term7 x) = x.
Proof. exact (EQ_MP (@lem1582179 x) (@lem1582178 x)). Qed.
Lemma lem1582272 (x : real) (y : real) : (term55 x y) = (real_mul x y).
Proof. exact (@lem1582271 (real_mul x y)). Qed.
Lemma lem1582273 (x : real) (y : real) : (term54 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1582269 x y) (@lem1582272 x y)). Qed.
Lemma lem1582274 (x : real) (y : real) : (term53 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1582265 x y) (@lem1582273 x y)). Qed.
Lemma lem1582275 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : (term32 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1582262 x y h1 h2) (@lem1582274 x y)). Qed.
Lemma lem1582276 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) (h3 : term34 x y) : ((term30 x y) = (term32 x y)) = ((real_mul x y) = (real_mul x y)).
Proof. exact (MK_COMB (@lem1582222 x y h3) (@lem1582275 x y h1 h2)). Qed.
Lemma lem1582278 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1582279 (x : real) : (x = x) = True.
Proof. exact (@lem1582278 real x). Qed.
Lemma lem1582280 (x : real) (y : real) : ((real_mul x y) = (real_mul x y)) = True.
Proof. exact (@lem1582279 (real_mul x y)). Qed.
Lemma lem1582281 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) (h3 : term34 x y) : ((term30 x y) = (term32 x y)) = True.
Proof. exact (TRANS (@lem1582276 x y h1 h2 h3) (@lem1582280 x y)). Qed.
Lemma lem1582282 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) (h3 : term34 x y) : True = ((term30 x y) = (term32 x y)).
Proof. exact (SYM (@lem1582281 x y h1 h2 h3)). Qed.
Lemma lem1582283 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) (h3 : term34 x y) : (term30 x y) = (term32 x y).
Proof. exact (EQ_MP (@lem1582282 x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1582284 (x : real) (y : real) (h1 : term23 y) (h2 : term24 x) (h3 : term45 x y) : (term30 x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1581896 x y) (@lem1582177 x y h1 h2 h3)). Qed.
Lemma lem1582285 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) (h3 : term45 x y) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1581888 x y) (@lem1582081 x y h1 h2 h3)). Qed.
Lemma lem1582286 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : term59 x y.
Proof. exact (fun h0 : term34 x y => @lem1582283 x y h1 h2 h0). Qed.
Lemma lem1582287 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : term52 x y.
Proof. exact (fun h0 : term45 x y => @lem1582284 x y h1 h2 h0). Qed.
Lemma lem1582288 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : term49 x y.
Proof. exact (fun h0 : term45 x y => @lem1582285 x y h1 h2 h0). Qed.
Lemma lem1582290 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : term58 x y.
Proof. exact (EQ_MP (@lem1581876 x y) (@lem1582286 x y h1 h2)). Qed.
Lemma lem1582291 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : term51 x y.
Proof. exact (EQ_MP (@lem1581851 x y) (@lem1582287 y x h1 h2)). Qed.
Lemma lem1582292 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : term48 x y.
Proof. exact (EQ_MP (@lem1581836 x y) (@lem1582288 x y h1 h2)). Qed.
Lemma lem1582293 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) : term85 x y.
Proof. exact (fun h0 : term34 x y => @lem1581985 x y h1 h2 h0). Qed.
Lemma lem1582294 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : (term30 x y) = (term32 x y).
Proof. exact (@lem1582290 x y h1 h2 (@lem1581815 x y h1 h2)). Qed.
Lemma lem1582295 (y : real) (x : real) (h1 : term23 y) (h2 : term24 x) : (term30 x y) = (term28 x y).
Proof. exact (@lem1582291 y x h1 h2 (@lem1581810 y x h1 h2)). Qed.
Lemma lem1582296 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : (term30 x y) = (term31 x y).
Proof. exact (@lem1582292 x y h1 h2 (@lem1581805 x y h1 h2)). Qed.
Lemma lem1582297 (x : real) (y : real) (h1 : term23 x) (h2 : term23 y) : (term30 x y) = (term27 x y).
Proof. exact (@lem1582293 x y h1 h2 (@lem1581800 x y h1 h2)). Qed.
Lemma lem1582298 (x : real) (y : real) (h1 : term24 x) (h2 : term24 y) : (term30 x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1581796 x y) (@lem1582294 x y h1 h2)). Qed.
Lemma lem1582299 (y : real) (x : real) (h1 : term24 x) : (term30 x y) = (term28 x y).
Proof. exact (or_elim (@lem1581751 y) (fun h0 : term23 y => @lem1582295 y x h0 h1) (fun h0 : term24 y => @lem1582298 x y h1 h0)). Qed.
Lemma lem1582300 (x : real) (y : real) (h1 : term23 x) (h2 : term24 y) : (term30 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1581788 x y) (@lem1582296 x y h1 h2)). Qed.
Lemma lem1582301 (y : real) (x : real) (h1 : term23 x) : (term30 x y) = (term27 x y).
Proof. exact (or_elim (@lem1581751 y) (fun h0 : term23 y => @lem1582297 x y h1 h0) (fun h0 : term24 y => @lem1582300 x y h1 h0)). Qed.
Lemma lem1582302 (y : real) (x : real) (h1 : term24 x) : (term30 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem1581780 x y) (@lem1582299 y x h1)). Qed.
Lemma lem1582303 (x : real) (y : real) : (term30 x y) = (term27 x y).
Proof. exact (or_elim (@lem1581769 x) (fun h0 : term23 x => @lem1582301 y x h0) (fun h0 : term24 x => @lem1582302 y x h0)). Qed.
Lemma lem1582308 (x : real) : term86 x.
Proof. exact (fun y : real => @lem1582303 x y). Qed.
Lemma lem1582313 : term87.
Proof. exact (fun x : real => @lem1582308 x). Qed.
