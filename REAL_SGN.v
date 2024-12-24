Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ABS_ZERO_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_MUL_RINV_spec.
Require Import REAL_SGN_ABS_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1710179_spec.
Require Import thm1710422_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1733753 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1733754 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1733753 x y z h1)). Qed.
Lemma lem1733755 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1733756 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1733755 x y z h1)). Qed.
Lemma lem1733757 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1733754 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1733756 x y z h1)). Qed.
Lemma lem1733758 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1733757 x y z)). Qed.
Lemma lem1733759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1733760 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1733759) (@lem1733758 x y)). Qed.
Lemma lem1733761 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1733760 x y)). Qed.
Lemma lem1733762 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1733763 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1733762) (@lem1733761 x)). Qed.
Lemma lem1733764 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1733763 x)). Qed.
Lemma lem1733765 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1733766 : term12 = term13.
Proof. exact (MK_COMB (@lem1733765) (@lem1733764)). Qed.
Lemma lem1733767 : term13.
Proof. exact (EQ_MP (@lem1733766) (@lem1338912)). Qed.
Lemma lem1733769 (x : real) (h1 : (term14 x) = x) : (term14 x) = x.
Proof. exact (h1). Qed.
Lemma lem1733770 (x : real) (h1 : (term14 x) = x) : x = (term14 x).
Proof. exact (SYM (@lem1733769 x h1)). Qed.
Lemma lem1733771 (x : real) (h1 : x = (term14 x)) : x = (term14 x).
Proof. exact (h1). Qed.
Lemma lem1733772 (x : real) (h1 : x = (term14 x)) : (term14 x) = x.
Proof. exact (SYM (@lem1733771 x h1)). Qed.
Lemma lem1733773 (x : real) : ((term14 x) = x) = (x = (term14 x)).
Proof. exact (prop_ext (fun h1 : (term14 x) = x => @lem1733770 x h1) (fun h1 : x = (term14 x) => @lem1733772 x h1)). Qed.
Lemma lem1733774 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1733773 x)). Qed.
Lemma lem1733775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1733776 : term17 = term18.
Proof. exact (MK_COMB (@lem1733775) (@lem1733774)). Qed.
Lemma lem1733777 : term18.
Proof. exact (EQ_MP (@lem1733776) (@lem1717545)). Qed.
Lemma lem1733778 (x : real) : term19 x.
Proof. exact (@lem1733777 x). Qed.
Lemma lem1733779 (x : real) : (term19 x) = (x = (term14 x)).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1733781 (x : real) : term20 x.
Proof. exact (@lem9784 (x = term21)). Qed.
Lemma lem1733782 (x : real) : (term20 x) = (term22 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1733783 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1733782 x) (@lem1733781 x)). Qed.
Lemma lem1733785 (x : real) (h1 : term23 x) : term23 x.
Proof. exact (h1). Qed.
Lemma lem1733786 (x : real) : term24 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1733787 (x : real) : (term24 x) = ((term25 x) = term21).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1733789 (x : real) : term26 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1733790 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1733791 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1733790 x) (@lem1733789 x)). Qed.
Lemma lem1733792 (x : real) (y : real) : term28 x y.
Proof. exact (@lem1733791 x y). Qed.
Lemma lem1733793 (x : real) (y : real) : (term28 x y) = ((real_div x y) = (term29 x y)).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1733798 (x : real) (h1 : x = term21) : x = term21.
Proof. exact (h1). Qed.
Lemma lem1733799 : real_sgn = real_sgn.
Proof. exact (eq_refl real_sgn). Qed.
Lemma lem1733800 (x : real) (h1 : x = term21) : (real_sgn x) = term30.
Proof. exact (MK_COMB (@lem1733799) (@lem1733798 x h1)). Qed.
Lemma lem1733802 : term30 = term21.
Proof. exact (EQ_MP (@lem1710179) (@lem1710422)). Qed.
Lemma lem1733803 (x : real) (h1 : x = term21) : (real_sgn x) = term21.
Proof. exact (TRANS (@lem1733800 x h1) (@lem1733802)). Qed.
Lemma lem1733804 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1733805 (x : real) (h1 : x = term21) : (term31 x) = term32.
Proof. exact (MK_COMB (@lem1733804) (@lem1733803 x h1)). Qed.
Lemma lem1733807 (x : real) (y : real) : (real_div x y) = (term29 x y).
Proof. exact (EQ_MP (@lem1733793 x y) (@lem1733792 x y)). Qed.
Lemma lem1733808 (x : real) : (term33 x) = (term34 x).
Proof. exact (@lem1733807 x (real_abs x)). Qed.
Lemma lem1733810 (x : real) (h1 : x = term21) : x = term21.
Proof. exact (h1). Qed.
Lemma lem1733811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1733812 (x : real) (h1 : x = term21) : (real_mul x) = term35.
Proof. exact (MK_COMB (@lem1733811) (@lem1733810 x h1)). Qed.
Lemma lem1733814 (x : real) (h1 : x = term21) : x = term21.
Proof. exact (h1). Qed.
Lemma lem1733815 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1733816 (x : real) (h1 : x = term21) : (real_abs x) = term36.
Proof. exact (MK_COMB (@lem1733815) (@lem1733814 x h1)). Qed.
Lemma lem1733817 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1733818 (x : real) (h1 : x = term21) : (term37 x) = term38.
Proof. exact (MK_COMB (@lem1733817) (@lem1733816 x h1)). Qed.
Lemma lem1733819 (x : real) (h1 : x = term21) : (term34 x) = term39.
Proof. exact (MK_COMB (@lem1733812 x h1) (@lem1733818 x h1)). Qed.
Lemma lem1733821 (x : real) : (term25 x) = term21.
Proof. exact (EQ_MP (@lem1733787 x) (@lem1733786 x)). Qed.
Lemma lem1733822 : term39 = term21.
Proof. exact (@lem1733821 term38). Qed.
Lemma lem1733823 (x : real) (h1 : x = term21) : (term34 x) = term21.
Proof. exact (TRANS (@lem1733819 x h1) (@lem1733822)). Qed.
Lemma lem1733824 (x : real) (h1 : x = term21) : (term33 x) = term21.
Proof. exact (TRANS (@lem1733808 x) (@lem1733823 x h1)). Qed.
Lemma lem1733825 (x : real) (h1 : x = term21) : ((real_sgn x) = (term33 x)) = (term21 = term21).
Proof. exact (MK_COMB (@lem1733805 x h1) (@lem1733824 x h1)). Qed.
Lemma lem1733827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1733828 (x : real) : (x = x) = True.
Proof. exact (@lem1733827 real x). Qed.
Lemma lem1733829 : (term21 = term21) = True.
Proof. exact (@lem1733828 term21). Qed.
Lemma lem1733830 (x : real) (h1 : x = term21) : ((real_sgn x) = (term33 x)) = True.
Proof. exact (TRANS (@lem1733825 x h1) (@lem1733829)). Qed.
Lemma lem1733831 (x : real) (h1 : x = term21) : True = ((real_sgn x) = (term33 x)).
Proof. exact (SYM (@lem1733830 x h1)). Qed.
Lemma lem1733832 (x : real) (h1 : x = term21) : (real_sgn x) = (term33 x).
Proof. exact (EQ_MP (@lem1733831 x h1) (@lem0)). Qed.
Lemma lem1733834 (x : real) : x = (term14 x).
Proof. exact (EQ_MP (@lem1733779 x) (@lem1733778 x)). Qed.
Lemma lem1733835 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1733836 (x : real) : (real_div x) = (term40 x).
Proof. exact (MK_COMB (@lem1733835) (@lem1733834 x)). Qed.
Lemma lem1733837 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1733838 (x : real) : (term33 x) = (term41 x).
Proof. exact (MK_COMB (@lem1733836 x) (@lem1733837 x)). Qed.
Lemma lem1733839 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1733840 (x : real) : ((real_sgn x) = (term33 x)) = ((real_sgn x) = (term41 x)).
Proof. exact (MK_COMB (@lem1733839 x) (@lem1733838 x)). Qed.
Lemma lem1733841 (x : real) : ((real_sgn x) = (term41 x)) = ((real_sgn x) = (term33 x)).
Proof. exact (SYM (@lem1733840 x)). Qed.
Lemma lem1733842 (x : real) : term42 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1733843 (x : real) : (term42 x) = ((term43 x) = x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1733845 (x : real) : term44 x.
Proof. exact (@lem1591985 x). Qed.
Lemma lem1733846 (x : real) : (term44 x) = (term45 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1733847 (x : real) : term45 x.
Proof. exact (EQ_MP (@lem1733846 x) (@lem1733845 x)). Qed.
Lemma lem1733848 (x : real) (h1 : term23 x) : term23 x.
Proof. exact (h1). Qed.
Lemma lem1733849 (x : real) (h1 : term23 x) : (term46 x) = term47.
Proof. exact (@lem1733847 x (@lem1733848 x h1)). Qed.
Lemma lem1733855 (x : real) : term48 x.
Proof. exact (@lem1527966 x). Qed.
Lemma lem1733856 (x : real) : (term48 x) = (((real_abs x) = term21) = (x = term21)).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1733858 (x : real) : term49 x.
Proof. exact (@lem1733767 x). Qed.
Lemma lem1733859 (x : real) : (term49 x) = (term9 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1733860 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1733859 x) (@lem1733858 x)). Qed.
Lemma lem1733861 (x : real) (y : real) : term50 x y.
Proof. exact (@lem1733860 x y). Qed.
Lemma lem1733862 (x : real) (y : real) : (term50 x y) = (term5 x y).
Proof. exact (eq_refl (term50 x y)). Qed.
Lemma lem1733863 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1733862 x y) (@lem1733861 x y)). Qed.
Lemma lem1733864 (x : real) (y : real) (z : real) : term51 x y z.
Proof. exact (@lem1733863 x y z). Qed.
Lemma lem1733865 (x : real) (y : real) (z : real) : (term51 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term51 x y z)). Qed.
Lemma lem1733867 (x : real) : term26 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1733868 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1733869 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1733868 x) (@lem1733867 x)). Qed.
Lemma lem1733870 (x : real) (y : real) : term28 x y.
Proof. exact (@lem1733869 x y). Qed.
Lemma lem1733871 (x : real) (y : real) : (term28 x y) = ((real_div x y) = (term29 x y)).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1733873 (x : real) : term52 x.
Proof. exact (@lem82 (x = term21)). Qed.
Lemma lem1733889 (x : real) (y : real) : (real_div x y) = (term29 x y).
Proof. exact (EQ_MP (@lem1733871 x y) (@lem1733870 x y)). Qed.
Lemma lem1733890 (x : real) : (term41 x) = (term53 x).
Proof. exact (@lem1733889 (term14 x) (real_abs x)). Qed.
Lemma lem1733892 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1733865 x y z) (@lem1733864 x y z)). Qed.
Lemma lem1733893 (x : real) : (term53 x) = (term54 x).
Proof. exact (@lem1733892 (real_sgn x) (real_abs x) (term37 x)). Qed.
Lemma lem1733895 (x : real) : term45 x.
Proof. exact (fun h0 : term23 x => @lem1733849 x h0). Qed.
Lemma lem1733896 (x : real) : term55 x.
Proof. exact (@lem1733895 (real_abs x)). Qed.
Lemma lem1733898 (x : real) : ((real_abs x) = term21) = (x = term21).
Proof. exact (EQ_MP (@lem1733856 x) (@lem1733855 x)). Qed.
Lemma lem1733900 (x : real) (h1 : term23 x) : (x = term21) = False.
Proof. exact (@lem1733873 x (@lem1733785 x h1)). Qed.
Lemma lem1733901 (x : real) (h1 : term23 x) : ((real_abs x) = term21) = False.
Proof. exact (TRANS (@lem1733898 x) (@lem1733900 x h1)). Qed.
Lemma lem1733902 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1733903 (x : real) (h1 : term23 x) : (term56 x) = (~ False).
Proof. exact (MK_COMB (@lem1733902) (@lem1733901 x h1)). Qed.
Lemma lem1733905 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1733906 (x : real) (h1 : term23 x) : (term56 x) = True.
Proof. exact (TRANS (@lem1733903 x h1) (@lem1733905)). Qed.
Lemma lem1733907 (x : real) (h1 : term23 x) : True = (term56 x).
Proof. exact (SYM (@lem1733906 x h1)). Qed.
Lemma lem1733908 (x : real) (h1 : term23 x) : term56 x.
Proof. exact (EQ_MP (@lem1733907 x h1) (@lem0)). Qed.
Lemma lem1733909 (x : real) (h1 : term23 x) : (term57 x) = term47.
Proof. exact (@lem1733896 x (@lem1733908 x h1)). Qed.
Lemma lem1733910 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1733911 (x : real) (h1 : term23 x) : (term54 x) = (term59 x).
Proof. exact (MK_COMB (@lem1733910 x) (@lem1733909 x h1)). Qed.
Lemma lem1733913 (x : real) : (term43 x) = x.
Proof. exact (EQ_MP (@lem1733843 x) (@lem1733842 x)). Qed.
Lemma lem1733914 (x : real) : (term59 x) = (real_sgn x).
Proof. exact (@lem1733913 (real_sgn x)). Qed.
Lemma lem1733915 (x : real) (h1 : term23 x) : (term54 x) = (real_sgn x).
Proof. exact (TRANS (@lem1733911 x h1) (@lem1733914 x)). Qed.
Lemma lem1733916 (x : real) (h1 : term23 x) : (term53 x) = (real_sgn x).
Proof. exact (TRANS (@lem1733893 x) (@lem1733915 x h1)). Qed.
Lemma lem1733917 (x : real) (h1 : term23 x) : (term41 x) = (real_sgn x).
Proof. exact (TRANS (@lem1733890 x) (@lem1733916 x h1)). Qed.
Lemma lem1733918 (x : real) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1733919 (x : real) (h1 : term23 x) : ((real_sgn x) = (term41 x)) = ((real_sgn x) = (real_sgn x)).
Proof. exact (MK_COMB (@lem1733918 x) (@lem1733917 x h1)). Qed.
Lemma lem1733921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1733922 (x : real) : (x = x) = True.
Proof. exact (@lem1733921 real x). Qed.
Lemma lem1733923 (x : real) : ((real_sgn x) = (real_sgn x)) = True.
Proof. exact (@lem1733922 (real_sgn x)). Qed.
Lemma lem1733924 (x : real) (h1 : term23 x) : ((real_sgn x) = (term41 x)) = True.
Proof. exact (TRANS (@lem1733919 x h1) (@lem1733923 x)). Qed.
Lemma lem1733925 (x : real) (h1 : term23 x) : True = ((real_sgn x) = (term41 x)).
Proof. exact (SYM (@lem1733924 x h1)). Qed.
Lemma lem1733926 (x : real) (h1 : term23 x) : (real_sgn x) = (term41 x).
Proof. exact (EQ_MP (@lem1733925 x h1) (@lem0)). Qed.
Lemma lem1733927 (x : real) (h1 : term23 x) : (real_sgn x) = (term33 x).
Proof. exact (EQ_MP (@lem1733841 x) (@lem1733926 x h1)). Qed.
Lemma lem1733928 (x : real) : (real_sgn x) = (term33 x).
Proof. exact (or_elim (@lem1733783 x) (fun h0 : x = term21 => @lem1733832 x h0) (fun h0 : term23 x => @lem1733927 x h0)). Qed.
Lemma lem1733933 : term60.
Proof. exact (fun x : real => @lem1733928 x). Qed.
