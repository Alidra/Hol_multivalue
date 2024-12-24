Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RAT_LEMMA1_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ADD_RDISTRIB_spec.
Require Import REAL_EQ_MUL_LCANCEL_spec.
Require Import REAL_MUL_AC_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_MUL_RINV_spec.
Require Import REFL_CLAUSE_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm82_spec.
Lemma lem1977712 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1977713 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1977712 h1 x). Qed.
Lemma lem1977714 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1977715 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1977714 x) (@lem1977713 x h1)). Qed.
Lemma lem1977716 (x : real) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1977717 (x : real) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1977715 x h1 (@lem1977716 x h2)). Qed.
Lemma lem1977718 (x : real) (h1 : term3 x) : term6 x.
Proof. exact (fun h0 : term0 => @lem1977717 x h0 h1). Qed.
Lemma lem1977719 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1977720 (x : real) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1977718 x h2 (@lem1977719 h1)). Qed.
Lemma lem1977721 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun h0 : term3 x => @lem1977720 x h1 h0). Qed.
Lemma lem1977722 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1977721 x h1). Qed.
Lemma lem1977723 : term7.
Proof. exact (fun h0 : term0 => @lem1977722 h0). Qed.
Lemma lem1977724 : term0.
Proof. exact (@lem1977723 (@lem1591985)). Qed.
Lemma lem1977725 (x : real) : term1 x.
Proof. exact (@lem1977724 x). Qed.
Lemma lem1977726 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1977728 (x : real) : term8 x.
Proof. exact (@lem1586590 x). Qed.
Lemma lem1977729 (x : real) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1977730 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1977729 x) (@lem1977728 x)). Qed.
Lemma lem1977731 (x : real) (y : real) : term10 x y.
Proof. exact (@lem1977730 x y). Qed.
Lemma lem1977732 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1977733 (x : real) (y : real) : term11 x y.
Proof. exact (EQ_MP (@lem1977732 x y) (@lem1977731 x y)). Qed.
Lemma lem1977734 (x : real) (y : real) (z : real) : term12 x y z.
Proof. exact (@lem1977733 x y z). Qed.
Lemma lem1977735 (x : real) (y : real) (z : real) : (term12 x y z) = (((real_mul x y) = (real_mul x z)) = (term13 x y z)).
Proof. exact (eq_refl (term12 x y z)). Qed.
Lemma lem1977740 (x : real) (y : real) (z : real) (h1 : (term14 x y z) = (term15 x y z)) : (term14 x y z) = (term15 x y z).
Proof. exact (h1). Qed.
Lemma lem1977741 (x : real) (y : real) (z : real) (h1 : (term14 x y z) = (term15 x y z)) : (term15 x y z) = (term14 x y z).
Proof. exact (SYM (@lem1977740 x y z h1)). Qed.
Lemma lem1977742 (x : real) (y : real) (z : real) (h1 : (term15 x y z) = (term14 x y z)) : (term15 x y z) = (term14 x y z).
Proof. exact (h1). Qed.
Lemma lem1977743 (x : real) (y : real) (z : real) (h1 : (term15 x y z) = (term14 x y z)) : (term14 x y z) = (term15 x y z).
Proof. exact (SYM (@lem1977742 x y z h1)). Qed.
Lemma lem1977744 (x : real) (y : real) (z : real) : ((term14 x y z) = (term15 x y z)) = ((term15 x y z) = (term14 x y z)).
Proof. exact (prop_ext (fun h1 : (term14 x y z) = (term15 x y z) => @lem1977741 x y z h1) (fun h1 : (term15 x y z) = (term14 x y z) => @lem1977743 x y z h1)). Qed.
Lemma lem1977745 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (fun_ext (fun z : real => @lem1977744 x y z)). Qed.
Lemma lem1977746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977747 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem1977746) (@lem1977745 x y)). Qed.
Lemma lem1977748 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1977747 x y)). Qed.
Lemma lem1977749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977750 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1977749) (@lem1977748 x)). Qed.
Lemma lem1977751 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem1977750 x)). Qed.
Lemma lem1977752 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977753 : term26 = term27.
Proof. exact (MK_COMB (@lem1977752) (@lem1977751)). Qed.
Lemma lem1977754 : term27.
Proof. exact (EQ_MP (@lem1977753) (@lem1338912)). Qed.
Lemma lem1977755 (x : real) : term28 x.
Proof. exact (@lem1977754 x). Qed.
Lemma lem1977756 (x : real) : (term28 x) = (term23 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1977757 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem1977756 x) (@lem1977755 x)). Qed.
Lemma lem1977758 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1977757 x y). Qed.
Lemma lem1977759 (x : real) (y : real) : (term29 x y) = (term19 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1977760 (x : real) (y : real) : term19 x y.
Proof. exact (EQ_MP (@lem1977759 x y) (@lem1977758 x y)). Qed.
Lemma lem1977761 (x : real) (y : real) (z : real) : term30 x y z.
Proof. exact (@lem1977760 x y z). Qed.
Lemma lem1977762 (x : real) (y : real) (z : real) : (term30 x y z) = ((term15 x y z) = (term14 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem1977765 (x : real) (h1 : (term31 x) = x) : (term31 x) = x.
Proof. exact (h1). Qed.
Lemma lem1977766 (x : real) (h1 : (term31 x) = x) : x = (term31 x).
Proof. exact (SYM (@lem1977765 x h1)). Qed.
Lemma lem1977767 (x : real) (h1 : x = (term31 x)) : x = (term31 x).
Proof. exact (h1). Qed.
Lemma lem1977768 (x : real) (h1 : x = (term31 x)) : (term31 x) = x.
Proof. exact (SYM (@lem1977767 x h1)). Qed.
Lemma lem1977769 (x : real) : ((term31 x) = x) = (x = (term31 x)).
Proof. exact (prop_ext (fun h1 : (term31 x) = x => @lem1977766 x h1) (fun h1 : x = (term31 x) => @lem1977768 x h1)). Qed.
Lemma lem1977770 : term32 = term33.
Proof. exact (fun_ext (fun x : real => @lem1977769 x)). Qed.
Lemma lem1977771 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977772 : term34 = term35.
Proof. exact (MK_COMB (@lem1977771) (@lem1977770)). Qed.
Lemma lem1977773 : term35.
Proof. exact (EQ_MP (@lem1977772) (@lem1383409)). Qed.
Lemma lem1977774 (x : real) : term36 x.
Proof. exact (@lem1977773 x). Qed.
Lemma lem1977775 (x : real) : (term36 x) = (x = (term31 x)).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1977777 (x : real) : term37 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1977778 (x : real) : (term37 x) = (term22 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1977779 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1977778 x) (@lem1977777 x)). Qed.
Lemma lem1977780 (x : real) (y : real) : term38 x y.
Proof. exact (@lem1977779 x y). Qed.
Lemma lem1977781 (x : real) (y : real) : (term38 x y) = (term18 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1977782 (x : real) (y : real) : term18 x y.
Proof. exact (EQ_MP (@lem1977781 x y) (@lem1977780 x y)). Qed.
Lemma lem1977783 (x : real) (y : real) (z : real) : term39 x y z.
Proof. exact (@lem1977782 x y z). Qed.
Lemma lem1977784 (x : real) (y : real) (z : real) : (term39 x y z) = ((term14 x y z) = (term15 x y z)).
Proof. exact (eq_refl (term39 x y z)). Qed.
Lemma lem1977786 {A : Type'} (x : A) : term40 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1977787 {A : Type'} (x : A) : (term40 A x) = ((x = x) = True).
Proof. exact (eq_refl (term40 A x)). Qed.
Lemma lem1977789 (n : real) (m : real) (p : real) : term41 n m p.
Proof. exact (proj2 (@lem1486340 n m p)). Qed.
Lemma lem1977805 (m : real) (n : real) (p : real) : (term15 m n p) = (term14 m n p).
Proof. exact (proj1 (@lem1977789 n m p)). Qed.
Lemma lem1977806 (b : real) (a : real) (c : real) : (term15 b a c) = (term14 b a c).
Proof. exact (@lem1977805 b a c). Qed.
Lemma lem1977808 (n : real) (m : real) (p : real) : (term14 m n p) = (term14 n m p).
Proof. exact (proj2 (@lem1977789 n m p)). Qed.
Lemma lem1977809 (a : real) (b : real) (c : real) : (term14 b a c) = (term14 a b c).
Proof. exact (@lem1977808 a b c). Qed.
Lemma lem1977816 (a : real) (b : real) (c : real) : (term15 b a c) = (term14 a b c).
Proof. exact (TRANS (@lem1977806 b a c) (@lem1977809 a b c)). Qed.
Lemma lem1977820 (a : real) (b : real) (c : real) : (term42 a b c) = (term42 a b c).
Proof. exact (eq_refl (term42 a b c)). Qed.
Lemma lem1977821 (a : real) (b : real) (c : real) : ((term14 a b c) = (term15 b a c)) = ((term14 a b c) = (term14 a b c)).
Proof. exact (MK_COMB (@lem1977820 a b c) (@lem1977816 a b c)). Qed.
Lemma lem1977823 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1977787 A x) (@lem1977786 A x)). Qed.
Lemma lem1977824 (x : real) : (x = x) = True.
Proof. exact (@lem1977823 real x). Qed.
Lemma lem1977825 (a : real) (b : real) (c : real) : ((term14 a b c) = (term14 a b c)) = True.
Proof. exact (@lem1977824 (term14 a b c)). Qed.
Lemma lem1977826 (b : real) (a : real) (c : real) : ((term14 a b c) = (term15 b a c)) = True.
Proof. exact (TRANS (@lem1977821 a b c) (@lem1977825 a b c)). Qed.
Lemma lem1977827 (b : real) (a : real) (c : real) : True = ((term14 a b c) = (term15 b a c)).
Proof. exact (SYM (@lem1977826 b a c)). Qed.
Lemma lem1977832 (x : real) (y : real) (z : real) (h1 : (term14 x y z) = (term15 x y z)) : (term14 x y z) = (term15 x y z).
Proof. exact (h1). Qed.
Lemma lem1977833 (x : real) (y : real) (z : real) (h1 : (term14 x y z) = (term15 x y z)) : (term15 x y z) = (term14 x y z).
Proof. exact (SYM (@lem1977832 x y z h1)). Qed.
Lemma lem1977834 (x : real) (y : real) (z : real) (h1 : (term15 x y z) = (term14 x y z)) : (term15 x y z) = (term14 x y z).
Proof. exact (h1). Qed.
Lemma lem1977835 (x : real) (y : real) (z : real) (h1 : (term15 x y z) = (term14 x y z)) : (term14 x y z) = (term15 x y z).
Proof. exact (SYM (@lem1977834 x y z h1)). Qed.
Lemma lem1977836 (x : real) (y : real) (z : real) : ((term14 x y z) = (term15 x y z)) = ((term15 x y z) = (term14 x y z)).
Proof. exact (prop_ext (fun h1 : (term14 x y z) = (term15 x y z) => @lem1977833 x y z h1) (fun h1 : (term15 x y z) = (term14 x y z) => @lem1977835 x y z h1)). Qed.
Lemma lem1977837 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (fun_ext (fun z : real => @lem1977836 x y z)). Qed.
Lemma lem1977838 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977839 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem1977838) (@lem1977837 x y)). Qed.
Lemma lem1977840 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1977839 x y)). Qed.
Lemma lem1977841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977842 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1977841) (@lem1977840 x)). Qed.
Lemma lem1977843 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem1977842 x)). Qed.
Lemma lem1977844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1977845 : term26 = term27.
Proof. exact (MK_COMB (@lem1977844) (@lem1977843)). Qed.
Lemma lem1977846 : term27.
Proof. exact (EQ_MP (@lem1977845) (@lem1338912)). Qed.
Lemma lem1977847 (x : real) : term28 x.
Proof. exact (@lem1977846 x). Qed.
Lemma lem1977848 (x : real) : (term28 x) = (term23 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1977849 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem1977848 x) (@lem1977847 x)). Qed.
Lemma lem1977850 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1977849 x y). Qed.
Lemma lem1977851 (x : real) (y : real) : (term29 x y) = (term19 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1977852 (x : real) (y : real) : term19 x y.
Proof. exact (EQ_MP (@lem1977851 x y) (@lem1977850 x y)). Qed.
Lemma lem1977853 (x : real) (y : real) (z : real) : term30 x y z.
Proof. exact (@lem1977852 x y z). Qed.
Lemma lem1977854 (x : real) (y : real) (z : real) : (term30 x y z) = ((term15 x y z) = (term14 x y z)).
Proof. exact (eq_refl (term30 x y z)). Qed.
Lemma lem1977856 (x : real) : term43 x.
Proof. exact (@lem1487144 x). Qed.
Lemma lem1977857 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1977858 (x : real) : term44 x.
Proof. exact (EQ_MP (@lem1977857 x) (@lem1977856 x)). Qed.
Lemma lem1977859 (x : real) (y : real) : term45 x y.
Proof. exact (@lem1977858 x y). Qed.
Lemma lem1977860 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1977861 (x : real) (y : real) : term46 x y.
Proof. exact (EQ_MP (@lem1977860 x y) (@lem1977859 x y)). Qed.
Lemma lem1977862 (x : real) (y : real) (z : real) : term47 x y z.
Proof. exact (@lem1977861 x y z). Qed.
Lemma lem1977863 (x : real) (y : real) (z : real) : (term47 x y z) = ((term48 x y z) = (term49 x y z)).
Proof. exact (eq_refl (term47 x y z)). Qed.
Lemma lem1977865 (x : real) : term50 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1977866 (x : real) : (term50 x) = (term51 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1977867 (x : real) : term51 x.
Proof. exact (EQ_MP (@lem1977866 x) (@lem1977865 x)). Qed.
Lemma lem1977868 (x : real) (y : real) : term52 x y.
Proof. exact (@lem1977867 x y). Qed.
Lemma lem1977869 (x : real) (y : real) : (term52 x y) = ((real_div x y) = (term53 x y)).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1977871 (y1 : real) (y2 : real) (h1 : term54 y1 y2) : term54 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1977872 (y2 : real) (h1 : term3 y2) : term3 y2.
Proof. exact (h1). Qed.
Lemma lem1977873 (y1 : real) (h1 : term3 y1) : term3 y1.
Proof. exact (h1). Qed.
Lemma lem1977877 (x : real) (y : real) : (real_div x y) = (term53 x y).
Proof. exact (EQ_MP (@lem1977869 x y) (@lem1977868 x y)). Qed.
Lemma lem1977878 (x1 : real) (y1 : real) : (real_div x1 y1) = (term53 x1 y1).
Proof. exact (@lem1977877 x1 y1). Qed.
Lemma lem1977879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1977880 (x1 : real) (y1 : real) : (term55 x1 y1) = (term56 x1 y1).
Proof. exact (MK_COMB (@lem1977879) (@lem1977878 x1 y1)). Qed.
Lemma lem1977882 (x : real) (y : real) : (real_div x y) = (term53 x y).
Proof. exact (EQ_MP (@lem1977869 x y) (@lem1977868 x y)). Qed.
Lemma lem1977883 (x2 : real) (y2 : real) : (real_div x2 y2) = (term53 x2 y2).
Proof. exact (@lem1977882 x2 y2). Qed.
Lemma lem1977884 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term57 x1 y1 x2 y2) = (term58 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1977880 x1 y1) (@lem1977883 x2 y2)). Qed.
Lemma lem1977885 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1977886 (x1 : real) (y1 : real) (x2 : real) (y2 : real) : (term59 x1 y1 x2 y2) = (term60 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1977885) (@lem1977884 x1 y1 x2 y2)). Qed.
Lemma lem1977888 (x : real) (y : real) (z : real) : (term48 x y z) = (term49 x y z).
Proof. exact (EQ_MP (@lem1977863 x y z) (@lem1977862 x y z)). Qed.
Lemma lem1977889 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : (term61 x1 x2 y1 y2) = (term62 x1 x2 y1 y2).
Proof. exact (@lem1977888 (real_mul x1 y2) (real_mul x2 y1) (term63 y1 y2)). Qed.
Lemma lem1977890 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2)) = ((term58 x1 y1 x2 y2) = (term62 x1 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1977886 x1 y1 x2 y2) (@lem1977889 x1 x2 y1 y2)). Qed.
Lemma lem1977893 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : ((term58 x1 y1 x2 y2) = (term62 x1 x2 y1 y2)) = ((term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2)).
Proof. exact (SYM (@lem1977890 x1 x2 y1 y2)). Qed.
Lemma lem1977894 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1977898 (x : real) (y : real) (z : real) : (term15 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1977854 x y z) (@lem1977853 x y z)). Qed.
Lemma lem1977899 (x1 : real) (y1 : real) (y2 : real) : (term64 x1 y1 y2) = (term65 x1 y1 y2).
Proof. exact (@lem1977898 x1 y2 (term63 y1 y2)). Qed.
Lemma lem1977900 (x1 : real) (y1 : real) : (term66 x1 y1) = (term66 x1 y1).
Proof. exact (eq_refl (term66 x1 y1)). Qed.
Lemma lem1977901 (x1 : real) (y1 : real) (y2 : real) : ((term53 x1 y1) = (term64 x1 y1 y2)) = ((term53 x1 y1) = (term65 x1 y1 y2)).
Proof. exact (MK_COMB (@lem1977900 x1 y1) (@lem1977899 x1 y1 y2)). Qed.
Lemma lem1977904 (x1 : real) (y1 : real) (y2 : real) : ((term53 x1 y1) = (term65 x1 y1 y2)) = ((term53 x1 y1) = (term64 x1 y1 y2)).
Proof. exact (SYM (@lem1977901 x1 y1 y2)). Qed.
Lemma lem1977905 (x1 : real) : (real_mul x1) = (real_mul x1).
Proof. exact (eq_refl (real_mul x1)). Qed.
Lemma lem1977909 (b : real) (a : real) (c : real) : (term14 a b c) = (term15 b a c).
Proof. exact (EQ_MP (@lem1977827 b a c) (@lem0)). Qed.
Lemma lem1977910 (y1 : real) (y2 : real) : (term67 y1 y2) = (term68 y1 y2).
Proof. exact (@lem1977909 (real_inv y1) y2 (real_inv y2)). Qed.
Lemma lem1977911 (y1 : real) : (term69 y1) = (term69 y1).
Proof. exact (eq_refl (term69 y1)). Qed.
Lemma lem1977912 (y1 : real) (y2 : real) : ((real_inv y1) = (term67 y1 y2)) = ((real_inv y1) = (term68 y1 y2)).
Proof. exact (MK_COMB (@lem1977911 y1) (@lem1977910 y1 y2)). Qed.
Lemma lem1977913 (y1 : real) (y2 : real) : ((real_inv y1) = (term68 y1 y2)) = ((real_inv y1) = (term67 y1 y2)).
Proof. exact (SYM (@lem1977912 y1 y2)). Qed.
Lemma lem1977917 (x : real) (y : real) (z : real) : (term14 x y z) = (term15 x y z).
Proof. exact (EQ_MP (@lem1977784 x y z) (@lem1977783 x y z)). Qed.
Lemma lem1977918 (x2 : real) (y1 : real) (y2 : real) : (term70 x2 y1 y2) = (term71 x2 y1 y2).
Proof. exact (@lem1977917 (real_mul x2 y1) (real_inv y1) (real_inv y2)). Qed.
Lemma lem1977919 (x2 : real) (y2 : real) : (term66 x2 y2) = (term66 x2 y2).
Proof. exact (eq_refl (term66 x2 y2)). Qed.
Lemma lem1977920 (x2 : real) (y1 : real) (y2 : real) : ((term53 x2 y2) = (term70 x2 y1 y2)) = ((term53 x2 y2) = (term71 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1977919 x2 y2) (@lem1977918 x2 y1 y2)). Qed.
Lemma lem1977923 (x2 : real) (y1 : real) (y2 : real) : ((term53 x2 y2) = (term71 x2 y1 y2)) = ((term53 x2 y2) = (term70 x2 y1 y2)).
Proof. exact (SYM (@lem1977920 x2 y1 y2)). Qed.
Lemma lem1977924 (y2 : real) : (real_inv y2) = (real_inv y2).
Proof. exact (eq_refl (real_inv y2)). Qed.
Lemma lem1977925 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1977927 (x : real) : x = (term31 x).
Proof. exact (EQ_MP (@lem1977775 x) (@lem1977774 x)). Qed.
Lemma lem1977928 (y1 : real) : (real_inv y1) = (term72 y1).
Proof. exact (@lem1977927 (real_inv y1)). Qed.
Lemma lem1977929 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1977930 (y1 : real) : (term69 y1) = (term73 y1).
Proof. exact (MK_COMB (@lem1977929) (@lem1977928 y1)). Qed.
Lemma lem1977931 (y1 : real) (y2 : real) : (term68 y1 y2) = (term68 y1 y2).
Proof. exact (eq_refl (term68 y1 y2)). Qed.
Lemma lem1977932 (y1 : real) (y2 : real) : ((real_inv y1) = (term68 y1 y2)) = ((term72 y1) = (term68 y1 y2)).
Proof. exact (MK_COMB (@lem1977930 y1) (@lem1977931 y1 y2)). Qed.
Lemma lem1977933 (y1 : real) (y2 : real) : ((term72 y1) = (term68 y1 y2)) = ((real_inv y1) = (term68 y1 y2)).
Proof. exact (SYM (@lem1977932 y1 y2)). Qed.
Lemma lem1977935 (x : real) : x = (term31 x).
Proof. exact (EQ_MP (@lem1977775 x) (@lem1977774 x)). Qed.
Lemma lem1977936 (x2 : real) : x2 = (term31 x2).
Proof. exact (@lem1977935 x2). Qed.
Lemma lem1977937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1977938 (x2 : real) : (@eq real x2) = (term74 x2).
Proof. exact (MK_COMB (@lem1977937) (@lem1977936 x2)). Qed.
Lemma lem1977939 (x2 : real) (y1 : real) : (term75 x2 y1) = (term75 x2 y1).
Proof. exact (eq_refl (term75 x2 y1)). Qed.
Lemma lem1977940 (x2 : real) (y1 : real) : (x2 = (term75 x2 y1)) = ((term31 x2) = (term75 x2 y1)).
Proof. exact (MK_COMB (@lem1977938 x2) (@lem1977939 x2 y1)). Qed.
Lemma lem1977941 (x2 : real) (y1 : real) : ((term31 x2) = (term75 x2 y1)) = (x2 = (term75 x2 y1)).
Proof. exact (SYM (@lem1977940 x2 y1)). Qed.
Lemma lem1977945 (x : real) (y : real) (z : real) : (term15 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1977762 x y z) (@lem1977761 x y z)). Qed.
Lemma lem1977946 (y1 : real) (y2 : real) : (term68 y1 y2) = (term76 y1 y2).
Proof. exact (@lem1977945 (real_inv y1) y2 (real_inv y2)). Qed.
Lemma lem1977947 (y1 : real) : (term73 y1) = (term73 y1).
Proof. exact (eq_refl (term73 y1)). Qed.
Lemma lem1977948 (y1 : real) (y2 : real) : ((term72 y1) = (term68 y1 y2)) = ((term72 y1) = (term76 y1 y2)).
Proof. exact (MK_COMB (@lem1977947 y1) (@lem1977946 y1 y2)). Qed.
Lemma lem1977951 (y1 : real) (y2 : real) : ((term72 y1) = (term76 y1 y2)) = ((term72 y1) = (term68 y1 y2)).
Proof. exact (SYM (@lem1977948 y1 y2)). Qed.
Lemma lem1977955 (x : real) (y : real) (z : real) : (term15 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1977762 x y z) (@lem1977761 x y z)). Qed.
Lemma lem1977956 (x2 : real) (y1 : real) : (term75 x2 y1) = (term77 x2 y1).
Proof. exact (@lem1977955 x2 y1 (real_inv y1)). Qed.
Lemma lem1977957 (x2 : real) : (term74 x2) = (term74 x2).
Proof. exact (eq_refl (term74 x2)). Qed.
Lemma lem1977958 (x2 : real) (y1 : real) : ((term31 x2) = (term75 x2 y1)) = ((term31 x2) = (term77 x2 y1)).
Proof. exact (MK_COMB (@lem1977957 x2) (@lem1977956 x2 y1)). Qed.
Lemma lem1977961 (x2 : real) (y1 : real) : ((term31 x2) = (term77 x2 y1)) = ((term31 x2) = (term75 x2 y1)).
Proof. exact (SYM (@lem1977958 x2 y1)). Qed.
Lemma lem1977963 (x : real) (y : real) (z : real) : ((real_mul x y) = (real_mul x z)) = (term13 x y z).
Proof. exact (EQ_MP (@lem1977735 x y z) (@lem1977734 x y z)). Qed.
Lemma lem1977964 (y1 : real) (y2 : real) : ((term72 y1) = (term76 y1 y2)) = (term78 y1 y2).
Proof. exact (@lem1977963 (real_inv y1) term5 (term4 y2)). Qed.
Lemma lem1977971 (y1 : real) (y2 : real) : (term78 y1 y2) = ((term72 y1) = (term76 y1 y2)).
Proof. exact (SYM (@lem1977964 y1 y2)). Qed.
Lemma lem1977973 (x : real) (y : real) (z : real) : ((real_mul x y) = (real_mul x z)) = (term13 x y z).
Proof. exact (EQ_MP (@lem1977735 x y z) (@lem1977734 x y z)). Qed.
Lemma lem1977974 (x2 : real) (y1 : real) : ((term31 x2) = (term77 x2 y1)) = (term79 x2 y1).
Proof. exact (@lem1977973 x2 term5 (term4 y1)). Qed.
Lemma lem1977981 (x2 : real) (y1 : real) : (term79 x2 y1) = ((term31 x2) = (term77 x2 y1)).
Proof. exact (SYM (@lem1977974 x2 y1)). Qed.
Lemma lem1977982 (y2 : real) (h1 : term5 = (term4 y2)) : term5 = (term4 y2).
Proof. exact (h1). Qed.
Lemma lem1977983 (y2 : real) (h1 : term5 = (term4 y2)) : (term4 y2) = term5.
Proof. exact (SYM (@lem1977982 y2 h1)). Qed.
Lemma lem1977984 (y2 : real) (h1 : (term4 y2) = term5) : (term4 y2) = term5.
Proof. exact (h1). Qed.
Lemma lem1977985 (y2 : real) (h1 : (term4 y2) = term5) : term5 = (term4 y2).
Proof. exact (SYM (@lem1977984 y2 h1)). Qed.
Lemma lem1977986 (y2 : real) : (term5 = (term4 y2)) = ((term4 y2) = term5).
Proof. exact (prop_ext (fun h1 : term5 = (term4 y2) => @lem1977983 y2 h1) (fun h1 : (term4 y2) = term5 => @lem1977985 y2 h1)). Qed.
Lemma lem1977987 (y2 : real) : ((term4 y2) = term5) = (term5 = (term4 y2)).
Proof. exact (SYM (@lem1977986 y2)). Qed.
Lemma lem1977988 (y1 : real) (h1 : term5 = (term4 y1)) : term5 = (term4 y1).
Proof. exact (h1). Qed.
Lemma lem1977989 (y1 : real) (h1 : term5 = (term4 y1)) : (term4 y1) = term5.
Proof. exact (SYM (@lem1977988 y1 h1)). Qed.
Lemma lem1977990 (y1 : real) (h1 : (term4 y1) = term5) : (term4 y1) = term5.
Proof. exact (h1). Qed.
Lemma lem1977991 (y1 : real) (h1 : (term4 y1) = term5) : term5 = (term4 y1).
Proof. exact (SYM (@lem1977990 y1 h1)). Qed.
Lemma lem1977992 (y1 : real) : (term5 = (term4 y1)) = ((term4 y1) = term5).
Proof. exact (prop_ext (fun h1 : term5 = (term4 y1) => @lem1977989 y1 h1) (fun h1 : (term4 y1) = term5 => @lem1977991 y1 h1)). Qed.
Lemma lem1977993 (y1 : real) : ((term4 y1) = term5) = (term5 = (term4 y1)).
Proof. exact (SYM (@lem1977992 y1)). Qed.
Lemma lem1977995 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1977726 x) (@lem1977725 x)). Qed.
Lemma lem1977996 (y2 : real) : term2 y2.
Proof. exact (@lem1977995 y2). Qed.
Lemma lem1977998 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1977726 x) (@lem1977725 x)). Qed.
Lemma lem1977999 (y1 : real) : term2 y1.
Proof. exact (@lem1977998 y1). Qed.
Lemma lem1978013 (y2 : real) : term80 y2.
Proof. exact (@lem82 (y2 = term81)). Qed.
Lemma lem1978027 (y2 : real) (h1 : term3 y2) : (y2 = term81) = False.
Proof. exact (@lem1978013 y2 (@lem1977872 y2 h1)). Qed.
Lemma lem1978028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1978029 (y2 : real) (h1 : term3 y2) : (term3 y2) = (~ False).
Proof. exact (MK_COMB (@lem1978028) (@lem1978027 y2 h1)). Qed.
Lemma lem1978031 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1978032 (y2 : real) (h1 : term3 y2) : (term3 y2) = True.
Proof. exact (TRANS (@lem1978029 y2 h1) (@lem1978031)). Qed.
Lemma lem1978033 (y2 : real) (h1 : term3 y2) : True = (term3 y2).
Proof. exact (SYM (@lem1978032 y2 h1)). Qed.
Lemma lem1978034 (y2 : real) (h1 : term3 y2) : term3 y2.
Proof. exact (EQ_MP (@lem1978033 y2 h1) (@lem0)). Qed.
Lemma lem1978035 (y1 : real) : term80 y1.
Proof. exact (@lem82 (y1 = term81)). Qed.
Lemma lem1978062 (y1 : real) (h1 : term3 y1) : (y1 = term81) = False.
Proof. exact (@lem1978035 y1 (@lem1977873 y1 h1)). Qed.
Lemma lem1978063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1978064 (y1 : real) (h1 : term3 y1) : (term3 y1) = (~ False).
Proof. exact (MK_COMB (@lem1978063) (@lem1978062 y1 h1)). Qed.
Lemma lem1978066 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1978067 (y1 : real) (h1 : term3 y1) : (term3 y1) = True.
Proof. exact (TRANS (@lem1978064 y1 h1) (@lem1978066)). Qed.
Lemma lem1978068 (y1 : real) (h1 : term3 y1) : True = (term3 y1).
Proof. exact (SYM (@lem1978067 y1 h1)). Qed.
Lemma lem1978069 (y1 : real) (h1 : term3 y1) : term3 y1.
Proof. exact (EQ_MP (@lem1978068 y1 h1) (@lem0)). Qed.
Lemma lem1978070 (y1 : real) (h1 : term3 y1) : (term4 y1) = term5.
Proof. exact (@lem1977999 y1 (@lem1978069 y1 h1)). Qed.
Lemma lem1978071 (y2 : real) (h1 : term3 y2) : (term4 y2) = term5.
Proof. exact (@lem1977996 y2 (@lem1978034 y2 h1)). Qed.
Lemma lem1978072 (y1 : real) (h1 : term3 y1) : term5 = (term4 y1).
Proof. exact (EQ_MP (@lem1977993 y1) (@lem1978070 y1 h1)). Qed.
Lemma lem1978073 (y2 : real) (h1 : term3 y2) : term5 = (term4 y2).
Proof. exact (EQ_MP (@lem1977987 y2) (@lem1978071 y2 h1)). Qed.
Lemma lem1978074 (x2 : real) (y1 : real) (h1 : term3 y1) : term79 x2 y1.
Proof. exact (or_intro2 (x2 = term81) (@lem1978072 y1 h1)). Qed.
Lemma lem1978075 (y1 : real) (y2 : real) (h1 : term3 y2) : term78 y1 y2.
Proof. exact (or_intro2 ((real_inv y1) = term81) (@lem1978073 y2 h1)). Qed.
Lemma lem1978076 (x2 : real) (y1 : real) (h1 : term3 y1) : (term31 x2) = (term77 x2 y1).
Proof. exact (EQ_MP (@lem1977981 x2 y1) (@lem1978074 x2 y1 h1)). Qed.
Lemma lem1978077 (y1 : real) (y2 : real) (h1 : term3 y2) : (term72 y1) = (term76 y1 y2).
Proof. exact (EQ_MP (@lem1977971 y1 y2) (@lem1978075 y1 y2 h1)). Qed.
Lemma lem1978078 (x2 : real) (y1 : real) (h1 : term3 y1) : (term31 x2) = (term75 x2 y1).
Proof. exact (EQ_MP (@lem1977961 x2 y1) (@lem1978076 x2 y1 h1)). Qed.
Lemma lem1978079 (y1 : real) (y2 : real) (h1 : term3 y2) : (term72 y1) = (term68 y1 y2).
Proof. exact (EQ_MP (@lem1977951 y1 y2) (@lem1978077 y1 y2 h1)). Qed.
Lemma lem1978080 (x2 : real) (y1 : real) (h1 : term3 y1) : x2 = (term75 x2 y1).
Proof. exact (EQ_MP (@lem1977941 x2 y1) (@lem1978078 x2 y1 h1)). Qed.
Lemma lem1978081 (y1 : real) (y2 : real) (h1 : term3 y2) : (real_inv y1) = (term68 y1 y2).
Proof. exact (EQ_MP (@lem1977933 y1 y2) (@lem1978079 y1 y2 h1)). Qed.
Lemma lem1978082 (x2 : real) (y1 : real) (h1 : term3 y1) : (real_mul x2) = (term82 x2 y1).
Proof. exact (MK_COMB (@lem1977925) (@lem1978080 x2 y1 h1)). Qed.
Lemma lem1978083 (x2 : real) (y2 : real) (y1 : real) (h1 : term3 y1) : (term53 x2 y2) = (term71 x2 y1 y2).
Proof. exact (MK_COMB (@lem1978082 x2 y1 h1) (@lem1977924 y2)). Qed.
Lemma lem1978084 (x2 : real) (y2 : real) (y1 : real) (h1 : term3 y1) : (term53 x2 y2) = (term70 x2 y1 y2).
Proof. exact (EQ_MP (@lem1977923 x2 y1 y2) (@lem1978083 x2 y2 y1 h1)). Qed.
Lemma lem1978085 (y1 : real) (y2 : real) (h1 : term3 y2) : (real_inv y1) = (term67 y1 y2).
Proof. exact (EQ_MP (@lem1977913 y1 y2) (@lem1978081 y1 y2 h1)). Qed.
Lemma lem1978086 (x1 : real) (y1 : real) (y2 : real) (h1 : term3 y2) : (term53 x1 y1) = (term65 x1 y1 y2).
Proof. exact (MK_COMB (@lem1977905 x1) (@lem1978085 y1 y2 h1)). Qed.
Lemma lem1978087 (x1 : real) (y1 : real) (y2 : real) (h1 : term3 y2) : (term53 x1 y1) = (term64 x1 y1 y2).
Proof. exact (EQ_MP (@lem1977904 x1 y1 y2) (@lem1978086 x1 y1 y2 h1)). Qed.
Lemma lem1978088 (x1 : real) (y1 : real) (y2 : real) (h1 : term3 y2) : (term56 x1 y1) = (term83 x1 y1 y2).
Proof. exact (MK_COMB (@lem1977894) (@lem1978087 x1 y1 y2 h1)). Qed.
Lemma lem1978089 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term3 y2) : (term58 x1 y1 x2 y2) = (term62 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1978088 x1 y1 y2 h2) (@lem1978084 x2 y2 y1 h1)). Qed.
Lemma lem1978090 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term3 y2) : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1977893 x1 x2 y1 y2) (@lem1978089 x1 x2 y1 y2 h1 h2)). Qed.
Lemma lem1978091 (y1 : real) (y2 : real) (h1 : term54 y1 y2) : term3 y2.
Proof. exact (proj2 (@lem1977871 y1 y2 h1)). Qed.
Lemma lem1978092 (y1 : real) (y2 : real) (h1 : term54 y1 y2) : term3 y1.
Proof. exact (proj1 (@lem1977871 y1 y2 h1)). Qed.
Lemma lem1978093 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term3 y2) : (term3 y2) = ((term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2)).
Proof. exact (prop_ext (fun h3 : term3 y2 => @lem1978090 x1 x2 y1 y2 h1 h2) (fun h3 : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2) => @lem1977872 y2 h2)). Qed.
Lemma lem1978094 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term3 y2) : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1978093 x1 x2 y1 y2 h1 h2) (@lem1977872 y2 h2)). Qed.
Lemma lem1978095 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term3 y2) : (term3 y1) = ((term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2)).
Proof. exact (prop_ext (fun h3 : term3 y1 => @lem1978094 x1 x2 y1 y2 h1 h2) (fun h3 : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2) => @lem1977873 y1 h1)). Qed.
Lemma lem1978096 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term3 y2) : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1978095 x1 x2 y1 y2 h1 h2) (@lem1977873 y1 h1)). Qed.
Lemma lem1978097 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term54 y1 y2) : (term3 y2) = ((term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2)).
Proof. exact (prop_ext (fun h3 : term3 y2 => @lem1978096 x1 x2 y1 y2 h1 h3) (fun h3 : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2) => @lem1978091 y1 y2 h2)). Qed.
Lemma lem1978098 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term3 y1) (h2 : term54 y1 y2) : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1978097 x1 x2 y1 y2 h1 h2) (@lem1978091 y1 y2 h2)). Qed.
Lemma lem1978099 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term54 y1 y2) : (term3 y1) = ((term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2)).
Proof. exact (prop_ext (fun h2 : term3 y1 => @lem1978098 x1 x2 y1 y2 h2 h1) (fun h2 : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2) => @lem1978092 y1 y2 h1)). Qed.
Lemma lem1978100 (x1 : real) (x2 : real) (y1 : real) (y2 : real) (h1 : term54 y1 y2) : (term57 x1 y1 x2 y2) = (term61 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1978099 x1 x2 y1 y2 h1) (@lem1978092 y1 y2 h1)). Qed.
Lemma lem1978101 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term84 x1 x2 y1 y2.
Proof. exact (fun h0 : term54 y1 y2 => @lem1978100 x1 x2 y1 y2 h0). Qed.
