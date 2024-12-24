Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_LE_0_term_abbrevs.
Require Import SQRT_EQ_0_spec.
Require Import SQRT_LT_0_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483533_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1947676 (x : real) : term0 x.
Proof. exact (@lem1947675 x). Qed.
Lemma lem1947677 (x : real) : (term0 x) = (((sqrt x) = term1) = (x = term1)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1947679 (x : real) : term2 x.
Proof. exact (@lem1947567 x). Qed.
Lemma lem1947680 (x : real) : (term2 x) = ((term3 x) = (term4 x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1947697 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem17160 (term4 x) (x = term1)). Qed.
Lemma lem1947703 (x : real) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1947705 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1947706 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1947705 x) (@lem1947697 x)). Qed.
Lemma lem1947707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1947708 (x : real) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1947707) (@lem1947706 x)). Qed.
Lemma lem1947709 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1947708 x) (@lem1947703 x)). Qed.
Lemma lem1947710 (x : real) : (term15 x) = (term13 x).
Proof. exact (@lem17646 (term16 x) (term17 x)). Qed.
Lemma lem1947740 (x : real) : (term15 x) = (term14 x).
Proof. exact (TRANS (@lem1947710 x) (@lem1947709 x)). Qed.
Lemma lem1947741 (x : real) : (term16 x) = (term18 x).
Proof. exact (@lem1483523 x term1). Qed.
Lemma lem1947747 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1947749 (x : nat) : (term21 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1947750 : term22 = term1.
Proof. exact (@lem1947749 term23). Qed.
Lemma lem1947751 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1947752 (x : real) : (term20 x) = (term24 x).
Proof. exact (MK_COMB (@lem1947751 x) (@lem1947750)). Qed.
Lemma lem1947753 (x : real) : (term24 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1947754 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1947752 x) (@lem1947753 x)). Qed.
Lemma lem1947756 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1947747 x) (@lem1947754 x)). Qed.
Lemma lem1947757 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1947758 (x : real) : (term25 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1947757) (@lem1947756 x)). Qed.
Lemma lem1947759 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947760 (x : real) : (term18 x) = (term26 x).
Proof. exact (MK_COMB (@lem1947758 x) (@lem1947759)). Qed.
Lemma lem1947761 (x : real) : (term16 x) = (term26 x).
Proof. exact (TRANS (@lem1947741 x) (@lem1947760 x)). Qed.
Lemma lem1947762 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem1483531 term1 x). Qed.
Lemma lem1947768 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483519 term1 x). Qed.
Lemma lem1947773 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1483448 (term31 x)). Qed.
Lemma lem1947775 (x : real) : (term29 x) = (term31 x).
Proof. exact (TRANS (@lem1947768 x) (@lem1947773 x)). Qed.
Lemma lem1947776 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1947777 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1947776) (@lem1947775 x)). Qed.
Lemma lem1947778 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947779 (x : real) : (term28 x) = (term34 x).
Proof. exact (MK_COMB (@lem1947777 x) (@lem1947778)). Qed.
Lemma lem1947780 (x : real) : (term27 x) = (term34 x).
Proof. exact (TRANS (@lem1947762 x) (@lem1947779 x)). Qed.
Lemma lem1947781 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483554 x term1). Qed.
Lemma lem1947787 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1947789 (x : nat) : (term21 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1947790 : term22 = term1.
Proof. exact (@lem1947789 term23). Qed.
Lemma lem1947791 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1947792 (x : real) : (term20 x) = (term24 x).
Proof. exact (MK_COMB (@lem1947791 x) (@lem1947790)). Qed.
Lemma lem1947793 (x : real) : (term24 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1947794 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1947792 x) (@lem1947793 x)). Qed.
Lemma lem1947796 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1947787 x) (@lem1947794 x)). Qed.
Lemma lem1947797 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1947798 (x : real) : (term37 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1947797) (@lem1947796 x)). Qed.
Lemma lem1947801 (x : real) : (real_neg x) = (term31 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1947802 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1947803 (x : real) : ((term37 x) = (real_neg x)) = ((term37 x) = (term31 x)).
Proof. exact (MK_COMB (@lem1947802 x) (@lem1947801 x)). Qed.
Lemma lem1947804 (x : real) : (term37 x) = (term31 x).
Proof. exact (EQ_MP (@lem1947803 x) (@lem1947798 x)). Qed.
Lemma lem1947805 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1947806 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1947805) (@lem1947804 x)). Qed.
Lemma lem1947807 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947808 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1947806 x) (@lem1947807)). Qed.
Lemma lem1947809 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1947810 (x : real) : (term43 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1947809) (@lem1947796 x)). Qed.
Lemma lem1947811 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947812 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1947810 x) (@lem1947811)). Qed.
Lemma lem1947813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1947814 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1947813) (@lem1947812 x)). Qed.
Lemma lem1947815 (x : real) : (term36 x) = (term48 x).
Proof. exact (MK_COMB (@lem1947814 x) (@lem1947808 x)). Qed.
Lemma lem1947816 (x : real) : (term35 x) = (term48 x).
Proof. exact (TRANS (@lem1947781 x) (@lem1947815 x)). Qed.
Lemma lem1947817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947818 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1947817) (@lem1947780 x)). Qed.
Lemma lem1947819 (x : real) : (term6 x) = (term51 x).
Proof. exact (MK_COMB (@lem1947818 x) (@lem1947816 x)). Qed.
Lemma lem1947820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947821 (x : real) : (term8 x) = (term52 x).
Proof. exact (MK_COMB (@lem1947820) (@lem1947761 x)). Qed.
Lemma lem1947822 (x : real) : (term10 x) = (term53 x).
Proof. exact (MK_COMB (@lem1947821 x) (@lem1947819 x)). Qed.
Lemma lem1947823 (x : real) : (term54 x) = (term55 x).
Proof. exact (@lem1483533 term1 x). Qed.
Lemma lem1947829 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483519 term1 x). Qed.
Lemma lem1947834 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1483448 (term31 x)). Qed.
Lemma lem1947836 (x : real) : (term29 x) = (term31 x).
Proof. exact (TRANS (@lem1947829 x) (@lem1947834 x)). Qed.
Lemma lem1947837 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1947838 (x : real) : (term56 x) = (term40 x).
Proof. exact (MK_COMB (@lem1947837) (@lem1947836 x)). Qed.
Lemma lem1947839 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947840 (x : real) : (term55 x) = (term42 x).
Proof. exact (MK_COMB (@lem1947838 x) (@lem1947839)). Qed.
Lemma lem1947841 (x : real) : (term54 x) = (term42 x).
Proof. exact (TRANS (@lem1947823 x) (@lem1947840 x)). Qed.
Lemma lem1947842 (x : real) : (term4 x) = (term44 x).
Proof. exact (@lem1483521 x term1). Qed.
Lemma lem1947848 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1947850 (x : nat) : (term21 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1947851 : term22 = term1.
Proof. exact (@lem1947850 term23). Qed.
Lemma lem1947852 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1947853 (x : real) : (term20 x) = (term24 x).
Proof. exact (MK_COMB (@lem1947852 x) (@lem1947851)). Qed.
Lemma lem1947854 (x : real) : (term24 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1947855 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1947853 x) (@lem1947854 x)). Qed.
Lemma lem1947857 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1947848 x) (@lem1947855 x)). Qed.
Lemma lem1947858 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1947859 (x : real) : (term43 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1947858) (@lem1947857 x)). Qed.
Lemma lem1947860 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947861 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1947859 x) (@lem1947860)). Qed.
Lemma lem1947862 (x : real) : (term4 x) = (term45 x).
Proof. exact (TRANS (@lem1947842 x) (@lem1947861 x)). Qed.
Lemma lem1947863 (x : real) : (x = term1) = ((term19 x) = term1).
Proof. exact (@lem1483529 x term1). Qed.
Lemma lem1947869 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 x term1). Qed.
Lemma lem1947871 (x : nat) : (term21 x) = term1.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1947872 : term22 = term1.
Proof. exact (@lem1947871 term23). Qed.
Lemma lem1947873 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1947874 (x : real) : (term20 x) = (term24 x).
Proof. exact (MK_COMB (@lem1947873 x) (@lem1947872)). Qed.
Lemma lem1947875 (x : real) : (term24 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1947876 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1947874 x) (@lem1947875 x)). Qed.
Lemma lem1947878 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1947869 x) (@lem1947876 x)). Qed.
Lemma lem1947879 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947880 (x : real) : (term57 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1947879) (@lem1947878 x)). Qed.
Lemma lem1947881 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947882 (x : real) : ((term19 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1947880 x) (@lem1947881)). Qed.
Lemma lem1947883 (x : real) : (x = term1) = (x = term1).
Proof. exact (TRANS (@lem1947863 x) (@lem1947882 x)). Qed.
Lemma lem1947884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1947885 (x : real) : (term58 x) = (term47 x).
Proof. exact (MK_COMB (@lem1947884) (@lem1947862 x)). Qed.
Lemma lem1947886 (x : real) : (term17 x) = (term59 x).
Proof. exact (MK_COMB (@lem1947885 x) (@lem1947883 x)). Qed.
Lemma lem1947887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947888 (x : real) : (term60 x) = (term61 x).
Proof. exact (MK_COMB (@lem1947887) (@lem1947841 x)). Qed.
Lemma lem1947889 (x : real) : (term7 x) = (term62 x).
Proof. exact (MK_COMB (@lem1947888 x) (@lem1947886 x)). Qed.
Lemma lem1947890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1947891 (x : real) : (term12 x) = (term63 x).
Proof. exact (MK_COMB (@lem1947890) (@lem1947822 x)). Qed.
Lemma lem1947892 (x : real) : (term14 x) = (term64 x).
Proof. exact (MK_COMB (@lem1947891 x) (@lem1947889 x)). Qed.
Lemma lem1947899 (x : real) : (term15 x) = (term64 x).
Proof. exact (TRANS (@lem1947740 x) (@lem1947892 x)). Qed.
Lemma lem1947916 (x : real) : (term62 x) = (term65 x).
Proof. exact (@lem19158 (term45 x) (term42 x) (x = term1)). Qed.
Lemma lem1947933 (x : real) : (term51 x) = (term66 x).
Proof. exact (@lem19158 (term45 x) (term34 x) (term42 x)). Qed.
Lemma lem1947936 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1947937 (x : real) : (term53 x) = (term67 x).
Proof. exact (MK_COMB (@lem1947936 x) (@lem1947933 x)). Qed.
Lemma lem1947944 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem19158 (term69 x) (term26 x) (term70 x)). Qed.
Lemma lem1947945 (x : real) : (term53 x) = (term68 x).
Proof. exact (TRANS (@lem1947937 x) (@lem1947944 x)). Qed.
Lemma lem1947946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1947947 (x : real) : (term63 x) = (term71 x).
Proof. exact (MK_COMB (@lem1947946) (@lem1947945 x)). Qed.
Lemma lem1947948 (x : real) : (term64 x) = (term72 x).
Proof. exact (MK_COMB (@lem1947947 x) (@lem1947916 x)). Qed.
Lemma lem1947949 (x : real) : (term15 x) = (term72 x).
Proof. exact (TRANS (@lem1947899 x) (@lem1947948 x)). Qed.
Lemma lem1947971 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1947972 (x : real) (h1 : term68 x) : term68 x.
Proof. exact (h1). Qed.
Lemma lem1947973 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1947974 (x : real) (h1 : term73 x) : term69 x.
Proof. exact (proj2 (@lem1947973 x h1)). Qed.
Lemma lem1947976 (x : real) (h1 : term73 x) : term45 x.
Proof. exact (proj2 (@lem1947974 x h1)). Qed.
Lemma lem1947977 (x : real) (h1 : term73 x) : term34 x.
Proof. exact (proj1 (@lem1947974 x h1)). Qed.
Lemma lem1947979 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1947980 : term75 = term76.
Proof. exact (@lem1947979 (NUMERAL 0) term23). Qed.
Lemma lem1947981 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1947982 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1947983 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1947982 h1) (fun h1 : term76 = True => @lem1947981)). Qed.
Lemma lem1947984 : term76 = True.
Proof. exact (EQ_MP (@lem1947983) (@lem1947981)). Qed.
Lemma lem1947985 : term75 = True.
Proof. exact (TRANS (@lem1947980) (@lem1947984)). Qed.
Lemma lem1947986 : True = term75.
Proof. exact (SYM (@lem1947985)). Qed.
Lemma lem1947987 : term75.
Proof. exact (EQ_MP (@lem1947986) (@lem0)). Qed.
Lemma lem1947988 (x : real) (h1 : term73 x) : term78 x.
Proof. exact (conj (@lem1947987) (@lem1947977 x h1)). Qed.
Lemma lem1947990 (x : real) (y : real) : term79 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1947991 (x : real) : term80 x.
Proof. exact (@lem1947990 term81 (term31 x)). Qed.
Lemma lem1947992 (x : real) (h1 : term73 x) : term82 x.
Proof. exact (@lem1947991 x (@lem1947988 x h1)). Qed.
Lemma lem1947993 (x : real) : (term83 x) = (term31 x).
Proof. exact (@lem1483460 (term31 x)). Qed.
Lemma lem1947994 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1947995 (x : real) : (term84 x) = (term33 x).
Proof. exact (MK_COMB (@lem1947994) (@lem1947993 x)). Qed.
Lemma lem1947996 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1947997 (x : real) : (term82 x) = (term34 x).
Proof. exact (MK_COMB (@lem1947995 x) (@lem1947996)). Qed.
Lemma lem1947998 (x : real) (h1 : term73 x) : term34 x.
Proof. exact (EQ_MP (@lem1947997 x) (@lem1947992 x h1)). Qed.
Lemma lem1948000 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948001 : term75 = term76.
Proof. exact (@lem1948000 (NUMERAL 0) term23). Qed.
Lemma lem1948002 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1948003 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1948004 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1948003 h1) (fun h1 : term76 = True => @lem1948002)). Qed.
Lemma lem1948005 : term76 = True.
Proof. exact (EQ_MP (@lem1948004) (@lem1948002)). Qed.
Lemma lem1948006 : term75 = True.
Proof. exact (TRANS (@lem1948001) (@lem1948005)). Qed.
Lemma lem1948007 : True = term75.
Proof. exact (SYM (@lem1948006)). Qed.
Lemma lem1948008 : term75.
Proof. exact (EQ_MP (@lem1948007) (@lem0)). Qed.
Lemma lem1948009 (x : real) (h1 : term73 x) : term85 x.
Proof. exact (conj (@lem1948008) (@lem1947976 x h1)). Qed.
Lemma lem1948011 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1948012 (x : real) : term87 x.
Proof. exact (@lem1948011 term81 x). Qed.
Lemma lem1948013 (x : real) (h1 : term73 x) : term88 x.
Proof. exact (@lem1948012 x (@lem1948009 x h1)). Qed.
Lemma lem1948014 (x : real) : (term89 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1948015 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948016 (x : real) : (term90 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1948015) (@lem1948014 x)). Qed.
Lemma lem1948017 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948018 (x : real) : (term88 x) = (term45 x).
Proof. exact (MK_COMB (@lem1948016 x) (@lem1948017)). Qed.
Lemma lem1948019 (x : real) (h1 : term73 x) : term45 x.
Proof. exact (EQ_MP (@lem1948018 x) (@lem1948013 x h1)). Qed.
Lemma lem1948020 (x : real) (h1 : term73 x) : term91 x.
Proof. exact (conj (@lem1948019 x h1) (@lem1947998 x h1)). Qed.
Lemma lem1948022 (x : real) (y : real) : term92 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1948023 (x : real) : term93 x.
Proof. exact (@lem1948022 x (term31 x)). Qed.
Lemma lem1948024 (x : real) (h1 : term73 x) : term94 x.
Proof. exact (@lem1948023 x (@lem1948020 x h1)). Qed.
Lemma lem1948025 (x : real) : (term95 x) = (term96 x).
Proof. exact (@lem1483442 term97 x). Qed.
Lemma lem1948027 (m : nat) : (term98 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1948028 : term99 = term1.
Proof. exact (@lem1948027 term23). Qed.
Lemma lem1948029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1948030 : term100 = term101.
Proof. exact (MK_COMB (@lem1948029) (@lem1948028)). Qed.
Lemma lem1948031 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1948032 (x : real) : (term96 x) = (term102 x).
Proof. exact (MK_COMB (@lem1948030) (@lem1948031 x)). Qed.
Lemma lem1948033 (x : real) : (term95 x) = (term102 x).
Proof. exact (TRANS (@lem1948025 x) (@lem1948032 x)). Qed.
Lemma lem1948034 (x : real) : (term102 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1948035 (x : real) : (term95 x) = term1.
Proof. exact (TRANS (@lem1948033 x) (@lem1948034 x)). Qed.
Lemma lem1948036 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948037 (x : real) : (term103 x) = term104.
Proof. exact (MK_COMB (@lem1948036) (@lem1948035 x)). Qed.
Lemma lem1948038 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948039 (x : real) : (term94 x) = term105.
Proof. exact (MK_COMB (@lem1948037 x) (@lem1948038)). Qed.
Lemma lem1948040 (x : real) (h1 : term73 x) : term105.
Proof. exact (EQ_MP (@lem1948039 x) (@lem1948024 x h1)). Qed.
Lemma lem1948042 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948043 : term105 = term106.
Proof. exact (@lem1948042 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1948044 : term106 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1948045 : term105 = False.
Proof. exact (TRANS (@lem1948043) (@lem1948044)). Qed.
Lemma lem1948046 (x : real) (h1 : term73 x) : False.
Proof. exact (EQ_MP (@lem1948045) (@lem1948040 x h1)). Qed.
Lemma lem1948047 (x : real) (h1 : term107 x) : term107 x.
Proof. exact (h1). Qed.
Lemma lem1948048 (x : real) (h1 : term107 x) : term70 x.
Proof. exact (proj2 (@lem1948047 x h1)). Qed.
Lemma lem1948049 (x : real) (h1 : term107 x) : term26 x.
Proof. exact (proj1 (@lem1948047 x h1)). Qed.
Lemma lem1948050 (x : real) (h1 : term107 x) : term42 x.
Proof. exact (proj2 (@lem1948048 x h1)). Qed.
Lemma lem1948053 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948054 : term75 = term76.
Proof. exact (@lem1948053 (NUMERAL 0) term23). Qed.
Lemma lem1948055 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1948056 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1948057 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1948056 h1) (fun h1 : term76 = True => @lem1948055)). Qed.
Lemma lem1948058 : term76 = True.
Proof. exact (EQ_MP (@lem1948057) (@lem1948055)). Qed.
Lemma lem1948059 : term75 = True.
Proof. exact (TRANS (@lem1948054) (@lem1948058)). Qed.
Lemma lem1948060 : True = term75.
Proof. exact (SYM (@lem1948059)). Qed.
Lemma lem1948061 : term75.
Proof. exact (EQ_MP (@lem1948060) (@lem0)). Qed.
Lemma lem1948062 (x : real) (h1 : term107 x) : term108 x.
Proof. exact (conj (@lem1948061) (@lem1948049 x h1)). Qed.
Lemma lem1948064 (x : real) (y : real) : term79 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1948065 (x : real) : term109 x.
Proof. exact (@lem1948064 term81 x). Qed.
Lemma lem1948066 (x : real) (h1 : term107 x) : term110 x.
Proof. exact (@lem1948065 x (@lem1948062 x h1)). Qed.
Lemma lem1948067 (x : real) : (term89 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1948068 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948069 (x : real) : (term111 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1948068) (@lem1948067 x)). Qed.
Lemma lem1948070 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948071 (x : real) : (term110 x) = (term26 x).
Proof. exact (MK_COMB (@lem1948069 x) (@lem1948070)). Qed.
Lemma lem1948072 (x : real) (h1 : term107 x) : term26 x.
Proof. exact (EQ_MP (@lem1948071 x) (@lem1948066 x h1)). Qed.
Lemma lem1948074 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948075 : term75 = term76.
Proof. exact (@lem1948074 (NUMERAL 0) term23). Qed.
Lemma lem1948076 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1948077 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1948078 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1948077 h1) (fun h1 : term76 = True => @lem1948076)). Qed.
Lemma lem1948079 : term76 = True.
Proof. exact (EQ_MP (@lem1948078) (@lem1948076)). Qed.
Lemma lem1948080 : term75 = True.
Proof. exact (TRANS (@lem1948075) (@lem1948079)). Qed.
Lemma lem1948081 : True = term75.
Proof. exact (SYM (@lem1948080)). Qed.
Lemma lem1948082 : term75.
Proof. exact (EQ_MP (@lem1948081) (@lem0)). Qed.
Lemma lem1948083 (x : real) (h1 : term107 x) : term112 x.
Proof. exact (conj (@lem1948082) (@lem1948050 x h1)). Qed.
Lemma lem1948085 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1948086 (x : real) : term113 x.
Proof. exact (@lem1948085 term81 (term31 x)). Qed.
Lemma lem1948087 (x : real) (h1 : term107 x) : term114 x.
Proof. exact (@lem1948086 x (@lem1948083 x h1)). Qed.
Lemma lem1948088 (x : real) : (term83 x) = (term31 x).
Proof. exact (@lem1483460 (term31 x)). Qed.
Lemma lem1948089 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948090 (x : real) : (term115 x) = (term40 x).
Proof. exact (MK_COMB (@lem1948089) (@lem1948088 x)). Qed.
Lemma lem1948091 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948092 (x : real) : (term114 x) = (term42 x).
Proof. exact (MK_COMB (@lem1948090 x) (@lem1948091)). Qed.
Lemma lem1948093 (x : real) (h1 : term107 x) : term42 x.
Proof. exact (EQ_MP (@lem1948092 x) (@lem1948087 x h1)). Qed.
Lemma lem1948094 (x : real) (h1 : term107 x) : term116 x.
Proof. exact (conj (@lem1948093 x h1) (@lem1948072 x h1)). Qed.
Lemma lem1948096 (x : real) (y : real) : term92 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1948097 (x : real) : term117 x.
Proof. exact (@lem1948096 (term31 x) x). Qed.
Lemma lem1948098 (x : real) (h1 : term107 x) : term118 x.
Proof. exact (@lem1948097 x (@lem1948094 x h1)). Qed.
Lemma lem1948099 (x : real) : (term119 x) = (term96 x).
Proof. exact (@lem1483440 term97 x). Qed.
Lemma lem1948101 (m : nat) : (term98 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1948102 : term99 = term1.
Proof. exact (@lem1948101 term23). Qed.
Lemma lem1948103 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1948104 : term100 = term101.
Proof. exact (MK_COMB (@lem1948103) (@lem1948102)). Qed.
Lemma lem1948105 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1948106 (x : real) : (term96 x) = (term102 x).
Proof. exact (MK_COMB (@lem1948104) (@lem1948105 x)). Qed.
Lemma lem1948107 (x : real) : (term119 x) = (term102 x).
Proof. exact (TRANS (@lem1948099 x) (@lem1948106 x)). Qed.
Lemma lem1948108 (x : real) : (term102 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1948109 (x : real) : (term119 x) = term1.
Proof. exact (TRANS (@lem1948107 x) (@lem1948108 x)). Qed.
Lemma lem1948110 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948111 (x : real) : (term120 x) = term104.
Proof. exact (MK_COMB (@lem1948110) (@lem1948109 x)). Qed.
Lemma lem1948112 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948113 (x : real) : (term118 x) = term105.
Proof. exact (MK_COMB (@lem1948111 x) (@lem1948112)). Qed.
Lemma lem1948114 (x : real) (h1 : term107 x) : term105.
Proof. exact (EQ_MP (@lem1948113 x) (@lem1948098 x h1)). Qed.
Lemma lem1948116 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948117 : term105 = term106.
Proof. exact (@lem1948116 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1948118 : term106 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1948119 : term105 = False.
Proof. exact (TRANS (@lem1948117) (@lem1948118)). Qed.
Lemma lem1948120 (x : real) (h1 : term107 x) : False.
Proof. exact (EQ_MP (@lem1948119) (@lem1948114 x h1)). Qed.
Lemma lem1948121 (x : real) (h1 : term68 x) : False.
Proof. exact (or_elim (@lem1947972 x h1) (fun h0 : term73 x => @lem1948046 x h0) (fun h0 : term107 x => @lem1948120 x h0)). Qed.
Lemma lem1948122 (x : real) (h1 : term65 x) : term65 x.
Proof. exact (h1). Qed.
Lemma lem1948123 (x : real) (h1 : term121 x) : term121 x.
Proof. exact (h1). Qed.
Lemma lem1948124 (x : real) (h1 : term121 x) : term45 x.
Proof. exact (proj2 (@lem1948123 x h1)). Qed.
Lemma lem1948125 (x : real) (h1 : term121 x) : term42 x.
Proof. exact (proj1 (@lem1948123 x h1)). Qed.
Lemma lem1948127 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948128 : term75 = term76.
Proof. exact (@lem1948127 (NUMERAL 0) term23). Qed.
Lemma lem1948129 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1948130 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1948131 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1948130 h1) (fun h1 : term76 = True => @lem1948129)). Qed.
Lemma lem1948132 : term76 = True.
Proof. exact (EQ_MP (@lem1948131) (@lem1948129)). Qed.
Lemma lem1948133 : term75 = True.
Proof. exact (TRANS (@lem1948128) (@lem1948132)). Qed.
Lemma lem1948134 : True = term75.
Proof. exact (SYM (@lem1948133)). Qed.
Lemma lem1948135 : term75.
Proof. exact (EQ_MP (@lem1948134) (@lem0)). Qed.
Lemma lem1948136 (x : real) (h1 : term121 x) : term85 x.
Proof. exact (conj (@lem1948135) (@lem1948124 x h1)). Qed.
Lemma lem1948138 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1948139 (x : real) : term87 x.
Proof. exact (@lem1948138 term81 x). Qed.
Lemma lem1948140 (x : real) (h1 : term121 x) : term88 x.
Proof. exact (@lem1948139 x (@lem1948136 x h1)). Qed.
Lemma lem1948141 (x : real) : (term89 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1948142 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948143 (x : real) : (term90 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1948142) (@lem1948141 x)). Qed.
Lemma lem1948144 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948145 (x : real) : (term88 x) = (term45 x).
Proof. exact (MK_COMB (@lem1948143 x) (@lem1948144)). Qed.
Lemma lem1948146 (x : real) (h1 : term121 x) : term45 x.
Proof. exact (EQ_MP (@lem1948145 x) (@lem1948140 x h1)). Qed.
Lemma lem1948148 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948149 : term75 = term76.
Proof. exact (@lem1948148 (NUMERAL 0) term23). Qed.
Lemma lem1948150 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1948151 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1948152 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1948151 h1) (fun h1 : term76 = True => @lem1948150)). Qed.
Lemma lem1948153 : term76 = True.
Proof. exact (EQ_MP (@lem1948152) (@lem1948150)). Qed.
Lemma lem1948154 : term75 = True.
Proof. exact (TRANS (@lem1948149) (@lem1948153)). Qed.
Lemma lem1948155 : True = term75.
Proof. exact (SYM (@lem1948154)). Qed.
Lemma lem1948156 : term75.
Proof. exact (EQ_MP (@lem1948155) (@lem0)). Qed.
Lemma lem1948157 (x : real) (h1 : term121 x) : term112 x.
Proof. exact (conj (@lem1948156) (@lem1948125 x h1)). Qed.
Lemma lem1948159 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1948160 (x : real) : term113 x.
Proof. exact (@lem1948159 term81 (term31 x)). Qed.
Lemma lem1948161 (x : real) (h1 : term121 x) : term114 x.
Proof. exact (@lem1948160 x (@lem1948157 x h1)). Qed.
Lemma lem1948162 (x : real) : (term83 x) = (term31 x).
Proof. exact (@lem1483460 (term31 x)). Qed.
Lemma lem1948163 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948164 (x : real) : (term115 x) = (term40 x).
Proof. exact (MK_COMB (@lem1948163) (@lem1948162 x)). Qed.
Lemma lem1948165 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948166 (x : real) : (term114 x) = (term42 x).
Proof. exact (MK_COMB (@lem1948164 x) (@lem1948165)). Qed.
Lemma lem1948167 (x : real) (h1 : term121 x) : term42 x.
Proof. exact (EQ_MP (@lem1948166 x) (@lem1948161 x h1)). Qed.
Lemma lem1948168 (x : real) (h1 : term121 x) : term121 x.
Proof. exact (conj (@lem1948167 x h1) (@lem1948146 x h1)). Qed.
Lemma lem1948170 (x : real) (y : real) : term122 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1948171 (x : real) : term123 x.
Proof. exact (@lem1948170 (term31 x) x). Qed.
Lemma lem1948172 (x : real) (h1 : term121 x) : term118 x.
Proof. exact (@lem1948171 x (@lem1948168 x h1)). Qed.
Lemma lem1948173 (x : real) : (term119 x) = (term96 x).
Proof. exact (@lem1483440 term97 x). Qed.
Lemma lem1948175 (m : nat) : (term98 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1948176 : term99 = term1.
Proof. exact (@lem1948175 term23). Qed.
Lemma lem1948177 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1948178 : term100 = term101.
Proof. exact (MK_COMB (@lem1948177) (@lem1948176)). Qed.
Lemma lem1948179 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1948180 (x : real) : (term96 x) = (term102 x).
Proof. exact (MK_COMB (@lem1948178) (@lem1948179 x)). Qed.
Lemma lem1948181 (x : real) : (term119 x) = (term102 x).
Proof. exact (TRANS (@lem1948173 x) (@lem1948180 x)). Qed.
Lemma lem1948182 (x : real) : (term102 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1948183 (x : real) : (term119 x) = term1.
Proof. exact (TRANS (@lem1948181 x) (@lem1948182 x)). Qed.
Lemma lem1948184 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948185 (x : real) : (term120 x) = term104.
Proof. exact (MK_COMB (@lem1948184) (@lem1948183 x)). Qed.
Lemma lem1948186 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948187 (x : real) : (term118 x) = term105.
Proof. exact (MK_COMB (@lem1948185 x) (@lem1948186)). Qed.
Lemma lem1948188 (x : real) (h1 : term121 x) : term105.
Proof. exact (EQ_MP (@lem1948187 x) (@lem1948172 x h1)). Qed.
Lemma lem1948190 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948191 : term105 = term106.
Proof. exact (@lem1948190 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1948192 : term106 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1948193 : term105 = False.
Proof. exact (TRANS (@lem1948191) (@lem1948192)). Qed.
Lemma lem1948194 (x : real) (h1 : term121 x) : False.
Proof. exact (EQ_MP (@lem1948193) (@lem1948188 x h1)). Qed.
Lemma lem1948195 (x : real) (h1 : term124 x) : term124 x.
Proof. exact (h1). Qed.
Lemma lem1948196 (x : real) (h1 : term124 x) : x = term1.
Proof. exact (proj2 (@lem1948195 x h1)). Qed.
Lemma lem1948197 (x : real) (h1 : term124 x) : term42 x.
Proof. exact (proj1 (@lem1948195 x h1)). Qed.
Lemma lem1948199 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948200 : term75 = term76.
Proof. exact (@lem1948199 (NUMERAL 0) term23). Qed.
Lemma lem1948201 : term77 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1948202 (h1 : term77 = (BIT1 0)) : term76 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1948203 : (term77 = (BIT1 0)) = (term76 = True).
Proof. exact (prop_ext (fun h1 : term77 = (BIT1 0) => @lem1948202 h1) (fun h1 : term76 = True => @lem1948201)). Qed.
Lemma lem1948204 : term76 = True.
Proof. exact (EQ_MP (@lem1948203) (@lem1948201)). Qed.
Lemma lem1948205 : term75 = True.
Proof. exact (TRANS (@lem1948200) (@lem1948204)). Qed.
Lemma lem1948206 : True = term75.
Proof. exact (SYM (@lem1948205)). Qed.
Lemma lem1948207 : term75.
Proof. exact (EQ_MP (@lem1948206) (@lem0)). Qed.
Lemma lem1948208 (x : real) (h1 : term124 x) : term112 x.
Proof. exact (conj (@lem1948207) (@lem1948197 x h1)). Qed.
Lemma lem1948210 (x : real) (y : real) : term86 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1948211 (x : real) : term113 x.
Proof. exact (@lem1948210 term81 (term31 x)). Qed.
Lemma lem1948212 (x : real) (h1 : term124 x) : term114 x.
Proof. exact (@lem1948211 x (@lem1948208 x h1)). Qed.
Lemma lem1948213 (x : real) : (term83 x) = (term31 x).
Proof. exact (@lem1483460 (term31 x)). Qed.
Lemma lem1948214 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948215 (x : real) : (term115 x) = (term40 x).
Proof. exact (MK_COMB (@lem1948214) (@lem1948213 x)). Qed.
Lemma lem1948216 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948217 (x : real) : (term114 x) = (term42 x).
Proof. exact (MK_COMB (@lem1948215 x) (@lem1948216)). Qed.
Lemma lem1948218 (x : real) (h1 : term124 x) : term42 x.
Proof. exact (EQ_MP (@lem1948217 x) (@lem1948212 x h1)). Qed.
Lemma lem1948220 (y : real) : term125 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1948221 (x : real) : term125 x.
Proof. exact (@lem1948220 x). Qed.
Lemma lem1948222 (x : real) (h1 : term124 x) : term126 x.
Proof. exact (@lem1948221 x (@lem1948196 x h1)). Qed.
Lemma lem1948223 (x : real) (h1 : term124 x) : term127 x.
Proof. exact (@lem1948222 x h1 term81). Qed.
Lemma lem1948224 (x : real) : (term127 x) = ((term89 x) = term1).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem1948225 (x : real) (h1 : term124 x) : (term89 x) = term1.
Proof. exact (EQ_MP (@lem1948224 x) (@lem1948223 x h1)). Qed.
Lemma lem1948226 (x : real) : (term89 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1948227 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1948228 (x : real) : (term128 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1948227) (@lem1948226 x)). Qed.
Lemma lem1948229 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948230 (x : real) : ((term89 x) = term1) = (x = term1).
Proof. exact (MK_COMB (@lem1948228 x) (@lem1948229)). Qed.
Lemma lem1948231 (x : real) (h1 : term124 x) : x = term1.
Proof. exact (EQ_MP (@lem1948230 x) (@lem1948225 x h1)). Qed.
Lemma lem1948232 (x : real) (h1 : term124 x) : term129 x.
Proof. exact (conj (@lem1948231 x h1) (@lem1948218 x h1)). Qed.
Lemma lem1948234 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1948235 (x : real) : term131 x.
Proof. exact (@lem1948234 x (term31 x)). Qed.
Lemma lem1948236 (x : real) (h1 : term124 x) : term94 x.
Proof. exact (@lem1948235 x (@lem1948232 x h1)). Qed.
Lemma lem1948237 (x : real) : (term95 x) = (term96 x).
Proof. exact (@lem1483442 term97 x). Qed.
Lemma lem1948239 (m : nat) : (term98 m) = term1.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1948240 : term99 = term1.
Proof. exact (@lem1948239 term23). Qed.
Lemma lem1948241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1948242 : term100 = term101.
Proof. exact (MK_COMB (@lem1948241) (@lem1948240)). Qed.
Lemma lem1948243 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1948244 (x : real) : (term96 x) = (term102 x).
Proof. exact (MK_COMB (@lem1948242) (@lem1948243 x)). Qed.
Lemma lem1948245 (x : real) : (term95 x) = (term102 x).
Proof. exact (TRANS (@lem1948237 x) (@lem1948244 x)). Qed.
Lemma lem1948246 (x : real) : (term102 x) = term1.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1948247 (x : real) : (term95 x) = term1.
Proof. exact (TRANS (@lem1948245 x) (@lem1948246 x)). Qed.
Lemma lem1948248 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948249 (x : real) : (term103 x) = term104.
Proof. exact (MK_COMB (@lem1948248) (@lem1948247 x)). Qed.
Lemma lem1948250 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1948251 (x : real) : (term94 x) = term105.
Proof. exact (MK_COMB (@lem1948249 x) (@lem1948250)). Qed.
Lemma lem1948252 (x : real) (h1 : term124 x) : term105.
Proof. exact (EQ_MP (@lem1948251 x) (@lem1948236 x h1)). Qed.
Lemma lem1948254 (n : nat) (m : nat) : (term74 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1948255 : term105 = term106.
Proof. exact (@lem1948254 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1948256 : term106 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1948257 : term105 = False.
Proof. exact (TRANS (@lem1948255) (@lem1948256)). Qed.
Lemma lem1948258 (x : real) (h1 : term124 x) : False.
Proof. exact (EQ_MP (@lem1948257) (@lem1948252 x h1)). Qed.
Lemma lem1948259 (x : real) (h1 : term65 x) : False.
Proof. exact (or_elim (@lem1948122 x h1) (fun h0 : term121 x => @lem1948194 x h0) (fun h0 : term124 x => @lem1948258 x h0)). Qed.
Lemma lem1948260 (x : real) (h1 : term72 x) : False.
Proof. exact (or_elim (@lem1947971 x h1) (fun h0 : term68 x => @lem1948121 x h0) (fun h0 : term65 x => @lem1948259 x h0)). Qed.
Lemma lem1948262 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1948263 (x : real) (h1 : term72 x) : (term72 x) = False.
Proof. exact (prop_ext (fun h2 : term72 x => @lem1948260 x h1) (fun h2 : False => @lem1948262 x h1)). Qed.
Lemma lem1948264 (x : real) (h1 : term72 x) : False.
Proof. exact (EQ_MP (@lem1948263 x h1) (@lem1948262 x h1)). Qed.
Lemma lem1948265 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1948266 (x : real) (h1 : term15 x) : term72 x.
Proof. exact (EQ_MP (@lem1947949 x) (@lem1948265 x h1)). Qed.
Lemma lem1948267 (x : real) (h1 : term15 x) : (term72 x) = False.
Proof. exact (prop_ext (fun h2 : term72 x => @lem1948264 x h2) (fun h2 : False => @lem1948266 x h1)). Qed.
Lemma lem1948268 (x : real) (h1 : term15 x) : False.
Proof. exact (EQ_MP (@lem1948267 x h1) (@lem1948266 x h1)). Qed.
Lemma lem1948269 (x : real) : term132 x.
Proof. exact (fun h0 : term15 x => @lem1948268 x h0). Qed.
Lemma lem1948270 (x : real) : term133 x.
Proof. exact (@lem1386578 ((term16 x) = (term17 x))). Qed.
Lemma lem1948279 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1948270 x (@lem1948269 x)). Qed.
Lemma lem1948280 (x : real) : (term134 x) = (term135 x).
Proof. exact (@lem1948279 (sqrt x)). Qed.
Lemma lem1948285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1948286 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1948285) (@lem1948280 x)). Qed.
Lemma lem1948288 (x : real) : (term16 x) = (term17 x).
Proof. exact (@lem1948270 x (@lem1948269 x)). Qed.
Lemma lem1948293 (x : real) : ((term134 x) = (term16 x)) = ((term135 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1948286 x) (@lem1948288 x)). Qed.
Lemma lem1948296 : term138 = term139.
Proof. exact (fun_ext (fun x : real => @lem1948293 x)). Qed.
Lemma lem1948297 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1948298 : term140 = term141.
Proof. exact (MK_COMB (@lem1948297) (@lem1948296)). Qed.
Lemma lem1948303 : term141 = term140.
Proof. exact (SYM (@lem1948298)). Qed.
Lemma lem1948313 (x : real) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem1947680 x) (@lem1947679 x)). Qed.
Lemma lem1948314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1948315 (x : real) : (term142 x) = (term58 x).
Proof. exact (MK_COMB (@lem1948314) (@lem1948313 x)). Qed.
Lemma lem1948317 (x : real) : ((sqrt x) = term1) = (x = term1).
Proof. exact (EQ_MP (@lem1947677 x) (@lem1947676 x)). Qed.
Lemma lem1948320 (x : real) : (term135 x) = (term17 x).
Proof. exact (MK_COMB (@lem1948315 x) (@lem1948317 x)). Qed.
Lemma lem1948323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1948324 (x : real) : (term137 x) = (term143 x).
Proof. exact (MK_COMB (@lem1948323) (@lem1948320 x)). Qed.
Lemma lem1948329 (x : real) : (term17 x) = (term17 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1948330 (x : real) : ((term135 x) = (term17 x)) = ((term17 x) = (term17 x)).
Proof. exact (MK_COMB (@lem1948324 x) (@lem1948329 x)). Qed.
Lemma lem1948332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1948333 (x : Prop) : (x = x) = True.
Proof. exact (@lem1948332 Prop x). Qed.
Lemma lem1948334 (x : real) : ((term17 x) = (term17 x)) = True.
Proof. exact (@lem1948333 (term17 x)). Qed.
Lemma lem1948335 (x : real) : ((term135 x) = (term17 x)) = True.
Proof. exact (TRANS (@lem1948330 x) (@lem1948334 x)). Qed.
Lemma lem1948336 : term139 = term144.
Proof. exact (fun_ext (fun x : real => @lem1948335 x)). Qed.
Lemma lem1948337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1948338 : term141 = term145.
Proof. exact (MK_COMB (@lem1948337) (@lem1948336)). Qed.
Lemma lem1948340 {A : Type'} (t : Prop) : (term146 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1948341 (t : Prop) : (term147 t) = t.
Proof. exact (@lem1948340 real t). Qed.
Lemma lem1948342 : term145 = True.
Proof. exact (@lem1948341 True). Qed.
Lemma lem1948343 : term141 = True.
Proof. exact (TRANS (@lem1948338) (@lem1948342)). Qed.
Lemma lem1948344 : True = term141.
Proof. exact (SYM (@lem1948343)). Qed.
Lemma lem1948345 : term141.
Proof. exact (EQ_MP (@lem1948344) (@lem0)). Qed.
Lemma lem1948346 : term140.
Proof. exact (EQ_MP (@lem1948303) (@lem1948345)). Qed.
