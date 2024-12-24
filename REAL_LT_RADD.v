Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_RADD_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1492722 (z : real) (x : real) (y : real) : (term0 z x y) = (term1 z x y).
Proof. exact (@lem17646 (term2 x y z) (real_lt x y)). Qed.
Lemma lem1492723 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1492724 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (@lem1492723 (term7 x y)). Qed.
Lemma lem1492725 (z : real) (x : real) (y : real) : (term8 x y z) = ((term2 x y z) = (real_lt x y)).
Proof. exact (eq_refl (term8 x y z)). Qed.
Lemma lem1492726 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1492727 (z : real) (x : real) (y : real) : (term9 x y z) = (term0 z x y).
Proof. exact (MK_COMB (@lem1492726) (@lem1492725 z x y)). Qed.
Lemma lem1492728 (z : real) (x : real) (y : real) : (term9 x y z) = (term1 z x y).
Proof. exact (TRANS (@lem1492727 z x y) (@lem1492722 z x y)). Qed.
Lemma lem1492729 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1492728 z x y)). Qed.
Lemma lem1492730 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492731 (x : real) (y : real) : (term6 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1492730) (@lem1492729 x y)). Qed.
Lemma lem1492732 (x : real) (y : real) : (term5 x y) = (term12 x y).
Proof. exact (TRANS (@lem1492724 x y) (@lem1492731 x y)). Qed.
Lemma lem1492733 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1492734 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1492733 (term15 x)). Qed.
Lemma lem1492735 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1492736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1492737 (x : real) (y : real) : (term18 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1492736) (@lem1492735 x y)). Qed.
Lemma lem1492738 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1492737 x y) (@lem1492732 x y)). Qed.
Lemma lem1492739 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1492738 x y)). Qed.
Lemma lem1492740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492741 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1492740) (@lem1492739 x)). Qed.
Lemma lem1492742 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1492734 x) (@lem1492741 x)). Qed.
Lemma lem1492743 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1492744 : term22 = term23.
Proof. exact (@lem1492743 term24). Qed.
Lemma lem1492745 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1492746 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1492747 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1492746) (@lem1492745 x)). Qed.
Lemma lem1492748 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1492747 x) (@lem1492742 x)). Qed.
Lemma lem1492749 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1492748 x)). Qed.
Lemma lem1492750 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492751 : term23 = term30.
Proof. exact (MK_COMB (@lem1492750) (@lem1492749)). Qed.
Lemma lem1492753 : term22 = term30.
Proof. exact (TRANS (@lem1492744) (@lem1492751)). Qed.
Lemma lem1492770 (z : real) (x : real) (y : real) : (term1 z x y) = (term1 z x y).
Proof. exact (eq_refl (term1 z x y)). Qed.
Lemma lem1492771 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1492770 z x y)). Qed.
Lemma lem1492772 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492773 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1492772) (@lem1492771 x y)). Qed.
Lemma lem1492774 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1492773 x y)). Qed.
Lemma lem1492775 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492776 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1492775) (@lem1492774 x)). Qed.
Lemma lem1492777 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1492776 x)). Qed.
Lemma lem1492778 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492779 : term30 = term30.
Proof. exact (MK_COMB (@lem1492778) (@lem1492777)). Qed.
Lemma lem1492780 : term22 = term30.
Proof. exact (TRANS (@lem1492753) (@lem1492779)). Qed.
Lemma lem1492781 (y : real) (x : real) (z : real) : (term2 x y z) = (term31 y x z).
Proof. exact (@lem1483521 (real_add y z) (real_add x z)). Qed.
Lemma lem1492799 (y : real) (x : real) (z : real) : (term32 y x z) = (term33 y x z).
Proof. exact (@lem1483519 (real_add y z) (real_add x z)). Qed.
Lemma lem1492806 (x : real) (z : real) : (term34 x z) = (term35 x z).
Proof. exact (@lem1483508 x term36 z). Qed.
Lemma lem1492807 (y : real) (z : real) : (term37 y z) = (term37 y z).
Proof. exact (eq_refl (term37 y z)). Qed.
Lemma lem1492808 (y : real) (x : real) (z : real) : (term33 y x z) = (term38 y x z).
Proof. exact (MK_COMB (@lem1492807 y z) (@lem1492806 x z)). Qed.
Lemma lem1492809 (x : real) (y : real) (z : real) : (term38 y x z) = (term39 x y z).
Proof. exact (@lem1483484 (term40 x) (real_add y z) (term40 z)). Qed.
Lemma lem1492810 (y : real) (z : real) : (term41 y z) = (term42 y z).
Proof. exact (@lem1483482 y z (term40 z)). Qed.
Lemma lem1492811 (z : real) : (term43 z) = (term44 z).
Proof. exact (@lem1483442 term36 z). Qed.
Lemma lem1492813 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492814 : term47 = term46.
Proof. exact (@lem1492813 term48). Qed.
Lemma lem1492815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492816 : term49 = term50.
Proof. exact (MK_COMB (@lem1492815) (@lem1492814)). Qed.
Lemma lem1492817 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1492818 (z : real) : (term44 z) = (term51 z).
Proof. exact (MK_COMB (@lem1492816) (@lem1492817 z)). Qed.
Lemma lem1492819 (z : real) : (term43 z) = (term51 z).
Proof. exact (TRANS (@lem1492811 z) (@lem1492818 z)). Qed.
Lemma lem1492820 (z : real) : (term51 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1492821 (z : real) : (term43 z) = term46.
Proof. exact (TRANS (@lem1492819 z) (@lem1492820 z)). Qed.
Lemma lem1492822 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1492823 (z : real) (y : real) : (term42 y z) = (term52 y).
Proof. exact (MK_COMB (@lem1492822 y) (@lem1492821 z)). Qed.
Lemma lem1492824 (z : real) (y : real) : (term41 y z) = (term52 y).
Proof. exact (TRANS (@lem1492810 y z) (@lem1492823 z y)). Qed.
Lemma lem1492825 (y : real) : (term52 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1492826 (z : real) (y : real) : (term41 y z) = y.
Proof. exact (TRANS (@lem1492824 z y) (@lem1492825 y)). Qed.
Lemma lem1492827 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1492828 (z : real) (x : real) (y : real) : (term39 x y z) = (term54 x y).
Proof. exact (MK_COMB (@lem1492827 x) (@lem1492826 z y)). Qed.
Lemma lem1492829 (z : real) (x : real) (y : real) : (term38 y x z) = (term54 x y).
Proof. exact (TRANS (@lem1492809 x y z) (@lem1492828 z x y)). Qed.
Lemma lem1492830 (z : real) (x : real) (y : real) : (term33 y x z) = (term54 x y).
Proof. exact (TRANS (@lem1492808 y x z) (@lem1492829 z x y)). Qed.
Lemma lem1492832 (z : real) (x : real) (y : real) : (term32 y x z) = (term54 x y).
Proof. exact (TRANS (@lem1492799 y x z) (@lem1492830 z x y)). Qed.
Lemma lem1492833 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492834 (z : real) (x : real) (y : real) : (term55 y x z) = (term56 x y).
Proof. exact (MK_COMB (@lem1492833) (@lem1492832 z x y)). Qed.
Lemma lem1492835 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1492836 (z : real) (x : real) (y : real) : (term31 y x z) = (term57 x y).
Proof. exact (MK_COMB (@lem1492834 z x y) (@lem1492835)). Qed.
Lemma lem1492837 (z : real) (x : real) (y : real) : (term2 x y z) = (term57 x y).
Proof. exact (TRANS (@lem1492781 y x z) (@lem1492836 z x y)). Qed.
Lemma lem1492838 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1483531 x y). Qed.
Lemma lem1492851 (x : real) (y : real) : (real_sub x y) = (term60 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1492852 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1492853 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1492852) (@lem1492851 x y)). Qed.
Lemma lem1492854 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1492855 (x : real) (y : real) : (term59 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1492853 x y) (@lem1492854)). Qed.
Lemma lem1492856 (x : real) (y : real) : (term58 x y) = (term63 x y).
Proof. exact (TRANS (@lem1492838 x y) (@lem1492855 x y)). Qed.
Lemma lem1492857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1492858 (z : real) (x : real) (y : real) : (term64 x y z) = (term65 x y).
Proof. exact (MK_COMB (@lem1492857) (@lem1492837 z x y)). Qed.
Lemma lem1492859 (z : real) (x : real) (y : real) : (term66 z x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1492858 z x y) (@lem1492856 x y)). Qed.
Lemma lem1492860 (x : real) (y : real) (z : real) : (term68 x y z) = (term69 x y z).
Proof. exact (@lem1483531 (real_add x z) (real_add y z)). Qed.
Lemma lem1492878 (x : real) (y : real) (z : real) : (term32 x y z) = (term33 x y z).
Proof. exact (@lem1483519 (real_add x z) (real_add y z)). Qed.
Lemma lem1492885 (y : real) (z : real) : (term34 y z) = (term35 y z).
Proof. exact (@lem1483508 y term36 z). Qed.
Lemma lem1492886 (x : real) (z : real) : (term37 x z) = (term37 x z).
Proof. exact (eq_refl (term37 x z)). Qed.
Lemma lem1492887 (x : real) (y : real) (z : real) : (term33 x y z) = (term38 x y z).
Proof. exact (MK_COMB (@lem1492886 x z) (@lem1492885 y z)). Qed.
Lemma lem1492888 (x : real) (y : real) (z : real) : (term38 x y z) = (term70 x y z).
Proof. exact (@lem1483482 x z (term35 y z)). Qed.
Lemma lem1492889 (y : real) (z : real) : (term71 y z) = (term72 y z).
Proof. exact (@lem1483484 (term40 y) z (term40 z)). Qed.
Lemma lem1492890 (z : real) : (term43 z) = (term44 z).
Proof. exact (@lem1483442 term36 z). Qed.
Lemma lem1492892 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492893 : term47 = term46.
Proof. exact (@lem1492892 term48). Qed.
Lemma lem1492894 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492895 : term49 = term50.
Proof. exact (MK_COMB (@lem1492894) (@lem1492893)). Qed.
Lemma lem1492896 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1492897 (z : real) : (term44 z) = (term51 z).
Proof. exact (MK_COMB (@lem1492895) (@lem1492896 z)). Qed.
Lemma lem1492898 (z : real) : (term43 z) = (term51 z).
Proof. exact (TRANS (@lem1492890 z) (@lem1492897 z)). Qed.
Lemma lem1492899 (z : real) : (term51 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1492900 (z : real) : (term43 z) = term46.
Proof. exact (TRANS (@lem1492898 z) (@lem1492899 z)). Qed.
Lemma lem1492901 (y : real) : (term53 y) = (term53 y).
Proof. exact (eq_refl (term53 y)). Qed.
Lemma lem1492902 (z : real) (y : real) : (term72 y z) = (term73 y).
Proof. exact (MK_COMB (@lem1492901 y) (@lem1492900 z)). Qed.
Lemma lem1492903 (z : real) (y : real) : (term71 y z) = (term73 y).
Proof. exact (TRANS (@lem1492889 y z) (@lem1492902 z y)). Qed.
Lemma lem1492904 (y : real) : (term73 y) = (term40 y).
Proof. exact (@lem1483450 (term40 y)). Qed.
Lemma lem1492905 (z : real) (y : real) : (term71 y z) = (term40 y).
Proof. exact (TRANS (@lem1492903 z y) (@lem1492904 y)). Qed.
Lemma lem1492906 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1492907 (z : real) (x : real) (y : real) : (term70 x y z) = (term60 x y).
Proof. exact (MK_COMB (@lem1492906 x) (@lem1492905 z y)). Qed.
Lemma lem1492908 (z : real) (x : real) (y : real) : (term38 x y z) = (term60 x y).
Proof. exact (TRANS (@lem1492888 x y z) (@lem1492907 z x y)). Qed.
Lemma lem1492909 (z : real) (x : real) (y : real) : (term33 x y z) = (term60 x y).
Proof. exact (TRANS (@lem1492887 x y z) (@lem1492908 z x y)). Qed.
Lemma lem1492911 (z : real) (x : real) (y : real) : (term32 x y z) = (term60 x y).
Proof. exact (TRANS (@lem1492878 x y z) (@lem1492909 z x y)). Qed.
Lemma lem1492912 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1492913 (z : real) (x : real) (y : real) : (term74 x y z) = (term62 x y).
Proof. exact (MK_COMB (@lem1492912) (@lem1492911 z x y)). Qed.
Lemma lem1492914 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1492915 (z : real) (x : real) (y : real) : (term69 x y z) = (term63 x y).
Proof. exact (MK_COMB (@lem1492913 z x y) (@lem1492914)). Qed.
Lemma lem1492916 (z : real) (x : real) (y : real) : (term68 x y z) = (term63 x y).
Proof. exact (TRANS (@lem1492860 x y z) (@lem1492915 z x y)). Qed.
Lemma lem1492917 (y : real) (x : real) : (real_lt x y) = (term75 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1492923 (y : real) (x : real) : (real_sub y x) = (term60 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1492928 (x : real) (y : real) : (term60 y x) = (term54 x y).
Proof. exact (@lem1483488 (term40 x) y). Qed.
Lemma lem1492930 (x : real) (y : real) : (real_sub y x) = (term54 x y).
Proof. exact (TRANS (@lem1492923 y x) (@lem1492928 x y)). Qed.
Lemma lem1492931 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492932 (x : real) (y : real) : (term76 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1492931) (@lem1492930 x y)). Qed.
Lemma lem1492933 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1492934 (x : real) (y : real) : (term75 y x) = (term57 x y).
Proof. exact (MK_COMB (@lem1492932 x y) (@lem1492933)). Qed.
Lemma lem1492935 (x : real) (y : real) : (real_lt x y) = (term57 x y).
Proof. exact (TRANS (@lem1492917 y x) (@lem1492934 x y)). Qed.
Lemma lem1492936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1492937 (z : real) (x : real) (y : real) : (term77 x y z) = (term78 x y).
Proof. exact (MK_COMB (@lem1492936) (@lem1492916 z x y)). Qed.
Lemma lem1492938 (z : real) (x : real) (y : real) : (term79 z x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1492937 z x y) (@lem1492935 x y)). Qed.
Lemma lem1492939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492940 (z : real) (x : real) (y : real) : (term81 z x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1492939) (@lem1492859 z x y)). Qed.
Lemma lem1492941 (z : real) (x : real) (y : real) : (term1 z x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1492940 z x y) (@lem1492938 z x y)). Qed.
Lemma lem1492942 (x : real) (y : real) : (term11 x y) = (term84 x y).
Proof. exact (fun_ext (fun z : real => @lem1492941 z x y)). Qed.
Lemma lem1492943 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492944 (x : real) (y : real) : (term12 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1492943) (@lem1492942 x y)). Qed.
Lemma lem1492945 (x : real) : (term20 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1492944 x y)). Qed.
Lemma lem1492946 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492947 (x : real) : (term21 x) = (term87 x).
Proof. exact (MK_COMB (@lem1492946) (@lem1492945 x)). Qed.
Lemma lem1492948 : term29 = term88.
Proof. exact (fun_ext (fun x : real => @lem1492947 x)). Qed.
Lemma lem1492949 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492950 : term30 = term89.
Proof. exact (MK_COMB (@lem1492949) (@lem1492948)). Qed.
Lemma lem1492951 : term22 = term89.
Proof. exact (TRANS (@lem1492780) (@lem1492950)). Qed.
Lemma lem1492961 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1492962 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1492961 real P Q). Qed.
Lemma lem1492963 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (@lem1492962 (term96 x y) (term97 x y)). Qed.
Lemma lem1492964 (z : real) (x : real) (y : real) : (term98 x y z) = (term67 x y).
Proof. exact (eq_refl (term98 x y z)). Qed.
Lemma lem1492965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492966 (z : real) (x : real) (y : real) : (term99 x y z) = (term82 x y).
Proof. exact (MK_COMB (@lem1492965) (@lem1492964 z x y)). Qed.
Lemma lem1492967 (z : real) (x : real) (y : real) : (term100 x y z) = (term80 x y).
Proof. exact (eq_refl (term100 x y z)). Qed.
Lemma lem1492968 (z : real) (x : real) (y : real) : (term101 x y z) = (term83 x y).
Proof. exact (MK_COMB (@lem1492966 z x y) (@lem1492967 z x y)). Qed.
Lemma lem1492969 (x : real) (y : real) : (term102 x y) = (term84 x y).
Proof. exact (fun_ext (fun z : real => @lem1492968 z x y)). Qed.
Lemma lem1492970 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492971 (x : real) (y : real) : (term94 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1492970) (@lem1492969 x y)). Qed.
Lemma lem1492972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1492973 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1492972) (@lem1492971 x y)). Qed.
Lemma lem1492974 (z : real) (x : real) (y : real) : (term98 x y z) = (term67 x y).
Proof. exact (eq_refl (term98 x y z)). Qed.
Lemma lem1492975 (x : real) (y : real) : (term105 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1492974 z x y)). Qed.
Lemma lem1492976 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492977 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1492976) (@lem1492975 x y)). Qed.
Lemma lem1492978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492979 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1492978) (@lem1492977 x y)). Qed.
Lemma lem1492980 (z : real) (x : real) (y : real) : (term100 x y z) = (term80 x y).
Proof. exact (eq_refl (term100 x y z)). Qed.
Lemma lem1492981 (x : real) (y : real) : (term110 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1492980 z x y)). Qed.
Lemma lem1492982 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492983 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1492982) (@lem1492981 x y)). Qed.
Lemma lem1492984 (x : real) (y : real) : (term95 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1492979 x y) (@lem1492983 x y)). Qed.
Lemma lem1492985 (x : real) (y : real) : ((term94 x y) = (term95 x y)) = ((term85 x y) = (term113 x y)).
Proof. exact (MK_COMB (@lem1492973 x y) (@lem1492984 x y)). Qed.
Lemma lem1492986 (x : real) (y : real) : (term85 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem1492985 x y) (@lem1492963 x y)). Qed.
Lemma lem1492988 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1492989 (P : Prop) (Q : real -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem1492988 real P Q). Qed.
Lemma lem1492990 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (@lem1492989 (term57 x y) (term120 x y)). Qed.
Lemma lem1492991 (z : real) (x : real) (y : real) : (term121 x y z) = (term63 x y).
Proof. exact (eq_refl (term121 x y z)). Qed.
Lemma lem1492992 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1492993 (z : real) (x : real) (y : real) : (term122 x y z) = (term67 x y).
Proof. exact (MK_COMB (@lem1492992 x y) (@lem1492991 z x y)). Qed.
Lemma lem1492994 (x : real) (y : real) : (term123 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1492993 z x y)). Qed.
Lemma lem1492995 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492996 (x : real) (y : real) : (term118 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1492995) (@lem1492994 x y)). Qed.
Lemma lem1492997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1492998 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1492997) (@lem1492996 x y)). Qed.
Lemma lem1492999 (z : real) (x : real) (y : real) : (term121 x y z) = (term63 x y).
Proof. exact (eq_refl (term121 x y z)). Qed.
Lemma lem1493000 (x : real) (y : real) : (term126 x y) = (term120 x y).
Proof. exact (fun_ext (fun z : real => @lem1492999 z x y)). Qed.
Lemma lem1493001 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493002 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1493001) (@lem1493000 x y)). Qed.
Lemma lem1493003 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1493004 (x : real) (y : real) : (term119 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1493003 x y) (@lem1493002 x y)). Qed.
Lemma lem1493005 (x : real) (y : real) : ((term118 x y) = (term119 x y)) = ((term107 x y) = (term129 x y)).
Proof. exact (MK_COMB (@lem1492998 x y) (@lem1493004 x y)). Qed.
Lemma lem1493006 (x : real) (y : real) : (term107 x y) = (term129 x y).
Proof. exact (EQ_MP (@lem1493005 x y) (@lem1492990 x y)). Qed.
Lemma lem1493008 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1493009 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1493008 real t). Qed.
Lemma lem1493010 (x : real) (y : real) : (term128 x y) = (term63 x y).
Proof. exact (@lem1493009 (term63 x y)). Qed.
Lemma lem1493011 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1493012 (x : real) (y : real) : (term129 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1493011 x y) (@lem1493010 x y)). Qed.
Lemma lem1493013 (x : real) (y : real) : (term107 x y) = (term67 x y).
Proof. exact (TRANS (@lem1493006 x y) (@lem1493012 x y)). Qed.
Lemma lem1493014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493015 (x : real) (y : real) : (term109 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1493014) (@lem1493013 x y)). Qed.
Lemma lem1493017 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1493018 (P : Prop) (Q : real -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem1493017 real P Q). Qed.
Lemma lem1493019 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (@lem1493018 (term63 x y) (term134 x y)). Qed.
Lemma lem1493020 (z : real) (x : real) (y : real) : (term135 x y z) = (term57 x y).
Proof. exact (eq_refl (term135 x y z)). Qed.
Lemma lem1493021 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1493022 (z : real) (x : real) (y : real) : (term136 x y z) = (term80 x y).
Proof. exact (MK_COMB (@lem1493021 x y) (@lem1493020 z x y)). Qed.
Lemma lem1493023 (x : real) (y : real) : (term137 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1493022 z x y)). Qed.
Lemma lem1493024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493025 (x : real) (y : real) : (term132 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1493024) (@lem1493023 x y)). Qed.
Lemma lem1493026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1493027 (x : real) (y : real) : (term138 x y) = (term139 x y).
Proof. exact (MK_COMB (@lem1493026) (@lem1493025 x y)). Qed.
Lemma lem1493028 (z : real) (x : real) (y : real) : (term135 x y z) = (term57 x y).
Proof. exact (eq_refl (term135 x y z)). Qed.
Lemma lem1493029 (x : real) (y : real) : (term140 x y) = (term134 x y).
Proof. exact (fun_ext (fun z : real => @lem1493028 z x y)). Qed.
Lemma lem1493030 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493031 (x : real) (y : real) : (term141 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem1493030) (@lem1493029 x y)). Qed.
Lemma lem1493032 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1493033 (x : real) (y : real) : (term133 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1493032 x y) (@lem1493031 x y)). Qed.
Lemma lem1493034 (x : real) (y : real) : ((term132 x y) = (term133 x y)) = ((term112 x y) = (term143 x y)).
Proof. exact (MK_COMB (@lem1493027 x y) (@lem1493033 x y)). Qed.
Lemma lem1493035 (x : real) (y : real) : (term112 x y) = (term143 x y).
Proof. exact (EQ_MP (@lem1493034 x y) (@lem1493019 x y)). Qed.
Lemma lem1493037 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1493038 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1493037 real t). Qed.
Lemma lem1493039 (x : real) (y : real) : (term142 x y) = (term57 x y).
Proof. exact (@lem1493038 (term57 x y)). Qed.
Lemma lem1493040 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1493041 (x : real) (y : real) : (term143 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1493040 x y) (@lem1493039 x y)). Qed.
Lemma lem1493042 (x : real) (y : real) : (term112 x y) = (term80 x y).
Proof. exact (TRANS (@lem1493035 x y) (@lem1493041 x y)). Qed.
Lemma lem1493043 (x : real) (y : real) : (term113 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1493015 x y) (@lem1493042 x y)). Qed.
Lemma lem1493044 (x : real) (y : real) : (term85 x y) = (term83 x y).
Proof. exact (TRANS (@lem1492986 x y) (@lem1493043 x y)). Qed.
Lemma lem1493045 (x : real) : (term86 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1493044 x y)). Qed.
Lemma lem1493046 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493047 (x : real) : (term87 x) = (term145 x).
Proof. exact (MK_COMB (@lem1493046) (@lem1493045 x)). Qed.
Lemma lem1493049 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1493050 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1493049 real P Q). Qed.
Lemma lem1493051 (x : real) : (term146 x) = (term147 x).
Proof. exact (@lem1493050 (term148 x) (term149 x)). Qed.
Lemma lem1493052 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1493053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493054 (x : real) (y : real) : (term151 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1493053) (@lem1493052 x y)). Qed.
Lemma lem1493055 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1493056 (x : real) (y : real) : (term153 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1493054 x y) (@lem1493055 x y)). Qed.
Lemma lem1493057 (x : real) : (term154 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1493056 x y)). Qed.
Lemma lem1493058 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493059 (x : real) : (term146 x) = (term145 x).
Proof. exact (MK_COMB (@lem1493058) (@lem1493057 x)). Qed.
Lemma lem1493060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1493061 (x : real) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem1493060) (@lem1493059 x)). Qed.
Lemma lem1493062 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1493063 (x : real) : (term157 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1493062 x y)). Qed.
Lemma lem1493064 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493065 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1493064) (@lem1493063 x)). Qed.
Lemma lem1493066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493067 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1493066) (@lem1493065 x)). Qed.
Lemma lem1493068 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1493069 (x : real) : (term162 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem1493068 x y)). Qed.
Lemma lem1493070 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493071 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1493070) (@lem1493069 x)). Qed.
Lemma lem1493072 (x : real) : (term147 x) = (term165 x).
Proof. exact (MK_COMB (@lem1493067 x) (@lem1493071 x)). Qed.
Lemma lem1493073 (x : real) : ((term146 x) = (term147 x)) = ((term145 x) = (term165 x)).
Proof. exact (MK_COMB (@lem1493061 x) (@lem1493072 x)). Qed.
Lemma lem1493074 (x : real) : (term145 x) = (term165 x).
Proof. exact (EQ_MP (@lem1493073 x) (@lem1493051 x)). Qed.
Lemma lem1493171 (x : real) : (term87 x) = (term165 x).
Proof. exact (TRANS (@lem1493047 x) (@lem1493074 x)). Qed.
Lemma lem1493172 : term88 = term166.
Proof. exact (fun_ext (fun x : real => @lem1493171 x)). Qed.
Lemma lem1493173 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493174 : term89 = term167.
Proof. exact (MK_COMB (@lem1493173) (@lem1493172)). Qed.
Lemma lem1493176 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1493177 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1493176 real P Q). Qed.
Lemma lem1493178 : term168 = term169.
Proof. exact (@lem1493177 term170 term171). Qed.
Lemma lem1493179 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1493180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493181 (x : real) : (term173 x) = (term161 x).
Proof. exact (MK_COMB (@lem1493180) (@lem1493179 x)). Qed.
Lemma lem1493182 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1493183 (x : real) : (term175 x) = (term165 x).
Proof. exact (MK_COMB (@lem1493181 x) (@lem1493182 x)). Qed.
Lemma lem1493184 : term176 = term166.
Proof. exact (fun_ext (fun x : real => @lem1493183 x)). Qed.
Lemma lem1493185 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493186 : term168 = term167.
Proof. exact (MK_COMB (@lem1493185) (@lem1493184)). Qed.
Lemma lem1493187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1493188 : term177 = term178.
Proof. exact (MK_COMB (@lem1493187) (@lem1493186)). Qed.
Lemma lem1493189 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1493190 : term179 = term170.
Proof. exact (fun_ext (fun x : real => @lem1493189 x)). Qed.
Lemma lem1493191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493192 : term180 = term181.
Proof. exact (MK_COMB (@lem1493191) (@lem1493190)). Qed.
Lemma lem1493193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493194 : term182 = term183.
Proof. exact (MK_COMB (@lem1493193) (@lem1493192)). Qed.
Lemma lem1493195 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1493196 : term184 = term171.
Proof. exact (fun_ext (fun x : real => @lem1493195 x)). Qed.
Lemma lem1493197 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493198 : term185 = term186.
Proof. exact (MK_COMB (@lem1493197) (@lem1493196)). Qed.
Lemma lem1493199 : term169 = term187.
Proof. exact (MK_COMB (@lem1493194) (@lem1493198)). Qed.
Lemma lem1493200 : (term168 = term169) = (term167 = term187).
Proof. exact (MK_COMB (@lem1493188) (@lem1493199)). Qed.
Lemma lem1493201 : term167 = term187.
Proof. exact (EQ_MP (@lem1493200) (@lem1493178)). Qed.
Lemma lem1493306 : term89 = term187.
Proof. exact (TRANS (@lem1493174) (@lem1493201)). Qed.
Lemma lem1493308 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1493309 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1493308 real P Q). Qed.
Lemma lem1493310 : term169 = term168.
Proof. exact (@lem1493309 term170 term171). Qed.
Lemma lem1493311 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1493312 : term179 = term170.
Proof. exact (fun_ext (fun x : real => @lem1493311 x)). Qed.
Lemma lem1493313 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493314 : term180 = term181.
Proof. exact (MK_COMB (@lem1493313) (@lem1493312)). Qed.
Lemma lem1493315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493316 : term182 = term183.
Proof. exact (MK_COMB (@lem1493315) (@lem1493314)). Qed.
Lemma lem1493317 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1493318 : term184 = term171.
Proof. exact (fun_ext (fun x : real => @lem1493317 x)). Qed.
Lemma lem1493319 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493320 : term185 = term186.
Proof. exact (MK_COMB (@lem1493319) (@lem1493318)). Qed.
Lemma lem1493321 : term169 = term187.
Proof. exact (MK_COMB (@lem1493316) (@lem1493320)). Qed.
Lemma lem1493322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1493323 : term188 = term189.
Proof. exact (MK_COMB (@lem1493322) (@lem1493321)). Qed.
Lemma lem1493324 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1493325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493326 (x : real) : (term173 x) = (term161 x).
Proof. exact (MK_COMB (@lem1493325) (@lem1493324 x)). Qed.
Lemma lem1493327 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1493328 (x : real) : (term175 x) = (term165 x).
Proof. exact (MK_COMB (@lem1493326 x) (@lem1493327 x)). Qed.
Lemma lem1493329 : term176 = term166.
Proof. exact (fun_ext (fun x : real => @lem1493328 x)). Qed.
Lemma lem1493330 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493331 : term168 = term167.
Proof. exact (MK_COMB (@lem1493330) (@lem1493329)). Qed.
Lemma lem1493332 : (term169 = term168) = (term187 = term167).
Proof. exact (MK_COMB (@lem1493323) (@lem1493331)). Qed.
Lemma lem1493333 : term187 = term167.
Proof. exact (EQ_MP (@lem1493332) (@lem1493310)). Qed.
Lemma lem1493335 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1493336 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1493335 real P Q). Qed.
Lemma lem1493337 (x : real) : (term147 x) = (term146 x).
Proof. exact (@lem1493336 (term148 x) (term149 x)). Qed.
Lemma lem1493338 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1493339 (x : real) : (term157 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1493338 x y)). Qed.
Lemma lem1493340 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493341 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1493340) (@lem1493339 x)). Qed.
Lemma lem1493342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493343 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1493342) (@lem1493341 x)). Qed.
Lemma lem1493344 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1493345 (x : real) : (term162 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem1493344 x y)). Qed.
Lemma lem1493346 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493347 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1493346) (@lem1493345 x)). Qed.
Lemma lem1493348 (x : real) : (term147 x) = (term165 x).
Proof. exact (MK_COMB (@lem1493343 x) (@lem1493347 x)). Qed.
Lemma lem1493349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1493350 (x : real) : (term190 x) = (term191 x).
Proof. exact (MK_COMB (@lem1493349) (@lem1493348 x)). Qed.
Lemma lem1493351 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1493352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1493353 (x : real) (y : real) : (term151 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1493352) (@lem1493351 x y)). Qed.
Lemma lem1493354 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1493355 (x : real) (y : real) : (term153 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1493353 x y) (@lem1493354 x y)). Qed.
Lemma lem1493356 (x : real) : (term154 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1493355 x y)). Qed.
Lemma lem1493357 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493358 (x : real) : (term146 x) = (term145 x).
Proof. exact (MK_COMB (@lem1493357) (@lem1493356 x)). Qed.
Lemma lem1493359 (x : real) : ((term147 x) = (term146 x)) = ((term165 x) = (term145 x)).
Proof. exact (MK_COMB (@lem1493350 x) (@lem1493358 x)). Qed.
Lemma lem1493360 (x : real) : (term165 x) = (term145 x).
Proof. exact (EQ_MP (@lem1493359 x) (@lem1493337 x)). Qed.
Lemma lem1493361 : term166 = term192.
Proof. exact (fun_ext (fun x : real => @lem1493360 x)). Qed.
Lemma lem1493362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493363 : term167 = term193.
Proof. exact (MK_COMB (@lem1493362) (@lem1493361)). Qed.
Lemma lem1493364 : term187 = term193.
Proof. exact (TRANS (@lem1493333) (@lem1493363)). Qed.
Lemma lem1493365 : term89 = term193.
Proof. exact (TRANS (@lem1493306) (@lem1493364)). Qed.
Lemma lem1493368 : term22 = term193.
Proof. exact (TRANS (@lem1492951) (@lem1493365)). Qed.
Lemma lem1493385 (x : real) (y : real) : (term83 x y) = (term83 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1493386 (x : real) : (term144 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1493385 x y)). Qed.
Lemma lem1493387 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493388 (x : real) : (term145 x) = (term145 x).
Proof. exact (MK_COMB (@lem1493387) (@lem1493386 x)). Qed.
Lemma lem1493389 : term192 = term192.
Proof. exact (fun_ext (fun x : real => @lem1493388 x)). Qed.
Lemma lem1493390 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493391 : term193 = term193.
Proof. exact (MK_COMB (@lem1493390) (@lem1493389)). Qed.
Lemma lem1493392 : term22 = term193.
Proof. exact (TRANS (@lem1493368) (@lem1493391)). Qed.
Lemma lem1493402 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1493403 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (h1). Qed.
Lemma lem1493404 (x : real) (y : real) (h1 : term67 x y) : term63 x y.
Proof. exact (proj2 (@lem1493403 x y h1)). Qed.
Lemma lem1493405 (x : real) (y : real) (h1 : term67 x y) : term57 x y.
Proof. exact (proj1 (@lem1493403 x y h1)). Qed.
Lemma lem1493407 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493408 : term195 = term196.
Proof. exact (@lem1493407 (NUMERAL 0) term48). Qed.
Lemma lem1493409 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1493410 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1493411 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1493410 h1) (fun h1 : term196 = True => @lem1493409)). Qed.
Lemma lem1493412 : term196 = True.
Proof. exact (EQ_MP (@lem1493411) (@lem1493409)). Qed.
Lemma lem1493413 : term195 = True.
Proof. exact (TRANS (@lem1493408) (@lem1493412)). Qed.
Lemma lem1493414 : True = term195.
Proof. exact (SYM (@lem1493413)). Qed.
Lemma lem1493415 : term195.
Proof. exact (EQ_MP (@lem1493414) (@lem0)). Qed.
Lemma lem1493416 (x : real) (y : real) (h1 : term67 x y) : term198 x y.
Proof. exact (conj (@lem1493415) (@lem1493404 x y h1)). Qed.
Lemma lem1493418 (x : real) (y : real) : term199 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1493419 (x : real) (y : real) : term200 x y.
Proof. exact (@lem1493418 term201 (term60 x y)). Qed.
Lemma lem1493420 (x : real) (y : real) (h1 : term67 x y) : term202 x y.
Proof. exact (@lem1493419 x y (@lem1493416 x y h1)). Qed.
Lemma lem1493421 (x : real) (y : real) : (term203 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1493422 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1493423 (x : real) (y : real) : (term204 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1493422) (@lem1493421 x y)). Qed.
Lemma lem1493424 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1493425 (x : real) (y : real) : (term202 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1493423 x y) (@lem1493424)). Qed.
Lemma lem1493426 (x : real) (y : real) (h1 : term67 x y) : term63 x y.
Proof. exact (EQ_MP (@lem1493425 x y) (@lem1493420 x y h1)). Qed.
Lemma lem1493428 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493429 : term195 = term196.
Proof. exact (@lem1493428 (NUMERAL 0) term48). Qed.
Lemma lem1493430 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1493431 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1493432 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1493431 h1) (fun h1 : term196 = True => @lem1493430)). Qed.
Lemma lem1493433 : term196 = True.
Proof. exact (EQ_MP (@lem1493432) (@lem1493430)). Qed.
Lemma lem1493434 : term195 = True.
Proof. exact (TRANS (@lem1493429) (@lem1493433)). Qed.
Lemma lem1493435 : True = term195.
Proof. exact (SYM (@lem1493434)). Qed.
Lemma lem1493436 : term195.
Proof. exact (EQ_MP (@lem1493435) (@lem0)). Qed.
Lemma lem1493437 (x : real) (y : real) (h1 : term67 x y) : term205 x y.
Proof. exact (conj (@lem1493436) (@lem1493405 x y h1)). Qed.
Lemma lem1493439 (x : real) (y : real) : term206 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1493440 (x : real) (y : real) : term207 x y.
Proof. exact (@lem1493439 term201 (term54 x y)). Qed.
Lemma lem1493441 (x : real) (y : real) (h1 : term67 x y) : term208 x y.
Proof. exact (@lem1493440 x y (@lem1493437 x y h1)). Qed.
Lemma lem1493442 (x : real) (y : real) : (term209 x y) = (term54 x y).
Proof. exact (@lem1483460 (term54 x y)). Qed.
Lemma lem1493443 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493444 (x : real) (y : real) : (term210 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1493443) (@lem1493442 x y)). Qed.
Lemma lem1493445 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1493446 (x : real) (y : real) : (term208 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1493444 x y) (@lem1493445)). Qed.
Lemma lem1493447 (x : real) (y : real) (h1 : term67 x y) : term57 x y.
Proof. exact (EQ_MP (@lem1493446 x y) (@lem1493441 x y h1)). Qed.
Lemma lem1493448 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (conj (@lem1493447 x y h1) (@lem1493426 x y h1)). Qed.
Lemma lem1493450 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1493451 (x : real) (y : real) : term212 x y.
Proof. exact (@lem1493450 (term54 x y) (term60 x y)). Qed.
Lemma lem1493452 (x : real) (y : real) (h1 : term67 x y) : term213 x y.
Proof. exact (@lem1493451 x y (@lem1493448 x y h1)). Qed.
Lemma lem1493453 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483480 (term40 x) x y (term40 y)). Qed.
Lemma lem1493454 (x : real) : (term216 x) = (term44 x).
Proof. exact (@lem1483440 term36 x). Qed.
Lemma lem1493456 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1493457 : term47 = term46.
Proof. exact (@lem1493456 term48). Qed.
Lemma lem1493458 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1493459 : term49 = term50.
Proof. exact (MK_COMB (@lem1493458) (@lem1493457)). Qed.
Lemma lem1493460 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1493461 (x : real) : (term44 x) = (term51 x).
Proof. exact (MK_COMB (@lem1493459) (@lem1493460 x)). Qed.
Lemma lem1493462 (x : real) : (term216 x) = (term51 x).
Proof. exact (TRANS (@lem1493454 x) (@lem1493461 x)). Qed.
Lemma lem1493463 (x : real) : (term51 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1493464 (x : real) : (term216 x) = term46.
Proof. exact (TRANS (@lem1493462 x) (@lem1493463 x)). Qed.
Lemma lem1493465 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1493466 (x : real) : (term217 x) = term218.
Proof. exact (MK_COMB (@lem1493465) (@lem1493464 x)). Qed.
Lemma lem1493467 (y : real) : (term43 y) = (term44 y).
Proof. exact (@lem1483442 term36 y). Qed.
Lemma lem1493469 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1493470 : term47 = term46.
Proof. exact (@lem1493469 term48). Qed.
Lemma lem1493471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1493472 : term49 = term50.
Proof. exact (MK_COMB (@lem1493471) (@lem1493470)). Qed.
Lemma lem1493473 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1493474 (y : real) : (term44 y) = (term51 y).
Proof. exact (MK_COMB (@lem1493472) (@lem1493473 y)). Qed.
Lemma lem1493475 (y : real) : (term43 y) = (term51 y).
Proof. exact (TRANS (@lem1493467 y) (@lem1493474 y)). Qed.
Lemma lem1493476 (y : real) : (term51 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1493477 (y : real) : (term43 y) = term46.
Proof. exact (TRANS (@lem1493475 y) (@lem1493476 y)). Qed.
Lemma lem1493478 (x : real) (y : real) : (term215 x y) = term219.
Proof. exact (MK_COMB (@lem1493466 x) (@lem1493477 y)). Qed.
Lemma lem1493479 (x : real) (y : real) : (term214 x y) = term219.
Proof. exact (TRANS (@lem1493453 x y) (@lem1493478 x y)). Qed.
Lemma lem1493480 : term219 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1493481 (x : real) (y : real) : (term214 x y) = term46.
Proof. exact (TRANS (@lem1493479 x y) (@lem1493480)). Qed.
Lemma lem1493482 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493483 (x : real) (y : real) : (term220 x y) = term221.
Proof. exact (MK_COMB (@lem1493482) (@lem1493481 x y)). Qed.
Lemma lem1493484 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1493485 (x : real) (y : real) : (term213 x y) = term222.
Proof. exact (MK_COMB (@lem1493483 x y) (@lem1493484)). Qed.
Lemma lem1493486 (x : real) (y : real) (h1 : term67 x y) : term222.
Proof. exact (EQ_MP (@lem1493485 x y) (@lem1493452 x y h1)). Qed.
Lemma lem1493488 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493489 : term222 = term223.
Proof. exact (@lem1493488 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1493490 : term223 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1493491 : term222 = False.
Proof. exact (TRANS (@lem1493489) (@lem1493490)). Qed.
Lemma lem1493492 (x : real) (y : real) (h1 : term67 x y) : False.
Proof. exact (EQ_MP (@lem1493491) (@lem1493486 x y h1)). Qed.
Lemma lem1493493 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (h1). Qed.
Lemma lem1493494 (x : real) (y : real) (h1 : term80 x y) : term57 x y.
Proof. exact (proj2 (@lem1493493 x y h1)). Qed.
Lemma lem1493495 (x : real) (y : real) (h1 : term80 x y) : term63 x y.
Proof. exact (proj1 (@lem1493493 x y h1)). Qed.
Lemma lem1493497 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493498 : term195 = term196.
Proof. exact (@lem1493497 (NUMERAL 0) term48). Qed.
Lemma lem1493499 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1493500 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1493501 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1493500 h1) (fun h1 : term196 = True => @lem1493499)). Qed.
Lemma lem1493502 : term196 = True.
Proof. exact (EQ_MP (@lem1493501) (@lem1493499)). Qed.
Lemma lem1493503 : term195 = True.
Proof. exact (TRANS (@lem1493498) (@lem1493502)). Qed.
Lemma lem1493504 : True = term195.
Proof. exact (SYM (@lem1493503)). Qed.
Lemma lem1493505 : term195.
Proof. exact (EQ_MP (@lem1493504) (@lem0)). Qed.
Lemma lem1493506 (x : real) (y : real) (h1 : term80 x y) : term198 x y.
Proof. exact (conj (@lem1493505) (@lem1493495 x y h1)). Qed.
Lemma lem1493508 (x : real) (y : real) : term199 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1493509 (x : real) (y : real) : term200 x y.
Proof. exact (@lem1493508 term201 (term60 x y)). Qed.
Lemma lem1493510 (x : real) (y : real) (h1 : term80 x y) : term202 x y.
Proof. exact (@lem1493509 x y (@lem1493506 x y h1)). Qed.
Lemma lem1493511 (x : real) (y : real) : (term203 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1493512 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1493513 (x : real) (y : real) : (term204 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1493512) (@lem1493511 x y)). Qed.
Lemma lem1493514 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1493515 (x : real) (y : real) : (term202 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1493513 x y) (@lem1493514)). Qed.
Lemma lem1493516 (x : real) (y : real) (h1 : term80 x y) : term63 x y.
Proof. exact (EQ_MP (@lem1493515 x y) (@lem1493510 x y h1)). Qed.
Lemma lem1493518 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493519 : term195 = term196.
Proof. exact (@lem1493518 (NUMERAL 0) term48). Qed.
Lemma lem1493520 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1493521 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1493522 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1493521 h1) (fun h1 : term196 = True => @lem1493520)). Qed.
Lemma lem1493523 : term196 = True.
Proof. exact (EQ_MP (@lem1493522) (@lem1493520)). Qed.
Lemma lem1493524 : term195 = True.
Proof. exact (TRANS (@lem1493519) (@lem1493523)). Qed.
Lemma lem1493525 : True = term195.
Proof. exact (SYM (@lem1493524)). Qed.
Lemma lem1493526 : term195.
Proof. exact (EQ_MP (@lem1493525) (@lem0)). Qed.
Lemma lem1493527 (x : real) (y : real) (h1 : term80 x y) : term205 x y.
Proof. exact (conj (@lem1493526) (@lem1493494 x y h1)). Qed.
Lemma lem1493529 (x : real) (y : real) : term206 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1493530 (x : real) (y : real) : term207 x y.
Proof. exact (@lem1493529 term201 (term54 x y)). Qed.
Lemma lem1493531 (x : real) (y : real) (h1 : term80 x y) : term208 x y.
Proof. exact (@lem1493530 x y (@lem1493527 x y h1)). Qed.
Lemma lem1493532 (x : real) (y : real) : (term209 x y) = (term54 x y).
Proof. exact (@lem1483460 (term54 x y)). Qed.
Lemma lem1493533 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493534 (x : real) (y : real) : (term210 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1493533) (@lem1493532 x y)). Qed.
Lemma lem1493535 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1493536 (x : real) (y : real) : (term208 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1493534 x y) (@lem1493535)). Qed.
Lemma lem1493537 (x : real) (y : real) (h1 : term80 x y) : term57 x y.
Proof. exact (EQ_MP (@lem1493536 x y) (@lem1493531 x y h1)). Qed.
Lemma lem1493538 (x : real) (y : real) (h1 : term80 x y) : term67 x y.
Proof. exact (conj (@lem1493537 x y h1) (@lem1493516 x y h1)). Qed.
Lemma lem1493540 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1493541 (x : real) (y : real) : term212 x y.
Proof. exact (@lem1493540 (term54 x y) (term60 x y)). Qed.
Lemma lem1493542 (x : real) (y : real) (h1 : term80 x y) : term213 x y.
Proof. exact (@lem1493541 x y (@lem1493538 x y h1)). Qed.
Lemma lem1493543 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483480 (term40 x) x y (term40 y)). Qed.
Lemma lem1493544 (x : real) : (term216 x) = (term44 x).
Proof. exact (@lem1483440 term36 x). Qed.
Lemma lem1493546 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1493547 : term47 = term46.
Proof. exact (@lem1493546 term48). Qed.
Lemma lem1493548 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1493549 : term49 = term50.
Proof. exact (MK_COMB (@lem1493548) (@lem1493547)). Qed.
Lemma lem1493550 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1493551 (x : real) : (term44 x) = (term51 x).
Proof. exact (MK_COMB (@lem1493549) (@lem1493550 x)). Qed.
Lemma lem1493552 (x : real) : (term216 x) = (term51 x).
Proof. exact (TRANS (@lem1493544 x) (@lem1493551 x)). Qed.
Lemma lem1493553 (x : real) : (term51 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1493554 (x : real) : (term216 x) = term46.
Proof. exact (TRANS (@lem1493552 x) (@lem1493553 x)). Qed.
Lemma lem1493555 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1493556 (x : real) : (term217 x) = term218.
Proof. exact (MK_COMB (@lem1493555) (@lem1493554 x)). Qed.
Lemma lem1493557 (y : real) : (term43 y) = (term44 y).
Proof. exact (@lem1483442 term36 y). Qed.
Lemma lem1493559 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1493560 : term47 = term46.
Proof. exact (@lem1493559 term48). Qed.
Lemma lem1493561 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1493562 : term49 = term50.
Proof. exact (MK_COMB (@lem1493561) (@lem1493560)). Qed.
Lemma lem1493563 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1493564 (y : real) : (term44 y) = (term51 y).
Proof. exact (MK_COMB (@lem1493562) (@lem1493563 y)). Qed.
Lemma lem1493565 (y : real) : (term43 y) = (term51 y).
Proof. exact (TRANS (@lem1493557 y) (@lem1493564 y)). Qed.
Lemma lem1493566 (y : real) : (term51 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1493567 (y : real) : (term43 y) = term46.
Proof. exact (TRANS (@lem1493565 y) (@lem1493566 y)). Qed.
Lemma lem1493568 (x : real) (y : real) : (term215 x y) = term219.
Proof. exact (MK_COMB (@lem1493556 x) (@lem1493567 y)). Qed.
Lemma lem1493569 (x : real) (y : real) : (term214 x y) = term219.
Proof. exact (TRANS (@lem1493543 x y) (@lem1493568 x y)). Qed.
Lemma lem1493570 : term219 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1493571 (x : real) (y : real) : (term214 x y) = term46.
Proof. exact (TRANS (@lem1493569 x y) (@lem1493570)). Qed.
Lemma lem1493572 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493573 (x : real) (y : real) : (term220 x y) = term221.
Proof. exact (MK_COMB (@lem1493572) (@lem1493571 x y)). Qed.
Lemma lem1493574 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1493575 (x : real) (y : real) : (term213 x y) = term222.
Proof. exact (MK_COMB (@lem1493573 x y) (@lem1493574)). Qed.
Lemma lem1493576 (x : real) (y : real) (h1 : term80 x y) : term222.
Proof. exact (EQ_MP (@lem1493575 x y) (@lem1493542 x y h1)). Qed.
Lemma lem1493578 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1493579 : term222 = term223.
Proof. exact (@lem1493578 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1493580 : term223 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1493581 : term222 = False.
Proof. exact (TRANS (@lem1493579) (@lem1493580)). Qed.
Lemma lem1493582 (x : real) (y : real) (h1 : term80 x y) : False.
Proof. exact (EQ_MP (@lem1493581) (@lem1493576 x y h1)). Qed.
Lemma lem1493583 (x : real) (y : real) (h1 : term83 x y) : False.
Proof. exact (or_elim (@lem1493402 x y h1) (fun h0 : term67 x y => @lem1493492 x y h0) (fun h0 : term80 x y => @lem1493582 x y h0)). Qed.
Lemma lem1493585 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1493586 (x : real) (y : real) (h1 : term83 x y) : (term83 x y) = False.
Proof. exact (prop_ext (fun h2 : term83 x y => @lem1493583 x y h1) (fun h2 : False => @lem1493585 x y h1)). Qed.
Lemma lem1493587 (x : real) (y : real) (h1 : term83 x y) : False.
Proof. exact (EQ_MP (@lem1493586 x y h1) (@lem1493585 x y h1)). Qed.
Lemma lem1493588 (x : real) (h1 : term145 x) : term145 x.
Proof. exact (h1). Qed.
Lemma lem1493589 (x : real) (h1 : term145 x) : False.
Proof. exact (ex_elim (@lem1493588 x h1) (fun y : real => fun h0 : term144 x y => @lem1493587 x y h0)). Qed.
Lemma lem1493590 (h1 : term193) : term193.
Proof. exact (h1). Qed.
Lemma lem1493591 (h1 : term193) : False.
Proof. exact (ex_elim (@lem1493590 h1) (fun x : real => fun h0 : term192 x => @lem1493589 x h0)). Qed.
Lemma lem1493592 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1493593 (h1 : term22) : term193.
Proof. exact (EQ_MP (@lem1493392) (@lem1493592 h1)). Qed.
Lemma lem1493594 (h1 : term22) : term193 = False.
Proof. exact (prop_ext (fun h2 : term193 => @lem1493591 h2) (fun h2 : False => @lem1493593 h1)). Qed.
Lemma lem1493595 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1493594 h1) (@lem1493593 h1)). Qed.
Lemma lem1493596 : term224.
Proof. exact (fun h0 : term22 => @lem1493595 h0). Qed.
Lemma lem1493597 : term225.
Proof. exact (@lem1386578 term226). Qed.
Lemma lem1493598 : term226.
Proof. exact (@lem1493597 (@lem1493596)). Qed.
