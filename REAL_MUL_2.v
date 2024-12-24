Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_2_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1483438_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm706885_spec.
Require Import thm996238_spec.
Lemma lem1629742 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1629743 : term2 = term3.
Proof. exact (@lem1629742 term4). Qed.
Lemma lem1629744 (x : real) : (term5 x) = ((term6 x) = (real_add x x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1629745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1629747 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1629745) (@lem1629744 x)). Qed.
Lemma lem1629748 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1629747 x)). Qed.
Lemma lem1629749 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1629750 : term3 = term11.
Proof. exact (MK_COMB (@lem1629749) (@lem1629748)). Qed.
Lemma lem1629752 : term2 = term11.
Proof. exact (TRANS (@lem1629743) (@lem1629750)). Qed.
Lemma lem1629755 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1629756 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1629755 x)). Qed.
Lemma lem1629757 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1629758 : term11 = term11.
Proof. exact (MK_COMB (@lem1629757) (@lem1629756)). Qed.
Lemma lem1629759 : term2 = term11.
Proof. exact (TRANS (@lem1629752) (@lem1629758)). Qed.
Lemma lem1629760 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483554 (term6 x) (real_add x x)). Qed.
Lemma lem1629766 (x : real) : (real_add x x) = (term13 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1629767 : term14 = term15.
Proof. exact (@lem1367770 term16 term16). Qed.
Lemma lem1629768 : term17 = term18.
Proof. exact (@lem706885). Qed.
Lemma lem1629769 : (term17 = term18) = (term19 = term20).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term18). Qed.
Lemma lem1629770 : term19 = term20.
Proof. exact (EQ_MP (@lem1629769) (@lem1629768)). Qed.
Lemma lem1629771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1629772 : term15 = term21.
Proof. exact (MK_COMB (@lem1629771) (@lem1629770)). Qed.
Lemma lem1629773 : term14 = term21.
Proof. exact (TRANS (@lem1629767) (@lem1629772)). Qed.
Lemma lem1629774 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1629775 : term22 = term23.
Proof. exact (MK_COMB (@lem1629774) (@lem1629773)). Qed.
Lemma lem1629776 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1629777 (x : real) : (term13 x) = (term6 x).
Proof. exact (MK_COMB (@lem1629775) (@lem1629776 x)). Qed.
Lemma lem1629779 (x : real) : (real_add x x) = (term6 x).
Proof. exact (TRANS (@lem1629766 x) (@lem1629777 x)). Qed.
Lemma lem1629788 (x : real) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1629789 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1629788 x) (@lem1629779 x)). Qed.
Lemma lem1629790 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem1483519 (term6 x) (term6 x)). Qed.
Lemma lem1629791 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483476 term30 term21 x). Qed.
Lemma lem1629793 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1629794 : term33 = term34.
Proof. exact (@lem1629793 term16 term20). Qed.
Lemma lem1629795 : term35 = term18.
Proof. exact (@lem996238 term18). Qed.
Lemma lem1629796 : (term35 = term18) = (term36 = term20).
Proof. exact (@lem1007663 (BIT1 0) term18 term18). Qed.
Lemma lem1629797 : term36 = term20.
Proof. exact (EQ_MP (@lem1629796) (@lem1629795)). Qed.
Lemma lem1629798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1629799 : term37 = term21.
Proof. exact (MK_COMB (@lem1629798) (@lem1629797)). Qed.
Lemma lem1629800 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1629801 : term34 = term38.
Proof. exact (MK_COMB (@lem1629800) (@lem1629799)). Qed.
Lemma lem1629802 : term33 = term38.
Proof. exact (TRANS (@lem1629794) (@lem1629801)). Qed.
Lemma lem1629803 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1629804 : term39 = term40.
Proof. exact (MK_COMB (@lem1629803) (@lem1629802)). Qed.
Lemma lem1629805 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1629806 (x : real) : (term29 x) = (term41 x).
Proof. exact (MK_COMB (@lem1629804) (@lem1629805 x)). Qed.
Lemma lem1629807 (x : real) : (term28 x) = (term41 x).
Proof. exact (TRANS (@lem1629791 x) (@lem1629806 x)). Qed.
Lemma lem1629808 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1629809 (x : real) : (term27 x) = (term43 x).
Proof. exact (MK_COMB (@lem1629808 x) (@lem1629807 x)). Qed.
Lemma lem1629810 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483438 term21 term38 x). Qed.
Lemma lem1629812 (m : nat) : (term45 m) = term46.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1629813 : term47 = term46.
Proof. exact (@lem1629812 term20). Qed.
Lemma lem1629814 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1629815 : term48 = term49.
Proof. exact (MK_COMB (@lem1629814) (@lem1629813)). Qed.
Lemma lem1629816 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1629817 (x : real) : (term44 x) = (term50 x).
Proof. exact (MK_COMB (@lem1629815) (@lem1629816 x)). Qed.
Lemma lem1629818 (x : real) : (term43 x) = (term50 x).
Proof. exact (TRANS (@lem1629810 x) (@lem1629817 x)). Qed.
Lemma lem1629819 (x : real) : (term50 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1629820 (x : real) : (term43 x) = term46.
Proof. exact (TRANS (@lem1629818 x) (@lem1629819 x)). Qed.
Lemma lem1629821 (x : real) : (term27 x) = term46.
Proof. exact (TRANS (@lem1629809 x) (@lem1629820 x)). Qed.
Lemma lem1629822 (x : real) : (term26 x) = term46.
Proof. exact (TRANS (@lem1629790 x) (@lem1629821 x)). Qed.
Lemma lem1629823 (x : real) : (term25 x) = term46.
Proof. exact (TRANS (@lem1629789 x) (@lem1629822 x)). Qed.
Lemma lem1629824 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1629825 (x : real) : (term51 x) = term52.
Proof. exact (MK_COMB (@lem1629824) (@lem1629823 x)). Qed.
Lemma lem1629826 : term52 = term53.
Proof. exact (@lem1483512 term46). Qed.
Lemma lem1629828 (x : nat) : (term54 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1629829 : term53 = term46.
Proof. exact (@lem1629828 term16). Qed.
Lemma lem1629830 : term52 = term46.
Proof. exact (TRANS (@lem1629826) (@lem1629829)). Qed.
Lemma lem1629831 (x : real) : (term55 x) = (term55 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1629832 (x : real) : ((term51 x) = term52) = ((term51 x) = term46).
Proof. exact (MK_COMB (@lem1629831 x) (@lem1629830)). Qed.
Lemma lem1629833 (x : real) : (term51 x) = term46.
Proof. exact (EQ_MP (@lem1629832 x) (@lem1629825 x)). Qed.
Lemma lem1629834 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1629835 (x : real) : (term56 x) = term57.
Proof. exact (MK_COMB (@lem1629834) (@lem1629833 x)). Qed.
Lemma lem1629836 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1629837 (x : real) : (term58 x) = term59.
Proof. exact (MK_COMB (@lem1629835 x) (@lem1629836)). Qed.
Lemma lem1629838 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1629839 (x : real) : (term60 x) = term57.
Proof. exact (MK_COMB (@lem1629838) (@lem1629823 x)). Qed.
Lemma lem1629840 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1629841 (x : real) : (term61 x) = term59.
Proof. exact (MK_COMB (@lem1629839 x) (@lem1629840)). Qed.
Lemma lem1629842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1629843 (x : real) : (term62 x) = term63.
Proof. exact (MK_COMB (@lem1629842) (@lem1629841 x)). Qed.
Lemma lem1629844 (x : real) : (term12 x) = term64.
Proof. exact (MK_COMB (@lem1629843 x) (@lem1629837 x)). Qed.
Lemma lem1629845 (x : real) : (term8 x) = term64.
Proof. exact (TRANS (@lem1629760 x) (@lem1629844 x)). Qed.
Lemma lem1629846 : term10 = term65.
Proof. exact (fun_ext (fun x : real => @lem1629845 x)). Qed.
Lemma lem1629847 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1629848 : term11 = term66.
Proof. exact (MK_COMB (@lem1629847) (@lem1629846)). Qed.
Lemma lem1629849 : term2 = term66.
Proof. exact (TRANS (@lem1629759) (@lem1629848)). Qed.
Lemma lem1629851 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1629852 (P : real -> Prop) (Q : real -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1629851 real P Q). Qed.
Lemma lem1629853 : term71 = term72.
Proof. exact (@lem1629852 term73 term73). Qed.
Lemma lem1629854 (x : real) : (term74 x) = term59.
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1629855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1629856 (x : real) : (term75 x) = term63.
Proof. exact (MK_COMB (@lem1629855) (@lem1629854 x)). Qed.
Lemma lem1629857 (x : real) : (term74 x) = term59.
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1629858 (x : real) : (term76 x) = term64.
Proof. exact (MK_COMB (@lem1629856 x) (@lem1629857 x)). Qed.
Lemma lem1629859 : term77 = term65.
Proof. exact (fun_ext (fun x : real => @lem1629858 x)). Qed.
Lemma lem1629860 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1629861 : term71 = term66.
Proof. exact (MK_COMB (@lem1629860) (@lem1629859)). Qed.
Lemma lem1629862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629863 : term78 = term79.
Proof. exact (MK_COMB (@lem1629862) (@lem1629861)). Qed.
Lemma lem1629864 (x : real) : (term74 x) = term59.
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1629865 : term80 = term73.
Proof. exact (fun_ext (fun x : real => @lem1629864 x)). Qed.
Lemma lem1629866 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1629867 : term81 = term82.
Proof. exact (MK_COMB (@lem1629866) (@lem1629865)). Qed.
Lemma lem1629868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1629869 : term83 = term84.
Proof. exact (MK_COMB (@lem1629868) (@lem1629867)). Qed.
Lemma lem1629870 (x : real) : (term74 x) = term59.
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1629871 : term80 = term73.
Proof. exact (fun_ext (fun x : real => @lem1629870 x)). Qed.
Lemma lem1629872 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1629873 : term81 = term82.
Proof. exact (MK_COMB (@lem1629872) (@lem1629871)). Qed.
Lemma lem1629874 : term72 = term85.
Proof. exact (MK_COMB (@lem1629869) (@lem1629873)). Qed.
Lemma lem1629875 : (term71 = term72) = (term66 = term85).
Proof. exact (MK_COMB (@lem1629863) (@lem1629874)). Qed.
Lemma lem1629876 : term66 = term85.
Proof. exact (EQ_MP (@lem1629875) (@lem1629853)). Qed.
Lemma lem1629878 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1629879 (t : Prop) : (term87 t) = t.
Proof. exact (@lem1629878 real t). Qed.
Lemma lem1629880 : term82 = term59.
Proof. exact (@lem1629879 term59). Qed.
Lemma lem1629881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1629882 : term84 = term63.
Proof. exact (MK_COMB (@lem1629881) (@lem1629880)). Qed.
Lemma lem1629884 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1629885 (t : Prop) : (term87 t) = t.
Proof. exact (@lem1629884 real t). Qed.
Lemma lem1629886 : term82 = term59.
Proof. exact (@lem1629885 term59). Qed.
Lemma lem1629887 : term85 = term64.
Proof. exact (MK_COMB (@lem1629882) (@lem1629886)). Qed.
Lemma lem1629890 : term66 = term64.
Proof. exact (TRANS (@lem1629876) (@lem1629887)). Qed.
Lemma lem1629899 : term2 = term64.
Proof. exact (TRANS (@lem1629849) (@lem1629890)). Qed.
Lemma lem1629909 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1629910 (h1 : term59) : term59.
Proof. exact (h1). Qed.
Lemma lem1629912 (n : nat) (m : nat) : (term88 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1629913 : term59 = term89.
Proof. exact (@lem1629912 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1629914 : term89 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1629915 : term59 = False.
Proof. exact (TRANS (@lem1629913) (@lem1629914)). Qed.
Lemma lem1629916 (h1 : term59) : False.
Proof. exact (EQ_MP (@lem1629915) (@lem1629910 h1)). Qed.
Lemma lem1629917 (h1 : term59) : term59.
Proof. exact (h1). Qed.
Lemma lem1629919 (n : nat) (m : nat) : (term88 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1629920 : term59 = term89.
Proof. exact (@lem1629919 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1629921 : term89 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1629922 : term59 = False.
Proof. exact (TRANS (@lem1629920) (@lem1629921)). Qed.
Lemma lem1629923 (h1 : term59) : False.
Proof. exact (EQ_MP (@lem1629922) (@lem1629917 h1)). Qed.
Lemma lem1629924 (h1 : term64) : False.
Proof. exact (or_elim (@lem1629909 h1) (fun h0 : term59 => @lem1629916 h0) (fun h0 : term59 => @lem1629923 h0)). Qed.
Lemma lem1629926 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1629927 (h1 : term64) : term64 = False.
Proof. exact (prop_ext (fun h2 : term64 => @lem1629924 h1) (fun h2 : False => @lem1629926 h1)). Qed.
Lemma lem1629928 (h1 : term64) : False.
Proof. exact (EQ_MP (@lem1629927 h1) (@lem1629926 h1)). Qed.
Lemma lem1629929 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1629930 (h1 : term2) : term64.
Proof. exact (EQ_MP (@lem1629899) (@lem1629929 h1)). Qed.
Lemma lem1629931 (h1 : term2) : term64 = False.
Proof. exact (prop_ext (fun h2 : term64 => @lem1629928 h2) (fun h2 : False => @lem1629930 h1)). Qed.
Lemma lem1629932 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1629931 h1) (@lem1629930 h1)). Qed.
Lemma lem1629933 : term90.
Proof. exact (fun h0 : term2 => @lem1629932 h0). Qed.
Lemma lem1629934 : term91.
Proof. exact (@lem1386578 term92). Qed.
Lemma lem1629935 : term92.
Proof. exact (@lem1629934 (@lem1629933)). Qed.
