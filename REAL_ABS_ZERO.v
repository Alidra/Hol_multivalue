Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_ZERO_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482702_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1526771 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 ((real_abs x) = term2) (x = term2)). Qed.
Lemma lem1526772 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1526773 : term5 = term6.
Proof. exact (@lem1526772 term7). Qed.
Lemma lem1526774 (x : real) : (term8 x) = (((real_abs x) = term2) = (x = term2)).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1526775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1526776 (x : real) : (term9 x) = (term0 x).
Proof. exact (MK_COMB (@lem1526775) (@lem1526774 x)). Qed.
Lemma lem1526777 (x : real) : (term9 x) = (term1 x).
Proof. exact (TRANS (@lem1526776 x) (@lem1526771 x)). Qed.
Lemma lem1526778 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1526777 x)). Qed.
Lemma lem1526779 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526780 : term6 = term12.
Proof. exact (MK_COMB (@lem1526779) (@lem1526778)). Qed.
Lemma lem1526782 : term5 = term12.
Proof. exact (TRANS (@lem1526773) (@lem1526780)). Qed.
Lemma lem1526799 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1526800 : term11 = term11.
Proof. exact (fun_ext (fun x : real => @lem1526799 x)). Qed.
Lemma lem1526801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526802 : term12 = term12.
Proof. exact (MK_COMB (@lem1526801) (@lem1526800)). Qed.
Lemma lem1526803 : term5 = term12.
Proof. exact (TRANS (@lem1526782) (@lem1526802)). Qed.
Lemma lem1526804 (x : real) : ((real_abs x) = term2) = ((term13 x) = term2).
Proof. exact (@lem1483529 (real_abs x) term2). Qed.
Lemma lem1526810 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1483519 (real_abs x) term2). Qed.
Lemma lem1526812 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1526813 : term16 = term2.
Proof. exact (@lem1526812 term17). Qed.
Lemma lem1526814 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1526815 (x : real) : (term14 x) = (term19 x).
Proof. exact (MK_COMB (@lem1526814 x) (@lem1526813)). Qed.
Lemma lem1526816 (x : real) : (term19 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1526817 (x : real) : (term14 x) = (real_abs x).
Proof. exact (TRANS (@lem1526815 x) (@lem1526816 x)). Qed.
Lemma lem1526819 (x : real) : (term13 x) = (real_abs x).
Proof. exact (TRANS (@lem1526810 x) (@lem1526817 x)). Qed.
Lemma lem1526820 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1526821 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1526820) (@lem1526819 x)). Qed.
Lemma lem1526822 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1526823 (x : real) : ((term13 x) = term2) = ((real_abs x) = term2).
Proof. exact (MK_COMB (@lem1526821 x) (@lem1526822)). Qed.
Lemma lem1526824 (x : real) : ((real_abs x) = term2) = ((real_abs x) = term2).
Proof. exact (TRANS (@lem1526804 x) (@lem1526823 x)). Qed.
Lemma lem1526825 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1483554 x term2). Qed.
Lemma lem1526831 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1526833 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1526834 : term16 = term2.
Proof. exact (@lem1526833 term17). Qed.
Lemma lem1526835 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1526836 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1526835 x) (@lem1526834)). Qed.
Lemma lem1526837 (x : real) : (term26 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1526838 (x : real) : (term25 x) = x.
Proof. exact (TRANS (@lem1526836 x) (@lem1526837 x)). Qed.
Lemma lem1526840 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1526831 x) (@lem1526838 x)). Qed.
Lemma lem1526841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1526842 (x : real) : (term27 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1526841) (@lem1526840 x)). Qed.
Lemma lem1526845 (x : real) : (real_neg x) = (term28 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1526846 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1526847 (x : real) : ((term27 x) = (real_neg x)) = ((term27 x) = (term28 x)).
Proof. exact (MK_COMB (@lem1526846 x) (@lem1526845 x)). Qed.
Lemma lem1526848 (x : real) : (term27 x) = (term28 x).
Proof. exact (EQ_MP (@lem1526847 x) (@lem1526842 x)). Qed.
Lemma lem1526849 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526850 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1526849) (@lem1526848 x)). Qed.
Lemma lem1526851 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1526852 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1526850 x) (@lem1526851)). Qed.
Lemma lem1526853 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526854 (x : real) : (term34 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1526853) (@lem1526840 x)). Qed.
Lemma lem1526855 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1526856 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1526854 x) (@lem1526855)). Qed.
Lemma lem1526857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526858 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1526857) (@lem1526856 x)). Qed.
Lemma lem1526859 (x : real) : (term23 x) = (term39 x).
Proof. exact (MK_COMB (@lem1526858 x) (@lem1526852 x)). Qed.
Lemma lem1526860 (x : real) : (term22 x) = (term39 x).
Proof. exact (TRANS (@lem1526825 x) (@lem1526859 x)). Qed.
Lemma lem1526861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1526862 (x : real) : (term40 x) = (term40 x).
Proof. exact (MK_COMB (@lem1526861) (@lem1526824 x)). Qed.
Lemma lem1526863 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1526862 x) (@lem1526860 x)). Qed.
Lemma lem1526864 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483554 (real_abs x) term2). Qed.
Lemma lem1526870 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1483519 (real_abs x) term2). Qed.
Lemma lem1526872 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1526873 : term16 = term2.
Proof. exact (@lem1526872 term17). Qed.
Lemma lem1526874 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1526875 (x : real) : (term14 x) = (term19 x).
Proof. exact (MK_COMB (@lem1526874 x) (@lem1526873)). Qed.
Lemma lem1526876 (x : real) : (term19 x) = (real_abs x).
Proof. exact (@lem1483450 (real_abs x)). Qed.
Lemma lem1526877 (x : real) : (term14 x) = (real_abs x).
Proof. exact (TRANS (@lem1526875 x) (@lem1526876 x)). Qed.
Lemma lem1526879 (x : real) : (term13 x) = (real_abs x).
Proof. exact (TRANS (@lem1526870 x) (@lem1526877 x)). Qed.
Lemma lem1526880 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1526881 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1526880) (@lem1526879 x)). Qed.
Lemma lem1526884 (x : real) : (term46 x) = (term47 x).
Proof. exact (@lem1483512 (real_abs x)). Qed.
Lemma lem1526885 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1526886 (x : real) : ((term45 x) = (term46 x)) = ((term45 x) = (term47 x)).
Proof. exact (MK_COMB (@lem1526885 x) (@lem1526884 x)). Qed.
Lemma lem1526887 (x : real) : (term45 x) = (term47 x).
Proof. exact (EQ_MP (@lem1526886 x) (@lem1526881 x)). Qed.
Lemma lem1526888 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526889 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1526888) (@lem1526887 x)). Qed.
Lemma lem1526890 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1526891 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1526889 x) (@lem1526890)). Qed.
Lemma lem1526892 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526893 (x : real) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem1526892) (@lem1526879 x)). Qed.
Lemma lem1526894 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1526895 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1526893 x) (@lem1526894)). Qed.
Lemma lem1526896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526897 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1526896) (@lem1526895 x)). Qed.
Lemma lem1526898 (x : real) : (term44 x) = (term59 x).
Proof. exact (MK_COMB (@lem1526897 x) (@lem1526891 x)). Qed.
Lemma lem1526899 (x : real) : (term43 x) = (term59 x).
Proof. exact (TRANS (@lem1526864 x) (@lem1526898 x)). Qed.
Lemma lem1526900 (x : real) : (x = term2) = ((term24 x) = term2).
Proof. exact (@lem1483529 x term2). Qed.
Lemma lem1526906 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1526908 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1526909 : term16 = term2.
Proof. exact (@lem1526908 term17). Qed.
Lemma lem1526910 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1526911 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1526910 x) (@lem1526909)). Qed.
Lemma lem1526912 (x : real) : (term26 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1526913 (x : real) : (term25 x) = x.
Proof. exact (TRANS (@lem1526911 x) (@lem1526912 x)). Qed.
Lemma lem1526915 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1526906 x) (@lem1526913 x)). Qed.
Lemma lem1526916 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1526917 (x : real) : (term60 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1526916) (@lem1526915 x)). Qed.
Lemma lem1526918 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1526919 (x : real) : ((term24 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1526917 x) (@lem1526918)). Qed.
Lemma lem1526920 (x : real) : (x = term2) = (x = term2).
Proof. exact (TRANS (@lem1526900 x) (@lem1526919 x)). Qed.
Lemma lem1526921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1526922 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1526921) (@lem1526899 x)). Qed.
Lemma lem1526923 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1526922 x) (@lem1526920 x)). Qed.
Lemma lem1526924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526925 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem1526924) (@lem1526863 x)). Qed.
Lemma lem1526926 (x : real) : (term1 x) = (term67 x).
Proof. exact (MK_COMB (@lem1526925 x) (@lem1526923 x)). Qed.
Lemma lem1526927 : term11 = term68.
Proof. exact (fun_ext (fun x : real => @lem1526926 x)). Qed.
Lemma lem1526928 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526929 : term12 = term69.
Proof. exact (MK_COMB (@lem1526928) (@lem1526927)). Qed.
Lemma lem1526930 : term5 = term69.
Proof. exact (TRANS (@lem1526803) (@lem1526929)). Qed.
Lemma lem1526932 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1526933 (P : real -> Prop) (Q : real -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem1526932 real P Q). Qed.
Lemma lem1526934 : term74 = term75.
Proof. exact (@lem1526933 term76 term77). Qed.
Lemma lem1526935 (x : real) : (term78 x) = (term42 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1526936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526937 (x : real) : (term79 x) = (term66 x).
Proof. exact (MK_COMB (@lem1526936) (@lem1526935 x)). Qed.
Lemma lem1526938 (x : real) : (term80 x) = (term64 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1526939 (x : real) : (term81 x) = (term67 x).
Proof. exact (MK_COMB (@lem1526937 x) (@lem1526938 x)). Qed.
Lemma lem1526940 : term82 = term68.
Proof. exact (fun_ext (fun x : real => @lem1526939 x)). Qed.
Lemma lem1526941 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526942 : term74 = term69.
Proof. exact (MK_COMB (@lem1526941) (@lem1526940)). Qed.
Lemma lem1526943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1526944 : term83 = term84.
Proof. exact (MK_COMB (@lem1526943) (@lem1526942)). Qed.
Lemma lem1526945 (x : real) : (term78 x) = (term42 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1526946 : term85 = term76.
Proof. exact (fun_ext (fun x : real => @lem1526945 x)). Qed.
Lemma lem1526947 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526948 : term86 = term87.
Proof. exact (MK_COMB (@lem1526947) (@lem1526946)). Qed.
Lemma lem1526949 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1526950 : term88 = term89.
Proof. exact (MK_COMB (@lem1526949) (@lem1526948)). Qed.
Lemma lem1526951 (x : real) : (term80 x) = (term64 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1526952 : term90 = term77.
Proof. exact (fun_ext (fun x : real => @lem1526951 x)). Qed.
Lemma lem1526953 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1526954 : term91 = term92.
Proof. exact (MK_COMB (@lem1526953) (@lem1526952)). Qed.
Lemma lem1526955 : term75 = term93.
Proof. exact (MK_COMB (@lem1526950) (@lem1526954)). Qed.
Lemma lem1526956 : (term74 = term75) = (term69 = term93).
Proof. exact (MK_COMB (@lem1526944) (@lem1526955)). Qed.
Lemma lem1526957 : term69 = term93.
Proof. exact (EQ_MP (@lem1526956) (@lem1526934)). Qed.
Lemma lem1527055 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term70 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1527056 (P : real -> Prop) (Q : real -> Prop) : (term73 P Q) = (term72 P Q).
Proof. exact (@lem1527055 real P Q). Qed.
Lemma lem1527057 : term75 = term74.
Proof. exact (@lem1527056 term76 term77). Qed.
Lemma lem1527058 (x : real) : (term78 x) = (term42 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1527059 : term85 = term76.
Proof. exact (fun_ext (fun x : real => @lem1527058 x)). Qed.
Lemma lem1527060 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1527061 : term86 = term87.
Proof. exact (MK_COMB (@lem1527060) (@lem1527059)). Qed.
Lemma lem1527062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527063 : term88 = term89.
Proof. exact (MK_COMB (@lem1527062) (@lem1527061)). Qed.
Lemma lem1527064 (x : real) : (term80 x) = (term64 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1527065 : term90 = term77.
Proof. exact (fun_ext (fun x : real => @lem1527064 x)). Qed.
Lemma lem1527066 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1527067 : term91 = term92.
Proof. exact (MK_COMB (@lem1527066) (@lem1527065)). Qed.
Lemma lem1527068 : term75 = term93.
Proof. exact (MK_COMB (@lem1527063) (@lem1527067)). Qed.
Lemma lem1527069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1527070 : term94 = term95.
Proof. exact (MK_COMB (@lem1527069) (@lem1527068)). Qed.
Lemma lem1527071 (x : real) : (term78 x) = (term42 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1527072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527073 (x : real) : (term79 x) = (term66 x).
Proof. exact (MK_COMB (@lem1527072) (@lem1527071 x)). Qed.
Lemma lem1527074 (x : real) : (term80 x) = (term64 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1527075 (x : real) : (term81 x) = (term67 x).
Proof. exact (MK_COMB (@lem1527073 x) (@lem1527074 x)). Qed.
Lemma lem1527076 : term82 = term68.
Proof. exact (fun_ext (fun x : real => @lem1527075 x)). Qed.
Lemma lem1527077 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1527078 : term74 = term69.
Proof. exact (MK_COMB (@lem1527077) (@lem1527076)). Qed.
Lemma lem1527079 : (term75 = term74) = (term93 = term69).
Proof. exact (MK_COMB (@lem1527070) (@lem1527078)). Qed.
Lemma lem1527080 : term93 = term69.
Proof. exact (EQ_MP (@lem1527079) (@lem1527057)). Qed.
Lemma lem1527081 : term69 = term69.
Proof. exact (TRANS (@lem1526957) (@lem1527080)). Qed.
Lemma lem1527084 : term5 = term69.
Proof. exact (TRANS (@lem1526930) (@lem1527081)). Qed.
Lemma lem1527101 (x : real) : (term64 x) = (term96 x).
Proof. exact (@lem19367 (term56 x) (term52 x) (x = term2)). Qed.
Lemma lem1527118 (x : real) : (term42 x) = (term97 x).
Proof. exact (@lem19158 (term36 x) ((real_abs x) = term2) (term33 x)). Qed.
Lemma lem1527119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527120 (x : real) : (term66 x) = (term98 x).
Proof. exact (MK_COMB (@lem1527119) (@lem1527118 x)). Qed.
Lemma lem1527121 (x : real) : (term67 x) = (term99 x).
Proof. exact (MK_COMB (@lem1527120 x) (@lem1527101 x)). Qed.
Lemma lem1527122 : term68 = term100.
Proof. exact (fun_ext (fun x : real => @lem1527121 x)). Qed.
Lemma lem1527123 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1527124 : term69 = term101.
Proof. exact (MK_COMB (@lem1527123) (@lem1527122)). Qed.
Lemma lem1527125 : term5 = term101.
Proof. exact (TRANS (@lem1527084) (@lem1527124)). Qed.
Lemma lem1527127 (x : real) : (term102 x) = (term103 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1527128 (x : real) : (term103 x) = (term102 x).
Proof. exact (SYM (@lem1527127 x)). Qed.
Lemma lem1527129 (x : real) : (term102 x) = (term104 x).
Proof. exact (@lem1482981 (term105 x) x). Qed.
Lemma lem1527130 (x : real) : (term103 x) = (term104 x).
Proof. exact (TRANS (@lem1527128 x) (@lem1527129 x)). Qed.
Lemma lem1527131 (x : real) : (term106 x) = (term107 x).
Proof. exact (eq_refl (term106 x)). Qed.
Lemma lem1527132 (x : real) : (term108 x) = (term108 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1527133 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1527132 x) (@lem1527131 x)). Qed.
Lemma lem1527134 (x : real) : (term111 x) = (term112 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1527135 (x : real) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1527136 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1527135 x) (@lem1527134 x)). Qed.
Lemma lem1527137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527138 (x : real) : (term116 x) = (term117 x).
Proof. exact (MK_COMB (@lem1527137) (@lem1527136 x)). Qed.
Lemma lem1527139 (x : real) : (term104 x) = (term118 x).
Proof. exact (MK_COMB (@lem1527138 x) (@lem1527133 x)). Qed.
Lemma lem1527140 (x : real) : (term119 x) = (term119 x).
Proof. exact (eq_refl (term119 x)). Qed.
Lemma lem1527141 (x : real) : ((term103 x) = (term104 x)) = ((term103 x) = (term118 x)).
Proof. exact (MK_COMB (@lem1527140 x) (@lem1527139 x)). Qed.
Lemma lem1527142 (x : real) : (term103 x) = (term118 x).
Proof. exact (EQ_MP (@lem1527141 x) (@lem1527130 x)). Qed.
Lemma lem1527143 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483527 x term2). Qed.
Lemma lem1527149 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1527151 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527152 : term16 = term2.
Proof. exact (@lem1527151 term17). Qed.
Lemma lem1527153 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1527154 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1527153 x) (@lem1527152)). Qed.
Lemma lem1527155 (x : real) : (term26 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1527156 (x : real) : (term25 x) = x.
Proof. exact (TRANS (@lem1527154 x) (@lem1527155 x)). Qed.
Lemma lem1527158 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1527149 x) (@lem1527156 x)). Qed.
Lemma lem1527159 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1527160 (x : real) : (term122 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1527159) (@lem1527158 x)). Qed.
Lemma lem1527161 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527162 (x : real) : (term121 x) = (term120 x).
Proof. exact (MK_COMB (@lem1527160 x) (@lem1527161)). Qed.
Lemma lem1527163 (x : real) : (term120 x) = (term120 x).
Proof. exact (TRANS (@lem1527143 x) (@lem1527162 x)). Qed.
Lemma lem1527164 (x : real) : (x = term2) = ((term24 x) = term2).
Proof. exact (@lem1483529 x term2). Qed.
Lemma lem1527170 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1527172 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527173 : term16 = term2.
Proof. exact (@lem1527172 term17). Qed.
Lemma lem1527174 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1527175 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1527174 x) (@lem1527173)). Qed.
Lemma lem1527176 (x : real) : (term26 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1527177 (x : real) : (term25 x) = x.
Proof. exact (TRANS (@lem1527175 x) (@lem1527176 x)). Qed.
Lemma lem1527179 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1527170 x) (@lem1527177 x)). Qed.
Lemma lem1527180 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1527181 (x : real) : (term60 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1527180) (@lem1527179 x)). Qed.
Lemma lem1527182 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527183 (x : real) : ((term24 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1527181 x) (@lem1527182)). Qed.
Lemma lem1527184 (x : real) : (x = term2) = (x = term2).
Proof. exact (TRANS (@lem1527164 x) (@lem1527183 x)). Qed.
Lemma lem1527185 (x : real) : (term36 x) = (term35 x).
Proof. exact (@lem1483525 x term2). Qed.
Lemma lem1527191 (x : real) : (term24 x) = (term25 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1527193 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527194 : term16 = term2.
Proof. exact (@lem1527193 term17). Qed.
Lemma lem1527195 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1527196 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1527195 x) (@lem1527194)). Qed.
Lemma lem1527197 (x : real) : (term26 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1527198 (x : real) : (term25 x) = x.
Proof. exact (TRANS (@lem1527196 x) (@lem1527197 x)). Qed.
Lemma lem1527200 (x : real) : (term24 x) = x.
Proof. exact (TRANS (@lem1527191 x) (@lem1527198 x)). Qed.
Lemma lem1527201 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527202 (x : real) : (term34 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1527201) (@lem1527200 x)). Qed.
Lemma lem1527203 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527204 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1527202 x) (@lem1527203)). Qed.
Lemma lem1527205 (x : real) : (term36 x) = (term36 x).
Proof. exact (TRANS (@lem1527185 x) (@lem1527204 x)). Qed.
Lemma lem1527206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527207 (x : real) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem1527206) (@lem1527184 x)). Qed.
Lemma lem1527208 (x : real) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem1527207 x) (@lem1527205 x)). Qed.
Lemma lem1527209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527210 (x : real) : (term113 x) = (term113 x).
Proof. exact (MK_COMB (@lem1527209) (@lem1527163 x)). Qed.
Lemma lem1527211 (x : real) : (term115 x) = (term115 x).
Proof. exact (MK_COMB (@lem1527210 x) (@lem1527208 x)). Qed.
Lemma lem1527212 (x : real) : (term124 x) = (term125 x).
Proof. exact (@lem1483525 term2 x). Qed.
Lemma lem1527218 (x : real) : (term126 x) = (term127 x).
Proof. exact (@lem1483519 term2 x). Qed.
Lemma lem1527223 (x : real) : (term127 x) = (term28 x).
Proof. exact (@lem1483448 (term28 x)). Qed.
Lemma lem1527225 (x : real) : (term126 x) = (term28 x).
Proof. exact (TRANS (@lem1527218 x) (@lem1527223 x)). Qed.
Lemma lem1527226 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527227 (x : real) : (term128 x) = (term31 x).
Proof. exact (MK_COMB (@lem1527226) (@lem1527225 x)). Qed.
Lemma lem1527228 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527229 (x : real) : (term125 x) = (term33 x).
Proof. exact (MK_COMB (@lem1527227 x) (@lem1527228)). Qed.
Lemma lem1527230 (x : real) : (term124 x) = (term33 x).
Proof. exact (TRANS (@lem1527212 x) (@lem1527229 x)). Qed.
Lemma lem1527231 (x : real) : ((real_neg x) = term2) = ((term129 x) = term2).
Proof. exact (@lem1483529 (real_neg x) term2). Qed.
Lemma lem1527232 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527239 (x : real) : (real_neg x) = (term28 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1527240 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1527241 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1527240) (@lem1527239 x)). Qed.
Lemma lem1527242 (x : real) : (term129 x) = (term132 x).
Proof. exact (MK_COMB (@lem1527241 x) (@lem1527232)). Qed.
Lemma lem1527243 (x : real) : (term132 x) = (term133 x).
Proof. exact (@lem1483519 (term28 x) term2). Qed.
Lemma lem1527245 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527246 : term16 = term2.
Proof. exact (@lem1527245 term17). Qed.
Lemma lem1527247 (x : real) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1527248 (x : real) : (term133 x) = (term135 x).
Proof. exact (MK_COMB (@lem1527247 x) (@lem1527246)). Qed.
Lemma lem1527249 (x : real) : (term135 x) = (term28 x).
Proof. exact (@lem1483450 (term28 x)). Qed.
Lemma lem1527250 (x : real) : (term133 x) = (term28 x).
Proof. exact (TRANS (@lem1527248 x) (@lem1527249 x)). Qed.
Lemma lem1527251 (x : real) : (term132 x) = (term28 x).
Proof. exact (TRANS (@lem1527243 x) (@lem1527250 x)). Qed.
Lemma lem1527252 (x : real) : (term129 x) = (term28 x).
Proof. exact (TRANS (@lem1527242 x) (@lem1527251 x)). Qed.
Lemma lem1527253 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1527254 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1527253) (@lem1527252 x)). Qed.
Lemma lem1527255 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527256 (x : real) : ((term129 x) = term2) = ((term28 x) = term2).
Proof. exact (MK_COMB (@lem1527254 x) (@lem1527255)). Qed.
Lemma lem1527257 (x : real) : ((real_neg x) = term2) = ((term28 x) = term2).
Proof. exact (TRANS (@lem1527231 x) (@lem1527256 x)). Qed.
Lemma lem1527258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527259 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1527258) (@lem1527257 x)). Qed.
Lemma lem1527260 (x : real) : (term107 x) = (term140 x).
Proof. exact (MK_COMB (@lem1527259 x) (@lem1527205 x)). Qed.
Lemma lem1527261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527262 (x : real) : (term108 x) = (term141 x).
Proof. exact (MK_COMB (@lem1527261) (@lem1527230 x)). Qed.
Lemma lem1527263 (x : real) : (term110 x) = (term142 x).
Proof. exact (MK_COMB (@lem1527262 x) (@lem1527260 x)). Qed.
Lemma lem1527264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527265 (x : real) : (term117 x) = (term117 x).
Proof. exact (MK_COMB (@lem1527264) (@lem1527211 x)). Qed.
Lemma lem1527266 (x : real) : (term118 x) = (term143 x).
Proof. exact (MK_COMB (@lem1527265 x) (@lem1527263 x)). Qed.
Lemma lem1527278 (x : real) : (term103 x) = (term143 x).
Proof. exact (TRANS (@lem1527142 x) (@lem1527266 x)). Qed.
Lemma lem1527280 (x : real) : (term144 x) = (term145 x).
Proof. exact (eq_refl (term144 x)). Qed.
Lemma lem1527281 (x : real) : (term145 x) = (term144 x).
Proof. exact (SYM (@lem1527280 x)). Qed.
Lemma lem1527282 (x : real) : (term144 x) = (term146 x).
Proof. exact (@lem1482981 (term147 x) x). Qed.
Lemma lem1527283 (x : real) : (term145 x) = (term146 x).
Proof. exact (TRANS (@lem1527281 x) (@lem1527282 x)). Qed.
Lemma lem1527284 (x : real) : (term148 x) = (term149 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1527285 (x : real) : (term108 x) = (term108 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1527286 (x : real) : (term150 x) = (term151 x).
Proof. exact (MK_COMB (@lem1527285 x) (@lem1527284 x)). Qed.
Lemma lem1527287 (x : real) : (term152 x) = (term153 x).
Proof. exact (eq_refl (term152 x)). Qed.
Lemma lem1527288 (x : real) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1527289 (x : real) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1527288 x) (@lem1527287 x)). Qed.
Lemma lem1527290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527291 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1527290) (@lem1527289 x)). Qed.
Lemma lem1527292 (x : real) : (term146 x) = (term158 x).
Proof. exact (MK_COMB (@lem1527291 x) (@lem1527286 x)). Qed.
Lemma lem1527293 (x : real) : (term159 x) = (term159 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1527294 (x : real) : ((term145 x) = (term146 x)) = ((term145 x) = (term158 x)).
Proof. exact (MK_COMB (@lem1527293 x) (@lem1527292 x)). Qed.
Lemma lem1527295 (x : real) : (term145 x) = (term158 x).
Proof. exact (EQ_MP (@lem1527294 x) (@lem1527283 x)). Qed.
Lemma lem1527296 (x : real) : (term33 x) = (term160 x).
Proof. exact (@lem1483525 (term28 x) term2). Qed.
Lemma lem1527308 (x : real) : (term132 x) = (term133 x).
Proof. exact (@lem1483519 (term28 x) term2). Qed.
Lemma lem1527310 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527311 : term16 = term2.
Proof. exact (@lem1527310 term17). Qed.
Lemma lem1527312 (x : real) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1527313 (x : real) : (term133 x) = (term135 x).
Proof. exact (MK_COMB (@lem1527312 x) (@lem1527311)). Qed.
Lemma lem1527314 (x : real) : (term135 x) = (term28 x).
Proof. exact (@lem1483450 (term28 x)). Qed.
Lemma lem1527315 (x : real) : (term133 x) = (term28 x).
Proof. exact (TRANS (@lem1527313 x) (@lem1527314 x)). Qed.
Lemma lem1527317 (x : real) : (term132 x) = (term28 x).
Proof. exact (TRANS (@lem1527308 x) (@lem1527315 x)). Qed.
Lemma lem1527318 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527319 (x : real) : (term161 x) = (term31 x).
Proof. exact (MK_COMB (@lem1527318) (@lem1527317 x)). Qed.
Lemma lem1527320 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527321 (x : real) : (term160 x) = (term33 x).
Proof. exact (MK_COMB (@lem1527319 x) (@lem1527320)). Qed.
Lemma lem1527322 (x : real) : (term33 x) = (term33 x).
Proof. exact (TRANS (@lem1527296 x) (@lem1527321 x)). Qed.
Lemma lem1527323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527324 (x : real) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem1527323) (@lem1527184 x)). Qed.
Lemma lem1527325 (x : real) : (term153 x) = (term153 x).
Proof. exact (MK_COMB (@lem1527324 x) (@lem1527322 x)). Qed.
Lemma lem1527326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527327 (x : real) : (term113 x) = (term113 x).
Proof. exact (MK_COMB (@lem1527326) (@lem1527163 x)). Qed.
Lemma lem1527328 (x : real) : (term155 x) = (term155 x).
Proof. exact (MK_COMB (@lem1527327 x) (@lem1527325 x)). Qed.
Lemma lem1527329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527330 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1527329) (@lem1527257 x)). Qed.
Lemma lem1527331 (x : real) : (term149 x) = (term162 x).
Proof. exact (MK_COMB (@lem1527330 x) (@lem1527322 x)). Qed.
Lemma lem1527332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527333 (x : real) : (term108 x) = (term141 x).
Proof. exact (MK_COMB (@lem1527332) (@lem1527230 x)). Qed.
Lemma lem1527334 (x : real) : (term151 x) = (term163 x).
Proof. exact (MK_COMB (@lem1527333 x) (@lem1527331 x)). Qed.
Lemma lem1527335 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527336 (x : real) : (term157 x) = (term157 x).
Proof. exact (MK_COMB (@lem1527335) (@lem1527328 x)). Qed.
Lemma lem1527337 (x : real) : (term158 x) = (term164 x).
Proof. exact (MK_COMB (@lem1527336 x) (@lem1527334 x)). Qed.
Lemma lem1527349 (x : real) : (term145 x) = (term164 x).
Proof. exact (TRANS (@lem1527295 x) (@lem1527337 x)). Qed.
Lemma lem1527350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527351 (x : real) : (term165 x) = (term166 x).
Proof. exact (MK_COMB (@lem1527350) (@lem1527278 x)). Qed.
Lemma lem1527352 (x : real) : (term97 x) = (term167 x).
Proof. exact (MK_COMB (@lem1527351 x) (@lem1527349 x)). Qed.
Lemma lem1527354 (x : real) : (term168 x) = (term169 x).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1527355 (x : real) : (term169 x) = (term168 x).
Proof. exact (SYM (@lem1527354 x)). Qed.
Lemma lem1527356 (x : real) : (term168 x) = (term170 x).
Proof. exact (@lem1482981 (term171 x) x). Qed.
Lemma lem1527357 (x : real) : (term169 x) = (term170 x).
Proof. exact (TRANS (@lem1527355 x) (@lem1527356 x)). Qed.
Lemma lem1527358 (x : real) : (term172 x) = (term173 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1527359 (x : real) : (term108 x) = (term108 x).
Proof. exact (eq_refl (term108 x)). Qed.
Lemma lem1527360 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1527359 x) (@lem1527358 x)). Qed.
Lemma lem1527361 (x : real) : (term176 x) = (term177 x).
Proof. exact (eq_refl (term176 x)). Qed.
Lemma lem1527362 (x : real) : (term113 x) = (term113 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1527363 (x : real) : (term178 x) = (term179 x).
Proof. exact (MK_COMB (@lem1527362 x) (@lem1527361 x)). Qed.
Lemma lem1527364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527365 (x : real) : (term180 x) = (term181 x).
Proof. exact (MK_COMB (@lem1527364) (@lem1527363 x)). Qed.
Lemma lem1527366 (x : real) : (term170 x) = (term182 x).
Proof. exact (MK_COMB (@lem1527365 x) (@lem1527360 x)). Qed.
Lemma lem1527367 (x : real) : (term183 x) = (term183 x).
Proof. exact (eq_refl (term183 x)). Qed.
Lemma lem1527368 (x : real) : ((term169 x) = (term170 x)) = ((term169 x) = (term182 x)).
Proof. exact (MK_COMB (@lem1527367 x) (@lem1527366 x)). Qed.
Lemma lem1527369 (x : real) : (term169 x) = (term182 x).
Proof. exact (EQ_MP (@lem1527368 x) (@lem1527357 x)). Qed.
Lemma lem1527370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527371 (x : real) : (term184 x) = (term184 x).
Proof. exact (MK_COMB (@lem1527370) (@lem1527205 x)). Qed.
Lemma lem1527372 (x : real) : (term177 x) = (term177 x).
Proof. exact (MK_COMB (@lem1527371 x) (@lem1527184 x)). Qed.
Lemma lem1527373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527374 (x : real) : (term113 x) = (term113 x).
Proof. exact (MK_COMB (@lem1527373) (@lem1527163 x)). Qed.
Lemma lem1527375 (x : real) : (term179 x) = (term179 x).
Proof. exact (MK_COMB (@lem1527374 x) (@lem1527372 x)). Qed.
Lemma lem1527376 (x : real) : (term185 x) = (term186 x).
Proof. exact (@lem1483525 (real_neg x) term2). Qed.
Lemma lem1527377 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527384 (x : real) : (real_neg x) = (term28 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1527385 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1527386 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1527385) (@lem1527384 x)). Qed.
Lemma lem1527387 (x : real) : (term129 x) = (term132 x).
Proof. exact (MK_COMB (@lem1527386 x) (@lem1527377)). Qed.
Lemma lem1527388 (x : real) : (term132 x) = (term133 x).
Proof. exact (@lem1483519 (term28 x) term2). Qed.
Lemma lem1527390 (x : nat) : (term15 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1527391 : term16 = term2.
Proof. exact (@lem1527390 term17). Qed.
Lemma lem1527392 (x : real) : (term134 x) = (term134 x).
Proof. exact (eq_refl (term134 x)). Qed.
Lemma lem1527393 (x : real) : (term133 x) = (term135 x).
Proof. exact (MK_COMB (@lem1527392 x) (@lem1527391)). Qed.
Lemma lem1527394 (x : real) : (term135 x) = (term28 x).
Proof. exact (@lem1483450 (term28 x)). Qed.
Lemma lem1527395 (x : real) : (term133 x) = (term28 x).
Proof. exact (TRANS (@lem1527393 x) (@lem1527394 x)). Qed.
Lemma lem1527396 (x : real) : (term132 x) = (term28 x).
Proof. exact (TRANS (@lem1527388 x) (@lem1527395 x)). Qed.
Lemma lem1527397 (x : real) : (term129 x) = (term28 x).
Proof. exact (TRANS (@lem1527387 x) (@lem1527396 x)). Qed.
Lemma lem1527398 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527399 (x : real) : (term187 x) = (term31 x).
Proof. exact (MK_COMB (@lem1527398) (@lem1527397 x)). Qed.
Lemma lem1527400 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527401 (x : real) : (term186 x) = (term33 x).
Proof. exact (MK_COMB (@lem1527399 x) (@lem1527400)). Qed.
Lemma lem1527402 (x : real) : (term185 x) = (term33 x).
Proof. exact (TRANS (@lem1527376 x) (@lem1527401 x)). Qed.
Lemma lem1527403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527404 (x : real) : (term188 x) = (term141 x).
Proof. exact (MK_COMB (@lem1527403) (@lem1527402 x)). Qed.
Lemma lem1527405 (x : real) : (term173 x) = (term189 x).
Proof. exact (MK_COMB (@lem1527404 x) (@lem1527184 x)). Qed.
Lemma lem1527406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527407 (x : real) : (term108 x) = (term141 x).
Proof. exact (MK_COMB (@lem1527406) (@lem1527230 x)). Qed.
Lemma lem1527408 (x : real) : (term175 x) = (term190 x).
Proof. exact (MK_COMB (@lem1527407 x) (@lem1527405 x)). Qed.
Lemma lem1527409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527410 (x : real) : (term181 x) = (term181 x).
Proof. exact (MK_COMB (@lem1527409) (@lem1527375 x)). Qed.
Lemma lem1527411 (x : real) : (term182 x) = (term191 x).
Proof. exact (MK_COMB (@lem1527410 x) (@lem1527408 x)). Qed.
Lemma lem1527423 (x : real) : (term169 x) = (term191 x).
Proof. exact (TRANS (@lem1527369 x) (@lem1527411 x)). Qed.
Lemma lem1527425 (x : real) (r : real) : (term192 x r) = (term193 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1527426 (x : real) : (term52 x) = (term194 x).
Proof. exact (@lem1527425 x term2). Qed.
Lemma lem1527433 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527434 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527435 (x : real) : (term196 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1527434) (@lem1527433 x)). Qed.
Lemma lem1527436 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527437 (x : real) : (term197 x) = (term36 x).
Proof. exact (MK_COMB (@lem1527435 x) (@lem1527436)). Qed.
Lemma lem1527450 (x : real) : (term141 x) = (term141 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1527451 (x : real) : (term194 x) = (term198 x).
Proof. exact (MK_COMB (@lem1527450 x) (@lem1527437 x)). Qed.
Lemma lem1527452 (x : real) : (term52 x) = (term198 x).
Proof. exact (TRANS (@lem1527426 x) (@lem1527451 x)). Qed.
Lemma lem1527453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1527454 (x : real) : (term199 x) = (term200 x).
Proof. exact (MK_COMB (@lem1527453) (@lem1527452 x)). Qed.
Lemma lem1527455 (x : real) : (x = term2) = (x = term2).
Proof. exact (eq_refl (x = term2)). Qed.
Lemma lem1527458 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1527454 x) (@lem1527455 x)). Qed.
Lemma lem1527459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527460 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1527459) (@lem1527423 x)). Qed.
Lemma lem1527461 (x : real) : (term96 x) = (term205 x).
Proof. exact (MK_COMB (@lem1527460 x) (@lem1527458 x)). Qed.
Lemma lem1527462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1527463 (x : real) : (term98 x) = (term206 x).
Proof. exact (MK_COMB (@lem1527462) (@lem1527352 x)). Qed.
Lemma lem1527464 (x : real) : (term99 x) = (term207 x).
Proof. exact (MK_COMB (@lem1527463 x) (@lem1527461 x)). Qed.
Lemma lem1527465 (x : real) (h1 : term207 x) : term207 x.
Proof. exact (h1). Qed.
Lemma lem1527466 (x : real) (h1 : term167 x) : term167 x.
Proof. exact (h1). Qed.
Lemma lem1527467 (x : real) (h1 : term143 x) : term143 x.
Proof. exact (h1). Qed.
Lemma lem1527468 (x : real) (h1 : term115 x) : term115 x.
Proof. exact (h1). Qed.
Lemma lem1527469 (x : real) (h1 : term115 x) : term112 x.
Proof. exact (proj2 (@lem1527468 x h1)). Qed.
Lemma lem1527471 (x : real) (h1 : term115 x) : term36 x.
Proof. exact (proj2 (@lem1527469 x h1)). Qed.
Lemma lem1527472 (x : real) (h1 : term115 x) : x = term2.
Proof. exact (proj1 (@lem1527469 x h1)). Qed.
Lemma lem1527474 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527475 : term209 = term210.
Proof. exact (@lem1527474 (NUMERAL 0) term17). Qed.
Lemma lem1527476 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527477 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527478 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527477 h1) (fun h1 : term210 = True => @lem1527476)). Qed.
Lemma lem1527479 : term210 = True.
Proof. exact (EQ_MP (@lem1527478) (@lem1527476)). Qed.
Lemma lem1527480 : term209 = True.
Proof. exact (TRANS (@lem1527475) (@lem1527479)). Qed.
Lemma lem1527481 : True = term209.
Proof. exact (SYM (@lem1527480)). Qed.
Lemma lem1527482 : term209.
Proof. exact (EQ_MP (@lem1527481) (@lem0)). Qed.
Lemma lem1527483 (x : real) (h1 : term115 x) : term212 x.
Proof. exact (conj (@lem1527482) (@lem1527471 x h1)). Qed.
Lemma lem1527485 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527486 (x : real) : term214 x.
Proof. exact (@lem1527485 term215 x). Qed.
Lemma lem1527487 (x : real) (h1 : term115 x) : term197 x.
Proof. exact (@lem1527486 x (@lem1527483 x h1)). Qed.
Lemma lem1527488 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527489 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527490 (x : real) : (term196 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1527489) (@lem1527488 x)). Qed.
Lemma lem1527491 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527492 (x : real) : (term197 x) = (term36 x).
Proof. exact (MK_COMB (@lem1527490 x) (@lem1527491)). Qed.
Lemma lem1527493 (x : real) (h1 : term115 x) : term36 x.
Proof. exact (EQ_MP (@lem1527492 x) (@lem1527487 x h1)). Qed.
Lemma lem1527495 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527496 (x : real) : term216 x.
Proof. exact (@lem1527495 x). Qed.
Lemma lem1527497 (x : real) (h1 : term115 x) : term217 x.
Proof. exact (@lem1527496 x (@lem1527472 x h1)). Qed.
Lemma lem1527498 (x : real) (h1 : term115 x) : term218 x.
Proof. exact (@lem1527497 x h1 term219). Qed.
Lemma lem1527499 (x : real) : (term218 x) = ((term28 x) = term2).
Proof. exact (eq_refl (term218 x)). Qed.
Lemma lem1527506 (x : real) (h1 : term115 x) : (term28 x) = term2.
Proof. exact (EQ_MP (@lem1527499 x) (@lem1527498 x h1)). Qed.
Lemma lem1527507 (x : real) (h1 : term115 x) : term140 x.
Proof. exact (conj (@lem1527506 x h1) (@lem1527493 x h1)). Qed.
Lemma lem1527509 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527510 (x : real) : term221 x.
Proof. exact (@lem1527509 (term28 x) x). Qed.
Lemma lem1527511 (x : real) (h1 : term115 x) : term222 x.
Proof. exact (@lem1527510 x (@lem1527507 x h1)). Qed.
Lemma lem1527512 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483440 term219 x). Qed.
Lemma lem1527514 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527515 : term226 = term2.
Proof. exact (@lem1527514 term17). Qed.
Lemma lem1527516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527517 : term227 = term228.
Proof. exact (MK_COMB (@lem1527516) (@lem1527515)). Qed.
Lemma lem1527518 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527519 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527517) (@lem1527518 x)). Qed.
Lemma lem1527520 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1527512 x) (@lem1527519 x)). Qed.
Lemma lem1527521 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527522 (x : real) : (term223 x) = term2.
Proof. exact (TRANS (@lem1527520 x) (@lem1527521 x)). Qed.
Lemma lem1527523 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527524 (x : real) : (term230 x) = term231.
Proof. exact (MK_COMB (@lem1527523) (@lem1527522 x)). Qed.
Lemma lem1527525 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527526 (x : real) : (term222 x) = term232.
Proof. exact (MK_COMB (@lem1527524 x) (@lem1527525)). Qed.
Lemma lem1527527 (x : real) (h1 : term115 x) : term232.
Proof. exact (EQ_MP (@lem1527526 x) (@lem1527511 x h1)). Qed.
Lemma lem1527529 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527530 : term232 = term233.
Proof. exact (@lem1527529 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527531 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527532 : term232 = False.
Proof. exact (TRANS (@lem1527530) (@lem1527531)). Qed.
Lemma lem1527533 (x : real) (h1 : term115 x) : False.
Proof. exact (EQ_MP (@lem1527532) (@lem1527527 x h1)). Qed.
Lemma lem1527534 (x : real) (h1 : term142 x) : term142 x.
Proof. exact (h1). Qed.
Lemma lem1527535 (x : real) (h1 : term142 x) : term140 x.
Proof. exact (proj2 (@lem1527534 x h1)). Qed.
Lemma lem1527537 (x : real) (h1 : term142 x) : term36 x.
Proof. exact (proj2 (@lem1527535 x h1)). Qed.
Lemma lem1527538 (x : real) (h1 : term142 x) : (term28 x) = term2.
Proof. exact (proj1 (@lem1527535 x h1)). Qed.
Lemma lem1527540 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527541 : term209 = term210.
Proof. exact (@lem1527540 (NUMERAL 0) term17). Qed.
Lemma lem1527542 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527543 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527544 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527543 h1) (fun h1 : term210 = True => @lem1527542)). Qed.
Lemma lem1527545 : term210 = True.
Proof. exact (EQ_MP (@lem1527544) (@lem1527542)). Qed.
Lemma lem1527546 : term209 = True.
Proof. exact (TRANS (@lem1527541) (@lem1527545)). Qed.
Lemma lem1527547 : True = term209.
Proof. exact (SYM (@lem1527546)). Qed.
Lemma lem1527548 : term209.
Proof. exact (EQ_MP (@lem1527547) (@lem0)). Qed.
Lemma lem1527549 (x : real) (h1 : term142 x) : term212 x.
Proof. exact (conj (@lem1527548) (@lem1527537 x h1)). Qed.
Lemma lem1527551 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527552 (x : real) : term214 x.
Proof. exact (@lem1527551 term215 x). Qed.
Lemma lem1527553 (x : real) (h1 : term142 x) : term197 x.
Proof. exact (@lem1527552 x (@lem1527549 x h1)). Qed.
Lemma lem1527554 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527555 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527556 (x : real) : (term196 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1527555) (@lem1527554 x)). Qed.
Lemma lem1527557 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527558 (x : real) : (term197 x) = (term36 x).
Proof. exact (MK_COMB (@lem1527556 x) (@lem1527557)). Qed.
Lemma lem1527559 (x : real) (h1 : term142 x) : term36 x.
Proof. exact (EQ_MP (@lem1527558 x) (@lem1527553 x h1)). Qed.
Lemma lem1527561 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527562 (x : real) : term234 x.
Proof. exact (@lem1527561 (term28 x)). Qed.
Lemma lem1527563 (x : real) (h1 : term142 x) : term235 x.
Proof. exact (@lem1527562 x (@lem1527538 x h1)). Qed.
Lemma lem1527564 (x : real) (h1 : term142 x) : term236 x.
Proof. exact (@lem1527563 x h1 term215). Qed.
Lemma lem1527565 (x : real) : (term236 x) = ((term237 x) = term2).
Proof. exact (eq_refl (term236 x)). Qed.
Lemma lem1527566 (x : real) (h1 : term142 x) : (term237 x) = term2.
Proof. exact (EQ_MP (@lem1527565 x) (@lem1527564 x h1)). Qed.
Lemma lem1527567 (x : real) : (term237 x) = (term28 x).
Proof. exact (@lem1483460 (term28 x)). Qed.
Lemma lem1527568 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1527569 (x : real) : (term238 x) = (term137 x).
Proof. exact (MK_COMB (@lem1527568) (@lem1527567 x)). Qed.
Lemma lem1527570 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527571 (x : real) : ((term237 x) = term2) = ((term28 x) = term2).
Proof. exact (MK_COMB (@lem1527569 x) (@lem1527570)). Qed.
Lemma lem1527572 (x : real) (h1 : term142 x) : (term28 x) = term2.
Proof. exact (EQ_MP (@lem1527571 x) (@lem1527566 x h1)). Qed.
Lemma lem1527573 (x : real) (h1 : term142 x) : term140 x.
Proof. exact (conj (@lem1527572 x h1) (@lem1527559 x h1)). Qed.
Lemma lem1527575 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527576 (x : real) : term221 x.
Proof. exact (@lem1527575 (term28 x) x). Qed.
Lemma lem1527577 (x : real) (h1 : term142 x) : term222 x.
Proof. exact (@lem1527576 x (@lem1527573 x h1)). Qed.
Lemma lem1527578 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483440 term219 x). Qed.
Lemma lem1527580 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527581 : term226 = term2.
Proof. exact (@lem1527580 term17). Qed.
Lemma lem1527582 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527583 : term227 = term228.
Proof. exact (MK_COMB (@lem1527582) (@lem1527581)). Qed.
Lemma lem1527584 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527585 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527583) (@lem1527584 x)). Qed.
Lemma lem1527586 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1527578 x) (@lem1527585 x)). Qed.
Lemma lem1527587 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527588 (x : real) : (term223 x) = term2.
Proof. exact (TRANS (@lem1527586 x) (@lem1527587 x)). Qed.
Lemma lem1527589 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527590 (x : real) : (term230 x) = term231.
Proof. exact (MK_COMB (@lem1527589) (@lem1527588 x)). Qed.
Lemma lem1527591 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527592 (x : real) : (term222 x) = term232.
Proof. exact (MK_COMB (@lem1527590 x) (@lem1527591)). Qed.
Lemma lem1527593 (x : real) (h1 : term142 x) : term232.
Proof. exact (EQ_MP (@lem1527592 x) (@lem1527577 x h1)). Qed.
Lemma lem1527595 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527596 : term232 = term233.
Proof. exact (@lem1527595 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527597 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527598 : term232 = False.
Proof. exact (TRANS (@lem1527596) (@lem1527597)). Qed.
Lemma lem1527599 (x : real) (h1 : term142 x) : False.
Proof. exact (EQ_MP (@lem1527598) (@lem1527593 x h1)). Qed.
Lemma lem1527600 (x : real) (h1 : term143 x) : False.
Proof. exact (or_elim (@lem1527467 x h1) (fun h0 : term115 x => @lem1527533 x h0) (fun h0 : term142 x => @lem1527599 x h0)). Qed.
Lemma lem1527601 (x : real) (h1 : term164 x) : term164 x.
Proof. exact (h1). Qed.
Lemma lem1527602 (x : real) (h1 : term155 x) : term155 x.
Proof. exact (h1). Qed.
Lemma lem1527603 (x : real) (h1 : term155 x) : term153 x.
Proof. exact (proj2 (@lem1527602 x h1)). Qed.
Lemma lem1527605 (x : real) (h1 : term155 x) : term33 x.
Proof. exact (proj2 (@lem1527603 x h1)). Qed.
Lemma lem1527606 (x : real) (h1 : term155 x) : x = term2.
Proof. exact (proj1 (@lem1527603 x h1)). Qed.
Lemma lem1527608 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527609 : term209 = term210.
Proof. exact (@lem1527608 (NUMERAL 0) term17). Qed.
Lemma lem1527610 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527611 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527612 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527611 h1) (fun h1 : term210 = True => @lem1527610)). Qed.
Lemma lem1527613 : term210 = True.
Proof. exact (EQ_MP (@lem1527612) (@lem1527610)). Qed.
Lemma lem1527614 : term209 = True.
Proof. exact (TRANS (@lem1527609) (@lem1527613)). Qed.
Lemma lem1527615 : True = term209.
Proof. exact (SYM (@lem1527614)). Qed.
Lemma lem1527616 : term209.
Proof. exact (EQ_MP (@lem1527615) (@lem0)). Qed.
Lemma lem1527617 (x : real) (h1 : term155 x) : term239 x.
Proof. exact (conj (@lem1527616) (@lem1527605 x h1)). Qed.
Lemma lem1527619 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527620 (x : real) : term240 x.
Proof. exact (@lem1527619 term215 (term28 x)). Qed.
Lemma lem1527621 (x : real) (h1 : term155 x) : term241 x.
Proof. exact (@lem1527620 x (@lem1527617 x h1)). Qed.
Lemma lem1527622 (x : real) : (term237 x) = (term28 x).
Proof. exact (@lem1483460 (term28 x)). Qed.
Lemma lem1527623 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527624 (x : real) : (term242 x) = (term31 x).
Proof. exact (MK_COMB (@lem1527623) (@lem1527622 x)). Qed.
Lemma lem1527625 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527626 (x : real) : (term241 x) = (term33 x).
Proof. exact (MK_COMB (@lem1527624 x) (@lem1527625)). Qed.
Lemma lem1527627 (x : real) (h1 : term155 x) : term33 x.
Proof. exact (EQ_MP (@lem1527626 x) (@lem1527621 x h1)). Qed.
Lemma lem1527629 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527630 (x : real) : term216 x.
Proof. exact (@lem1527629 x). Qed.
Lemma lem1527631 (x : real) (h1 : term155 x) : term217 x.
Proof. exact (@lem1527630 x (@lem1527606 x h1)). Qed.
Lemma lem1527632 (x : real) (h1 : term155 x) : term243 x.
Proof. exact (@lem1527631 x h1 term215). Qed.
Lemma lem1527633 (x : real) : (term243 x) = ((term195 x) = term2).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1527634 (x : real) (h1 : term155 x) : (term195 x) = term2.
Proof. exact (EQ_MP (@lem1527633 x) (@lem1527632 x h1)). Qed.
Lemma lem1527635 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527636 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1527637 (x : real) : (term244 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1527636) (@lem1527635 x)). Qed.
Lemma lem1527638 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527639 (x : real) : ((term195 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1527637 x) (@lem1527638)). Qed.
Lemma lem1527640 (x : real) (h1 : term155 x) : x = term2.
Proof. exact (EQ_MP (@lem1527639 x) (@lem1527634 x h1)). Qed.
Lemma lem1527641 (x : real) (h1 : term155 x) : term153 x.
Proof. exact (conj (@lem1527640 x h1) (@lem1527627 x h1)). Qed.
Lemma lem1527643 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527644 (x : real) : term245 x.
Proof. exact (@lem1527643 x (term28 x)). Qed.
Lemma lem1527645 (x : real) (h1 : term155 x) : term246 x.
Proof. exact (@lem1527644 x (@lem1527641 x h1)). Qed.
Lemma lem1527646 (x : real) : (term247 x) = (term224 x).
Proof. exact (@lem1483442 term219 x). Qed.
Lemma lem1527648 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527649 : term226 = term2.
Proof. exact (@lem1527648 term17). Qed.
Lemma lem1527650 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527651 : term227 = term228.
Proof. exact (MK_COMB (@lem1527650) (@lem1527649)). Qed.
Lemma lem1527652 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527653 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527651) (@lem1527652 x)). Qed.
Lemma lem1527654 (x : real) : (term247 x) = (term229 x).
Proof. exact (TRANS (@lem1527646 x) (@lem1527653 x)). Qed.
Lemma lem1527655 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527656 (x : real) : (term247 x) = term2.
Proof. exact (TRANS (@lem1527654 x) (@lem1527655 x)). Qed.
Lemma lem1527657 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527658 (x : real) : (term248 x) = term231.
Proof. exact (MK_COMB (@lem1527657) (@lem1527656 x)). Qed.
Lemma lem1527659 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527660 (x : real) : (term246 x) = term232.
Proof. exact (MK_COMB (@lem1527658 x) (@lem1527659)). Qed.
Lemma lem1527661 (x : real) (h1 : term155 x) : term232.
Proof. exact (EQ_MP (@lem1527660 x) (@lem1527645 x h1)). Qed.
Lemma lem1527663 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527664 : term232 = term233.
Proof. exact (@lem1527663 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527665 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527666 : term232 = False.
Proof. exact (TRANS (@lem1527664) (@lem1527665)). Qed.
Lemma lem1527667 (x : real) (h1 : term155 x) : False.
Proof. exact (EQ_MP (@lem1527666) (@lem1527661 x h1)). Qed.
Lemma lem1527668 (x : real) (h1 : term163 x) : term163 x.
Proof. exact (h1). Qed.
Lemma lem1527669 (x : real) (h1 : term163 x) : term162 x.
Proof. exact (proj2 (@lem1527668 x h1)). Qed.
Lemma lem1527671 (x : real) (h1 : term163 x) : term33 x.
Proof. exact (proj2 (@lem1527669 x h1)). Qed.
Lemma lem1527672 (x : real) (h1 : term163 x) : (term28 x) = term2.
Proof. exact (proj1 (@lem1527669 x h1)). Qed.
Lemma lem1527674 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527675 : term209 = term210.
Proof. exact (@lem1527674 (NUMERAL 0) term17). Qed.
Lemma lem1527676 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527677 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527678 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527677 h1) (fun h1 : term210 = True => @lem1527676)). Qed.
Lemma lem1527679 : term210 = True.
Proof. exact (EQ_MP (@lem1527678) (@lem1527676)). Qed.
Lemma lem1527680 : term209 = True.
Proof. exact (TRANS (@lem1527675) (@lem1527679)). Qed.
Lemma lem1527681 : True = term209.
Proof. exact (SYM (@lem1527680)). Qed.
Lemma lem1527682 : term209.
Proof. exact (EQ_MP (@lem1527681) (@lem0)). Qed.
Lemma lem1527683 (x : real) (h1 : term163 x) : term239 x.
Proof. exact (conj (@lem1527682) (@lem1527671 x h1)). Qed.
Lemma lem1527685 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527686 (x : real) : term240 x.
Proof. exact (@lem1527685 term215 (term28 x)). Qed.
Lemma lem1527687 (x : real) (h1 : term163 x) : term241 x.
Proof. exact (@lem1527686 x (@lem1527683 x h1)). Qed.
Lemma lem1527688 (x : real) : (term237 x) = (term28 x).
Proof. exact (@lem1483460 (term28 x)). Qed.
Lemma lem1527689 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527690 (x : real) : (term242 x) = (term31 x).
Proof. exact (MK_COMB (@lem1527689) (@lem1527688 x)). Qed.
Lemma lem1527691 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527692 (x : real) : (term241 x) = (term33 x).
Proof. exact (MK_COMB (@lem1527690 x) (@lem1527691)). Qed.
Lemma lem1527693 (x : real) (h1 : term163 x) : term33 x.
Proof. exact (EQ_MP (@lem1527692 x) (@lem1527687 x h1)). Qed.
Lemma lem1527695 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527696 (x : real) : term234 x.
Proof. exact (@lem1527695 (term28 x)). Qed.
Lemma lem1527697 (x : real) (h1 : term163 x) : term235 x.
Proof. exact (@lem1527696 x (@lem1527672 x h1)). Qed.
Lemma lem1527698 (x : real) (h1 : term163 x) : term249 x.
Proof. exact (@lem1527697 x h1 term219). Qed.
Lemma lem1527699 (x : real) : (term249 x) = ((term250 x) = term2).
Proof. exact (eq_refl (term249 x)). Qed.
Lemma lem1527700 (x : real) (h1 : term163 x) : (term250 x) = term2.
Proof. exact (EQ_MP (@lem1527699 x) (@lem1527698 x h1)). Qed.
Lemma lem1527701 (x : real) : (term250 x) = (term251 x).
Proof. exact (@lem1483476 term219 term219 x). Qed.
Lemma lem1527703 (m : nat) (n : nat) : (term252 m n) = (term253 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1527704 : term254 = term255.
Proof. exact (@lem1527703 term17 term17). Qed.
Lemma lem1527705 : (term256 = (BIT1 0)) = (term257 = term17).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1527706 : term257 = term17.
Proof. exact (EQ_MP (@lem1527705) (@lem940073)). Qed.
Lemma lem1527707 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1527708 : term255 = term215.
Proof. exact (MK_COMB (@lem1527707) (@lem1527706)). Qed.
Lemma lem1527709 : term254 = term215.
Proof. exact (TRANS (@lem1527704) (@lem1527708)). Qed.
Lemma lem1527710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527711 : term258 = term259.
Proof. exact (MK_COMB (@lem1527710) (@lem1527709)). Qed.
Lemma lem1527712 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527713 (x : real) : (term251 x) = (term195 x).
Proof. exact (MK_COMB (@lem1527711) (@lem1527712 x)). Qed.
Lemma lem1527714 (x : real) : (term250 x) = (term195 x).
Proof. exact (TRANS (@lem1527701 x) (@lem1527713 x)). Qed.
Lemma lem1527715 (x : real) : (term195 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1527716 (x : real) : (term250 x) = x.
Proof. exact (TRANS (@lem1527714 x) (@lem1527715 x)). Qed.
Lemma lem1527717 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1527718 (x : real) : (term260 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1527717) (@lem1527716 x)). Qed.
Lemma lem1527719 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527720 (x : real) : ((term250 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1527718 x) (@lem1527719)). Qed.
Lemma lem1527721 (x : real) (h1 : term163 x) : x = term2.
Proof. exact (EQ_MP (@lem1527720 x) (@lem1527700 x h1)). Qed.
Lemma lem1527722 (x : real) (h1 : term163 x) : term153 x.
Proof. exact (conj (@lem1527721 x h1) (@lem1527693 x h1)). Qed.
Lemma lem1527724 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527725 (x : real) : term245 x.
Proof. exact (@lem1527724 x (term28 x)). Qed.
Lemma lem1527726 (x : real) (h1 : term163 x) : term246 x.
Proof. exact (@lem1527725 x (@lem1527722 x h1)). Qed.
Lemma lem1527727 (x : real) : (term247 x) = (term224 x).
Proof. exact (@lem1483442 term219 x). Qed.
Lemma lem1527729 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527730 : term226 = term2.
Proof. exact (@lem1527729 term17). Qed.
Lemma lem1527731 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527732 : term227 = term228.
Proof. exact (MK_COMB (@lem1527731) (@lem1527730)). Qed.
Lemma lem1527733 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527734 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527732) (@lem1527733 x)). Qed.
Lemma lem1527735 (x : real) : (term247 x) = (term229 x).
Proof. exact (TRANS (@lem1527727 x) (@lem1527734 x)). Qed.
Lemma lem1527736 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527737 (x : real) : (term247 x) = term2.
Proof. exact (TRANS (@lem1527735 x) (@lem1527736 x)). Qed.
Lemma lem1527738 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527739 (x : real) : (term248 x) = term231.
Proof. exact (MK_COMB (@lem1527738) (@lem1527737 x)). Qed.
Lemma lem1527740 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527741 (x : real) : (term246 x) = term232.
Proof. exact (MK_COMB (@lem1527739 x) (@lem1527740)). Qed.
Lemma lem1527742 (x : real) (h1 : term163 x) : term232.
Proof. exact (EQ_MP (@lem1527741 x) (@lem1527726 x h1)). Qed.
Lemma lem1527744 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527745 : term232 = term233.
Proof. exact (@lem1527744 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527746 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527747 : term232 = False.
Proof. exact (TRANS (@lem1527745) (@lem1527746)). Qed.
Lemma lem1527748 (x : real) (h1 : term163 x) : False.
Proof. exact (EQ_MP (@lem1527747) (@lem1527742 x h1)). Qed.
Lemma lem1527749 (x : real) (h1 : term164 x) : False.
Proof. exact (or_elim (@lem1527601 x h1) (fun h0 : term155 x => @lem1527667 x h0) (fun h0 : term163 x => @lem1527748 x h0)). Qed.
Lemma lem1527750 (x : real) (h1 : term167 x) : False.
Proof. exact (or_elim (@lem1527466 x h1) (fun h0 : term143 x => @lem1527600 x h0) (fun h0 : term164 x => @lem1527749 x h0)). Qed.
Lemma lem1527751 (x : real) (h1 : term205 x) : term205 x.
Proof. exact (h1). Qed.
Lemma lem1527752 (x : real) (h1 : term191 x) : term191 x.
Proof. exact (h1). Qed.
Lemma lem1527753 (x : real) (h1 : term179 x) : term179 x.
Proof. exact (h1). Qed.
Lemma lem1527754 (x : real) (h1 : term179 x) : term177 x.
Proof. exact (proj2 (@lem1527753 x h1)). Qed.
Lemma lem1527756 (x : real) (h1 : term179 x) : x = term2.
Proof. exact (proj2 (@lem1527754 x h1)). Qed.
Lemma lem1527757 (x : real) (h1 : term179 x) : term36 x.
Proof. exact (proj1 (@lem1527754 x h1)). Qed.
Lemma lem1527759 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527760 : term209 = term210.
Proof. exact (@lem1527759 (NUMERAL 0) term17). Qed.
Lemma lem1527761 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527762 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527763 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527762 h1) (fun h1 : term210 = True => @lem1527761)). Qed.
Lemma lem1527764 : term210 = True.
Proof. exact (EQ_MP (@lem1527763) (@lem1527761)). Qed.
Lemma lem1527765 : term209 = True.
Proof. exact (TRANS (@lem1527760) (@lem1527764)). Qed.
Lemma lem1527766 : True = term209.
Proof. exact (SYM (@lem1527765)). Qed.
Lemma lem1527767 : term209.
Proof. exact (EQ_MP (@lem1527766) (@lem0)). Qed.
Lemma lem1527768 (x : real) (h1 : term179 x) : term212 x.
Proof. exact (conj (@lem1527767) (@lem1527757 x h1)). Qed.
Lemma lem1527770 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527771 (x : real) : term214 x.
Proof. exact (@lem1527770 term215 x). Qed.
Lemma lem1527772 (x : real) (h1 : term179 x) : term197 x.
Proof. exact (@lem1527771 x (@lem1527768 x h1)). Qed.
Lemma lem1527773 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527774 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527775 (x : real) : (term196 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1527774) (@lem1527773 x)). Qed.
Lemma lem1527776 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527777 (x : real) : (term197 x) = (term36 x).
Proof. exact (MK_COMB (@lem1527775 x) (@lem1527776)). Qed.
Lemma lem1527778 (x : real) (h1 : term179 x) : term36 x.
Proof. exact (EQ_MP (@lem1527777 x) (@lem1527772 x h1)). Qed.
Lemma lem1527780 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527781 (x : real) : term216 x.
Proof. exact (@lem1527780 x). Qed.
Lemma lem1527782 (x : real) (h1 : term179 x) : term217 x.
Proof. exact (@lem1527781 x (@lem1527756 x h1)). Qed.
Lemma lem1527783 (x : real) (h1 : term179 x) : term218 x.
Proof. exact (@lem1527782 x h1 term219). Qed.
Lemma lem1527784 (x : real) : (term218 x) = ((term28 x) = term2).
Proof. exact (eq_refl (term218 x)). Qed.
Lemma lem1527791 (x : real) (h1 : term179 x) : (term28 x) = term2.
Proof. exact (EQ_MP (@lem1527784 x) (@lem1527783 x h1)). Qed.
Lemma lem1527792 (x : real) (h1 : term179 x) : term140 x.
Proof. exact (conj (@lem1527791 x h1) (@lem1527778 x h1)). Qed.
Lemma lem1527794 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527795 (x : real) : term221 x.
Proof. exact (@lem1527794 (term28 x) x). Qed.
Lemma lem1527796 (x : real) (h1 : term179 x) : term222 x.
Proof. exact (@lem1527795 x (@lem1527792 x h1)). Qed.
Lemma lem1527797 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483440 term219 x). Qed.
Lemma lem1527799 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527800 : term226 = term2.
Proof. exact (@lem1527799 term17). Qed.
Lemma lem1527801 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527802 : term227 = term228.
Proof. exact (MK_COMB (@lem1527801) (@lem1527800)). Qed.
Lemma lem1527803 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527804 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527802) (@lem1527803 x)). Qed.
Lemma lem1527805 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1527797 x) (@lem1527804 x)). Qed.
Lemma lem1527806 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527807 (x : real) : (term223 x) = term2.
Proof. exact (TRANS (@lem1527805 x) (@lem1527806 x)). Qed.
Lemma lem1527808 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527809 (x : real) : (term230 x) = term231.
Proof. exact (MK_COMB (@lem1527808) (@lem1527807 x)). Qed.
Lemma lem1527810 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527811 (x : real) : (term222 x) = term232.
Proof. exact (MK_COMB (@lem1527809 x) (@lem1527810)). Qed.
Lemma lem1527812 (x : real) (h1 : term179 x) : term232.
Proof. exact (EQ_MP (@lem1527811 x) (@lem1527796 x h1)). Qed.
Lemma lem1527814 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527815 : term232 = term233.
Proof. exact (@lem1527814 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527816 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527817 : term232 = False.
Proof. exact (TRANS (@lem1527815) (@lem1527816)). Qed.
Lemma lem1527818 (x : real) (h1 : term179 x) : False.
Proof. exact (EQ_MP (@lem1527817) (@lem1527812 x h1)). Qed.
Lemma lem1527819 (x : real) (h1 : term190 x) : term190 x.
Proof. exact (h1). Qed.
Lemma lem1527820 (x : real) (h1 : term190 x) : term189 x.
Proof. exact (proj2 (@lem1527819 x h1)). Qed.
Lemma lem1527822 (x : real) (h1 : term190 x) : x = term2.
Proof. exact (proj2 (@lem1527820 x h1)). Qed.
Lemma lem1527823 (x : real) (h1 : term190 x) : term33 x.
Proof. exact (proj1 (@lem1527820 x h1)). Qed.
Lemma lem1527825 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527826 : term209 = term210.
Proof. exact (@lem1527825 (NUMERAL 0) term17). Qed.
Lemma lem1527827 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527828 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527829 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527828 h1) (fun h1 : term210 = True => @lem1527827)). Qed.
Lemma lem1527830 : term210 = True.
Proof. exact (EQ_MP (@lem1527829) (@lem1527827)). Qed.
Lemma lem1527831 : term209 = True.
Proof. exact (TRANS (@lem1527826) (@lem1527830)). Qed.
Lemma lem1527832 : True = term209.
Proof. exact (SYM (@lem1527831)). Qed.
Lemma lem1527833 : term209.
Proof. exact (EQ_MP (@lem1527832) (@lem0)). Qed.
Lemma lem1527834 (x : real) (h1 : term190 x) : term239 x.
Proof. exact (conj (@lem1527833) (@lem1527823 x h1)). Qed.
Lemma lem1527836 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527837 (x : real) : term240 x.
Proof. exact (@lem1527836 term215 (term28 x)). Qed.
Lemma lem1527838 (x : real) (h1 : term190 x) : term241 x.
Proof. exact (@lem1527837 x (@lem1527834 x h1)). Qed.
Lemma lem1527839 (x : real) : (term237 x) = (term28 x).
Proof. exact (@lem1483460 (term28 x)). Qed.
Lemma lem1527840 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527841 (x : real) : (term242 x) = (term31 x).
Proof. exact (MK_COMB (@lem1527840) (@lem1527839 x)). Qed.
Lemma lem1527842 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527843 (x : real) : (term241 x) = (term33 x).
Proof. exact (MK_COMB (@lem1527841 x) (@lem1527842)). Qed.
Lemma lem1527844 (x : real) (h1 : term190 x) : term33 x.
Proof. exact (EQ_MP (@lem1527843 x) (@lem1527838 x h1)). Qed.
Lemma lem1527846 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527847 (x : real) : term216 x.
Proof. exact (@lem1527846 x). Qed.
Lemma lem1527848 (x : real) (h1 : term190 x) : term217 x.
Proof. exact (@lem1527847 x (@lem1527822 x h1)). Qed.
Lemma lem1527849 (x : real) (h1 : term190 x) : term243 x.
Proof. exact (@lem1527848 x h1 term215). Qed.
Lemma lem1527850 (x : real) : (term243 x) = ((term195 x) = term2).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1527851 (x : real) (h1 : term190 x) : (term195 x) = term2.
Proof. exact (EQ_MP (@lem1527850 x) (@lem1527849 x h1)). Qed.
Lemma lem1527852 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527853 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1527854 (x : real) : (term244 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1527853) (@lem1527852 x)). Qed.
Lemma lem1527855 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527856 (x : real) : ((term195 x) = term2) = (x = term2).
Proof. exact (MK_COMB (@lem1527854 x) (@lem1527855)). Qed.
Lemma lem1527857 (x : real) (h1 : term190 x) : x = term2.
Proof. exact (EQ_MP (@lem1527856 x) (@lem1527851 x h1)). Qed.
Lemma lem1527858 (x : real) (h1 : term190 x) : term153 x.
Proof. exact (conj (@lem1527857 x h1) (@lem1527844 x h1)). Qed.
Lemma lem1527860 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527861 (x : real) : term245 x.
Proof. exact (@lem1527860 x (term28 x)). Qed.
Lemma lem1527862 (x : real) (h1 : term190 x) : term246 x.
Proof. exact (@lem1527861 x (@lem1527858 x h1)). Qed.
Lemma lem1527863 (x : real) : (term247 x) = (term224 x).
Proof. exact (@lem1483442 term219 x). Qed.
Lemma lem1527865 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527866 : term226 = term2.
Proof. exact (@lem1527865 term17). Qed.
Lemma lem1527867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527868 : term227 = term228.
Proof. exact (MK_COMB (@lem1527867) (@lem1527866)). Qed.
Lemma lem1527869 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527870 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527868) (@lem1527869 x)). Qed.
Lemma lem1527871 (x : real) : (term247 x) = (term229 x).
Proof. exact (TRANS (@lem1527863 x) (@lem1527870 x)). Qed.
Lemma lem1527872 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527873 (x : real) : (term247 x) = term2.
Proof. exact (TRANS (@lem1527871 x) (@lem1527872 x)). Qed.
Lemma lem1527874 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527875 (x : real) : (term248 x) = term231.
Proof. exact (MK_COMB (@lem1527874) (@lem1527873 x)). Qed.
Lemma lem1527876 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527877 (x : real) : (term246 x) = term232.
Proof. exact (MK_COMB (@lem1527875 x) (@lem1527876)). Qed.
Lemma lem1527878 (x : real) (h1 : term190 x) : term232.
Proof. exact (EQ_MP (@lem1527877 x) (@lem1527862 x h1)). Qed.
Lemma lem1527880 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527881 : term232 = term233.
Proof. exact (@lem1527880 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527882 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527883 : term232 = False.
Proof. exact (TRANS (@lem1527881) (@lem1527882)). Qed.
Lemma lem1527884 (x : real) (h1 : term190 x) : False.
Proof. exact (EQ_MP (@lem1527883) (@lem1527878 x h1)). Qed.
Lemma lem1527885 (x : real) (h1 : term191 x) : False.
Proof. exact (or_elim (@lem1527752 x h1) (fun h0 : term179 x => @lem1527818 x h0) (fun h0 : term190 x => @lem1527884 x h0)). Qed.
Lemma lem1527886 (x : real) (h1 : term202 x) : term202 x.
Proof. exact (h1). Qed.
Lemma lem1527887 (x : real) (h1 : term202 x) : x = term2.
Proof. exact (proj2 (@lem1527886 x h1)). Qed.
Lemma lem1527888 (x : real) (h1 : term202 x) : term198 x.
Proof. exact (proj1 (@lem1527886 x h1)). Qed.
Lemma lem1527889 (x : real) (h1 : term202 x) : term36 x.
Proof. exact (proj2 (@lem1527888 x h1)). Qed.
Lemma lem1527892 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527893 : term209 = term210.
Proof. exact (@lem1527892 (NUMERAL 0) term17). Qed.
Lemma lem1527894 : term211 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1527895 (h1 : term211 = (BIT1 0)) : term210 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1527896 : (term211 = (BIT1 0)) = (term210 = True).
Proof. exact (prop_ext (fun h1 : term211 = (BIT1 0) => @lem1527895 h1) (fun h1 : term210 = True => @lem1527894)). Qed.
Lemma lem1527897 : term210 = True.
Proof. exact (EQ_MP (@lem1527896) (@lem1527894)). Qed.
Lemma lem1527898 : term209 = True.
Proof. exact (TRANS (@lem1527893) (@lem1527897)). Qed.
Lemma lem1527899 : True = term209.
Proof. exact (SYM (@lem1527898)). Qed.
Lemma lem1527900 : term209.
Proof. exact (EQ_MP (@lem1527899) (@lem0)). Qed.
Lemma lem1527901 (x : real) (h1 : term202 x) : term212 x.
Proof. exact (conj (@lem1527900) (@lem1527889 x h1)). Qed.
Lemma lem1527903 (x : real) (y : real) : term213 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1527904 (x : real) : term214 x.
Proof. exact (@lem1527903 term215 x). Qed.
Lemma lem1527905 (x : real) (h1 : term202 x) : term197 x.
Proof. exact (@lem1527904 x (@lem1527901 x h1)). Qed.
Lemma lem1527906 (x : real) : (term195 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1527907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527908 (x : real) : (term196 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1527907) (@lem1527906 x)). Qed.
Lemma lem1527909 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527910 (x : real) : (term197 x) = (term36 x).
Proof. exact (MK_COMB (@lem1527908 x) (@lem1527909)). Qed.
Lemma lem1527911 (x : real) (h1 : term202 x) : term36 x.
Proof. exact (EQ_MP (@lem1527910 x) (@lem1527905 x h1)). Qed.
Lemma lem1527913 (y : real) : term216 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1527914 (x : real) : term216 x.
Proof. exact (@lem1527913 x). Qed.
Lemma lem1527915 (x : real) (h1 : term202 x) : term217 x.
Proof. exact (@lem1527914 x (@lem1527887 x h1)). Qed.
Lemma lem1527916 (x : real) (h1 : term202 x) : term218 x.
Proof. exact (@lem1527915 x h1 term219). Qed.
Lemma lem1527917 (x : real) : (term218 x) = ((term28 x) = term2).
Proof. exact (eq_refl (term218 x)). Qed.
Lemma lem1527924 (x : real) (h1 : term202 x) : (term28 x) = term2.
Proof. exact (EQ_MP (@lem1527917 x) (@lem1527916 x h1)). Qed.
Lemma lem1527925 (x : real) (h1 : term202 x) : term140 x.
Proof. exact (conj (@lem1527924 x h1) (@lem1527911 x h1)). Qed.
Lemma lem1527927 (x : real) (y : real) : term220 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1527928 (x : real) : term221 x.
Proof. exact (@lem1527927 (term28 x) x). Qed.
Lemma lem1527929 (x : real) (h1 : term202 x) : term222 x.
Proof. exact (@lem1527928 x (@lem1527925 x h1)). Qed.
Lemma lem1527930 (x : real) : (term223 x) = (term224 x).
Proof. exact (@lem1483440 term219 x). Qed.
Lemma lem1527932 (m : nat) : (term225 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1527933 : term226 = term2.
Proof. exact (@lem1527932 term17). Qed.
Lemma lem1527934 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1527935 : term227 = term228.
Proof. exact (MK_COMB (@lem1527934) (@lem1527933)). Qed.
Lemma lem1527936 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1527937 (x : real) : (term224 x) = (term229 x).
Proof. exact (MK_COMB (@lem1527935) (@lem1527936 x)). Qed.
Lemma lem1527938 (x : real) : (term223 x) = (term229 x).
Proof. exact (TRANS (@lem1527930 x) (@lem1527937 x)). Qed.
Lemma lem1527939 (x : real) : (term229 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1527940 (x : real) : (term223 x) = term2.
Proof. exact (TRANS (@lem1527938 x) (@lem1527939 x)). Qed.
Lemma lem1527941 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1527942 (x : real) : (term230 x) = term231.
Proof. exact (MK_COMB (@lem1527941) (@lem1527940 x)). Qed.
Lemma lem1527943 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1527944 (x : real) : (term222 x) = term232.
Proof. exact (MK_COMB (@lem1527942 x) (@lem1527943)). Qed.
Lemma lem1527945 (x : real) (h1 : term202 x) : term232.
Proof. exact (EQ_MP (@lem1527944 x) (@lem1527929 x h1)). Qed.
Lemma lem1527947 (n : nat) (m : nat) : (term208 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1527948 : term232 = term233.
Proof. exact (@lem1527947 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1527949 : term233 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1527950 : term232 = False.
Proof. exact (TRANS (@lem1527948) (@lem1527949)). Qed.
Lemma lem1527951 (x : real) (h1 : term202 x) : False.
Proof. exact (EQ_MP (@lem1527950) (@lem1527945 x h1)). Qed.
Lemma lem1527952 (x : real) (h1 : term205 x) : False.
Proof. exact (or_elim (@lem1527751 x h1) (fun h0 : term191 x => @lem1527885 x h0) (fun h0 : term202 x => @lem1527951 x h0)). Qed.
Lemma lem1527953 (x : real) (h1 : term207 x) : False.
Proof. exact (or_elim (@lem1527465 x h1) (fun h0 : term167 x => @lem1527750 x h0) (fun h0 : term205 x => @lem1527952 x h0)). Qed.
Lemma lem1527954 (x : real) (h1 : term99 x) : term99 x.
Proof. exact (h1). Qed.
Lemma lem1527955 (x : real) (h1 : term99 x) : term207 x.
Proof. exact (EQ_MP (@lem1527464 x) (@lem1527954 x h1)). Qed.
Lemma lem1527956 (x : real) (h1 : term99 x) : (term207 x) = False.
Proof. exact (prop_ext (fun h2 : term207 x => @lem1527953 x h2) (fun h2 : False => @lem1527955 x h1)). Qed.
Lemma lem1527957 (x : real) (h1 : term99 x) : False.
Proof. exact (EQ_MP (@lem1527956 x h1) (@lem1527955 x h1)). Qed.
Lemma lem1527958 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem1527959 (h1 : term101) : False.
Proof. exact (ex_elim (@lem1527958 h1) (fun x : real => fun h0 : term100 x => @lem1527957 x h0)). Qed.
Lemma lem1527960 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1527961 (h1 : term5) : term101.
Proof. exact (EQ_MP (@lem1527125) (@lem1527960 h1)). Qed.
Lemma lem1527962 (h1 : term5) : term101 = False.
Proof. exact (prop_ext (fun h2 : term101 => @lem1527959 h2) (fun h2 : False => @lem1527961 h1)). Qed.
Lemma lem1527963 (h1 : term5) : False.
Proof. exact (EQ_MP (@lem1527962 h1) (@lem1527961 h1)). Qed.
Lemma lem1527964 : term261.
Proof. exact (fun h0 : term5 => @lem1527963 h0). Qed.
Lemma lem1527965 : term262.
Proof. exact (@lem1386578 term263). Qed.
Lemma lem1527966 : term263.
Proof. exact (@lem1527965 (@lem1527964)). Qed.
