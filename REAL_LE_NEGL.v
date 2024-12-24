Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_NEGL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem1505841 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1505842 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1505843 : term6 = term7.
Proof. exact (@lem1505842 term8). Qed.
Lemma lem1505844 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1505845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1505846 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1505845) (@lem1505844 x)). Qed.
Lemma lem1505847 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1505846 x) (@lem1505841 x)). Qed.
Lemma lem1505848 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1505847 x)). Qed.
Lemma lem1505849 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505850 : term7 = term13.
Proof. exact (MK_COMB (@lem1505849) (@lem1505848)). Qed.
Lemma lem1505852 : term6 = term13.
Proof. exact (TRANS (@lem1505843) (@lem1505850)). Qed.
Lemma lem1505869 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1505870 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1505869 x)). Qed.
Lemma lem1505871 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505872 : term13 = term13.
Proof. exact (MK_COMB (@lem1505871) (@lem1505870)). Qed.
Lemma lem1505873 : term6 = term13.
Proof. exact (TRANS (@lem1505852) (@lem1505872)). Qed.
Lemma lem1505874 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483523 x (real_neg x)). Qed.
Lemma lem1505881 (x : real) : (real_neg x) = (term15 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1505884 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1505885 (x : real) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1505884 x) (@lem1505881 x)). Qed.
Lemma lem1505886 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem1483519 x (term15 x)). Qed.
Lemma lem1505887 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483476 term21 term21 x). Qed.
Lemma lem1505889 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1505890 : term24 = term25.
Proof. exact (@lem1505889 term26 term26). Qed.
Lemma lem1505891 : (term27 = (BIT1 0)) = (term28 = term26).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1505892 : term28 = term26.
Proof. exact (EQ_MP (@lem1505891) (@lem940073)). Qed.
Lemma lem1505893 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505894 : term25 = term29.
Proof. exact (MK_COMB (@lem1505893) (@lem1505892)). Qed.
Lemma lem1505895 : term24 = term29.
Proof. exact (TRANS (@lem1505890) (@lem1505894)). Qed.
Lemma lem1505896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505897 : term30 = term31.
Proof. exact (MK_COMB (@lem1505896) (@lem1505895)). Qed.
Lemma lem1505898 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505899 (x : real) : (term20 x) = (term32 x).
Proof. exact (MK_COMB (@lem1505897) (@lem1505898 x)). Qed.
Lemma lem1505900 (x : real) : (term19 x) = (term32 x).
Proof. exact (TRANS (@lem1505887 x) (@lem1505899 x)). Qed.
Lemma lem1505901 (x : real) : (term32 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1505902 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1505900 x) (@lem1505901 x)). Qed.
Lemma lem1505903 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1505904 (x : real) : (term18 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1505903 x) (@lem1505902 x)). Qed.
Lemma lem1505905 (x : real) : (real_add x x) = (term33 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1505906 : term34 = term35.
Proof. exact (@lem1367770 term26 term26). Qed.
Lemma lem1505907 : term36 = term37.
Proof. exact (@lem706885). Qed.
Lemma lem1505908 : (term36 = term37) = (term38 = term39).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term37). Qed.
Lemma lem1505909 : term38 = term39.
Proof. exact (EQ_MP (@lem1505908) (@lem1505907)). Qed.
Lemma lem1505910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505911 : term35 = term40.
Proof. exact (MK_COMB (@lem1505910) (@lem1505909)). Qed.
Lemma lem1505912 : term34 = term40.
Proof. exact (TRANS (@lem1505906) (@lem1505911)). Qed.
Lemma lem1505913 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505914 : term41 = term42.
Proof. exact (MK_COMB (@lem1505913) (@lem1505912)). Qed.
Lemma lem1505915 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505916 (x : real) : (term33 x) = (term43 x).
Proof. exact (MK_COMB (@lem1505914) (@lem1505915 x)). Qed.
Lemma lem1505917 (x : real) : (real_add x x) = (term43 x).
Proof. exact (TRANS (@lem1505905 x) (@lem1505916 x)). Qed.
Lemma lem1505918 (x : real) : (term18 x) = (term43 x).
Proof. exact (TRANS (@lem1505904 x) (@lem1505917 x)). Qed.
Lemma lem1505919 (x : real) : (term17 x) = (term43 x).
Proof. exact (TRANS (@lem1505886 x) (@lem1505918 x)). Qed.
Lemma lem1505920 (x : real) : (term16 x) = (term43 x).
Proof. exact (TRANS (@lem1505885 x) (@lem1505919 x)). Qed.
Lemma lem1505921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1505922 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1505921) (@lem1505920 x)). Qed.
Lemma lem1505923 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1505924 (x : real) : (term14 x) = (term47 x).
Proof. exact (MK_COMB (@lem1505922 x) (@lem1505923)). Qed.
Lemma lem1505925 (x : real) : (term2 x) = (term47 x).
Proof. exact (TRANS (@lem1505874 x) (@lem1505924 x)). Qed.
Lemma lem1505926 (x : real) : (term48 x) = (term49 x).
Proof. exact (@lem1483533 term46 x). Qed.
Lemma lem1505932 (x : real) : (term50 x) = (term51 x).
Proof. exact (@lem1483519 term46 x). Qed.
Lemma lem1505937 (x : real) : (term51 x) = (term15 x).
Proof. exact (@lem1483448 (term15 x)). Qed.
Lemma lem1505939 (x : real) : (term50 x) = (term15 x).
Proof. exact (TRANS (@lem1505932 x) (@lem1505937 x)). Qed.
Lemma lem1505940 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505941 (x : real) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1505940) (@lem1505939 x)). Qed.
Lemma lem1505942 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1505943 (x : real) : (term49 x) = (term54 x).
Proof. exact (MK_COMB (@lem1505941 x) (@lem1505942)). Qed.
Lemma lem1505944 (x : real) : (term48 x) = (term54 x).
Proof. exact (TRANS (@lem1505926 x) (@lem1505943 x)). Qed.
Lemma lem1505945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1505946 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1505945) (@lem1505925 x)). Qed.
Lemma lem1505947 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1505946 x) (@lem1505944 x)). Qed.
Lemma lem1505948 (x : real) : (term59 x) = (term60 x).
Proof. exact (@lem1483533 (real_neg x) x). Qed.
Lemma lem1505949 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505956 (x : real) : (real_neg x) = (term15 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1505957 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1505958 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1505957) (@lem1505956 x)). Qed.
Lemma lem1505959 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1505958 x) (@lem1505949 x)). Qed.
Lemma lem1505960 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1483519 (term15 x) x). Qed.
Lemma lem1505964 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1483438 term21 term21 x). Qed.
Lemma lem1505965 : term67 = term68.
Proof. exact (@lem1367763 term26 term26). Qed.
Lemma lem1505966 : term36 = term37.
Proof. exact (@lem706885). Qed.
Lemma lem1505967 : (term36 = term37) = (term38 = term39).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term37). Qed.
Lemma lem1505968 : term38 = term39.
Proof. exact (EQ_MP (@lem1505967) (@lem1505966)). Qed.
Lemma lem1505969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1505970 : term35 = term40.
Proof. exact (MK_COMB (@lem1505969) (@lem1505968)). Qed.
Lemma lem1505971 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1505972 : term68 = term69.
Proof. exact (MK_COMB (@lem1505971) (@lem1505970)). Qed.
Lemma lem1505973 : term67 = term69.
Proof. exact (TRANS (@lem1505965) (@lem1505972)). Qed.
Lemma lem1505974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505975 : term70 = term71.
Proof. exact (MK_COMB (@lem1505974) (@lem1505973)). Qed.
Lemma lem1505976 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505977 (x : real) : (term66 x) = (term72 x).
Proof. exact (MK_COMB (@lem1505975) (@lem1505976 x)). Qed.
Lemma lem1505979 (x : real) : (term65 x) = (term72 x).
Proof. exact (TRANS (@lem1505964 x) (@lem1505977 x)). Qed.
Lemma lem1505980 (x : real) : (term64 x) = (term72 x).
Proof. exact (TRANS (@lem1505960 x) (@lem1505979 x)). Qed.
Lemma lem1505981 (x : real) : (term63 x) = (term72 x).
Proof. exact (TRANS (@lem1505959 x) (@lem1505980 x)). Qed.
Lemma lem1505982 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505983 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1505982) (@lem1505981 x)). Qed.
Lemma lem1505984 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1505985 (x : real) : (term60 x) = (term75 x).
Proof. exact (MK_COMB (@lem1505983 x) (@lem1505984)). Qed.
Lemma lem1505986 (x : real) : (term59 x) = (term75 x).
Proof. exact (TRANS (@lem1505948 x) (@lem1505985 x)). Qed.
Lemma lem1505987 (x : real) : (term3 x) = (term76 x).
Proof. exact (@lem1483523 x term46). Qed.
Lemma lem1505993 (x : real) : (term77 x) = (term78 x).
Proof. exact (@lem1483519 x term46). Qed.
Lemma lem1505995 (x : nat) : (term79 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1505996 : term80 = term46.
Proof. exact (@lem1505995 term26). Qed.
Lemma lem1505997 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1505998 (x : real) : (term78 x) = (term81 x).
Proof. exact (MK_COMB (@lem1505997 x) (@lem1505996)). Qed.
Lemma lem1505999 (x : real) : (term81 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1506000 (x : real) : (term78 x) = x.
Proof. exact (TRANS (@lem1505998 x) (@lem1505999 x)). Qed.
Lemma lem1506002 (x : real) : (term77 x) = x.
Proof. exact (TRANS (@lem1505993 x) (@lem1506000 x)). Qed.
Lemma lem1506003 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1506004 (x : real) : (term82 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1506003) (@lem1506002 x)). Qed.
Lemma lem1506005 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1506006 (x : real) : (term76 x) = (term83 x).
Proof. exact (MK_COMB (@lem1506004 x) (@lem1506005)). Qed.
Lemma lem1506007 (x : real) : (term3 x) = (term83 x).
Proof. exact (TRANS (@lem1505987 x) (@lem1506006 x)). Qed.
Lemma lem1506008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1506009 (x : real) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1506008) (@lem1505986 x)). Qed.
Lemma lem1506010 (x : real) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1506009 x) (@lem1506007 x)). Qed.
Lemma lem1506011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506012 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1506011) (@lem1505947 x)). Qed.
Lemma lem1506013 (x : real) : (term1 x) = (term90 x).
Proof. exact (MK_COMB (@lem1506012 x) (@lem1506010 x)). Qed.
Lemma lem1506014 : term12 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506013 x)). Qed.
Lemma lem1506015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506016 : term13 = term92.
Proof. exact (MK_COMB (@lem1506015) (@lem1506014)). Qed.
Lemma lem1506017 : term6 = term92.
Proof. exact (TRANS (@lem1505873) (@lem1506016)). Qed.
Lemma lem1506019 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1506020 (P : real -> Prop) (Q : real -> Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem1506019 real P Q). Qed.
Lemma lem1506021 : term97 = term98.
Proof. exact (@lem1506020 term99 term100). Qed.
Lemma lem1506022 (x : real) : (term101 x) = (term58 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506024 (x : real) : (term102 x) = (term89 x).
Proof. exact (MK_COMB (@lem1506023) (@lem1506022 x)). Qed.
Lemma lem1506025 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506026 (x : real) : (term104 x) = (term90 x).
Proof. exact (MK_COMB (@lem1506024 x) (@lem1506025 x)). Qed.
Lemma lem1506027 : term105 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506026 x)). Qed.
Lemma lem1506028 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506029 : term97 = term92.
Proof. exact (MK_COMB (@lem1506028) (@lem1506027)). Qed.
Lemma lem1506030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1506031 : term106 = term107.
Proof. exact (MK_COMB (@lem1506030) (@lem1506029)). Qed.
Lemma lem1506032 (x : real) : (term101 x) = (term58 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506033 : term108 = term99.
Proof. exact (fun_ext (fun x : real => @lem1506032 x)). Qed.
Lemma lem1506034 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506035 : term109 = term110.
Proof. exact (MK_COMB (@lem1506034) (@lem1506033)). Qed.
Lemma lem1506036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506037 : term111 = term112.
Proof. exact (MK_COMB (@lem1506036) (@lem1506035)). Qed.
Lemma lem1506038 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506039 : term113 = term100.
Proof. exact (fun_ext (fun x : real => @lem1506038 x)). Qed.
Lemma lem1506040 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506041 : term114 = term115.
Proof. exact (MK_COMB (@lem1506040) (@lem1506039)). Qed.
Lemma lem1506042 : term98 = term116.
Proof. exact (MK_COMB (@lem1506037) (@lem1506041)). Qed.
Lemma lem1506043 : (term97 = term98) = (term92 = term116).
Proof. exact (MK_COMB (@lem1506031) (@lem1506042)). Qed.
Lemma lem1506044 : term92 = term116.
Proof. exact (EQ_MP (@lem1506043) (@lem1506021)). Qed.
Lemma lem1506142 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1506143 (P : real -> Prop) (Q : real -> Prop) : (term96 P Q) = (term95 P Q).
Proof. exact (@lem1506142 real P Q). Qed.
Lemma lem1506144 : term98 = term97.
Proof. exact (@lem1506143 term99 term100). Qed.
Lemma lem1506145 (x : real) : (term101 x) = (term58 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506146 : term108 = term99.
Proof. exact (fun_ext (fun x : real => @lem1506145 x)). Qed.
Lemma lem1506147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506148 : term109 = term110.
Proof. exact (MK_COMB (@lem1506147) (@lem1506146)). Qed.
Lemma lem1506149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506150 : term111 = term112.
Proof. exact (MK_COMB (@lem1506149) (@lem1506148)). Qed.
Lemma lem1506151 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506152 : term113 = term100.
Proof. exact (fun_ext (fun x : real => @lem1506151 x)). Qed.
Lemma lem1506153 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506154 : term114 = term115.
Proof. exact (MK_COMB (@lem1506153) (@lem1506152)). Qed.
Lemma lem1506155 : term98 = term116.
Proof. exact (MK_COMB (@lem1506150) (@lem1506154)). Qed.
Lemma lem1506156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1506157 : term117 = term118.
Proof. exact (MK_COMB (@lem1506156) (@lem1506155)). Qed.
Lemma lem1506158 (x : real) : (term101 x) = (term58 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506160 (x : real) : (term102 x) = (term89 x).
Proof. exact (MK_COMB (@lem1506159) (@lem1506158 x)). Qed.
Lemma lem1506161 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506162 (x : real) : (term104 x) = (term90 x).
Proof. exact (MK_COMB (@lem1506160 x) (@lem1506161 x)). Qed.
Lemma lem1506163 : term105 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506162 x)). Qed.
Lemma lem1506164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506165 : term97 = term92.
Proof. exact (MK_COMB (@lem1506164) (@lem1506163)). Qed.
Lemma lem1506166 : (term98 = term97) = (term116 = term92).
Proof. exact (MK_COMB (@lem1506157) (@lem1506165)). Qed.
Lemma lem1506167 : term116 = term92.
Proof. exact (EQ_MP (@lem1506166) (@lem1506144)). Qed.
Lemma lem1506168 : term92 = term92.
Proof. exact (TRANS (@lem1506044) (@lem1506167)). Qed.
Lemma lem1506171 : term6 = term92.
Proof. exact (TRANS (@lem1506017) (@lem1506168)). Qed.
Lemma lem1506188 (x : real) : (term90 x) = (term90 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1506189 : term91 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506188 x)). Qed.
Lemma lem1506190 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506191 : term92 = term92.
Proof. exact (MK_COMB (@lem1506190) (@lem1506189)). Qed.
Lemma lem1506192 : term6 = term92.
Proof. exact (TRANS (@lem1506171) (@lem1506191)). Qed.
Lemma lem1506202 (x : real) (h1 : term90 x) : term90 x.
Proof. exact (h1). Qed.
Lemma lem1506203 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1506204 (x : real) (h1 : term58 x) : term54 x.
Proof. exact (proj2 (@lem1506203 x h1)). Qed.
Lemma lem1506205 (x : real) (h1 : term58 x) : term47 x.
Proof. exact (proj1 (@lem1506203 x h1)). Qed.
Lemma lem1506207 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506208 : term120 = term121.
Proof. exact (@lem1506207 (NUMERAL 0) term26). Qed.
Lemma lem1506209 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1506210 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1506211 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem1506210 h1) (fun h1 : term121 = True => @lem1506209)). Qed.
Lemma lem1506212 : term121 = True.
Proof. exact (EQ_MP (@lem1506211) (@lem1506209)). Qed.
Lemma lem1506213 : term120 = True.
Proof. exact (TRANS (@lem1506208) (@lem1506212)). Qed.
Lemma lem1506214 : True = term120.
Proof. exact (SYM (@lem1506213)). Qed.
Lemma lem1506215 : term120.
Proof. exact (EQ_MP (@lem1506214) (@lem0)). Qed.
Lemma lem1506216 (x : real) (h1 : term58 x) : term123 x.
Proof. exact (conj (@lem1506215) (@lem1506205 x h1)). Qed.
Lemma lem1506218 (x : real) (y : real) : term124 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1506219 (x : real) : term125 x.
Proof. exact (@lem1506218 term29 (term43 x)). Qed.
Lemma lem1506220 (x : real) (h1 : term58 x) : term126 x.
Proof. exact (@lem1506219 x (@lem1506216 x h1)). Qed.
Lemma lem1506221 (x : real) : (term127 x) = (term43 x).
Proof. exact (@lem1483460 (term43 x)). Qed.
Lemma lem1506222 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1506223 (x : real) : (term128 x) = (term45 x).
Proof. exact (MK_COMB (@lem1506222) (@lem1506221 x)). Qed.
Lemma lem1506224 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1506225 (x : real) : (term126 x) = (term47 x).
Proof. exact (MK_COMB (@lem1506223 x) (@lem1506224)). Qed.
Lemma lem1506226 (x : real) (h1 : term58 x) : term47 x.
Proof. exact (EQ_MP (@lem1506225 x) (@lem1506220 x h1)). Qed.
Lemma lem1506228 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506229 : term129 = term130.
Proof. exact (@lem1506228 (NUMERAL 0) term39). Qed.
Lemma lem1506230 : term131 = term37.
Proof. exact (@lem912803). Qed.
Lemma lem1506231 (h1 : term131 = term37) : term130 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term37 h1). Qed.
Lemma lem1506232 : (term131 = term37) = (term130 = True).
Proof. exact (prop_ext (fun h1 : term131 = term37 => @lem1506231 h1) (fun h1 : term130 = True => @lem1506230)). Qed.
Lemma lem1506233 : term130 = True.
Proof. exact (EQ_MP (@lem1506232) (@lem1506230)). Qed.
Lemma lem1506234 : term129 = True.
Proof. exact (TRANS (@lem1506229) (@lem1506233)). Qed.
Lemma lem1506235 : True = term129.
Proof. exact (SYM (@lem1506234)). Qed.
Lemma lem1506236 : term129.
Proof. exact (EQ_MP (@lem1506235) (@lem0)). Qed.
Lemma lem1506237 (x : real) (h1 : term58 x) : term132 x.
Proof. exact (conj (@lem1506236) (@lem1506204 x h1)). Qed.
Lemma lem1506239 (x : real) (y : real) : term133 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1506240 (x : real) : term134 x.
Proof. exact (@lem1506239 term40 (term15 x)). Qed.
Lemma lem1506241 (x : real) (h1 : term58 x) : term135 x.
Proof. exact (@lem1506240 x (@lem1506237 x h1)). Qed.
Lemma lem1506242 (x : real) : (term136 x) = (term137 x).
Proof. exact (@lem1483476 term40 term21 x). Qed.
Lemma lem1506244 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1506245 : term140 = term141.
Proof. exact (@lem1506244 term39 term26). Qed.
Lemma lem1506246 : term142 = term37.
Proof. exact (@lem996237 term37). Qed.
Lemma lem1506247 : (term142 = term37) = (term143 = term39).
Proof. exact (@lem1007663 term37 (BIT1 0) term37). Qed.
Lemma lem1506248 : term143 = term39.
Proof. exact (EQ_MP (@lem1506247) (@lem1506246)). Qed.
Lemma lem1506249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1506250 : term144 = term40.
Proof. exact (MK_COMB (@lem1506249) (@lem1506248)). Qed.
Lemma lem1506251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1506252 : term141 = term69.
Proof. exact (MK_COMB (@lem1506251) (@lem1506250)). Qed.
Lemma lem1506253 : term140 = term69.
Proof. exact (TRANS (@lem1506245) (@lem1506252)). Qed.
Lemma lem1506254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506255 : term145 = term71.
Proof. exact (MK_COMB (@lem1506254) (@lem1506253)). Qed.
Lemma lem1506256 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506257 (x : real) : (term137 x) = (term72 x).
Proof. exact (MK_COMB (@lem1506255) (@lem1506256 x)). Qed.
Lemma lem1506258 (x : real) : (term136 x) = (term72 x).
Proof. exact (TRANS (@lem1506242 x) (@lem1506257 x)). Qed.
Lemma lem1506259 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506260 (x : real) : (term146 x) = (term74 x).
Proof. exact (MK_COMB (@lem1506259) (@lem1506258 x)). Qed.
Lemma lem1506261 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1506262 (x : real) : (term135 x) = (term75 x).
Proof. exact (MK_COMB (@lem1506260 x) (@lem1506261)). Qed.
Lemma lem1506263 (x : real) (h1 : term58 x) : term75 x.
Proof. exact (EQ_MP (@lem1506262 x) (@lem1506241 x h1)). Qed.
Lemma lem1506264 (x : real) (h1 : term58 x) : term147 x.
Proof. exact (conj (@lem1506263 x h1) (@lem1506226 x h1)). Qed.
Lemma lem1506266 (x : real) (y : real) : term148 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1506267 (x : real) : term149 x.
Proof. exact (@lem1506266 (term72 x) (term43 x)). Qed.
Lemma lem1506268 (x : real) (h1 : term58 x) : term150 x.
Proof. exact (@lem1506267 x (@lem1506264 x h1)). Qed.
Lemma lem1506269 (x : real) : (term151 x) = (term152 x).
Proof. exact (@lem1483438 term69 term40 x). Qed.
Lemma lem1506271 (m : nat) : (term153 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1506272 : term154 = term46.
Proof. exact (@lem1506271 term39). Qed.
Lemma lem1506273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506274 : term155 = term156.
Proof. exact (MK_COMB (@lem1506273) (@lem1506272)). Qed.
Lemma lem1506275 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506276 (x : real) : (term152 x) = (term157 x).
Proof. exact (MK_COMB (@lem1506274) (@lem1506275 x)). Qed.
Lemma lem1506277 (x : real) : (term151 x) = (term157 x).
Proof. exact (TRANS (@lem1506269 x) (@lem1506276 x)). Qed.
Lemma lem1506278 (x : real) : (term157 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1506279 (x : real) : (term151 x) = term46.
Proof. exact (TRANS (@lem1506277 x) (@lem1506278 x)). Qed.
Lemma lem1506280 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506281 (x : real) : (term158 x) = term159.
Proof. exact (MK_COMB (@lem1506280) (@lem1506279 x)). Qed.
Lemma lem1506282 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1506283 (x : real) : (term150 x) = term160.
Proof. exact (MK_COMB (@lem1506281 x) (@lem1506282)). Qed.
Lemma lem1506284 (x : real) (h1 : term58 x) : term160.
Proof. exact (EQ_MP (@lem1506283 x) (@lem1506268 x h1)). Qed.
Lemma lem1506286 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506287 : term160 = term161.
Proof. exact (@lem1506286 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1506288 : term161 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1506289 : term160 = False.
Proof. exact (TRANS (@lem1506287) (@lem1506288)). Qed.
Lemma lem1506290 (x : real) (h1 : term58 x) : False.
Proof. exact (EQ_MP (@lem1506289) (@lem1506284 x h1)). Qed.
Lemma lem1506291 (x : real) (h1 : term87 x) : term87 x.
Proof. exact (h1). Qed.
Lemma lem1506292 (x : real) (h1 : term87 x) : term83 x.
Proof. exact (proj2 (@lem1506291 x h1)). Qed.
Lemma lem1506293 (x : real) (h1 : term87 x) : term75 x.
Proof. exact (proj1 (@lem1506291 x h1)). Qed.
Lemma lem1506295 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506296 : term129 = term130.
Proof. exact (@lem1506295 (NUMERAL 0) term39). Qed.
Lemma lem1506297 : term131 = term37.
Proof. exact (@lem912803). Qed.
Lemma lem1506298 (h1 : term131 = term37) : term130 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term37 h1). Qed.
Lemma lem1506299 : (term131 = term37) = (term130 = True).
Proof. exact (prop_ext (fun h1 : term131 = term37 => @lem1506298 h1) (fun h1 : term130 = True => @lem1506297)). Qed.
Lemma lem1506300 : term130 = True.
Proof. exact (EQ_MP (@lem1506299) (@lem1506297)). Qed.
Lemma lem1506301 : term129 = True.
Proof. exact (TRANS (@lem1506296) (@lem1506300)). Qed.
Lemma lem1506302 : True = term129.
Proof. exact (SYM (@lem1506301)). Qed.
Lemma lem1506303 : term129.
Proof. exact (EQ_MP (@lem1506302) (@lem0)). Qed.
Lemma lem1506304 (x : real) (h1 : term87 x) : term162 x.
Proof. exact (conj (@lem1506303) (@lem1506292 x h1)). Qed.
Lemma lem1506306 (x : real) (y : real) : term124 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1506307 (x : real) : term163 x.
Proof. exact (@lem1506306 term40 x). Qed.
Lemma lem1506314 (x : real) (h1 : term87 x) : term47 x.
Proof. exact (@lem1506307 x (@lem1506304 x h1)). Qed.
Lemma lem1506316 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506317 : term120 = term121.
Proof. exact (@lem1506316 (NUMERAL 0) term26). Qed.
Lemma lem1506318 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1506319 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1506320 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem1506319 h1) (fun h1 : term121 = True => @lem1506318)). Qed.
Lemma lem1506321 : term121 = True.
Proof. exact (EQ_MP (@lem1506320) (@lem1506318)). Qed.
Lemma lem1506322 : term120 = True.
Proof. exact (TRANS (@lem1506317) (@lem1506321)). Qed.
Lemma lem1506323 : True = term120.
Proof. exact (SYM (@lem1506322)). Qed.
Lemma lem1506324 : term120.
Proof. exact (EQ_MP (@lem1506323) (@lem0)). Qed.
Lemma lem1506325 (x : real) (h1 : term87 x) : term164 x.
Proof. exact (conj (@lem1506324) (@lem1506293 x h1)). Qed.
Lemma lem1506327 (x : real) (y : real) : term133 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1506328 (x : real) : term165 x.
Proof. exact (@lem1506327 term29 (term72 x)). Qed.
Lemma lem1506329 (x : real) (h1 : term87 x) : term166 x.
Proof. exact (@lem1506328 x (@lem1506325 x h1)). Qed.
Lemma lem1506330 (x : real) : (term167 x) = (term72 x).
Proof. exact (@lem1483460 (term72 x)). Qed.
Lemma lem1506331 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506332 (x : real) : (term168 x) = (term74 x).
Proof. exact (MK_COMB (@lem1506331) (@lem1506330 x)). Qed.
Lemma lem1506333 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1506334 (x : real) : (term166 x) = (term75 x).
Proof. exact (MK_COMB (@lem1506332 x) (@lem1506333)). Qed.
Lemma lem1506335 (x : real) (h1 : term87 x) : term75 x.
Proof. exact (EQ_MP (@lem1506334 x) (@lem1506329 x h1)). Qed.
Lemma lem1506336 (x : real) (h1 : term87 x) : term147 x.
Proof. exact (conj (@lem1506335 x h1) (@lem1506314 x h1)). Qed.
Lemma lem1506338 (x : real) (y : real) : term148 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1506339 (x : real) : term149 x.
Proof. exact (@lem1506338 (term72 x) (term43 x)). Qed.
Lemma lem1506340 (x : real) (h1 : term87 x) : term150 x.
Proof. exact (@lem1506339 x (@lem1506336 x h1)). Qed.
Lemma lem1506341 (x : real) : (term151 x) = (term152 x).
Proof. exact (@lem1483438 term69 term40 x). Qed.
Lemma lem1506343 (m : nat) : (term153 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1506344 : term154 = term46.
Proof. exact (@lem1506343 term39). Qed.
Lemma lem1506345 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506346 : term155 = term156.
Proof. exact (MK_COMB (@lem1506345) (@lem1506344)). Qed.
Lemma lem1506347 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506348 (x : real) : (term152 x) = (term157 x).
Proof. exact (MK_COMB (@lem1506346) (@lem1506347 x)). Qed.
Lemma lem1506349 (x : real) : (term151 x) = (term157 x).
Proof. exact (TRANS (@lem1506341 x) (@lem1506348 x)). Qed.
Lemma lem1506350 (x : real) : (term157 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1506351 (x : real) : (term151 x) = term46.
Proof. exact (TRANS (@lem1506349 x) (@lem1506350 x)). Qed.
Lemma lem1506352 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506353 (x : real) : (term158 x) = term159.
Proof. exact (MK_COMB (@lem1506352) (@lem1506351 x)). Qed.
Lemma lem1506354 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1506355 (x : real) : (term150 x) = term160.
Proof. exact (MK_COMB (@lem1506353 x) (@lem1506354)). Qed.
Lemma lem1506356 (x : real) (h1 : term87 x) : term160.
Proof. exact (EQ_MP (@lem1506355 x) (@lem1506340 x h1)). Qed.
Lemma lem1506358 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506359 : term160 = term161.
Proof. exact (@lem1506358 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1506360 : term161 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1506361 : term160 = False.
Proof. exact (TRANS (@lem1506359) (@lem1506360)). Qed.
Lemma lem1506362 (x : real) (h1 : term87 x) : False.
Proof. exact (EQ_MP (@lem1506361) (@lem1506356 x h1)). Qed.
Lemma lem1506363 (x : real) (h1 : term90 x) : False.
Proof. exact (or_elim (@lem1506202 x h1) (fun h0 : term58 x => @lem1506290 x h0) (fun h0 : term87 x => @lem1506362 x h0)). Qed.
Lemma lem1506365 (x : real) (h1 : term90 x) : term90 x.
Proof. exact (h1). Qed.
Lemma lem1506366 (x : real) (h1 : term90 x) : (term90 x) = False.
Proof. exact (prop_ext (fun h2 : term90 x => @lem1506363 x h1) (fun h2 : False => @lem1506365 x h1)). Qed.
Lemma lem1506367 (x : real) (h1 : term90 x) : False.
Proof. exact (EQ_MP (@lem1506366 x h1) (@lem1506365 x h1)). Qed.
Lemma lem1506368 (h1 : term92) : term92.
Proof. exact (h1). Qed.
Lemma lem1506369 (h1 : term92) : False.
Proof. exact (ex_elim (@lem1506368 h1) (fun x : real => fun h0 : term91 x => @lem1506367 x h0)). Qed.
Lemma lem1506370 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1506371 (h1 : term6) : term92.
Proof. exact (EQ_MP (@lem1506192) (@lem1506370 h1)). Qed.
Lemma lem1506372 (h1 : term6) : term92 = False.
Proof. exact (prop_ext (fun h2 : term92 => @lem1506369 h2) (fun h2 : False => @lem1506371 h1)). Qed.
Lemma lem1506373 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1506372 h1) (@lem1506371 h1)). Qed.
Lemma lem1506374 : term169.
Proof. exact (fun h0 : term6 => @lem1506373 h0). Qed.
Lemma lem1506375 : term170.
Proof. exact (@lem1386578 term171). Qed.
Lemma lem1506376 : term171.
Proof. exact (@lem1506375 (@lem1506374)). Qed.
