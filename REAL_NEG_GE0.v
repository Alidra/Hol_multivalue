Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_GE0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
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
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1497787 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1497788 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1497789 : term6 = term7.
Proof. exact (@lem1497788 term8). Qed.
Lemma lem1497790 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1497791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1497792 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1497791) (@lem1497790 x)). Qed.
Lemma lem1497793 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1497792 x) (@lem1497787 x)). Qed.
Lemma lem1497794 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1497793 x)). Qed.
Lemma lem1497795 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497796 : term7 = term13.
Proof. exact (MK_COMB (@lem1497795) (@lem1497794)). Qed.
Lemma lem1497798 : term6 = term13.
Proof. exact (TRANS (@lem1497789) (@lem1497796)). Qed.
Lemma lem1497815 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1497816 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1497815 x)). Qed.
Lemma lem1497817 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497818 : term13 = term13.
Proof. exact (MK_COMB (@lem1497817) (@lem1497816)). Qed.
Lemma lem1497819 : term6 = term13.
Proof. exact (TRANS (@lem1497798) (@lem1497818)). Qed.
Lemma lem1497820 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483523 (real_neg x) term15). Qed.
Lemma lem1497821 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497828 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1497829 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1497830 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1497829) (@lem1497828 x)). Qed.
Lemma lem1497831 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1497830 x) (@lem1497821)). Qed.
Lemma lem1497832 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1483519 (term16 x) term15). Qed.
Lemma lem1497834 (x : nat) : (term22 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1497835 : term23 = term15.
Proof. exact (@lem1497834 term24). Qed.
Lemma lem1497836 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1497837 (x : real) : (term21 x) = (term26 x).
Proof. exact (MK_COMB (@lem1497836 x) (@lem1497835)). Qed.
Lemma lem1497838 (x : real) : (term26 x) = (term16 x).
Proof. exact (@lem1483450 (term16 x)). Qed.
Lemma lem1497839 (x : real) : (term21 x) = (term16 x).
Proof. exact (TRANS (@lem1497837 x) (@lem1497838 x)). Qed.
Lemma lem1497840 (x : real) : (term20 x) = (term16 x).
Proof. exact (TRANS (@lem1497832 x) (@lem1497839 x)). Qed.
Lemma lem1497841 (x : real) : (term19 x) = (term16 x).
Proof. exact (TRANS (@lem1497831 x) (@lem1497840 x)). Qed.
Lemma lem1497842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497843 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1497842) (@lem1497841 x)). Qed.
Lemma lem1497844 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497845 (x : real) : (term14 x) = (term29 x).
Proof. exact (MK_COMB (@lem1497843 x) (@lem1497844)). Qed.
Lemma lem1497846 (x : real) : (term2 x) = (term29 x).
Proof. exact (TRANS (@lem1497820 x) (@lem1497845 x)). Qed.
Lemma lem1497847 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1483533 x term15). Qed.
Lemma lem1497853 (x : real) : (term32 x) = (term33 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1497855 (x : nat) : (term22 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1497856 : term23 = term15.
Proof. exact (@lem1497855 term24). Qed.
Lemma lem1497857 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1497858 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1497857 x) (@lem1497856)). Qed.
Lemma lem1497859 (x : real) : (term34 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1497860 (x : real) : (term33 x) = x.
Proof. exact (TRANS (@lem1497858 x) (@lem1497859 x)). Qed.
Lemma lem1497862 (x : real) : (term32 x) = x.
Proof. exact (TRANS (@lem1497853 x) (@lem1497860 x)). Qed.
Lemma lem1497863 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497864 (x : real) : (term35 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1497863) (@lem1497862 x)). Qed.
Lemma lem1497865 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497866 (x : real) : (term31 x) = (term36 x).
Proof. exact (MK_COMB (@lem1497864 x) (@lem1497865)). Qed.
Lemma lem1497867 (x : real) : (term30 x) = (term36 x).
Proof. exact (TRANS (@lem1497847 x) (@lem1497866 x)). Qed.
Lemma lem1497868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1497869 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem1497868) (@lem1497846 x)). Qed.
Lemma lem1497870 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1497869 x) (@lem1497867 x)). Qed.
Lemma lem1497871 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483533 term15 (real_neg x)). Qed.
Lemma lem1497878 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1497881 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem1497882 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1497881) (@lem1497878 x)). Qed.
Lemma lem1497883 (x : real) : (term45 x) = (term46 x).
Proof. exact (@lem1483519 term15 (term16 x)). Qed.
Lemma lem1497884 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1483476 term49 term49 x). Qed.
Lemma lem1497886 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1497887 : term52 = term53.
Proof. exact (@lem1497886 term24 term24). Qed.
Lemma lem1497888 : (term54 = (BIT1 0)) = (term55 = term24).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1497889 : term55 = term24.
Proof. exact (EQ_MP (@lem1497888) (@lem940073)). Qed.
Lemma lem1497890 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1497891 : term53 = term56.
Proof. exact (MK_COMB (@lem1497890) (@lem1497889)). Qed.
Lemma lem1497892 : term52 = term56.
Proof. exact (TRANS (@lem1497887) (@lem1497891)). Qed.
Lemma lem1497893 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1497894 : term57 = term58.
Proof. exact (MK_COMB (@lem1497893) (@lem1497892)). Qed.
Lemma lem1497895 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1497896 (x : real) : (term48 x) = (term59 x).
Proof. exact (MK_COMB (@lem1497894) (@lem1497895 x)). Qed.
Lemma lem1497897 (x : real) : (term47 x) = (term59 x).
Proof. exact (TRANS (@lem1497884 x) (@lem1497896 x)). Qed.
Lemma lem1497898 (x : real) : (term59 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1497899 (x : real) : (term47 x) = x.
Proof. exact (TRANS (@lem1497897 x) (@lem1497898 x)). Qed.
Lemma lem1497900 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1497901 (x : real) : (term46 x) = (term61 x).
Proof. exact (MK_COMB (@lem1497900) (@lem1497899 x)). Qed.
Lemma lem1497902 (x : real) : (term61 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1497903 (x : real) : (term46 x) = x.
Proof. exact (TRANS (@lem1497901 x) (@lem1497902 x)). Qed.
Lemma lem1497904 (x : real) : (term45 x) = x.
Proof. exact (TRANS (@lem1497883 x) (@lem1497903 x)). Qed.
Lemma lem1497905 (x : real) : (term44 x) = x.
Proof. exact (TRANS (@lem1497882 x) (@lem1497904 x)). Qed.
Lemma lem1497906 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1497907 (x : real) : (term62 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1497906) (@lem1497905 x)). Qed.
Lemma lem1497908 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497909 (x : real) : (term42 x) = (term36 x).
Proof. exact (MK_COMB (@lem1497907 x) (@lem1497908)). Qed.
Lemma lem1497910 (x : real) : (term41 x) = (term36 x).
Proof. exact (TRANS (@lem1497871 x) (@lem1497909 x)). Qed.
Lemma lem1497911 (x : real) : (term3 x) = (term63 x).
Proof. exact (@lem1483523 term15 x). Qed.
Lemma lem1497917 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1497922 (x : real) : (term65 x) = (term16 x).
Proof. exact (@lem1483448 (term16 x)). Qed.
Lemma lem1497924 (x : real) : (term64 x) = (term16 x).
Proof. exact (TRANS (@lem1497917 x) (@lem1497922 x)). Qed.
Lemma lem1497925 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1497926 (x : real) : (term66 x) = (term28 x).
Proof. exact (MK_COMB (@lem1497925) (@lem1497924 x)). Qed.
Lemma lem1497927 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1497928 (x : real) : (term63 x) = (term29 x).
Proof. exact (MK_COMB (@lem1497926 x) (@lem1497927)). Qed.
Lemma lem1497929 (x : real) : (term3 x) = (term29 x).
Proof. exact (TRANS (@lem1497911 x) (@lem1497928 x)). Qed.
Lemma lem1497930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1497931 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1497930) (@lem1497910 x)). Qed.
Lemma lem1497932 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1497931 x) (@lem1497929 x)). Qed.
Lemma lem1497933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497934 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1497933) (@lem1497870 x)). Qed.
Lemma lem1497935 (x : real) : (term1 x) = (term73 x).
Proof. exact (MK_COMB (@lem1497934 x) (@lem1497932 x)). Qed.
Lemma lem1497936 : term12 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497935 x)). Qed.
Lemma lem1497937 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497938 : term13 = term75.
Proof. exact (MK_COMB (@lem1497937) (@lem1497936)). Qed.
Lemma lem1497939 : term6 = term75.
Proof. exact (TRANS (@lem1497819) (@lem1497938)). Qed.
Lemma lem1497941 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1497942 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1497941 real P Q). Qed.
Lemma lem1497943 : term80 = term81.
Proof. exact (@lem1497942 term82 term83). Qed.
Lemma lem1497944 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497946 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1497945) (@lem1497944 x)). Qed.
Lemma lem1497947 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497948 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1497946 x) (@lem1497947 x)). Qed.
Lemma lem1497949 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1497948 x)). Qed.
Lemma lem1497950 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497951 : term80 = term75.
Proof. exact (MK_COMB (@lem1497950) (@lem1497949)). Qed.
Lemma lem1497952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1497953 : term89 = term90.
Proof. exact (MK_COMB (@lem1497952) (@lem1497951)). Qed.
Lemma lem1497954 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1497955 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1497954 x)). Qed.
Lemma lem1497956 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497957 : term92 = term93.
Proof. exact (MK_COMB (@lem1497956) (@lem1497955)). Qed.
Lemma lem1497958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1497959 : term94 = term95.
Proof. exact (MK_COMB (@lem1497958) (@lem1497957)). Qed.
Lemma lem1497960 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1497961 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1497960 x)). Qed.
Lemma lem1497962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1497963 : term97 = term98.
Proof. exact (MK_COMB (@lem1497962) (@lem1497961)). Qed.
Lemma lem1497964 : term81 = term99.
Proof. exact (MK_COMB (@lem1497959) (@lem1497963)). Qed.
Lemma lem1497965 : (term80 = term81) = (term75 = term99).
Proof. exact (MK_COMB (@lem1497953) (@lem1497964)). Qed.
Lemma lem1497966 : term75 = term99.
Proof. exact (EQ_MP (@lem1497965) (@lem1497943)). Qed.
Lemma lem1498064 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1498065 (P : real -> Prop) (Q : real -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1498064 real P Q). Qed.
Lemma lem1498066 : term81 = term80.
Proof. exact (@lem1498065 term82 term83). Qed.
Lemma lem1498067 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1498068 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1498067 x)). Qed.
Lemma lem1498069 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498070 : term92 = term93.
Proof. exact (MK_COMB (@lem1498069) (@lem1498068)). Qed.
Lemma lem1498071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1498072 : term94 = term95.
Proof. exact (MK_COMB (@lem1498071) (@lem1498070)). Qed.
Lemma lem1498073 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1498074 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1498073 x)). Qed.
Lemma lem1498075 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498076 : term97 = term98.
Proof. exact (MK_COMB (@lem1498075) (@lem1498074)). Qed.
Lemma lem1498077 : term81 = term99.
Proof. exact (MK_COMB (@lem1498072) (@lem1498076)). Qed.
Lemma lem1498078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1498079 : term100 = term101.
Proof. exact (MK_COMB (@lem1498078) (@lem1498077)). Qed.
Lemma lem1498080 (x : real) : (term84 x) = (term40 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1498081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1498082 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1498081) (@lem1498080 x)). Qed.
Lemma lem1498083 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1498084 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1498082 x) (@lem1498083 x)). Qed.
Lemma lem1498085 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1498084 x)). Qed.
Lemma lem1498086 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498087 : term80 = term75.
Proof. exact (MK_COMB (@lem1498086) (@lem1498085)). Qed.
Lemma lem1498088 : (term81 = term80) = (term99 = term75).
Proof. exact (MK_COMB (@lem1498079) (@lem1498087)). Qed.
Lemma lem1498089 : term99 = term75.
Proof. exact (EQ_MP (@lem1498088) (@lem1498066)). Qed.
Lemma lem1498090 : term75 = term75.
Proof. exact (TRANS (@lem1497966) (@lem1498089)). Qed.
Lemma lem1498093 : term6 = term75.
Proof. exact (TRANS (@lem1497939) (@lem1498090)). Qed.
Lemma lem1498110 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1498111 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem1498110 x)). Qed.
Lemma lem1498112 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1498113 : term75 = term75.
Proof. exact (MK_COMB (@lem1498112) (@lem1498111)). Qed.
Lemma lem1498114 : term6 = term75.
Proof. exact (TRANS (@lem1498093) (@lem1498113)). Qed.
Lemma lem1498124 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1498125 (x : real) (h1 : term40 x) : term40 x.
Proof. exact (h1). Qed.
Lemma lem1498126 (x : real) (h1 : term40 x) : term36 x.
Proof. exact (proj2 (@lem1498125 x h1)). Qed.
Lemma lem1498127 (x : real) (h1 : term40 x) : term29 x.
Proof. exact (proj1 (@lem1498125 x h1)). Qed.
Lemma lem1498129 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498130 : term103 = term104.
Proof. exact (@lem1498129 (NUMERAL 0) term24). Qed.
Lemma lem1498131 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498132 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498133 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1498132 h1) (fun h1 : term104 = True => @lem1498131)). Qed.
Lemma lem1498134 : term104 = True.
Proof. exact (EQ_MP (@lem1498133) (@lem1498131)). Qed.
Lemma lem1498135 : term103 = True.
Proof. exact (TRANS (@lem1498130) (@lem1498134)). Qed.
Lemma lem1498136 : True = term103.
Proof. exact (SYM (@lem1498135)). Qed.
Lemma lem1498137 : term103.
Proof. exact (EQ_MP (@lem1498136) (@lem0)). Qed.
Lemma lem1498138 (x : real) (h1 : term40 x) : term106 x.
Proof. exact (conj (@lem1498137) (@lem1498127 x h1)). Qed.
Lemma lem1498140 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1498141 (x : real) : term108 x.
Proof. exact (@lem1498140 term56 (term16 x)). Qed.
Lemma lem1498142 (x : real) (h1 : term40 x) : term109 x.
Proof. exact (@lem1498141 x (@lem1498138 x h1)). Qed.
Lemma lem1498143 (x : real) : (term110 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1498144 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498145 (x : real) : (term111 x) = (term28 x).
Proof. exact (MK_COMB (@lem1498144) (@lem1498143 x)). Qed.
Lemma lem1498146 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1498147 (x : real) : (term109 x) = (term29 x).
Proof. exact (MK_COMB (@lem1498145 x) (@lem1498146)). Qed.
Lemma lem1498148 (x : real) (h1 : term40 x) : term29 x.
Proof. exact (EQ_MP (@lem1498147 x) (@lem1498142 x h1)). Qed.
Lemma lem1498150 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498151 : term103 = term104.
Proof. exact (@lem1498150 (NUMERAL 0) term24). Qed.
Lemma lem1498152 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498153 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498154 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1498153 h1) (fun h1 : term104 = True => @lem1498152)). Qed.
Lemma lem1498155 : term104 = True.
Proof. exact (EQ_MP (@lem1498154) (@lem1498152)). Qed.
Lemma lem1498156 : term103 = True.
Proof. exact (TRANS (@lem1498151) (@lem1498155)). Qed.
Lemma lem1498157 : True = term103.
Proof. exact (SYM (@lem1498156)). Qed.
Lemma lem1498158 : term103.
Proof. exact (EQ_MP (@lem1498157) (@lem0)). Qed.
Lemma lem1498159 (x : real) (h1 : term40 x) : term112 x.
Proof. exact (conj (@lem1498158) (@lem1498126 x h1)). Qed.
Lemma lem1498161 (x : real) (y : real) : term113 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1498162 (x : real) : term114 x.
Proof. exact (@lem1498161 term56 x). Qed.
Lemma lem1498163 (x : real) (h1 : term40 x) : term115 x.
Proof. exact (@lem1498162 x (@lem1498159 x h1)). Qed.
Lemma lem1498164 (x : real) : (term59 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1498165 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498166 (x : real) : (term116 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1498165) (@lem1498164 x)). Qed.
Lemma lem1498167 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1498168 (x : real) : (term115 x) = (term36 x).
Proof. exact (MK_COMB (@lem1498166 x) (@lem1498167)). Qed.
Lemma lem1498169 (x : real) (h1 : term40 x) : term36 x.
Proof. exact (EQ_MP (@lem1498168 x) (@lem1498163 x h1)). Qed.
Lemma lem1498170 (x : real) (h1 : term40 x) : term70 x.
Proof. exact (conj (@lem1498169 x h1) (@lem1498148 x h1)). Qed.
Lemma lem1498172 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1498173 (x : real) : term118 x.
Proof. exact (@lem1498172 x (term16 x)). Qed.
Lemma lem1498174 (x : real) (h1 : term40 x) : term119 x.
Proof. exact (@lem1498173 x (@lem1498170 x h1)). Qed.
Lemma lem1498175 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483442 term49 x). Qed.
Lemma lem1498177 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1498178 : term123 = term15.
Proof. exact (@lem1498177 term24). Qed.
Lemma lem1498179 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498180 : term124 = term125.
Proof. exact (MK_COMB (@lem1498179) (@lem1498178)). Qed.
Lemma lem1498181 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1498182 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1498180) (@lem1498181 x)). Qed.
Lemma lem1498183 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1498175 x) (@lem1498182 x)). Qed.
Lemma lem1498184 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1498185 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1498183 x) (@lem1498184 x)). Qed.
Lemma lem1498186 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498187 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1498186) (@lem1498185 x)). Qed.
Lemma lem1498188 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1498189 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1498187 x) (@lem1498188)). Qed.
Lemma lem1498190 (x : real) (h1 : term40 x) : term129.
Proof. exact (EQ_MP (@lem1498189 x) (@lem1498174 x h1)). Qed.
Lemma lem1498192 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498193 : term129 = term130.
Proof. exact (@lem1498192 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1498194 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1498195 : term129 = False.
Proof. exact (TRANS (@lem1498193) (@lem1498194)). Qed.
Lemma lem1498196 (x : real) (h1 : term40 x) : False.
Proof. exact (EQ_MP (@lem1498195) (@lem1498190 x h1)). Qed.
Lemma lem1498197 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1498198 (x : real) (h1 : term70 x) : term29 x.
Proof. exact (proj2 (@lem1498197 x h1)). Qed.
Lemma lem1498199 (x : real) (h1 : term70 x) : term36 x.
Proof. exact (proj1 (@lem1498197 x h1)). Qed.
Lemma lem1498201 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498202 : term103 = term104.
Proof. exact (@lem1498201 (NUMERAL 0) term24). Qed.
Lemma lem1498203 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498204 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498205 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1498204 h1) (fun h1 : term104 = True => @lem1498203)). Qed.
Lemma lem1498206 : term104 = True.
Proof. exact (EQ_MP (@lem1498205) (@lem1498203)). Qed.
Lemma lem1498207 : term103 = True.
Proof. exact (TRANS (@lem1498202) (@lem1498206)). Qed.
Lemma lem1498208 : True = term103.
Proof. exact (SYM (@lem1498207)). Qed.
Lemma lem1498209 : term103.
Proof. exact (EQ_MP (@lem1498208) (@lem0)). Qed.
Lemma lem1498210 (x : real) (h1 : term70 x) : term106 x.
Proof. exact (conj (@lem1498209) (@lem1498198 x h1)). Qed.
Lemma lem1498212 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1498213 (x : real) : term108 x.
Proof. exact (@lem1498212 term56 (term16 x)). Qed.
Lemma lem1498214 (x : real) (h1 : term70 x) : term109 x.
Proof. exact (@lem1498213 x (@lem1498210 x h1)). Qed.
Lemma lem1498215 (x : real) : (term110 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1498216 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1498217 (x : real) : (term111 x) = (term28 x).
Proof. exact (MK_COMB (@lem1498216) (@lem1498215 x)). Qed.
Lemma lem1498218 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1498219 (x : real) : (term109 x) = (term29 x).
Proof. exact (MK_COMB (@lem1498217 x) (@lem1498218)). Qed.
Lemma lem1498220 (x : real) (h1 : term70 x) : term29 x.
Proof. exact (EQ_MP (@lem1498219 x) (@lem1498214 x h1)). Qed.
Lemma lem1498222 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498223 : term103 = term104.
Proof. exact (@lem1498222 (NUMERAL 0) term24). Qed.
Lemma lem1498224 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1498225 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1498226 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1498225 h1) (fun h1 : term104 = True => @lem1498224)). Qed.
Lemma lem1498227 : term104 = True.
Proof. exact (EQ_MP (@lem1498226) (@lem1498224)). Qed.
Lemma lem1498228 : term103 = True.
Proof. exact (TRANS (@lem1498223) (@lem1498227)). Qed.
Lemma lem1498229 : True = term103.
Proof. exact (SYM (@lem1498228)). Qed.
Lemma lem1498230 : term103.
Proof. exact (EQ_MP (@lem1498229) (@lem0)). Qed.
Lemma lem1498231 (x : real) (h1 : term70 x) : term112 x.
Proof. exact (conj (@lem1498230) (@lem1498199 x h1)). Qed.
Lemma lem1498233 (x : real) (y : real) : term113 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1498234 (x : real) : term114 x.
Proof. exact (@lem1498233 term56 x). Qed.
Lemma lem1498235 (x : real) (h1 : term70 x) : term115 x.
Proof. exact (@lem1498234 x (@lem1498231 x h1)). Qed.
Lemma lem1498236 (x : real) : (term59 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1498237 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498238 (x : real) : (term116 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1498237) (@lem1498236 x)). Qed.
Lemma lem1498239 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1498240 (x : real) : (term115 x) = (term36 x).
Proof. exact (MK_COMB (@lem1498238 x) (@lem1498239)). Qed.
Lemma lem1498241 (x : real) (h1 : term70 x) : term36 x.
Proof. exact (EQ_MP (@lem1498240 x) (@lem1498235 x h1)). Qed.
Lemma lem1498242 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (conj (@lem1498241 x h1) (@lem1498220 x h1)). Qed.
Lemma lem1498244 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1498245 (x : real) : term118 x.
Proof. exact (@lem1498244 x (term16 x)). Qed.
Lemma lem1498246 (x : real) (h1 : term70 x) : term119 x.
Proof. exact (@lem1498245 x (@lem1498242 x h1)). Qed.
Lemma lem1498247 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483442 term49 x). Qed.
Lemma lem1498249 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1498250 : term123 = term15.
Proof. exact (@lem1498249 term24). Qed.
Lemma lem1498251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1498252 : term124 = term125.
Proof. exact (MK_COMB (@lem1498251) (@lem1498250)). Qed.
Lemma lem1498253 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1498254 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1498252) (@lem1498253 x)). Qed.
Lemma lem1498255 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1498247 x) (@lem1498254 x)). Qed.
Lemma lem1498256 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1498257 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1498255 x) (@lem1498256 x)). Qed.
Lemma lem1498258 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1498259 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1498258) (@lem1498257 x)). Qed.
Lemma lem1498260 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1498261 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1498259 x) (@lem1498260)). Qed.
Lemma lem1498262 (x : real) (h1 : term70 x) : term129.
Proof. exact (EQ_MP (@lem1498261 x) (@lem1498246 x h1)). Qed.
Lemma lem1498264 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1498265 : term129 = term130.
Proof. exact (@lem1498264 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1498266 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1498267 : term129 = False.
Proof. exact (TRANS (@lem1498265) (@lem1498266)). Qed.
Lemma lem1498268 (x : real) (h1 : term70 x) : False.
Proof. exact (EQ_MP (@lem1498267) (@lem1498262 x h1)). Qed.
Lemma lem1498269 (x : real) (h1 : term73 x) : False.
Proof. exact (or_elim (@lem1498124 x h1) (fun h0 : term40 x => @lem1498196 x h0) (fun h0 : term70 x => @lem1498268 x h0)). Qed.
Lemma lem1498271 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1498272 (x : real) (h1 : term73 x) : (term73 x) = False.
Proof. exact (prop_ext (fun h2 : term73 x => @lem1498269 x h1) (fun h2 : False => @lem1498271 x h1)). Qed.
Lemma lem1498273 (x : real) (h1 : term73 x) : False.
Proof. exact (EQ_MP (@lem1498272 x h1) (@lem1498271 x h1)). Qed.
Lemma lem1498274 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem1498275 (h1 : term75) : False.
Proof. exact (ex_elim (@lem1498274 h1) (fun x : real => fun h0 : term74 x => @lem1498273 x h0)). Qed.
Lemma lem1498276 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1498277 (h1 : term6) : term75.
Proof. exact (EQ_MP (@lem1498114) (@lem1498276 h1)). Qed.
Lemma lem1498278 (h1 : term6) : term75 = False.
Proof. exact (prop_ext (fun h2 : term75 => @lem1498275 h2) (fun h2 : False => @lem1498277 h1)). Qed.
Lemma lem1498279 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1498278 h1) (@lem1498277 h1)). Qed.
Lemma lem1498280 : term131.
Proof. exact (fun h0 : term6 => @lem1498279 h0). Qed.
Lemma lem1498281 : term132.
Proof. exact (@lem1386578 term133). Qed.
Lemma lem1498282 : term133.
Proof. exact (@lem1498281 (@lem1498280)). Qed.
