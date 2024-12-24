Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_REFL_term_abbrevs.
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
Require Import thm1396750_spec.
Require Import thm1482704_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483529_spec.
Require Import thm1483533_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19367_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem1535839 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 ((real_abs x) = x) (term2 x)). Qed.
Lemma lem1535840 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1535841 : term5 = term6.
Proof. exact (@lem1535840 term7). Qed.
Lemma lem1535842 (x : real) : (term8 x) = (((real_abs x) = x) = (term2 x)).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1535843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1535844 (x : real) : (term9 x) = (term0 x).
Proof. exact (MK_COMB (@lem1535843) (@lem1535842 x)). Qed.
Lemma lem1535845 (x : real) : (term9 x) = (term1 x).
Proof. exact (TRANS (@lem1535844 x) (@lem1535839 x)). Qed.
Lemma lem1535846 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1535845 x)). Qed.
Lemma lem1535847 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535848 : term6 = term12.
Proof. exact (MK_COMB (@lem1535847) (@lem1535846)). Qed.
Lemma lem1535850 : term5 = term12.
Proof. exact (TRANS (@lem1535841) (@lem1535848)). Qed.
Lemma lem1535867 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1535868 : term11 = term11.
Proof. exact (fun_ext (fun x : real => @lem1535867 x)). Qed.
Lemma lem1535869 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535870 : term12 = term12.
Proof. exact (MK_COMB (@lem1535869) (@lem1535868)). Qed.
Lemma lem1535871 : term5 = term12.
Proof. exact (TRANS (@lem1535850) (@lem1535870)). Qed.
Lemma lem1535872 (x : real) : ((real_abs x) = x) = ((term13 x) = term14).
Proof. exact (@lem1483529 (real_abs x) x). Qed.
Lemma lem1535878 (x : real) : (term13 x) = (term15 x).
Proof. exact (@lem1483519 (real_abs x) x). Qed.
Lemma lem1535883 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1483488 (term17 x) (real_abs x)). Qed.
Lemma lem1535885 (x : real) : (term13 x) = (term16 x).
Proof. exact (TRANS (@lem1535878 x) (@lem1535883 x)). Qed.
Lemma lem1535886 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1535887 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1535886) (@lem1535885 x)). Qed.
Lemma lem1535888 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1535889 (x : real) : ((term13 x) = term14) = ((term16 x) = term14).
Proof. exact (MK_COMB (@lem1535887 x) (@lem1535888)). Qed.
Lemma lem1535890 (x : real) : ((real_abs x) = x) = ((term16 x) = term14).
Proof. exact (TRANS (@lem1535872 x) (@lem1535889 x)). Qed.
Lemma lem1535891 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1483533 term14 x). Qed.
Lemma lem1535897 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1535902 (x : real) : (term23 x) = (term17 x).
Proof. exact (@lem1483448 (term17 x)). Qed.
Lemma lem1535904 (x : real) : (term22 x) = (term17 x).
Proof. exact (TRANS (@lem1535897 x) (@lem1535902 x)). Qed.
Lemma lem1535905 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535906 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1535905) (@lem1535904 x)). Qed.
Lemma lem1535907 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1535908 (x : real) : (term21 x) = (term26 x).
Proof. exact (MK_COMB (@lem1535906 x) (@lem1535907)). Qed.
Lemma lem1535909 (x : real) : (term20 x) = (term26 x).
Proof. exact (TRANS (@lem1535891 x) (@lem1535908 x)). Qed.
Lemma lem1535910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535911 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1535910) (@lem1535890 x)). Qed.
Lemma lem1535912 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1535911 x) (@lem1535909 x)). Qed.
Lemma lem1535913 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1483554 (real_abs x) x). Qed.
Lemma lem1535919 (x : real) : (term13 x) = (term15 x).
Proof. exact (@lem1483519 (real_abs x) x). Qed.
Lemma lem1535924 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1483488 (term17 x) (real_abs x)). Qed.
Lemma lem1535926 (x : real) : (term13 x) = (term16 x).
Proof. exact (TRANS (@lem1535919 x) (@lem1535924 x)). Qed.
Lemma lem1535927 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1535928 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1535927) (@lem1535926 x)). Qed.
Lemma lem1535929 (x : real) : (term34 x) = (term35 x).
Proof. exact (@lem1483512 (term16 x)). Qed.
Lemma lem1535930 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem1483508 (term17 x) term37 (real_abs x)). Qed.
Lemma lem1535931 (x : real) : (term38 x) = (term38 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1535932 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483476 term37 term37 x). Qed.
Lemma lem1535934 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1535935 : term43 = term44.
Proof. exact (@lem1535934 term45 term45). Qed.
Lemma lem1535936 : (term46 = (BIT1 0)) = (term47 = term45).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1535937 : term47 = term45.
Proof. exact (EQ_MP (@lem1535936) (@lem940073)). Qed.
Lemma lem1535938 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1535939 : term44 = term48.
Proof. exact (MK_COMB (@lem1535938) (@lem1535937)). Qed.
Lemma lem1535940 : term43 = term48.
Proof. exact (TRANS (@lem1535935) (@lem1535939)). Qed.
Lemma lem1535941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1535942 : term49 = term50.
Proof. exact (MK_COMB (@lem1535941) (@lem1535940)). Qed.
Lemma lem1535943 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1535944 (x : real) : (term40 x) = (term51 x).
Proof. exact (MK_COMB (@lem1535942) (@lem1535943 x)). Qed.
Lemma lem1535945 (x : real) : (term39 x) = (term51 x).
Proof. exact (TRANS (@lem1535932 x) (@lem1535944 x)). Qed.
Lemma lem1535946 (x : real) : (term51 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1535947 (x : real) : (term39 x) = x.
Proof. exact (TRANS (@lem1535945 x) (@lem1535946 x)). Qed.
Lemma lem1535948 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1535949 (x : real) : (term52 x) = (real_add x).
Proof. exact (MK_COMB (@lem1535948) (@lem1535947 x)). Qed.
Lemma lem1535950 (x : real) : (term36 x) = (term53 x).
Proof. exact (MK_COMB (@lem1535949 x) (@lem1535931 x)). Qed.
Lemma lem1535951 (x : real) : (term35 x) = (term53 x).
Proof. exact (TRANS (@lem1535930 x) (@lem1535950 x)). Qed.
Lemma lem1535952 (x : real) : (term34 x) = (term53 x).
Proof. exact (TRANS (@lem1535929 x) (@lem1535951 x)). Qed.
Lemma lem1535953 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1535954 (x : real) : ((term33 x) = (term34 x)) = ((term33 x) = (term53 x)).
Proof. exact (MK_COMB (@lem1535953 x) (@lem1535952 x)). Qed.
Lemma lem1535955 (x : real) : (term33 x) = (term53 x).
Proof. exact (EQ_MP (@lem1535954 x) (@lem1535928 x)). Qed.
Lemma lem1535956 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535957 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1535956) (@lem1535955 x)). Qed.
Lemma lem1535958 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1535959 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1535957 x) (@lem1535958)). Qed.
Lemma lem1535960 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1535961 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1535960) (@lem1535926 x)). Qed.
Lemma lem1535962 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1535963 (x : real) : (term61 x) = (term62 x).
Proof. exact (MK_COMB (@lem1535961 x) (@lem1535962)). Qed.
Lemma lem1535964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535965 (x : real) : (term63 x) = (term64 x).
Proof. exact (MK_COMB (@lem1535964) (@lem1535963 x)). Qed.
Lemma lem1535966 (x : real) : (term32 x) = (term65 x).
Proof. exact (MK_COMB (@lem1535965 x) (@lem1535959 x)). Qed.
Lemma lem1535967 (x : real) : (term31 x) = (term65 x).
Proof. exact (TRANS (@lem1535913 x) (@lem1535966 x)). Qed.
Lemma lem1535968 (x : real) : (term2 x) = (term66 x).
Proof. exact (@lem1483523 x term14). Qed.
Lemma lem1535974 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1535976 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1535977 : term70 = term14.
Proof. exact (@lem1535976 term45). Qed.
Lemma lem1535978 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1535979 (x : real) : (term68 x) = (term71 x).
Proof. exact (MK_COMB (@lem1535978 x) (@lem1535977)). Qed.
Lemma lem1535980 (x : real) : (term71 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1535981 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1535979 x) (@lem1535980 x)). Qed.
Lemma lem1535983 (x : real) : (term67 x) = x.
Proof. exact (TRANS (@lem1535974 x) (@lem1535981 x)). Qed.
Lemma lem1535984 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1535985 (x : real) : (term72 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1535984) (@lem1535983 x)). Qed.
Lemma lem1535986 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1535987 (x : real) : (term66 x) = (term73 x).
Proof. exact (MK_COMB (@lem1535985 x) (@lem1535986)). Qed.
Lemma lem1535988 (x : real) : (term2 x) = (term73 x).
Proof. exact (TRANS (@lem1535968 x) (@lem1535987 x)). Qed.
Lemma lem1535989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1535990 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1535989) (@lem1535967 x)). Qed.
Lemma lem1535991 (x : real) : (term76 x) = (term77 x).
Proof. exact (MK_COMB (@lem1535990 x) (@lem1535988 x)). Qed.
Lemma lem1535992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1535993 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1535992) (@lem1535912 x)). Qed.
Lemma lem1535994 (x : real) : (term1 x) = (term80 x).
Proof. exact (MK_COMB (@lem1535993 x) (@lem1535991 x)). Qed.
Lemma lem1535995 : term11 = term81.
Proof. exact (fun_ext (fun x : real => @lem1535994 x)). Qed.
Lemma lem1535996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1535997 : term12 = term82.
Proof. exact (MK_COMB (@lem1535996) (@lem1535995)). Qed.
Lemma lem1535998 : term5 = term82.
Proof. exact (TRANS (@lem1535871) (@lem1535997)). Qed.
Lemma lem1536000 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1536001 (P : real -> Prop) (Q : real -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem1536000 real P Q). Qed.
Lemma lem1536002 : term87 = term88.
Proof. exact (@lem1536001 term89 term90). Qed.
Lemma lem1536003 (x : real) : (term91 x) = (term30 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1536004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536005 (x : real) : (term92 x) = (term79 x).
Proof. exact (MK_COMB (@lem1536004) (@lem1536003 x)). Qed.
Lemma lem1536006 (x : real) : (term93 x) = (term77 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1536007 (x : real) : (term94 x) = (term80 x).
Proof. exact (MK_COMB (@lem1536005 x) (@lem1536006 x)). Qed.
Lemma lem1536008 : term95 = term81.
Proof. exact (fun_ext (fun x : real => @lem1536007 x)). Qed.
Lemma lem1536009 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536010 : term87 = term82.
Proof. exact (MK_COMB (@lem1536009) (@lem1536008)). Qed.
Lemma lem1536011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1536012 : term96 = term97.
Proof. exact (MK_COMB (@lem1536011) (@lem1536010)). Qed.
Lemma lem1536013 (x : real) : (term91 x) = (term30 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1536014 : term98 = term89.
Proof. exact (fun_ext (fun x : real => @lem1536013 x)). Qed.
Lemma lem1536015 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536016 : term99 = term100.
Proof. exact (MK_COMB (@lem1536015) (@lem1536014)). Qed.
Lemma lem1536017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536018 : term101 = term102.
Proof. exact (MK_COMB (@lem1536017) (@lem1536016)). Qed.
Lemma lem1536019 (x : real) : (term93 x) = (term77 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1536020 : term103 = term90.
Proof. exact (fun_ext (fun x : real => @lem1536019 x)). Qed.
Lemma lem1536021 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536022 : term104 = term105.
Proof. exact (MK_COMB (@lem1536021) (@lem1536020)). Qed.
Lemma lem1536023 : term88 = term106.
Proof. exact (MK_COMB (@lem1536018) (@lem1536022)). Qed.
Lemma lem1536024 : (term87 = term88) = (term82 = term106).
Proof. exact (MK_COMB (@lem1536012) (@lem1536023)). Qed.
Lemma lem1536025 : term82 = term106.
Proof. exact (EQ_MP (@lem1536024) (@lem1536002)). Qed.
Lemma lem1536123 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term84 A P Q) = (term83 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1536124 (P : real -> Prop) (Q : real -> Prop) : (term86 P Q) = (term85 P Q).
Proof. exact (@lem1536123 real P Q). Qed.
Lemma lem1536125 : term88 = term87.
Proof. exact (@lem1536124 term89 term90). Qed.
Lemma lem1536126 (x : real) : (term91 x) = (term30 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1536127 : term98 = term89.
Proof. exact (fun_ext (fun x : real => @lem1536126 x)). Qed.
Lemma lem1536128 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536129 : term99 = term100.
Proof. exact (MK_COMB (@lem1536128) (@lem1536127)). Qed.
Lemma lem1536130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536131 : term101 = term102.
Proof. exact (MK_COMB (@lem1536130) (@lem1536129)). Qed.
Lemma lem1536132 (x : real) : (term93 x) = (term77 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1536133 : term103 = term90.
Proof. exact (fun_ext (fun x : real => @lem1536132 x)). Qed.
Lemma lem1536134 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536135 : term104 = term105.
Proof. exact (MK_COMB (@lem1536134) (@lem1536133)). Qed.
Lemma lem1536136 : term88 = term106.
Proof. exact (MK_COMB (@lem1536131) (@lem1536135)). Qed.
Lemma lem1536137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1536138 : term107 = term108.
Proof. exact (MK_COMB (@lem1536137) (@lem1536136)). Qed.
Lemma lem1536139 (x : real) : (term91 x) = (term30 x).
Proof. exact (eq_refl (term91 x)). Qed.
Lemma lem1536140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536141 (x : real) : (term92 x) = (term79 x).
Proof. exact (MK_COMB (@lem1536140) (@lem1536139 x)). Qed.
Lemma lem1536142 (x : real) : (term93 x) = (term77 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem1536143 (x : real) : (term94 x) = (term80 x).
Proof. exact (MK_COMB (@lem1536141 x) (@lem1536142 x)). Qed.
Lemma lem1536144 : term95 = term81.
Proof. exact (fun_ext (fun x : real => @lem1536143 x)). Qed.
Lemma lem1536145 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536146 : term87 = term82.
Proof. exact (MK_COMB (@lem1536145) (@lem1536144)). Qed.
Lemma lem1536147 : (term88 = term87) = (term106 = term82).
Proof. exact (MK_COMB (@lem1536138) (@lem1536146)). Qed.
Lemma lem1536148 : term106 = term82.
Proof. exact (EQ_MP (@lem1536147) (@lem1536125)). Qed.
Lemma lem1536149 : term82 = term82.
Proof. exact (TRANS (@lem1536025) (@lem1536148)). Qed.
Lemma lem1536152 : term5 = term82.
Proof. exact (TRANS (@lem1535998) (@lem1536149)). Qed.
Lemma lem1536169 (x : real) : (term77 x) = (term109 x).
Proof. exact (@lem19367 (term62 x) (term58 x) (term73 x)). Qed.
Lemma lem1536178 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1536179 (x : real) : (term80 x) = (term110 x).
Proof. exact (MK_COMB (@lem1536178 x) (@lem1536169 x)). Qed.
Lemma lem1536180 : term81 = term111.
Proof. exact (fun_ext (fun x : real => @lem1536179 x)). Qed.
Lemma lem1536181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536182 : term82 = term112.
Proof. exact (MK_COMB (@lem1536181) (@lem1536180)). Qed.
Lemma lem1536183 : term5 = term112.
Proof. exact (TRANS (@lem1536152) (@lem1536182)). Qed.
Lemma lem1536185 (x : real) : (term113 x) = (term30 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem1536186 (x : real) : (term30 x) = (term113 x).
Proof. exact (SYM (@lem1536185 x)). Qed.
Lemma lem1536187 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1482981 (term115 x) x). Qed.
Lemma lem1536188 (x : real) : (term30 x) = (term114 x).
Proof. exact (TRANS (@lem1536186 x) (@lem1536187 x)). Qed.
Lemma lem1536189 (x : real) : (term116 x) = (term117 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem1536190 (x : real) : (term118 x) = (term118 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem1536191 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1536190 x) (@lem1536189 x)). Qed.
Lemma lem1536192 (x : real) : (term121 x) = (term122 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1536193 (x : real) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1536194 (x : real) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1536193 x) (@lem1536192 x)). Qed.
Lemma lem1536195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536196 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1536195) (@lem1536194 x)). Qed.
Lemma lem1536197 (x : real) : (term114 x) = (term128 x).
Proof. exact (MK_COMB (@lem1536196 x) (@lem1536191 x)). Qed.
Lemma lem1536198 (x : real) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1536199 (x : real) : ((term30 x) = (term114 x)) = ((term30 x) = (term128 x)).
Proof. exact (MK_COMB (@lem1536198 x) (@lem1536197 x)). Qed.
Lemma lem1536200 (x : real) : (term30 x) = (term128 x).
Proof. exact (EQ_MP (@lem1536199 x) (@lem1536188 x)). Qed.
Lemma lem1536201 (x : real) : (term73 x) = (term66 x).
Proof. exact (@lem1483527 x term14). Qed.
Lemma lem1536207 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem1483519 x term14). Qed.
Lemma lem1536209 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1536210 : term70 = term14.
Proof. exact (@lem1536209 term45). Qed.
Lemma lem1536211 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1536212 (x : real) : (term68 x) = (term71 x).
Proof. exact (MK_COMB (@lem1536211 x) (@lem1536210)). Qed.
Lemma lem1536213 (x : real) : (term71 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1536214 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1536212 x) (@lem1536213 x)). Qed.
Lemma lem1536216 (x : real) : (term67 x) = x.
Proof. exact (TRANS (@lem1536207 x) (@lem1536214 x)). Qed.
Lemma lem1536217 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1536218 (x : real) : (term72 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1536217) (@lem1536216 x)). Qed.
Lemma lem1536219 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536220 (x : real) : (term66 x) = (term73 x).
Proof. exact (MK_COMB (@lem1536218 x) (@lem1536219)). Qed.
Lemma lem1536221 (x : real) : (term73 x) = (term73 x).
Proof. exact (TRANS (@lem1536201 x) (@lem1536220 x)). Qed.
Lemma lem1536222 (x : real) : ((term130 x) = term14) = ((term131 x) = term14).
Proof. exact (@lem1483529 (term130 x) term14). Qed.
Lemma lem1536223 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536235 (x : real) : (term130 x) = (term132 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1536237 (m : nat) : (term133 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1536238 : term134 = term14.
Proof. exact (@lem1536237 term45). Qed.
Lemma lem1536239 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536240 : term135 = term136.
Proof. exact (MK_COMB (@lem1536239) (@lem1536238)). Qed.
Lemma lem1536241 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536242 (x : real) : (term132 x) = (term137 x).
Proof. exact (MK_COMB (@lem1536240) (@lem1536241 x)). Qed.
Lemma lem1536243 (x : real) : (term130 x) = (term137 x).
Proof. exact (TRANS (@lem1536235 x) (@lem1536242 x)). Qed.
Lemma lem1536244 (x : real) : (term137 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1536246 (x : real) : (term130 x) = term14.
Proof. exact (TRANS (@lem1536243 x) (@lem1536244 x)). Qed.
Lemma lem1536247 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1536248 (x : real) : (term138 x) = term139.
Proof. exact (MK_COMB (@lem1536247) (@lem1536246 x)). Qed.
Lemma lem1536249 (x : real) : (term131 x) = term140.
Proof. exact (MK_COMB (@lem1536248 x) (@lem1536223)). Qed.
Lemma lem1536250 : term140 = term141.
Proof. exact (@lem1483519 term14 term14). Qed.
Lemma lem1536252 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1536253 : term70 = term14.
Proof. exact (@lem1536252 term45). Qed.
Lemma lem1536254 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1536255 : term141 = term143.
Proof. exact (MK_COMB (@lem1536254) (@lem1536253)). Qed.
Lemma lem1536256 : term143 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1536257 : term141 = term14.
Proof. exact (TRANS (@lem1536255) (@lem1536256)). Qed.
Lemma lem1536258 : term140 = term14.
Proof. exact (TRANS (@lem1536250) (@lem1536257)). Qed.
Lemma lem1536259 (x : real) : (term131 x) = term14.
Proof. exact (TRANS (@lem1536249 x) (@lem1536258)). Qed.
Lemma lem1536260 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1536261 (x : real) : (term144 x) = term145.
Proof. exact (MK_COMB (@lem1536260) (@lem1536259 x)). Qed.
Lemma lem1536262 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536263 (x : real) : ((term131 x) = term14) = (term14 = term14).
Proof. exact (MK_COMB (@lem1536261 x) (@lem1536262)). Qed.
Lemma lem1536264 (x : real) : ((term130 x) = term14) = (term14 = term14).
Proof. exact (TRANS (@lem1536222 x) (@lem1536263 x)). Qed.
Lemma lem1536265 (x : real) : (term26 x) = (term146 x).
Proof. exact (@lem1483525 (term17 x) term14). Qed.
Lemma lem1536277 (x : real) : (term147 x) = (term148 x).
Proof. exact (@lem1483519 (term17 x) term14). Qed.
Lemma lem1536279 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1536280 : term70 = term14.
Proof. exact (@lem1536279 term45). Qed.
Lemma lem1536281 (x : real) : (term149 x) = (term149 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1536282 (x : real) : (term148 x) = (term150 x).
Proof. exact (MK_COMB (@lem1536281 x) (@lem1536280)). Qed.
Lemma lem1536283 (x : real) : (term150 x) = (term17 x).
Proof. exact (@lem1483450 (term17 x)). Qed.
Lemma lem1536284 (x : real) : (term148 x) = (term17 x).
Proof. exact (TRANS (@lem1536282 x) (@lem1536283 x)). Qed.
Lemma lem1536286 (x : real) : (term147 x) = (term17 x).
Proof. exact (TRANS (@lem1536277 x) (@lem1536284 x)). Qed.
Lemma lem1536287 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536288 (x : real) : (term151 x) = (term25 x).
Proof. exact (MK_COMB (@lem1536287) (@lem1536286 x)). Qed.
Lemma lem1536289 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536290 (x : real) : (term146 x) = (term26 x).
Proof. exact (MK_COMB (@lem1536288 x) (@lem1536289)). Qed.
Lemma lem1536291 (x : real) : (term26 x) = (term26 x).
Proof. exact (TRANS (@lem1536265 x) (@lem1536290 x)). Qed.
Lemma lem1536292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536293 (x : real) : (term152 x) = term153.
Proof. exact (MK_COMB (@lem1536292) (@lem1536264 x)). Qed.
Lemma lem1536294 (x : real) : (term122 x) = (term154 x).
Proof. exact (MK_COMB (@lem1536293 x) (@lem1536291 x)). Qed.
Lemma lem1536295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536296 (x : real) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem1536295) (@lem1536221 x)). Qed.
Lemma lem1536297 (x : real) : (term125 x) = (term155 x).
Proof. exact (MK_COMB (@lem1536296 x) (@lem1536294 x)). Qed.
Lemma lem1536298 (x : real) : (term156 x) = (term21 x).
Proof. exact (@lem1483525 term14 x). Qed.
Lemma lem1536304 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1483519 term14 x). Qed.
Lemma lem1536309 (x : real) : (term23 x) = (term17 x).
Proof. exact (@lem1483448 (term17 x)). Qed.
Lemma lem1536311 (x : real) : (term22 x) = (term17 x).
Proof. exact (TRANS (@lem1536304 x) (@lem1536309 x)). Qed.
Lemma lem1536312 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536313 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1536312) (@lem1536311 x)). Qed.
Lemma lem1536314 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536315 (x : real) : (term21 x) = (term26 x).
Proof. exact (MK_COMB (@lem1536313 x) (@lem1536314)). Qed.
Lemma lem1536316 (x : real) : (term156 x) = (term26 x).
Proof. exact (TRANS (@lem1536298 x) (@lem1536315 x)). Qed.
Lemma lem1536317 (x : real) : ((term157 x) = term14) = ((term158 x) = term14).
Proof. exact (@lem1483529 (term157 x) term14). Qed.
Lemma lem1536318 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536325 (x : real) : (real_neg x) = (term17 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1536334 (x : real) : (term149 x) = (term149 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1536335 (x : real) : (term157 x) = (term159 x).
Proof. exact (MK_COMB (@lem1536334 x) (@lem1536325 x)). Qed.
Lemma lem1536336 (x : real) : (term159 x) = (term160 x).
Proof. exact (@lem1483438 term37 term37 x). Qed.
Lemma lem1536337 : term161 = term162.
Proof. exact (@lem1367763 term45 term45). Qed.
Lemma lem1536338 : term163 = term164.
Proof. exact (@lem706885). Qed.
Lemma lem1536339 : (term163 = term164) = (term165 = term166).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term164). Qed.
Lemma lem1536340 : term165 = term166.
Proof. exact (EQ_MP (@lem1536339) (@lem1536338)). Qed.
Lemma lem1536341 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1536342 : term167 = term168.
Proof. exact (MK_COMB (@lem1536341) (@lem1536340)). Qed.
Lemma lem1536343 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1536344 : term162 = term169.
Proof. exact (MK_COMB (@lem1536343) (@lem1536342)). Qed.
Lemma lem1536345 : term161 = term169.
Proof. exact (TRANS (@lem1536337) (@lem1536344)). Qed.
Lemma lem1536346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536347 : term170 = term171.
Proof. exact (MK_COMB (@lem1536346) (@lem1536345)). Qed.
Lemma lem1536348 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536349 (x : real) : (term160 x) = (term172 x).
Proof. exact (MK_COMB (@lem1536347) (@lem1536348 x)). Qed.
Lemma lem1536350 (x : real) : (term159 x) = (term172 x).
Proof. exact (TRANS (@lem1536336 x) (@lem1536349 x)). Qed.
Lemma lem1536351 (x : real) : (term157 x) = (term172 x).
Proof. exact (TRANS (@lem1536335 x) (@lem1536350 x)). Qed.
Lemma lem1536352 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1536353 (x : real) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem1536352) (@lem1536351 x)). Qed.
Lemma lem1536354 (x : real) : (term158 x) = (term175 x).
Proof. exact (MK_COMB (@lem1536353 x) (@lem1536318)). Qed.
Lemma lem1536355 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 (term172 x) term14). Qed.
Lemma lem1536357 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1536358 : term70 = term14.
Proof. exact (@lem1536357 term45). Qed.
Lemma lem1536359 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1536360 (x : real) : (term176 x) = (term178 x).
Proof. exact (MK_COMB (@lem1536359 x) (@lem1536358)). Qed.
Lemma lem1536361 (x : real) : (term178 x) = (term172 x).
Proof. exact (@lem1483450 (term172 x)). Qed.
Lemma lem1536362 (x : real) : (term176 x) = (term172 x).
Proof. exact (TRANS (@lem1536360 x) (@lem1536361 x)). Qed.
Lemma lem1536363 (x : real) : (term175 x) = (term172 x).
Proof. exact (TRANS (@lem1536355 x) (@lem1536362 x)). Qed.
Lemma lem1536364 (x : real) : (term158 x) = (term172 x).
Proof. exact (TRANS (@lem1536354 x) (@lem1536363 x)). Qed.
Lemma lem1536365 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1536366 (x : real) : (term179 x) = (term180 x).
Proof. exact (MK_COMB (@lem1536365) (@lem1536364 x)). Qed.
Lemma lem1536367 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536368 (x : real) : ((term158 x) = term14) = ((term172 x) = term14).
Proof. exact (MK_COMB (@lem1536366 x) (@lem1536367)). Qed.
Lemma lem1536369 (x : real) : ((term157 x) = term14) = ((term172 x) = term14).
Proof. exact (TRANS (@lem1536317 x) (@lem1536368 x)). Qed.
Lemma lem1536370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536371 (x : real) : (term181 x) = (term182 x).
Proof. exact (MK_COMB (@lem1536370) (@lem1536369 x)). Qed.
Lemma lem1536372 (x : real) : (term117 x) = (term183 x).
Proof. exact (MK_COMB (@lem1536371 x) (@lem1536291 x)). Qed.
Lemma lem1536373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536374 (x : real) : (term118 x) = (term184 x).
Proof. exact (MK_COMB (@lem1536373) (@lem1536316 x)). Qed.
Lemma lem1536375 (x : real) : (term120 x) = (term185 x).
Proof. exact (MK_COMB (@lem1536374 x) (@lem1536372 x)). Qed.
Lemma lem1536376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536377 (x : real) : (term127 x) = (term186 x).
Proof. exact (MK_COMB (@lem1536376) (@lem1536297 x)). Qed.
Lemma lem1536378 (x : real) : (term128 x) = (term187 x).
Proof. exact (MK_COMB (@lem1536377 x) (@lem1536375 x)). Qed.
Lemma lem1536390 (x : real) : (term30 x) = (term187 x).
Proof. exact (TRANS (@lem1536200 x) (@lem1536378 x)). Qed.
Lemma lem1536392 (x : real) : (term188 x) = (term189 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem1536393 (x : real) : (term189 x) = (term188 x).
Proof. exact (SYM (@lem1536392 x)). Qed.
Lemma lem1536394 (x : real) : (term188 x) = (term190 x).
Proof. exact (@lem1482981 (term191 x) x). Qed.
Lemma lem1536395 (x : real) : (term189 x) = (term190 x).
Proof. exact (TRANS (@lem1536393 x) (@lem1536394 x)). Qed.
Lemma lem1536396 (x : real) : (term192 x) = (term193 x).
Proof. exact (eq_refl (term192 x)). Qed.
Lemma lem1536397 (x : real) : (term118 x) = (term118 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem1536398 (x : real) : (term194 x) = (term195 x).
Proof. exact (MK_COMB (@lem1536397 x) (@lem1536396 x)). Qed.
Lemma lem1536399 (x : real) : (term196 x) = (term197 x).
Proof. exact (eq_refl (term196 x)). Qed.
Lemma lem1536400 (x : real) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1536401 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1536400 x) (@lem1536399 x)). Qed.
Lemma lem1536402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536403 (x : real) : (term200 x) = (term201 x).
Proof. exact (MK_COMB (@lem1536402) (@lem1536401 x)). Qed.
Lemma lem1536404 (x : real) : (term190 x) = (term202 x).
Proof. exact (MK_COMB (@lem1536403 x) (@lem1536398 x)). Qed.
Lemma lem1536405 (x : real) : (term203 x) = (term203 x).
Proof. exact (eq_refl (term203 x)). Qed.
Lemma lem1536406 (x : real) : ((term189 x) = (term190 x)) = ((term189 x) = (term202 x)).
Proof. exact (MK_COMB (@lem1536405 x) (@lem1536404 x)). Qed.
Lemma lem1536407 (x : real) : (term189 x) = (term202 x).
Proof. exact (EQ_MP (@lem1536406 x) (@lem1536395 x)). Qed.
Lemma lem1536408 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483525 (term130 x) term14). Qed.
Lemma lem1536409 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536421 (x : real) : (term130 x) = (term132 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1536423 (m : nat) : (term133 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1536424 : term134 = term14.
Proof. exact (@lem1536423 term45). Qed.
Lemma lem1536425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536426 : term135 = term136.
Proof. exact (MK_COMB (@lem1536425) (@lem1536424)). Qed.
Lemma lem1536427 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536428 (x : real) : (term132 x) = (term137 x).
Proof. exact (MK_COMB (@lem1536426) (@lem1536427 x)). Qed.
Lemma lem1536429 (x : real) : (term130 x) = (term137 x).
Proof. exact (TRANS (@lem1536421 x) (@lem1536428 x)). Qed.
Lemma lem1536430 (x : real) : (term137 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1536432 (x : real) : (term130 x) = term14.
Proof. exact (TRANS (@lem1536429 x) (@lem1536430 x)). Qed.
Lemma lem1536433 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1536434 (x : real) : (term138 x) = term139.
Proof. exact (MK_COMB (@lem1536433) (@lem1536432 x)). Qed.
Lemma lem1536435 (x : real) : (term131 x) = term140.
Proof. exact (MK_COMB (@lem1536434 x) (@lem1536409)). Qed.
Lemma lem1536436 : term140 = term141.
Proof. exact (@lem1483519 term14 term14). Qed.
Lemma lem1536438 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1536439 : term70 = term14.
Proof. exact (@lem1536438 term45). Qed.
Lemma lem1536440 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem1536441 : term141 = term143.
Proof. exact (MK_COMB (@lem1536440) (@lem1536439)). Qed.
Lemma lem1536442 : term143 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1536443 : term141 = term14.
Proof. exact (TRANS (@lem1536441) (@lem1536442)). Qed.
Lemma lem1536444 : term140 = term14.
Proof. exact (TRANS (@lem1536436) (@lem1536443)). Qed.
Lemma lem1536445 (x : real) : (term131 x) = term14.
Proof. exact (TRANS (@lem1536435 x) (@lem1536444)). Qed.
Lemma lem1536446 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536447 (x : real) : (term206 x) = term207.
Proof. exact (MK_COMB (@lem1536446) (@lem1536445 x)). Qed.
Lemma lem1536448 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536449 (x : real) : (term205 x) = term208.
Proof. exact (MK_COMB (@lem1536447 x) (@lem1536448)). Qed.
Lemma lem1536450 (x : real) : (term204 x) = term208.
Proof. exact (TRANS (@lem1536408 x) (@lem1536449 x)). Qed.
Lemma lem1536451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536452 (x : real) : (term209 x) = term210.
Proof. exact (MK_COMB (@lem1536451) (@lem1536450 x)). Qed.
Lemma lem1536453 (x : real) : (term197 x) = (term211 x).
Proof. exact (MK_COMB (@lem1536452 x) (@lem1536221 x)). Qed.
Lemma lem1536454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536455 (x : real) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem1536454) (@lem1536221 x)). Qed.
Lemma lem1536456 (x : real) : (term199 x) = (term212 x).
Proof. exact (MK_COMB (@lem1536455 x) (@lem1536453 x)). Qed.
Lemma lem1536457 (x : real) : (term213 x) = (term214 x).
Proof. exact (@lem1483525 (term157 x) term14). Qed.
Lemma lem1536458 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536465 (x : real) : (real_neg x) = (term17 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1536474 (x : real) : (term149 x) = (term149 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1536475 (x : real) : (term157 x) = (term159 x).
Proof. exact (MK_COMB (@lem1536474 x) (@lem1536465 x)). Qed.
Lemma lem1536476 (x : real) : (term159 x) = (term160 x).
Proof. exact (@lem1483438 term37 term37 x). Qed.
Lemma lem1536477 : term161 = term162.
Proof. exact (@lem1367763 term45 term45). Qed.
Lemma lem1536478 : term163 = term164.
Proof. exact (@lem706885). Qed.
Lemma lem1536479 : (term163 = term164) = (term165 = term166).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term164). Qed.
Lemma lem1536480 : term165 = term166.
Proof. exact (EQ_MP (@lem1536479) (@lem1536478)). Qed.
Lemma lem1536481 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1536482 : term167 = term168.
Proof. exact (MK_COMB (@lem1536481) (@lem1536480)). Qed.
Lemma lem1536483 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1536484 : term162 = term169.
Proof. exact (MK_COMB (@lem1536483) (@lem1536482)). Qed.
Lemma lem1536485 : term161 = term169.
Proof. exact (TRANS (@lem1536477) (@lem1536484)). Qed.
Lemma lem1536486 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536487 : term170 = term171.
Proof. exact (MK_COMB (@lem1536486) (@lem1536485)). Qed.
Lemma lem1536488 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536489 (x : real) : (term160 x) = (term172 x).
Proof. exact (MK_COMB (@lem1536487) (@lem1536488 x)). Qed.
Lemma lem1536490 (x : real) : (term159 x) = (term172 x).
Proof. exact (TRANS (@lem1536476 x) (@lem1536489 x)). Qed.
Lemma lem1536491 (x : real) : (term157 x) = (term172 x).
Proof. exact (TRANS (@lem1536475 x) (@lem1536490 x)). Qed.
Lemma lem1536492 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1536493 (x : real) : (term173 x) = (term174 x).
Proof. exact (MK_COMB (@lem1536492) (@lem1536491 x)). Qed.
Lemma lem1536494 (x : real) : (term158 x) = (term175 x).
Proof. exact (MK_COMB (@lem1536493 x) (@lem1536458)). Qed.
Lemma lem1536495 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 (term172 x) term14). Qed.
Lemma lem1536497 (x : nat) : (term69 x) = term14.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1536498 : term70 = term14.
Proof. exact (@lem1536497 term45). Qed.
Lemma lem1536499 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1536500 (x : real) : (term176 x) = (term178 x).
Proof. exact (MK_COMB (@lem1536499 x) (@lem1536498)). Qed.
Lemma lem1536501 (x : real) : (term178 x) = (term172 x).
Proof. exact (@lem1483450 (term172 x)). Qed.
Lemma lem1536502 (x : real) : (term176 x) = (term172 x).
Proof. exact (TRANS (@lem1536500 x) (@lem1536501 x)). Qed.
Lemma lem1536503 (x : real) : (term175 x) = (term172 x).
Proof. exact (TRANS (@lem1536495 x) (@lem1536502 x)). Qed.
Lemma lem1536504 (x : real) : (term158 x) = (term172 x).
Proof. exact (TRANS (@lem1536494 x) (@lem1536503 x)). Qed.
Lemma lem1536505 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536506 (x : real) : (term215 x) = (term216 x).
Proof. exact (MK_COMB (@lem1536505) (@lem1536504 x)). Qed.
Lemma lem1536507 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536508 (x : real) : (term214 x) = (term217 x).
Proof. exact (MK_COMB (@lem1536506 x) (@lem1536507)). Qed.
Lemma lem1536509 (x : real) : (term213 x) = (term217 x).
Proof. exact (TRANS (@lem1536457 x) (@lem1536508 x)). Qed.
Lemma lem1536510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536511 (x : real) : (term218 x) = (term219 x).
Proof. exact (MK_COMB (@lem1536510) (@lem1536509 x)). Qed.
Lemma lem1536512 (x : real) : (term193 x) = (term220 x).
Proof. exact (MK_COMB (@lem1536511 x) (@lem1536221 x)). Qed.
Lemma lem1536513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536514 (x : real) : (term118 x) = (term184 x).
Proof. exact (MK_COMB (@lem1536513) (@lem1536316 x)). Qed.
Lemma lem1536515 (x : real) : (term195 x) = (term221 x).
Proof. exact (MK_COMB (@lem1536514 x) (@lem1536512 x)). Qed.
Lemma lem1536516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536517 (x : real) : (term201 x) = (term222 x).
Proof. exact (MK_COMB (@lem1536516) (@lem1536456 x)). Qed.
Lemma lem1536518 (x : real) : (term202 x) = (term223 x).
Proof. exact (MK_COMB (@lem1536517 x) (@lem1536515 x)). Qed.
Lemma lem1536530 (x : real) : (term189 x) = (term223 x).
Proof. exact (TRANS (@lem1536407 x) (@lem1536518 x)). Qed.
Lemma lem1536532 (a : real) (x : real) (r : real) : (term224 a x r) = (term225 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1536533 (x : real) : (term58 x) = (term226 x).
Proof. exact (@lem1536532 x x term14). Qed.
Lemma lem1536540 (x : real) : (term51 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1536543 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1536544 (x : real) : (term227 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1536543 x) (@lem1536540 x)). Qed.
Lemma lem1536545 (x : real) : (real_add x x) = (term228 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1536546 : term229 = term167.
Proof. exact (@lem1367770 term45 term45). Qed.
Lemma lem1536547 : term163 = term164.
Proof. exact (@lem706885). Qed.
Lemma lem1536548 : (term163 = term164) = (term165 = term166).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term164). Qed.
Lemma lem1536549 : term165 = term166.
Proof. exact (EQ_MP (@lem1536548) (@lem1536547)). Qed.
Lemma lem1536550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1536551 : term167 = term168.
Proof. exact (MK_COMB (@lem1536550) (@lem1536549)). Qed.
Lemma lem1536552 : term229 = term168.
Proof. exact (TRANS (@lem1536546) (@lem1536551)). Qed.
Lemma lem1536553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536554 : term230 = term231.
Proof. exact (MK_COMB (@lem1536553) (@lem1536552)). Qed.
Lemma lem1536555 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536556 (x : real) : (term228 x) = (term232 x).
Proof. exact (MK_COMB (@lem1536554) (@lem1536555 x)). Qed.
Lemma lem1536557 (x : real) : (real_add x x) = (term232 x).
Proof. exact (TRANS (@lem1536545 x) (@lem1536556 x)). Qed.
Lemma lem1536558 (x : real) : (term227 x) = (term232 x).
Proof. exact (TRANS (@lem1536544 x) (@lem1536557 x)). Qed.
Lemma lem1536559 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536560 (x : real) : (term233 x) = (term234 x).
Proof. exact (MK_COMB (@lem1536559) (@lem1536558 x)). Qed.
Lemma lem1536561 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536562 (x : real) : (term235 x) = (term236 x).
Proof. exact (MK_COMB (@lem1536560 x) (@lem1536561)). Qed.
Lemma lem1536574 (x : real) : (term237 x) = (term132 x).
Proof. exact (@lem1483442 term37 x). Qed.
Lemma lem1536576 (m : nat) : (term133 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1536577 : term134 = term14.
Proof. exact (@lem1536576 term45). Qed.
Lemma lem1536578 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536579 : term135 = term136.
Proof. exact (MK_COMB (@lem1536578) (@lem1536577)). Qed.
Lemma lem1536580 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536581 (x : real) : (term132 x) = (term137 x).
Proof. exact (MK_COMB (@lem1536579) (@lem1536580 x)). Qed.
Lemma lem1536582 (x : real) : (term237 x) = (term137 x).
Proof. exact (TRANS (@lem1536574 x) (@lem1536581 x)). Qed.
Lemma lem1536583 (x : real) : (term137 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1536585 (x : real) : (term237 x) = term14.
Proof. exact (TRANS (@lem1536582 x) (@lem1536583 x)). Qed.
Lemma lem1536586 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536587 (x : real) : (term238 x) = term207.
Proof. exact (MK_COMB (@lem1536586) (@lem1536585 x)). Qed.
Lemma lem1536588 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536589 (x : real) : (term239 x) = term208.
Proof. exact (MK_COMB (@lem1536587 x) (@lem1536588)). Qed.
Lemma lem1536590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536591 (x : real) : (term240 x) = term210.
Proof. exact (MK_COMB (@lem1536590) (@lem1536589 x)). Qed.
Lemma lem1536592 (x : real) : (term226 x) = (term241 x).
Proof. exact (MK_COMB (@lem1536591 x) (@lem1536562 x)). Qed.
Lemma lem1536593 (x : real) : (term58 x) = (term241 x).
Proof. exact (TRANS (@lem1536533 x) (@lem1536592 x)). Qed.
Lemma lem1536594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536595 (x : real) : (term242 x) = (term243 x).
Proof. exact (MK_COMB (@lem1536594) (@lem1536593 x)). Qed.
Lemma lem1536596 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1536599 (x : real) : (term244 x) = (term245 x).
Proof. exact (MK_COMB (@lem1536595 x) (@lem1536596 x)). Qed.
Lemma lem1536600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536601 (x : real) : (term246 x) = (term247 x).
Proof. exact (MK_COMB (@lem1536600) (@lem1536530 x)). Qed.
Lemma lem1536602 (x : real) : (term109 x) = (term248 x).
Proof. exact (MK_COMB (@lem1536601 x) (@lem1536599 x)). Qed.
Lemma lem1536603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1536604 (x : real) : (term79 x) = (term249 x).
Proof. exact (MK_COMB (@lem1536603) (@lem1536390 x)). Qed.
Lemma lem1536605 (x : real) : (term110 x) = (term250 x).
Proof. exact (MK_COMB (@lem1536604 x) (@lem1536602 x)). Qed.
Lemma lem1536606 (x : real) (h1 : term250 x) : term250 x.
Proof. exact (h1). Qed.
Lemma lem1536607 (x : real) (h1 : term187 x) : term187 x.
Proof. exact (h1). Qed.
Lemma lem1536608 (x : real) (h1 : term155 x) : term155 x.
Proof. exact (h1). Qed.
Lemma lem1536609 (x : real) (h1 : term155 x) : term154 x.
Proof. exact (proj2 (@lem1536608 x h1)). Qed.
Lemma lem1536610 (x : real) (h1 : term155 x) : term73 x.
Proof. exact (proj1 (@lem1536608 x h1)). Qed.
Lemma lem1536611 (x : real) (h1 : term155 x) : term26 x.
Proof. exact (proj2 (@lem1536609 x h1)). Qed.
Lemma lem1536614 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536615 : term252 = term253.
Proof. exact (@lem1536614 (NUMERAL 0) term45). Qed.
Lemma lem1536616 : term254 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1536617 (h1 : term254 = (BIT1 0)) : term253 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1536618 : (term254 = (BIT1 0)) = (term253 = True).
Proof. exact (prop_ext (fun h1 : term254 = (BIT1 0) => @lem1536617 h1) (fun h1 : term253 = True => @lem1536616)). Qed.
Lemma lem1536619 : term253 = True.
Proof. exact (EQ_MP (@lem1536618) (@lem1536616)). Qed.
Lemma lem1536620 : term252 = True.
Proof. exact (TRANS (@lem1536615) (@lem1536619)). Qed.
Lemma lem1536621 : True = term252.
Proof. exact (SYM (@lem1536620)). Qed.
Lemma lem1536622 : term252.
Proof. exact (EQ_MP (@lem1536621) (@lem0)). Qed.
Lemma lem1536623 (x : real) (h1 : term155 x) : term255 x.
Proof. exact (conj (@lem1536622) (@lem1536610 x h1)). Qed.
Lemma lem1536625 (x : real) (y : real) : term256 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1536626 (x : real) : term257 x.
Proof. exact (@lem1536625 term48 x). Qed.
Lemma lem1536627 (x : real) (h1 : term155 x) : term258 x.
Proof. exact (@lem1536626 x (@lem1536623 x h1)). Qed.
Lemma lem1536628 (x : real) : (term51 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1536629 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1536630 (x : real) : (term259 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1536629) (@lem1536628 x)). Qed.
Lemma lem1536631 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536632 (x : real) : (term258 x) = (term73 x).
Proof. exact (MK_COMB (@lem1536630 x) (@lem1536631)). Qed.
Lemma lem1536633 (x : real) (h1 : term155 x) : term73 x.
Proof. exact (EQ_MP (@lem1536632 x) (@lem1536627 x h1)). Qed.
Lemma lem1536635 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536636 : term252 = term253.
Proof. exact (@lem1536635 (NUMERAL 0) term45). Qed.
Lemma lem1536637 : term254 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1536638 (h1 : term254 = (BIT1 0)) : term253 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1536639 : (term254 = (BIT1 0)) = (term253 = True).
Proof. exact (prop_ext (fun h1 : term254 = (BIT1 0) => @lem1536638 h1) (fun h1 : term253 = True => @lem1536637)). Qed.
Lemma lem1536640 : term253 = True.
Proof. exact (EQ_MP (@lem1536639) (@lem1536637)). Qed.
Lemma lem1536641 : term252 = True.
Proof. exact (TRANS (@lem1536636) (@lem1536640)). Qed.
Lemma lem1536642 : True = term252.
Proof. exact (SYM (@lem1536641)). Qed.
Lemma lem1536643 : term252.
Proof. exact (EQ_MP (@lem1536642) (@lem0)). Qed.
Lemma lem1536644 (x : real) (h1 : term155 x) : term260 x.
Proof. exact (conj (@lem1536643) (@lem1536611 x h1)). Qed.
Lemma lem1536646 (x : real) (y : real) : term261 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1536647 (x : real) : term262 x.
Proof. exact (@lem1536646 term48 (term17 x)). Qed.
Lemma lem1536648 (x : real) (h1 : term155 x) : term263 x.
Proof. exact (@lem1536647 x (@lem1536644 x h1)). Qed.
Lemma lem1536649 (x : real) : (term264 x) = (term17 x).
Proof. exact (@lem1483460 (term17 x)). Qed.
Lemma lem1536650 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536651 (x : real) : (term265 x) = (term25 x).
Proof. exact (MK_COMB (@lem1536650) (@lem1536649 x)). Qed.
Lemma lem1536652 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536653 (x : real) : (term263 x) = (term26 x).
Proof. exact (MK_COMB (@lem1536651 x) (@lem1536652)). Qed.
Lemma lem1536654 (x : real) (h1 : term155 x) : term26 x.
Proof. exact (EQ_MP (@lem1536653 x) (@lem1536648 x h1)). Qed.
Lemma lem1536655 (x : real) (h1 : term155 x) : term266 x.
Proof. exact (conj (@lem1536654 x h1) (@lem1536633 x h1)). Qed.
Lemma lem1536657 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1536658 (x : real) : term268 x.
Proof. exact (@lem1536657 (term17 x) x). Qed.
Lemma lem1536659 (x : real) (h1 : term155 x) : term204 x.
Proof. exact (@lem1536658 x (@lem1536655 x h1)). Qed.
Lemma lem1536660 (x : real) : (term130 x) = (term132 x).
Proof. exact (@lem1483440 term37 x). Qed.
Lemma lem1536662 (m : nat) : (term133 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1536663 : term134 = term14.
Proof. exact (@lem1536662 term45). Qed.
Lemma lem1536664 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536665 : term135 = term136.
Proof. exact (MK_COMB (@lem1536664) (@lem1536663)). Qed.
Lemma lem1536666 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536667 (x : real) : (term132 x) = (term137 x).
Proof. exact (MK_COMB (@lem1536665) (@lem1536666 x)). Qed.
Lemma lem1536668 (x : real) : (term130 x) = (term137 x).
Proof. exact (TRANS (@lem1536660 x) (@lem1536667 x)). Qed.
Lemma lem1536669 (x : real) : (term137 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1536670 (x : real) : (term130 x) = term14.
Proof. exact (TRANS (@lem1536668 x) (@lem1536669 x)). Qed.
Lemma lem1536671 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536672 (x : real) : (term269 x) = term207.
Proof. exact (MK_COMB (@lem1536671) (@lem1536670 x)). Qed.
Lemma lem1536673 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536674 (x : real) : (term204 x) = term208.
Proof. exact (MK_COMB (@lem1536672 x) (@lem1536673)). Qed.
Lemma lem1536675 (x : real) (h1 : term155 x) : term208.
Proof. exact (EQ_MP (@lem1536674 x) (@lem1536659 x h1)). Qed.
Lemma lem1536677 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536678 : term208 = term270.
Proof. exact (@lem1536677 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1536679 : term270 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1536680 : term208 = False.
Proof. exact (TRANS (@lem1536678) (@lem1536679)). Qed.
Lemma lem1536681 (x : real) (h1 : term155 x) : False.
Proof. exact (EQ_MP (@lem1536680) (@lem1536675 x h1)). Qed.
Lemma lem1536682 (x : real) (h1 : term185 x) : term185 x.
Proof. exact (h1). Qed.
Lemma lem1536683 (x : real) (h1 : term185 x) : term183 x.
Proof. exact (proj2 (@lem1536682 x h1)). Qed.
Lemma lem1536685 (x : real) (h1 : term185 x) : term26 x.
Proof. exact (proj2 (@lem1536683 x h1)). Qed.
Lemma lem1536686 (x : real) (h1 : term185 x) : (term172 x) = term14.
Proof. exact (proj1 (@lem1536683 x h1)). Qed.
Lemma lem1536688 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536689 : term271 = term272.
Proof. exact (@lem1536688 (NUMERAL 0) term166). Qed.
Lemma lem1536690 : term273 = term164.
Proof. exact (@lem912803). Qed.
Lemma lem1536691 (h1 : term273 = term164) : term272 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term164 h1). Qed.
Lemma lem1536692 : (term273 = term164) = (term272 = True).
Proof. exact (prop_ext (fun h1 : term273 = term164 => @lem1536691 h1) (fun h1 : term272 = True => @lem1536690)). Qed.
Lemma lem1536693 : term272 = True.
Proof. exact (EQ_MP (@lem1536692) (@lem1536690)). Qed.
Lemma lem1536694 : term271 = True.
Proof. exact (TRANS (@lem1536689) (@lem1536693)). Qed.
Lemma lem1536695 : True = term271.
Proof. exact (SYM (@lem1536694)). Qed.
Lemma lem1536696 : term271.
Proof. exact (EQ_MP (@lem1536695) (@lem0)). Qed.
Lemma lem1536697 (x : real) (h1 : term185 x) : term274 x.
Proof. exact (conj (@lem1536696) (@lem1536685 x h1)). Qed.
Lemma lem1536699 (x : real) (y : real) : term261 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1536700 (x : real) : term275 x.
Proof. exact (@lem1536699 term168 (term17 x)). Qed.
Lemma lem1536701 (x : real) (h1 : term185 x) : term276 x.
Proof. exact (@lem1536700 x (@lem1536697 x h1)). Qed.
Lemma lem1536702 (x : real) : (term277 x) = (term278 x).
Proof. exact (@lem1483476 term168 term37 x). Qed.
Lemma lem1536704 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1536705 : term281 = term282.
Proof. exact (@lem1536704 term166 term45). Qed.
Lemma lem1536706 : term283 = term164.
Proof. exact (@lem996237 term164). Qed.
Lemma lem1536707 : (term283 = term164) = (term284 = term166).
Proof. exact (@lem1007663 term164 (BIT1 0) term164). Qed.
Lemma lem1536708 : term284 = term166.
Proof. exact (EQ_MP (@lem1536707) (@lem1536706)). Qed.
Lemma lem1536709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1536710 : term285 = term168.
Proof. exact (MK_COMB (@lem1536709) (@lem1536708)). Qed.
Lemma lem1536711 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1536712 : term282 = term169.
Proof. exact (MK_COMB (@lem1536711) (@lem1536710)). Qed.
Lemma lem1536713 : term281 = term169.
Proof. exact (TRANS (@lem1536705) (@lem1536712)). Qed.
Lemma lem1536714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536715 : term286 = term171.
Proof. exact (MK_COMB (@lem1536714) (@lem1536713)). Qed.
Lemma lem1536716 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536717 (x : real) : (term278 x) = (term172 x).
Proof. exact (MK_COMB (@lem1536715) (@lem1536716 x)). Qed.
Lemma lem1536718 (x : real) : (term277 x) = (term172 x).
Proof. exact (TRANS (@lem1536702 x) (@lem1536717 x)). Qed.
Lemma lem1536719 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536720 (x : real) : (term287 x) = (term216 x).
Proof. exact (MK_COMB (@lem1536719) (@lem1536718 x)). Qed.
Lemma lem1536721 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536722 (x : real) : (term276 x) = (term217 x).
Proof. exact (MK_COMB (@lem1536720 x) (@lem1536721)). Qed.
Lemma lem1536723 (x : real) (h1 : term185 x) : term217 x.
Proof. exact (EQ_MP (@lem1536722 x) (@lem1536701 x h1)). Qed.
Lemma lem1536725 (y : real) : term288 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1536726 (x : real) : term289 x.
Proof. exact (@lem1536725 (term172 x)). Qed.
Lemma lem1536727 (x : real) (h1 : term185 x) : term290 x.
Proof. exact (@lem1536726 x (@lem1536686 x h1)). Qed.
Lemma lem1536728 (x : real) (h1 : term185 x) : term291 x.
Proof. exact (@lem1536727 x h1 term37). Qed.
Lemma lem1536729 (x : real) : (term291 x) = ((term292 x) = term14).
Proof. exact (eq_refl (term291 x)). Qed.
Lemma lem1536730 (x : real) (h1 : term185 x) : (term292 x) = term14.
Proof. exact (EQ_MP (@lem1536729 x) (@lem1536728 x h1)). Qed.
Lemma lem1536731 (x : real) : (term292 x) = (term293 x).
Proof. exact (@lem1483476 term37 term169 x). Qed.
Lemma lem1536733 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1536734 : term294 = term295.
Proof. exact (@lem1536733 term45 term166). Qed.
Lemma lem1536735 : term296 = term164.
Proof. exact (@lem996238 term164). Qed.
Lemma lem1536736 : (term296 = term164) = (term297 = term166).
Proof. exact (@lem1007663 (BIT1 0) term164 term164). Qed.
Lemma lem1536737 : term297 = term166.
Proof. exact (EQ_MP (@lem1536736) (@lem1536735)). Qed.
Lemma lem1536738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1536739 : term295 = term168.
Proof. exact (MK_COMB (@lem1536738) (@lem1536737)). Qed.
Lemma lem1536740 : term294 = term168.
Proof. exact (TRANS (@lem1536734) (@lem1536739)). Qed.
Lemma lem1536741 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536742 : term298 = term231.
Proof. exact (MK_COMB (@lem1536741) (@lem1536740)). Qed.
Lemma lem1536743 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536744 (x : real) : (term293 x) = (term232 x).
Proof. exact (MK_COMB (@lem1536742) (@lem1536743 x)). Qed.
Lemma lem1536745 (x : real) : (term292 x) = (term232 x).
Proof. exact (TRANS (@lem1536731 x) (@lem1536744 x)). Qed.
Lemma lem1536746 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1536747 (x : real) : (term299 x) = (term300 x).
Proof. exact (MK_COMB (@lem1536746) (@lem1536745 x)). Qed.
Lemma lem1536748 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536749 (x : real) : ((term292 x) = term14) = ((term232 x) = term14).
Proof. exact (MK_COMB (@lem1536747 x) (@lem1536748)). Qed.
Lemma lem1536750 (x : real) (h1 : term185 x) : (term232 x) = term14.
Proof. exact (EQ_MP (@lem1536749 x) (@lem1536730 x h1)). Qed.
Lemma lem1536751 (x : real) (h1 : term185 x) : term301 x.
Proof. exact (conj (@lem1536750 x h1) (@lem1536723 x h1)). Qed.
Lemma lem1536753 (x : real) (y : real) : term302 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1536754 (x : real) : term303 x.
Proof. exact (@lem1536753 (term232 x) (term172 x)). Qed.
Lemma lem1536755 (x : real) (h1 : term185 x) : term304 x.
Proof. exact (@lem1536754 x (@lem1536751 x h1)). Qed.
Lemma lem1536756 (x : real) : (term305 x) = (term306 x).
Proof. exact (@lem1483438 term168 term169 x). Qed.
Lemma lem1536758 (m : nat) : (term307 m) = term14.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1536759 : term308 = term14.
Proof. exact (@lem1536758 term166). Qed.
Lemma lem1536760 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536761 : term309 = term136.
Proof. exact (MK_COMB (@lem1536760) (@lem1536759)). Qed.
Lemma lem1536762 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536763 (x : real) : (term306 x) = (term137 x).
Proof. exact (MK_COMB (@lem1536761) (@lem1536762 x)). Qed.
Lemma lem1536764 (x : real) : (term305 x) = (term137 x).
Proof. exact (TRANS (@lem1536756 x) (@lem1536763 x)). Qed.
Lemma lem1536765 (x : real) : (term137 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1536766 (x : real) : (term305 x) = term14.
Proof. exact (TRANS (@lem1536764 x) (@lem1536765 x)). Qed.
Lemma lem1536767 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536768 (x : real) : (term310 x) = term207.
Proof. exact (MK_COMB (@lem1536767) (@lem1536766 x)). Qed.
Lemma lem1536769 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536770 (x : real) : (term304 x) = term208.
Proof. exact (MK_COMB (@lem1536768 x) (@lem1536769)). Qed.
Lemma lem1536771 (x : real) (h1 : term185 x) : term208.
Proof. exact (EQ_MP (@lem1536770 x) (@lem1536755 x h1)). Qed.
Lemma lem1536773 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536774 : term208 = term270.
Proof. exact (@lem1536773 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1536775 : term270 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1536776 : term208 = False.
Proof. exact (TRANS (@lem1536774) (@lem1536775)). Qed.
Lemma lem1536777 (x : real) (h1 : term185 x) : False.
Proof. exact (EQ_MP (@lem1536776) (@lem1536771 x h1)). Qed.
Lemma lem1536778 (x : real) (h1 : term187 x) : False.
Proof. exact (or_elim (@lem1536607 x h1) (fun h0 : term155 x => @lem1536681 x h0) (fun h0 : term185 x => @lem1536777 x h0)). Qed.
Lemma lem1536779 (x : real) (h1 : term248 x) : term248 x.
Proof. exact (h1). Qed.
Lemma lem1536780 (x : real) (h1 : term223 x) : term223 x.
Proof. exact (h1). Qed.
Lemma lem1536781 (x : real) (h1 : term212 x) : term212 x.
Proof. exact (h1). Qed.
Lemma lem1536782 (x : real) (h1 : term212 x) : term211 x.
Proof. exact (proj2 (@lem1536781 x h1)). Qed.
Lemma lem1536785 (x : real) (h1 : term212 x) : term208.
Proof. exact (proj1 (@lem1536782 x h1)). Qed.
Lemma lem1536787 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536788 : term208 = term270.
Proof. exact (@lem1536787 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1536789 : term270 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1536790 : term208 = False.
Proof. exact (TRANS (@lem1536788) (@lem1536789)). Qed.
Lemma lem1536791 (x : real) (h1 : term212 x) : False.
Proof. exact (EQ_MP (@lem1536790) (@lem1536785 x h1)). Qed.
Lemma lem1536792 (x : real) (h1 : term221 x) : term221 x.
Proof. exact (h1). Qed.
Lemma lem1536793 (x : real) (h1 : term221 x) : term220 x.
Proof. exact (proj2 (@lem1536792 x h1)). Qed.
Lemma lem1536795 (x : real) (h1 : term221 x) : term73 x.
Proof. exact (proj2 (@lem1536793 x h1)). Qed.
Lemma lem1536796 (x : real) (h1 : term221 x) : term217 x.
Proof. exact (proj1 (@lem1536793 x h1)). Qed.
Lemma lem1536798 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536799 : term271 = term272.
Proof. exact (@lem1536798 (NUMERAL 0) term166). Qed.
Lemma lem1536800 : term273 = term164.
Proof. exact (@lem912803). Qed.
Lemma lem1536801 (h1 : term273 = term164) : term272 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term164 h1). Qed.
Lemma lem1536802 : (term273 = term164) = (term272 = True).
Proof. exact (prop_ext (fun h1 : term273 = term164 => @lem1536801 h1) (fun h1 : term272 = True => @lem1536800)). Qed.
Lemma lem1536803 : term272 = True.
Proof. exact (EQ_MP (@lem1536802) (@lem1536800)). Qed.
Lemma lem1536804 : term271 = True.
Proof. exact (TRANS (@lem1536799) (@lem1536803)). Qed.
Lemma lem1536805 : True = term271.
Proof. exact (SYM (@lem1536804)). Qed.
Lemma lem1536806 : term271.
Proof. exact (EQ_MP (@lem1536805) (@lem0)). Qed.
Lemma lem1536807 (x : real) (h1 : term221 x) : term311 x.
Proof. exact (conj (@lem1536806) (@lem1536795 x h1)). Qed.
Lemma lem1536809 (x : real) (y : real) : term256 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1536810 (x : real) : term312 x.
Proof. exact (@lem1536809 term168 x). Qed.
Lemma lem1536817 (x : real) (h1 : term221 x) : term313 x.
Proof. exact (@lem1536810 x (@lem1536807 x h1)). Qed.
Lemma lem1536819 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536820 : term252 = term253.
Proof. exact (@lem1536819 (NUMERAL 0) term45). Qed.
Lemma lem1536821 : term254 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1536822 (h1 : term254 = (BIT1 0)) : term253 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1536823 : (term254 = (BIT1 0)) = (term253 = True).
Proof. exact (prop_ext (fun h1 : term254 = (BIT1 0) => @lem1536822 h1) (fun h1 : term253 = True => @lem1536821)). Qed.
Lemma lem1536824 : term253 = True.
Proof. exact (EQ_MP (@lem1536823) (@lem1536821)). Qed.
Lemma lem1536825 : term252 = True.
Proof. exact (TRANS (@lem1536820) (@lem1536824)). Qed.
Lemma lem1536826 : True = term252.
Proof. exact (SYM (@lem1536825)). Qed.
Lemma lem1536827 : term252.
Proof. exact (EQ_MP (@lem1536826) (@lem0)). Qed.
Lemma lem1536828 (x : real) (h1 : term221 x) : term314 x.
Proof. exact (conj (@lem1536827) (@lem1536796 x h1)). Qed.
Lemma lem1536830 (x : real) (y : real) : term261 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1536831 (x : real) : term315 x.
Proof. exact (@lem1536830 term48 (term172 x)). Qed.
Lemma lem1536832 (x : real) (h1 : term221 x) : term316 x.
Proof. exact (@lem1536831 x (@lem1536828 x h1)). Qed.
Lemma lem1536833 (x : real) : (term317 x) = (term172 x).
Proof. exact (@lem1483460 (term172 x)). Qed.
Lemma lem1536834 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536835 (x : real) : (term318 x) = (term216 x).
Proof. exact (MK_COMB (@lem1536834) (@lem1536833 x)). Qed.
Lemma lem1536836 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536837 (x : real) : (term316 x) = (term217 x).
Proof. exact (MK_COMB (@lem1536835 x) (@lem1536836)). Qed.
Lemma lem1536838 (x : real) (h1 : term221 x) : term217 x.
Proof. exact (EQ_MP (@lem1536837 x) (@lem1536832 x h1)). Qed.
Lemma lem1536839 (x : real) (h1 : term221 x) : term319 x.
Proof. exact (conj (@lem1536838 x h1) (@lem1536817 x h1)). Qed.
Lemma lem1536841 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1536842 (x : real) : term320 x.
Proof. exact (@lem1536841 (term172 x) (term232 x)). Qed.
Lemma lem1536843 (x : real) (h1 : term221 x) : term321 x.
Proof. exact (@lem1536842 x (@lem1536839 x h1)). Qed.
Lemma lem1536844 (x : real) : (term322 x) = (term323 x).
Proof. exact (@lem1483438 term169 term168 x). Qed.
Lemma lem1536846 (m : nat) : (term133 m) = term14.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1536847 : term324 = term14.
Proof. exact (@lem1536846 term166). Qed.
Lemma lem1536848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1536849 : term325 = term136.
Proof. exact (MK_COMB (@lem1536848) (@lem1536847)). Qed.
Lemma lem1536850 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1536851 (x : real) : (term323 x) = (term137 x).
Proof. exact (MK_COMB (@lem1536849) (@lem1536850 x)). Qed.
Lemma lem1536852 (x : real) : (term322 x) = (term137 x).
Proof. exact (TRANS (@lem1536844 x) (@lem1536851 x)). Qed.
Lemma lem1536853 (x : real) : (term137 x) = term14.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1536854 (x : real) : (term322 x) = term14.
Proof. exact (TRANS (@lem1536852 x) (@lem1536853 x)). Qed.
Lemma lem1536855 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1536856 (x : real) : (term326 x) = term207.
Proof. exact (MK_COMB (@lem1536855) (@lem1536854 x)). Qed.
Lemma lem1536857 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1536858 (x : real) : (term321 x) = term208.
Proof. exact (MK_COMB (@lem1536856 x) (@lem1536857)). Qed.
Lemma lem1536859 (x : real) (h1 : term221 x) : term208.
Proof. exact (EQ_MP (@lem1536858 x) (@lem1536843 x h1)). Qed.
Lemma lem1536861 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536862 : term208 = term270.
Proof. exact (@lem1536861 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1536863 : term270 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1536864 : term208 = False.
Proof. exact (TRANS (@lem1536862) (@lem1536863)). Qed.
Lemma lem1536865 (x : real) (h1 : term221 x) : False.
Proof. exact (EQ_MP (@lem1536864) (@lem1536859 x h1)). Qed.
Lemma lem1536866 (x : real) (h1 : term223 x) : False.
Proof. exact (or_elim (@lem1536780 x h1) (fun h0 : term212 x => @lem1536791 x h0) (fun h0 : term221 x => @lem1536865 x h0)). Qed.
Lemma lem1536867 (x : real) (h1 : term245 x) : term245 x.
Proof. exact (h1). Qed.
Lemma lem1536869 (x : real) (h1 : term245 x) : term241 x.
Proof. exact (proj1 (@lem1536867 x h1)). Qed.
Lemma lem1536871 (x : real) (h1 : term245 x) : term208.
Proof. exact (proj1 (@lem1536869 x h1)). Qed.
Lemma lem1536873 (n : nat) (m : nat) : (term251 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1536874 : term208 = term270.
Proof. exact (@lem1536873 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1536875 : term270 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1536876 : term208 = False.
Proof. exact (TRANS (@lem1536874) (@lem1536875)). Qed.
Lemma lem1536877 (x : real) (h1 : term245 x) : False.
Proof. exact (EQ_MP (@lem1536876) (@lem1536871 x h1)). Qed.
Lemma lem1536878 (x : real) (h1 : term248 x) : False.
Proof. exact (or_elim (@lem1536779 x h1) (fun h0 : term223 x => @lem1536866 x h0) (fun h0 : term245 x => @lem1536877 x h0)). Qed.
Lemma lem1536879 (x : real) (h1 : term250 x) : False.
Proof. exact (or_elim (@lem1536606 x h1) (fun h0 : term187 x => @lem1536778 x h0) (fun h0 : term248 x => @lem1536878 x h0)). Qed.
Lemma lem1536880 (x : real) (h1 : term110 x) : term110 x.
Proof. exact (h1). Qed.
Lemma lem1536881 (x : real) (h1 : term110 x) : term250 x.
Proof. exact (EQ_MP (@lem1536605 x) (@lem1536880 x h1)). Qed.
Lemma lem1536882 (x : real) (h1 : term110 x) : (term250 x) = False.
Proof. exact (prop_ext (fun h2 : term250 x => @lem1536879 x h2) (fun h2 : False => @lem1536881 x h1)). Qed.
Lemma lem1536883 (x : real) (h1 : term110 x) : False.
Proof. exact (EQ_MP (@lem1536882 x h1) (@lem1536881 x h1)). Qed.
Lemma lem1536884 (h1 : term112) : term112.
Proof. exact (h1). Qed.
Lemma lem1536885 (h1 : term112) : False.
Proof. exact (ex_elim (@lem1536884 h1) (fun x : real => fun h0 : term111 x => @lem1536883 x h0)). Qed.
Lemma lem1536886 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1536887 (h1 : term5) : term112.
Proof. exact (EQ_MP (@lem1536183) (@lem1536886 h1)). Qed.
Lemma lem1536888 (h1 : term5) : term112 = False.
Proof. exact (prop_ext (fun h2 : term112 => @lem1536885 h2) (fun h2 : False => @lem1536887 h1)). Qed.
Lemma lem1536889 (h1 : term5) : False.
Proof. exact (EQ_MP (@lem1536888 h1) (@lem1536887 h1)). Qed.
Lemma lem1536890 : term327.
Proof. exact (fun h0 : term5 => @lem1536889 h0). Qed.
Lemma lem1536891 : term328.
Proof. exact (@lem1386578 term329). Qed.
Lemma lem1536892 : term329.
Proof. exact (@lem1536891 (@lem1536890)). Qed.
