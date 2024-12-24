Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_GT_term_abbrevs.
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
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1493896 (y : real) (x : real) : (term0 y x) = (real_lt y x).
Proof. exact (@lem16933 (real_lt y x)). Qed.
Lemma lem1493898 (x : real) (y : real) : (term1 x y) = (term1 x y).
Proof. exact (eq_refl (term1 x y)). Qed.
Lemma lem1493899 (y : real) (x : real) : (term2 y x) = (term3 y x).
Proof. exact (MK_COMB (@lem1493898 x y) (@lem1493896 y x)). Qed.
Lemma lem1493900 (y : real) (x : real) : (term4 y x) = (term2 y x).
Proof. exact (@lem17362 (real_lt x y) (term5 y x)). Qed.
Lemma lem1493901 (y : real) (x : real) : (term4 y x) = (term3 y x).
Proof. exact (TRANS (@lem1493900 y x) (@lem1493899 y x)). Qed.
Lemma lem1493902 (P : real -> Prop) : (term6 P) = (term7 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1493903 (x : real) : (term8 x) = (term9 x).
Proof. exact (@lem1493902 (term10 x)). Qed.
Lemma lem1493904 (y : real) (x : real) : (term11 x y) = (term12 y x).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1493905 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1493906 (y : real) (x : real) : (term13 x y) = (term4 y x).
Proof. exact (MK_COMB (@lem1493905) (@lem1493904 y x)). Qed.
Lemma lem1493907 (y : real) (x : real) : (term13 x y) = (term3 y x).
Proof. exact (TRANS (@lem1493906 y x) (@lem1493901 y x)). Qed.
Lemma lem1493908 (x : real) : (term14 x) = (term15 x).
Proof. exact (fun_ext (fun y : real => @lem1493907 y x)). Qed.
Lemma lem1493909 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493910 (x : real) : (term9 x) = (term16 x).
Proof. exact (MK_COMB (@lem1493909) (@lem1493908 x)). Qed.
Lemma lem1493911 (x : real) : (term8 x) = (term16 x).
Proof. exact (TRANS (@lem1493903 x) (@lem1493910 x)). Qed.
Lemma lem1493912 (P : real -> Prop) : (term6 P) = (term7 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1493913 : term17 = term18.
Proof. exact (@lem1493912 term19). Qed.
Lemma lem1493914 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1493915 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1493916 (x : real) : (term22 x) = (term8 x).
Proof. exact (MK_COMB (@lem1493915) (@lem1493914 x)). Qed.
Lemma lem1493917 (x : real) : (term22 x) = (term16 x).
Proof. exact (TRANS (@lem1493916 x) (@lem1493911 x)). Qed.
Lemma lem1493918 : term23 = term24.
Proof. exact (fun_ext (fun x : real => @lem1493917 x)). Qed.
Lemma lem1493919 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493920 : term18 = term25.
Proof. exact (MK_COMB (@lem1493919) (@lem1493918)). Qed.
Lemma lem1493922 : term17 = term25.
Proof. exact (TRANS (@lem1493913) (@lem1493920)). Qed.
Lemma lem1493927 (y : real) (x : real) : (term3 y x) = (term3 y x).
Proof. exact (eq_refl (term3 y x)). Qed.
Lemma lem1493928 (x : real) : (term15 x) = (term15 x).
Proof. exact (fun_ext (fun y : real => @lem1493927 y x)). Qed.
Lemma lem1493929 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493930 (x : real) : (term16 x) = (term16 x).
Proof. exact (MK_COMB (@lem1493929) (@lem1493928 x)). Qed.
Lemma lem1493931 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1493930 x)). Qed.
Lemma lem1493932 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493933 : term25 = term25.
Proof. exact (MK_COMB (@lem1493932) (@lem1493931)). Qed.
Lemma lem1493934 : term17 = term25.
Proof. exact (TRANS (@lem1493922) (@lem1493933)). Qed.
Lemma lem1493935 (y : real) (x : real) : (real_lt x y) = (term26 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1493941 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1493946 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1493948 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1493941 y x) (@lem1493946 x y)). Qed.
Lemma lem1493949 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493950 (x : real) (y : real) : (term30 y x) = (term31 x y).
Proof. exact (MK_COMB (@lem1493949) (@lem1493948 x y)). Qed.
Lemma lem1493951 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1493952 (x : real) (y : real) : (term26 y x) = (term33 x y).
Proof. exact (MK_COMB (@lem1493950 x y) (@lem1493951)). Qed.
Lemma lem1493953 (x : real) (y : real) : (real_lt x y) = (term33 x y).
Proof. exact (TRANS (@lem1493935 y x) (@lem1493952 x y)). Qed.
Lemma lem1493954 (x : real) (y : real) : (real_lt y x) = (term26 x y).
Proof. exact (@lem1483521 x y). Qed.
Lemma lem1493967 (x : real) (y : real) : (real_sub x y) = (term27 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1493968 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1493969 (x : real) (y : real) : (term30 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1493968) (@lem1493967 x y)). Qed.
Lemma lem1493970 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1493971 (x : real) (y : real) : (term26 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1493969 x y) (@lem1493970)). Qed.
Lemma lem1493972 (x : real) (y : real) : (real_lt y x) = (term35 x y).
Proof. exact (TRANS (@lem1493954 x y) (@lem1493971 x y)). Qed.
Lemma lem1493973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1493974 (x : real) (y : real) : (term1 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1493973) (@lem1493953 x y)). Qed.
Lemma lem1493975 (x : real) (y : real) : (term3 y x) = (term37 x y).
Proof. exact (MK_COMB (@lem1493974 x y) (@lem1493972 x y)). Qed.
Lemma lem1493976 (x : real) : (term15 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1493975 x y)). Qed.
Lemma lem1493977 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493978 (x : real) : (term16 x) = (term39 x).
Proof. exact (MK_COMB (@lem1493977) (@lem1493976 x)). Qed.
Lemma lem1493979 : term24 = term40.
Proof. exact (fun_ext (fun x : real => @lem1493978 x)). Qed.
Lemma lem1493980 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1493981 : term25 = term41.
Proof. exact (MK_COMB (@lem1493980) (@lem1493979)). Qed.
Lemma lem1494040 : term17 = term41.
Proof. exact (TRANS (@lem1493934) (@lem1493981)). Qed.
Lemma lem1494047 (x : real) (y : real) : (term37 x y) = (term37 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1494048 (x : real) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1494047 x y)). Qed.
Lemma lem1494049 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494050 (x : real) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1494049) (@lem1494048 x)). Qed.
Lemma lem1494051 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1494050 x)). Qed.
Lemma lem1494052 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1494053 : term41 = term41.
Proof. exact (MK_COMB (@lem1494052) (@lem1494051)). Qed.
Lemma lem1494054 : term17 = term41.
Proof. exact (TRANS (@lem1494040) (@lem1494053)). Qed.
Lemma lem1494058 (x : real) (y : real) (h1 : term37 x y) : term37 x y.
Proof. exact (h1). Qed.
Lemma lem1494059 (x : real) (y : real) (h1 : term37 x y) : term35 x y.
Proof. exact (proj2 (@lem1494058 x y h1)). Qed.
Lemma lem1494060 (x : real) (y : real) (h1 : term37 x y) : term33 x y.
Proof. exact (proj1 (@lem1494058 x y h1)). Qed.
Lemma lem1494062 (n : nat) (m : nat) : (term42 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494063 : term43 = term44.
Proof. exact (@lem1494062 (NUMERAL 0) term45). Qed.
Lemma lem1494064 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1494065 (h1 : term46 = (BIT1 0)) : term44 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1494066 : (term46 = (BIT1 0)) = (term44 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1494065 h1) (fun h1 : term44 = True => @lem1494064)). Qed.
Lemma lem1494067 : term44 = True.
Proof. exact (EQ_MP (@lem1494066) (@lem1494064)). Qed.
Lemma lem1494068 : term43 = True.
Proof. exact (TRANS (@lem1494063) (@lem1494067)). Qed.
Lemma lem1494069 : True = term43.
Proof. exact (SYM (@lem1494068)). Qed.
Lemma lem1494070 : term43.
Proof. exact (EQ_MP (@lem1494069) (@lem0)). Qed.
Lemma lem1494071 (x : real) (y : real) (h1 : term37 x y) : term47 x y.
Proof. exact (conj (@lem1494070) (@lem1494060 x y h1)). Qed.
Lemma lem1494073 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1494074 (x : real) (y : real) : term49 x y.
Proof. exact (@lem1494073 term50 (term28 x y)). Qed.
Lemma lem1494075 (x : real) (y : real) (h1 : term37 x y) : term51 x y.
Proof. exact (@lem1494074 x y (@lem1494071 x y h1)). Qed.
Lemma lem1494076 (x : real) (y : real) : (term52 x y) = (term28 x y).
Proof. exact (@lem1483460 (term28 x y)). Qed.
Lemma lem1494077 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494078 (x : real) (y : real) : (term53 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1494077) (@lem1494076 x y)). Qed.
Lemma lem1494079 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1494080 (x : real) (y : real) : (term51 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1494078 x y) (@lem1494079)). Qed.
Lemma lem1494081 (x : real) (y : real) (h1 : term37 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1494080 x y) (@lem1494075 x y h1)). Qed.
Lemma lem1494083 (n : nat) (m : nat) : (term42 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494084 : term43 = term44.
Proof. exact (@lem1494083 (NUMERAL 0) term45). Qed.
Lemma lem1494085 : term46 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1494086 (h1 : term46 = (BIT1 0)) : term44 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1494087 : (term46 = (BIT1 0)) = (term44 = True).
Proof. exact (prop_ext (fun h1 : term46 = (BIT1 0) => @lem1494086 h1) (fun h1 : term44 = True => @lem1494085)). Qed.
Lemma lem1494088 : term44 = True.
Proof. exact (EQ_MP (@lem1494087) (@lem1494085)). Qed.
Lemma lem1494089 : term43 = True.
Proof. exact (TRANS (@lem1494084) (@lem1494088)). Qed.
Lemma lem1494090 : True = term43.
Proof. exact (SYM (@lem1494089)). Qed.
Lemma lem1494091 : term43.
Proof. exact (EQ_MP (@lem1494090) (@lem0)). Qed.
Lemma lem1494092 (x : real) (y : real) (h1 : term37 x y) : term54 x y.
Proof. exact (conj (@lem1494091) (@lem1494059 x y h1)). Qed.
Lemma lem1494094 (x : real) (y : real) : term48 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1494095 (x : real) (y : real) : term55 x y.
Proof. exact (@lem1494094 term50 (term27 x y)). Qed.
Lemma lem1494096 (x : real) (y : real) (h1 : term37 x y) : term56 x y.
Proof. exact (@lem1494095 x y (@lem1494092 x y h1)). Qed.
Lemma lem1494097 (x : real) (y : real) : (term57 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1494098 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494099 (x : real) (y : real) : (term58 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1494098) (@lem1494097 x y)). Qed.
Lemma lem1494100 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1494101 (x : real) (y : real) : (term56 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1494099 x y) (@lem1494100)). Qed.
Lemma lem1494102 (x : real) (y : real) (h1 : term37 x y) : term35 x y.
Proof. exact (EQ_MP (@lem1494101 x y) (@lem1494096 x y h1)). Qed.
Lemma lem1494103 (x : real) (y : real) (h1 : term37 x y) : term59 x y.
Proof. exact (conj (@lem1494102 x y h1) (@lem1494081 x y h1)). Qed.
Lemma lem1494105 (x : real) (y : real) : term60 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1494106 (x : real) (y : real) : term61 x y.
Proof. exact (@lem1494105 (term27 x y) (term28 x y)). Qed.
Lemma lem1494107 (x : real) (y : real) (h1 : term37 x y) : term62 x y.
Proof. exact (@lem1494106 x y (@lem1494103 x y h1)). Qed.
Lemma lem1494108 (x : real) (y : real) : (term63 x y) = (term64 x y).
Proof. exact (@lem1483480 x (term29 x) (term29 y) y). Qed.
Lemma lem1494109 (x : real) : (term65 x) = (term66 x).
Proof. exact (@lem1483442 term67 x). Qed.
Lemma lem1494111 (m : nat) : (term68 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1494112 : term69 = term32.
Proof. exact (@lem1494111 term45). Qed.
Lemma lem1494113 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494114 : term70 = term71.
Proof. exact (MK_COMB (@lem1494113) (@lem1494112)). Qed.
Lemma lem1494115 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1494116 (x : real) : (term66 x) = (term72 x).
Proof. exact (MK_COMB (@lem1494114) (@lem1494115 x)). Qed.
Lemma lem1494117 (x : real) : (term65 x) = (term72 x).
Proof. exact (TRANS (@lem1494109 x) (@lem1494116 x)). Qed.
Lemma lem1494118 (x : real) : (term72 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1494119 (x : real) : (term65 x) = term32.
Proof. exact (TRANS (@lem1494117 x) (@lem1494118 x)). Qed.
Lemma lem1494120 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1494121 (x : real) : (term73 x) = term74.
Proof. exact (MK_COMB (@lem1494120) (@lem1494119 x)). Qed.
Lemma lem1494122 (y : real) : (term75 y) = (term66 y).
Proof. exact (@lem1483440 term67 y). Qed.
Lemma lem1494124 (m : nat) : (term68 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1494125 : term69 = term32.
Proof. exact (@lem1494124 term45). Qed.
Lemma lem1494126 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1494127 : term70 = term71.
Proof. exact (MK_COMB (@lem1494126) (@lem1494125)). Qed.
Lemma lem1494128 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1494129 (y : real) : (term66 y) = (term72 y).
Proof. exact (MK_COMB (@lem1494127) (@lem1494128 y)). Qed.
Lemma lem1494130 (y : real) : (term75 y) = (term72 y).
Proof. exact (TRANS (@lem1494122 y) (@lem1494129 y)). Qed.
Lemma lem1494131 (y : real) : (term72 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1494132 (y : real) : (term75 y) = term32.
Proof. exact (TRANS (@lem1494130 y) (@lem1494131 y)). Qed.
Lemma lem1494133 (x : real) (y : real) : (term64 x y) = term76.
Proof. exact (MK_COMB (@lem1494121 x) (@lem1494132 y)). Qed.
Lemma lem1494134 (x : real) (y : real) : (term63 x y) = term76.
Proof. exact (TRANS (@lem1494108 x y) (@lem1494133 x y)). Qed.
Lemma lem1494135 : term76 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1494136 (x : real) (y : real) : (term63 x y) = term32.
Proof. exact (TRANS (@lem1494134 x y) (@lem1494135)). Qed.
Lemma lem1494137 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1494138 (x : real) (y : real) : (term77 x y) = term78.
Proof. exact (MK_COMB (@lem1494137) (@lem1494136 x y)). Qed.
Lemma lem1494139 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1494140 (x : real) (y : real) : (term62 x y) = term79.
Proof. exact (MK_COMB (@lem1494138 x y) (@lem1494139)). Qed.
Lemma lem1494141 (x : real) (y : real) (h1 : term37 x y) : term79.
Proof. exact (EQ_MP (@lem1494140 x y) (@lem1494107 x y h1)). Qed.
Lemma lem1494143 (n : nat) (m : nat) : (term42 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1494144 : term79 = term80.
Proof. exact (@lem1494143 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1494145 : term80 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1494146 : term79 = False.
Proof. exact (TRANS (@lem1494144) (@lem1494145)). Qed.
Lemma lem1494147 (x : real) (y : real) (h1 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1494146) (@lem1494141 x y h1)). Qed.
Lemma lem1494149 (x : real) (y : real) (h1 : term37 x y) : term37 x y.
Proof. exact (h1). Qed.
Lemma lem1494150 (x : real) (y : real) (h1 : term37 x y) : (term37 x y) = False.
Proof. exact (prop_ext (fun h2 : term37 x y => @lem1494147 x y h1) (fun h2 : False => @lem1494149 x y h1)). Qed.
Lemma lem1494151 (x : real) (y : real) (h1 : term37 x y) : False.
Proof. exact (EQ_MP (@lem1494150 x y h1) (@lem1494149 x y h1)). Qed.
Lemma lem1494152 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1494153 (x : real) (h1 : term39 x) : False.
Proof. exact (ex_elim (@lem1494152 x h1) (fun y : real => fun h0 : term38 x y => @lem1494151 x y h0)). Qed.
Lemma lem1494154 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1494155 (h1 : term41) : False.
Proof. exact (ex_elim (@lem1494154 h1) (fun x : real => fun h0 : term40 x => @lem1494153 x h0)). Qed.
Lemma lem1494156 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1494157 (h1 : term17) : term41.
Proof. exact (EQ_MP (@lem1494054) (@lem1494156 h1)). Qed.
Lemma lem1494158 (h1 : term17) : term41 = False.
Proof. exact (prop_ext (fun h2 : term41 => @lem1494155 h2) (fun h2 : False => @lem1494157 h1)). Qed.
Lemma lem1494159 (h1 : term17) : False.
Proof. exact (EQ_MP (@lem1494158 h1) (@lem1494157 h1)). Qed.
Lemma lem1494160 : term81.
Proof. exact (fun h0 : term17 => @lem1494159 h0). Qed.
Lemma lem1494161 : term82.
Proof. exact (@lem1386578 term83). Qed.
Lemma lem1494162 : term83.
Proof. exact (@lem1494161 (@lem1494160)). Qed.
