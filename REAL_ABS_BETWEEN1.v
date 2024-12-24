Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_BETWEEN1_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482706_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1540897 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17362 (term2 y z x) (real_lt y z)). Qed.
Lemma lem1540898 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1540899 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (@lem1540898 (term7 x y)). Qed.
Lemma lem1540900 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (eq_refl (term8 x y z)). Qed.
Lemma lem1540901 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1540902 (x : real) (y : real) (z : real) : (term10 x y z) = (term0 x y z).
Proof. exact (MK_COMB (@lem1540901) (@lem1540900 x y z)). Qed.
Lemma lem1540903 (x : real) (y : real) (z : real) : (term10 x y z) = (term1 x y z).
Proof. exact (TRANS (@lem1540902 x y z) (@lem1540897 x y z)). Qed.
Lemma lem1540904 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1540903 x y z)). Qed.
Lemma lem1540905 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540906 (x : real) (y : real) : (term6 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1540905) (@lem1540904 x y)). Qed.
Lemma lem1540907 (x : real) (y : real) : (term5 x y) = (term13 x y).
Proof. exact (TRANS (@lem1540899 x y) (@lem1540906 x y)). Qed.
Lemma lem1540908 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1540909 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1540908 (term16 x)). Qed.
Lemma lem1540910 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1540911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1540912 (x : real) (y : real) : (term19 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1540911) (@lem1540910 x y)). Qed.
Lemma lem1540913 (x : real) (y : real) : (term19 x y) = (term13 x y).
Proof. exact (TRANS (@lem1540912 x y) (@lem1540907 x y)). Qed.
Lemma lem1540914 (x : real) : (term20 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1540913 x y)). Qed.
Lemma lem1540915 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540916 (x : real) : (term15 x) = (term22 x).
Proof. exact (MK_COMB (@lem1540915) (@lem1540914 x)). Qed.
Lemma lem1540917 (x : real) : (term14 x) = (term22 x).
Proof. exact (TRANS (@lem1540909 x) (@lem1540916 x)). Qed.
Lemma lem1540918 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1540919 : term23 = term24.
Proof. exact (@lem1540918 term25). Qed.
Lemma lem1540920 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1540921 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1540922 (x : real) : (term28 x) = (term14 x).
Proof. exact (MK_COMB (@lem1540921) (@lem1540920 x)). Qed.
Lemma lem1540923 (x : real) : (term28 x) = (term22 x).
Proof. exact (TRANS (@lem1540922 x) (@lem1540917 x)). Qed.
Lemma lem1540924 : term29 = term30.
Proof. exact (fun_ext (fun x : real => @lem1540923 x)). Qed.
Lemma lem1540925 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540926 : term24 = term31.
Proof. exact (MK_COMB (@lem1540925) (@lem1540924)). Qed.
Lemma lem1540928 : term23 = term31.
Proof. exact (TRANS (@lem1540919) (@lem1540926)). Qed.
Lemma lem1540939 (x : real) (y : real) (z : real) : (term1 x y z) = (term1 x y z).
Proof. exact (eq_refl (term1 x y z)). Qed.
Lemma lem1540940 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (fun_ext (fun z : real => @lem1540939 x y z)). Qed.
Lemma lem1540941 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540942 (x : real) (y : real) : (term13 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1540941) (@lem1540940 x y)). Qed.
Lemma lem1540943 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1540942 x y)). Qed.
Lemma lem1540944 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540945 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1540944) (@lem1540943 x)). Qed.
Lemma lem1540946 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1540945 x)). Qed.
Lemma lem1540947 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540948 : term31 = term31.
Proof. exact (MK_COMB (@lem1540947) (@lem1540946)). Qed.
Lemma lem1540949 : term23 = term31.
Proof. exact (TRANS (@lem1540928) (@lem1540948)). Qed.
Lemma lem1540950 (z : real) (x : real) : (real_lt x z) = (term32 z x).
Proof. exact (@lem1483521 z x). Qed.
Lemma lem1540956 (z : real) (x : real) : (real_sub z x) = (term33 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1540961 (x : real) (z : real) : (term33 z x) = (term34 x z).
Proof. exact (@lem1483488 (term35 x) z). Qed.
Lemma lem1540963 (x : real) (z : real) : (real_sub z x) = (term34 x z).
Proof. exact (TRANS (@lem1540956 z x) (@lem1540961 x z)). Qed.
Lemma lem1540964 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540965 (x : real) (z : real) : (term36 z x) = (term37 x z).
Proof. exact (MK_COMB (@lem1540964) (@lem1540963 x z)). Qed.
Lemma lem1540966 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1540967 (x : real) (z : real) : (term32 z x) = (term39 x z).
Proof. exact (MK_COMB (@lem1540965 x z) (@lem1540966)). Qed.
Lemma lem1540968 (x : real) (z : real) : (real_lt x z) = (term39 x z).
Proof. exact (TRANS (@lem1540950 z x) (@lem1540967 x z)). Qed.
Lemma lem1540969 (z : real) (y : real) (x : real) : (term40 y z x) = (term41 z y x).
Proof. exact (@lem1483521 (real_sub z x) (term42 y x)). Qed.
Lemma lem1540970 (y : real) (x : real) : (term42 y x) = (term42 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem1540976 (z : real) (x : real) : (real_sub z x) = (term33 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1540981 (x : real) (z : real) : (term33 z x) = (term34 x z).
Proof. exact (@lem1483488 (term35 x) z). Qed.
Lemma lem1540983 (x : real) (z : real) : (real_sub z x) = (term34 x z).
Proof. exact (TRANS (@lem1540976 z x) (@lem1540981 x z)). Qed.
Lemma lem1540984 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1540985 (x : real) (z : real) : (term43 z x) = (term44 x z).
Proof. exact (MK_COMB (@lem1540984) (@lem1540983 x z)). Qed.
Lemma lem1540986 (z : real) (y : real) (x : real) : (term45 z y x) = (term46 z y x).
Proof. exact (MK_COMB (@lem1540985 x z) (@lem1540970 y x)). Qed.
Lemma lem1540987 (z : real) (y : real) (x : real) : (term46 z y x) = (term47 z y x).
Proof. exact (@lem1483519 (term34 x z) (term42 y x)). Qed.
Lemma lem1540996 (z : real) (y : real) (x : real) : (term47 z y x) = (term48 z y x).
Proof. exact (@lem1483482 (term35 x) z (term49 y x)). Qed.
Lemma lem1540997 (z : real) (y : real) (x : real) : (term46 z y x) = (term48 z y x).
Proof. exact (TRANS (@lem1540987 z y x) (@lem1540996 z y x)). Qed.
Lemma lem1540998 (z : real) (y : real) (x : real) : (term45 z y x) = (term48 z y x).
Proof. exact (TRANS (@lem1540986 z y x) (@lem1540997 z y x)). Qed.
Lemma lem1540999 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541000 (z : real) (y : real) (x : real) : (term50 z y x) = (term51 z y x).
Proof. exact (MK_COMB (@lem1540999) (@lem1540998 z y x)). Qed.
Lemma lem1541001 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541002 (z : real) (y : real) (x : real) : (term41 z y x) = (term52 z y x).
Proof. exact (MK_COMB (@lem1541000 z y x) (@lem1541001)). Qed.
Lemma lem1541003 (z : real) (y : real) (x : real) : (term40 y z x) = (term52 z y x).
Proof. exact (TRANS (@lem1540969 z y x) (@lem1541002 z y x)). Qed.
Lemma lem1541004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541005 (x : real) (z : real) : (term53 x z) = (term54 x z).
Proof. exact (MK_COMB (@lem1541004) (@lem1540968 x z)). Qed.
Lemma lem1541006 (z : real) (y : real) (x : real) : (term2 y z x) = (term55 z y x).
Proof. exact (MK_COMB (@lem1541005 x z) (@lem1541003 z y x)). Qed.
Lemma lem1541007 (y : real) (z : real) : (term56 y z) = (term57 y z).
Proof. exact (@lem1483531 y z). Qed.
Lemma lem1541020 (y : real) (z : real) : (real_sub y z) = (term33 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1541021 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1541022 (y : real) (z : real) : (term58 y z) = (term59 y z).
Proof. exact (MK_COMB (@lem1541021) (@lem1541020 y z)). Qed.
Lemma lem1541023 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541024 (y : real) (z : real) : (term57 y z) = (term60 y z).
Proof. exact (MK_COMB (@lem1541022 y z) (@lem1541023)). Qed.
Lemma lem1541025 (y : real) (z : real) : (term56 y z) = (term60 y z).
Proof. exact (TRANS (@lem1541007 y z) (@lem1541024 y z)). Qed.
Lemma lem1541026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541027 (z : real) (y : real) (x : real) : (term61 y z x) = (term62 z y x).
Proof. exact (MK_COMB (@lem1541026) (@lem1541006 z y x)). Qed.
Lemma lem1541028 (x : real) (y : real) (z : real) : (term1 x y z) = (term63 x y z).
Proof. exact (MK_COMB (@lem1541027 z y x) (@lem1541025 y z)). Qed.
Lemma lem1541029 (x : real) (y : real) : (term12 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1541028 x y z)). Qed.
Lemma lem1541030 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541031 (x : real) (y : real) : (term13 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1541030) (@lem1541029 x y)). Qed.
Lemma lem1541032 (x : real) : (term21 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1541031 x y)). Qed.
Lemma lem1541033 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541034 (x : real) : (term22 x) = (term67 x).
Proof. exact (MK_COMB (@lem1541033) (@lem1541032 x)). Qed.
Lemma lem1541035 : term30 = term68.
Proof. exact (fun_ext (fun x : real => @lem1541034 x)). Qed.
Lemma lem1541036 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541037 : term31 = term69.
Proof. exact (MK_COMB (@lem1541036) (@lem1541035)). Qed.
Lemma lem1541100 : term23 = term69.
Proof. exact (TRANS (@lem1540949) (@lem1541037)). Qed.
Lemma lem1541113 (x : real) (y : real) (z : real) : (term63 x y z) = (term63 x y z).
Proof. exact (eq_refl (term63 x y z)). Qed.
Lemma lem1541114 (x : real) (y : real) : (term64 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1541113 x y z)). Qed.
Lemma lem1541115 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541116 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1541115) (@lem1541114 x y)). Qed.
Lemma lem1541117 (x : real) : (term66 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1541116 x y)). Qed.
Lemma lem1541118 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541119 (x : real) : (term67 x) = (term67 x).
Proof. exact (MK_COMB (@lem1541118) (@lem1541117 x)). Qed.
Lemma lem1541120 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem1541119 x)). Qed.
Lemma lem1541121 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1541122 : term69 = term69.
Proof. exact (MK_COMB (@lem1541121) (@lem1541120)). Qed.
Lemma lem1541123 : term23 = term69.
Proof. exact (TRANS (@lem1541100) (@lem1541122)). Qed.
Lemma lem1541125 (a : real) (b : real) (x : real) (r : real) : (term70 a b x r) = (term71 a b x r).
Proof. exact (proj1 (@lem1482706 x a b (@el real) (@el real) r)). Qed.
Lemma lem1541126 (z : real) (y : real) (x : real) : (term52 z y x) = (term72 z y x).
Proof. exact (@lem1541125 (term35 x) z (real_sub y x) term38). Qed.
Lemma lem1541132 (y : real) (x : real) : (real_sub y x) = (term33 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1541137 (x : real) (y : real) : (term33 y x) = (term34 x y).
Proof. exact (@lem1483488 (term35 x) y). Qed.
Lemma lem1541139 (x : real) (y : real) : (real_sub y x) = (term34 x y).
Proof. exact (TRANS (@lem1541132 y x) (@lem1541137 x y)). Qed.
Lemma lem1541142 : term73 = term73.
Proof. exact (eq_refl term73). Qed.
Lemma lem1541143 (x : real) (y : real) : (term74 y x) = (term75 x y).
Proof. exact (MK_COMB (@lem1541142) (@lem1541139 x y)). Qed.
Lemma lem1541144 (x : real) (y : real) : (term75 x y) = (term34 x y).
Proof. exact (@lem1483460 (term34 x y)). Qed.
Lemma lem1541145 (x : real) (y : real) : (term74 y x) = (term34 x y).
Proof. exact (TRANS (@lem1541143 x y) (@lem1541144 x y)). Qed.
Lemma lem1541148 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1541149 (z : real) (x : real) (y : real) : (term76 z y x) = (term77 z x y).
Proof. exact (MK_COMB (@lem1541148 z) (@lem1541145 x y)). Qed.
Lemma lem1541150 (x : real) (z : real) (y : real) : (term77 z x y) = (term78 x z y).
Proof. exact (@lem1483484 (term35 x) z y). Qed.
Lemma lem1541151 (y : real) (z : real) : (real_add z y) = (real_add y z).
Proof. exact (@lem1483488 y z). Qed.
Lemma lem1541152 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1541153 (x : real) (y : real) (z : real) : (term78 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1541152 x) (@lem1541151 y z)). Qed.
Lemma lem1541154 (x : real) (y : real) (z : real) : (term77 z x y) = (term78 x y z).
Proof. exact (TRANS (@lem1541150 x z y) (@lem1541153 x y z)). Qed.
Lemma lem1541155 (x : real) (y : real) (z : real) : (term76 z y x) = (term78 x y z).
Proof. exact (TRANS (@lem1541149 z x y) (@lem1541154 x y z)). Qed.
Lemma lem1541164 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1541165 (x : real) (y : real) (z : real) : (term80 z y x) = (term81 x y z).
Proof. exact (MK_COMB (@lem1541164 x) (@lem1541155 x y z)). Qed.
Lemma lem1541166 (x : real) (y : real) (z : real) : (term81 x y z) = (term82 x y z).
Proof. exact (@lem1483490 (term35 x) (term35 x) (real_add y z)). Qed.
Lemma lem1541167 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1483438 term85 term85 x). Qed.
Lemma lem1541168 : term86 = term87.
Proof. exact (@lem1367763 term88 term88). Qed.
Lemma lem1541169 : term89 = term90.
Proof. exact (@lem706885). Qed.
Lemma lem1541170 : (term89 = term90) = (term91 = term92).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term90). Qed.
Lemma lem1541171 : term91 = term92.
Proof. exact (EQ_MP (@lem1541170) (@lem1541169)). Qed.
Lemma lem1541172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1541173 : term93 = term94.
Proof. exact (MK_COMB (@lem1541172) (@lem1541171)). Qed.
Lemma lem1541174 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1541175 : term87 = term95.
Proof. exact (MK_COMB (@lem1541174) (@lem1541173)). Qed.
Lemma lem1541176 : term86 = term95.
Proof. exact (TRANS (@lem1541168) (@lem1541175)). Qed.
Lemma lem1541177 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541178 : term96 = term97.
Proof. exact (MK_COMB (@lem1541177) (@lem1541176)). Qed.
Lemma lem1541179 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1541180 (x : real) : (term84 x) = (term98 x).
Proof. exact (MK_COMB (@lem1541178) (@lem1541179 x)). Qed.
Lemma lem1541181 (x : real) : (term83 x) = (term98 x).
Proof. exact (TRANS (@lem1541167 x) (@lem1541180 x)). Qed.
Lemma lem1541182 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1541183 (x : real) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem1541182) (@lem1541181 x)). Qed.
Lemma lem1541184 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (eq_refl (real_add y z)). Qed.
Lemma lem1541185 (x : real) (y : real) (z : real) : (term82 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1541183 x) (@lem1541184 y z)). Qed.
Lemma lem1541186 (x : real) (y : real) (z : real) : (term81 x y z) = (term101 x y z).
Proof. exact (TRANS (@lem1541166 x y z) (@lem1541185 x y z)). Qed.
Lemma lem1541187 (x : real) (y : real) (z : real) : (term80 z y x) = (term101 x y z).
Proof. exact (TRANS (@lem1541165 x y z) (@lem1541186 x y z)). Qed.
Lemma lem1541188 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541189 (x : real) (y : real) (z : real) : (term102 z y x) = (term103 x y z).
Proof. exact (MK_COMB (@lem1541188) (@lem1541187 x y z)). Qed.
Lemma lem1541190 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541191 (x : real) (y : real) (z : real) : (term104 z y x) = (term105 x y z).
Proof. exact (MK_COMB (@lem1541189 x y z) (@lem1541190)). Qed.
Lemma lem1541197 (y : real) (x : real) : (real_sub y x) = (term33 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1541202 (x : real) (y : real) : (term33 y x) = (term34 x y).
Proof. exact (@lem1483488 (term35 x) y). Qed.
Lemma lem1541204 (x : real) (y : real) : (real_sub y x) = (term34 x y).
Proof. exact (TRANS (@lem1541197 y x) (@lem1541202 x y)). Qed.
Lemma lem1541207 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem1541208 (x : real) (y : real) : (term107 y x) = (term108 x y).
Proof. exact (MK_COMB (@lem1541207) (@lem1541204 x y)). Qed.
Lemma lem1541209 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (@lem1483508 (term35 x) term85 y). Qed.
Lemma lem1541210 (y : real) : (term35 y) = (term35 y).
Proof. exact (eq_refl (term35 y)). Qed.
Lemma lem1541211 (x : real) : (term110 x) = (term111 x).
Proof. exact (@lem1483476 term85 term85 x). Qed.
Lemma lem1541213 (m : nat) (n : nat) : (term112 m n) = (term113 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1541214 : term114 = term115.
Proof. exact (@lem1541213 term88 term88). Qed.
Lemma lem1541215 : (term116 = (BIT1 0)) = (term117 = term88).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1541216 : term117 = term88.
Proof. exact (EQ_MP (@lem1541215) (@lem940073)). Qed.
Lemma lem1541217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1541218 : term115 = term118.
Proof. exact (MK_COMB (@lem1541217) (@lem1541216)). Qed.
Lemma lem1541219 : term114 = term118.
Proof. exact (TRANS (@lem1541214) (@lem1541218)). Qed.
Lemma lem1541220 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541221 : term119 = term73.
Proof. exact (MK_COMB (@lem1541220) (@lem1541219)). Qed.
Lemma lem1541222 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1541223 (x : real) : (term111 x) = (term120 x).
Proof. exact (MK_COMB (@lem1541221) (@lem1541222 x)). Qed.
Lemma lem1541224 (x : real) : (term110 x) = (term120 x).
Proof. exact (TRANS (@lem1541211 x) (@lem1541223 x)). Qed.
Lemma lem1541225 (x : real) : (term120 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1541226 (x : real) : (term110 x) = x.
Proof. exact (TRANS (@lem1541224 x) (@lem1541225 x)). Qed.
Lemma lem1541227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1541228 (x : real) : (term121 x) = (real_add x).
Proof. exact (MK_COMB (@lem1541227) (@lem1541226 x)). Qed.
Lemma lem1541229 (x : real) (y : real) : (term109 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1541228 x) (@lem1541210 y)). Qed.
Lemma lem1541230 (x : real) (y : real) : (term108 x y) = (term33 x y).
Proof. exact (TRANS (@lem1541209 x y) (@lem1541229 x y)). Qed.
Lemma lem1541231 (x : real) (y : real) : (term107 y x) = (term33 x y).
Proof. exact (TRANS (@lem1541208 x y) (@lem1541230 x y)). Qed.
Lemma lem1541234 (z : real) : (real_add z) = (real_add z).
Proof. exact (eq_refl (real_add z)). Qed.
Lemma lem1541235 (z : real) (x : real) (y : real) : (term122 z y x) = (term123 z x y).
Proof. exact (MK_COMB (@lem1541234 z) (@lem1541231 x y)). Qed.
Lemma lem1541236 (x : real) (z : real) (y : real) : (term123 z x y) = (term123 x z y).
Proof. exact (@lem1483484 x z (term35 y)). Qed.
Lemma lem1541237 (y : real) (z : real) : (term33 z y) = (term34 y z).
Proof. exact (@lem1483488 (term35 y) z). Qed.
Lemma lem1541238 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1541239 (x : real) (y : real) (z : real) : (term123 x z y) = (term77 x y z).
Proof. exact (MK_COMB (@lem1541238 x) (@lem1541237 y z)). Qed.
Lemma lem1541240 (x : real) (y : real) (z : real) : (term123 z x y) = (term77 x y z).
Proof. exact (TRANS (@lem1541236 x z y) (@lem1541239 x y z)). Qed.
Lemma lem1541241 (x : real) (y : real) (z : real) : (term122 z y x) = (term77 x y z).
Proof. exact (TRANS (@lem1541235 z x y) (@lem1541240 x y z)). Qed.
Lemma lem1541250 (x : real) : (term79 x) = (term79 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1541251 (x : real) (y : real) (z : real) : (term124 z y x) = (term125 x y z).
Proof. exact (MK_COMB (@lem1541250 x) (@lem1541241 x y z)). Qed.
Lemma lem1541252 (x : real) (y : real) (z : real) : (term125 x y z) = (term126 x y z).
Proof. exact (@lem1483490 (term35 x) x (term34 y z)). Qed.
Lemma lem1541253 (x : real) : (term127 x) = (term128 x).
Proof. exact (@lem1483440 term85 x). Qed.
Lemma lem1541255 (m : nat) : (term129 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1541256 : term130 = term38.
Proof. exact (@lem1541255 term88). Qed.
Lemma lem1541257 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541258 : term131 = term132.
Proof. exact (MK_COMB (@lem1541257) (@lem1541256)). Qed.
Lemma lem1541259 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1541260 (x : real) : (term128 x) = (term133 x).
Proof. exact (MK_COMB (@lem1541258) (@lem1541259 x)). Qed.
Lemma lem1541261 (x : real) : (term127 x) = (term133 x).
Proof. exact (TRANS (@lem1541253 x) (@lem1541260 x)). Qed.
Lemma lem1541262 (x : real) : (term133 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1541263 (x : real) : (term127 x) = term38.
Proof. exact (TRANS (@lem1541261 x) (@lem1541262 x)). Qed.
Lemma lem1541264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1541265 (x : real) : (term134 x) = term135.
Proof. exact (MK_COMB (@lem1541264) (@lem1541263 x)). Qed.
Lemma lem1541266 (y : real) (z : real) : (term34 y z) = (term34 y z).
Proof. exact (eq_refl (term34 y z)). Qed.
Lemma lem1541267 (x : real) (y : real) (z : real) : (term126 x y z) = (term136 y z).
Proof. exact (MK_COMB (@lem1541265 x) (@lem1541266 y z)). Qed.
Lemma lem1541268 (x : real) (y : real) (z : real) : (term125 x y z) = (term136 y z).
Proof. exact (TRANS (@lem1541252 x y z) (@lem1541267 x y z)). Qed.
Lemma lem1541269 (y : real) (z : real) : (term136 y z) = (term34 y z).
Proof. exact (@lem1483448 (term34 y z)). Qed.
Lemma lem1541270 (x : real) (y : real) (z : real) : (term125 x y z) = (term34 y z).
Proof. exact (TRANS (@lem1541268 x y z) (@lem1541269 y z)). Qed.
Lemma lem1541271 (x : real) (y : real) (z : real) : (term124 z y x) = (term34 y z).
Proof. exact (TRANS (@lem1541251 x y z) (@lem1541270 x y z)). Qed.
Lemma lem1541272 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541273 (x : real) (y : real) (z : real) : (term137 z y x) = (term37 y z).
Proof. exact (MK_COMB (@lem1541272) (@lem1541271 x y z)). Qed.
Lemma lem1541274 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541275 (x : real) (y : real) (z : real) : (term138 z y x) = (term39 y z).
Proof. exact (MK_COMB (@lem1541273 x y z) (@lem1541274)). Qed.
Lemma lem1541276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541277 (x : real) (y : real) (z : real) : (term139 z y x) = (term54 y z).
Proof. exact (MK_COMB (@lem1541276) (@lem1541275 x y z)). Qed.
Lemma lem1541278 (x : real) (y : real) (z : real) : (term72 z y x) = (term140 x y z).
Proof. exact (MK_COMB (@lem1541277 x y z) (@lem1541191 x y z)). Qed.
Lemma lem1541279 (x : real) (y : real) (z : real) : (term52 z y x) = (term140 x y z).
Proof. exact (TRANS (@lem1541126 z y x) (@lem1541278 x y z)). Qed.
Lemma lem1541280 (x : real) (z : real) : (term54 x z) = (term54 x z).
Proof. exact (eq_refl (term54 x z)). Qed.
Lemma lem1541281 (x : real) (y : real) (z : real) : (term55 z y x) = (term141 x y z).
Proof. exact (MK_COMB (@lem1541280 x z) (@lem1541279 x y z)). Qed.
Lemma lem1541282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1541283 (x : real) (y : real) (z : real) : (term62 z y x) = (term142 x y z).
Proof. exact (MK_COMB (@lem1541282) (@lem1541281 x y z)). Qed.
Lemma lem1541284 (y : real) (z : real) : (term60 y z) = (term60 y z).
Proof. exact (eq_refl (term60 y z)). Qed.
Lemma lem1541287 (x : real) (y : real) (z : real) : (term63 x y z) = (term143 x y z).
Proof. exact (MK_COMB (@lem1541283 x y z) (@lem1541284 y z)). Qed.
Lemma lem1541288 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term143 x y z.
Proof. exact (h1). Qed.
Lemma lem1541289 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term60 y z.
Proof. exact (proj2 (@lem1541288 x y z h1)). Qed.
Lemma lem1541290 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term141 x y z.
Proof. exact (proj1 (@lem1541288 x y z h1)). Qed.
Lemma lem1541291 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term140 x y z.
Proof. exact (proj2 (@lem1541290 x y z h1)). Qed.
Lemma lem1541294 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term39 y z.
Proof. exact (proj1 (@lem1541291 x y z h1)). Qed.
Lemma lem1541296 (n : nat) (m : nat) : (term144 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1541297 : term145 = term146.
Proof. exact (@lem1541296 (NUMERAL 0) term88). Qed.
Lemma lem1541298 : term147 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1541299 (h1 : term147 = (BIT1 0)) : term146 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1541300 : (term147 = (BIT1 0)) = (term146 = True).
Proof. exact (prop_ext (fun h1 : term147 = (BIT1 0) => @lem1541299 h1) (fun h1 : term146 = True => @lem1541298)). Qed.
Lemma lem1541301 : term146 = True.
Proof. exact (EQ_MP (@lem1541300) (@lem1541298)). Qed.
Lemma lem1541302 : term145 = True.
Proof. exact (TRANS (@lem1541297) (@lem1541301)). Qed.
Lemma lem1541303 : True = term145.
Proof. exact (SYM (@lem1541302)). Qed.
Lemma lem1541304 : term145.
Proof. exact (EQ_MP (@lem1541303) (@lem0)). Qed.
Lemma lem1541305 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term148 y z.
Proof. exact (conj (@lem1541304) (@lem1541289 x y z h1)). Qed.
Lemma lem1541307 (x : real) (y : real) : term149 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1541308 (y : real) (z : real) : term150 y z.
Proof. exact (@lem1541307 term118 (term33 y z)). Qed.
Lemma lem1541309 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term151 y z.
Proof. exact (@lem1541308 y z (@lem1541305 x y z h1)). Qed.
Lemma lem1541310 (y : real) (z : real) : (term152 y z) = (term33 y z).
Proof. exact (@lem1483460 (term33 y z)). Qed.
Lemma lem1541311 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1541312 (y : real) (z : real) : (term153 y z) = (term59 y z).
Proof. exact (MK_COMB (@lem1541311) (@lem1541310 y z)). Qed.
Lemma lem1541313 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541314 (y : real) (z : real) : (term151 y z) = (term60 y z).
Proof. exact (MK_COMB (@lem1541312 y z) (@lem1541313)). Qed.
Lemma lem1541315 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term60 y z.
Proof. exact (EQ_MP (@lem1541314 y z) (@lem1541309 x y z h1)). Qed.
Lemma lem1541317 (n : nat) (m : nat) : (term144 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1541318 : term145 = term146.
Proof. exact (@lem1541317 (NUMERAL 0) term88). Qed.
Lemma lem1541319 : term147 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1541320 (h1 : term147 = (BIT1 0)) : term146 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1541321 : (term147 = (BIT1 0)) = (term146 = True).
Proof. exact (prop_ext (fun h1 : term147 = (BIT1 0) => @lem1541320 h1) (fun h1 : term146 = True => @lem1541319)). Qed.
Lemma lem1541322 : term146 = True.
Proof. exact (EQ_MP (@lem1541321) (@lem1541319)). Qed.
Lemma lem1541323 : term145 = True.
Proof. exact (TRANS (@lem1541318) (@lem1541322)). Qed.
Lemma lem1541324 : True = term145.
Proof. exact (SYM (@lem1541323)). Qed.
Lemma lem1541325 : term145.
Proof. exact (EQ_MP (@lem1541324) (@lem0)). Qed.
Lemma lem1541326 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term154 y z.
Proof. exact (conj (@lem1541325) (@lem1541294 x y z h1)). Qed.
Lemma lem1541328 (x : real) (y : real) : term155 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1541329 (y : real) (z : real) : term156 y z.
Proof. exact (@lem1541328 term118 (term34 y z)). Qed.
Lemma lem1541330 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term157 y z.
Proof. exact (@lem1541329 y z (@lem1541326 x y z h1)). Qed.
Lemma lem1541331 (y : real) (z : real) : (term75 y z) = (term34 y z).
Proof. exact (@lem1483460 (term34 y z)). Qed.
Lemma lem1541332 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541333 (y : real) (z : real) : (term158 y z) = (term37 y z).
Proof. exact (MK_COMB (@lem1541332) (@lem1541331 y z)). Qed.
Lemma lem1541334 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541335 (y : real) (z : real) : (term157 y z) = (term39 y z).
Proof. exact (MK_COMB (@lem1541333 y z) (@lem1541334)). Qed.
Lemma lem1541336 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term39 y z.
Proof. exact (EQ_MP (@lem1541335 y z) (@lem1541330 x y z h1)). Qed.
Lemma lem1541337 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term159 y z.
Proof. exact (conj (@lem1541336 x y z h1) (@lem1541315 x y z h1)). Qed.
Lemma lem1541339 (x : real) (y : real) : term160 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1541340 (y : real) (z : real) : term161 y z.
Proof. exact (@lem1541339 (term34 y z) (term33 y z)). Qed.
Lemma lem1541341 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term162 y z.
Proof. exact (@lem1541340 y z (@lem1541337 x y z h1)). Qed.
Lemma lem1541342 (y : real) (z : real) : (term163 y z) = (term164 y z).
Proof. exact (@lem1483480 (term35 y) y z (term35 z)). Qed.
Lemma lem1541343 (y : real) : (term127 y) = (term128 y).
Proof. exact (@lem1483440 term85 y). Qed.
Lemma lem1541345 (m : nat) : (term129 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1541346 : term130 = term38.
Proof. exact (@lem1541345 term88). Qed.
Lemma lem1541347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541348 : term131 = term132.
Proof. exact (MK_COMB (@lem1541347) (@lem1541346)). Qed.
Lemma lem1541349 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1541350 (y : real) : (term128 y) = (term133 y).
Proof. exact (MK_COMB (@lem1541348) (@lem1541349 y)). Qed.
Lemma lem1541351 (y : real) : (term127 y) = (term133 y).
Proof. exact (TRANS (@lem1541343 y) (@lem1541350 y)). Qed.
Lemma lem1541352 (y : real) : (term133 y) = term38.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1541353 (y : real) : (term127 y) = term38.
Proof. exact (TRANS (@lem1541351 y) (@lem1541352 y)). Qed.
Lemma lem1541354 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1541355 (y : real) : (term134 y) = term135.
Proof. exact (MK_COMB (@lem1541354) (@lem1541353 y)). Qed.
Lemma lem1541356 (z : real) : (term165 z) = (term128 z).
Proof. exact (@lem1483442 term85 z). Qed.
Lemma lem1541358 (m : nat) : (term129 m) = term38.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1541359 : term130 = term38.
Proof. exact (@lem1541358 term88). Qed.
Lemma lem1541360 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1541361 : term131 = term132.
Proof. exact (MK_COMB (@lem1541360) (@lem1541359)). Qed.
Lemma lem1541362 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1541363 (z : real) : (term128 z) = (term133 z).
Proof. exact (MK_COMB (@lem1541361) (@lem1541362 z)). Qed.
Lemma lem1541364 (z : real) : (term165 z) = (term133 z).
Proof. exact (TRANS (@lem1541356 z) (@lem1541363 z)). Qed.
Lemma lem1541365 (z : real) : (term133 z) = term38.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1541366 (z : real) : (term165 z) = term38.
Proof. exact (TRANS (@lem1541364 z) (@lem1541365 z)). Qed.
Lemma lem1541367 (y : real) (z : real) : (term164 y z) = term166.
Proof. exact (MK_COMB (@lem1541355 y) (@lem1541366 z)). Qed.
Lemma lem1541368 (y : real) (z : real) : (term163 y z) = term166.
Proof. exact (TRANS (@lem1541342 y z) (@lem1541367 y z)). Qed.
Lemma lem1541369 : term166 = term38.
Proof. exact (@lem1483448 term38). Qed.
Lemma lem1541370 (y : real) (z : real) : (term163 y z) = term38.
Proof. exact (TRANS (@lem1541368 y z) (@lem1541369)). Qed.
Lemma lem1541371 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1541372 (y : real) (z : real) : (term167 y z) = term168.
Proof. exact (MK_COMB (@lem1541371) (@lem1541370 y z)). Qed.
Lemma lem1541373 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1541374 (y : real) (z : real) : (term162 y z) = term169.
Proof. exact (MK_COMB (@lem1541372 y z) (@lem1541373)). Qed.
Lemma lem1541375 (x : real) (y : real) (z : real) (h1 : term143 x y z) : term169.
Proof. exact (EQ_MP (@lem1541374 y z) (@lem1541341 x y z h1)). Qed.
Lemma lem1541377 (n : nat) (m : nat) : (term144 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1541378 : term169 = term170.
Proof. exact (@lem1541377 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1541379 : term170 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1541380 : term169 = False.
Proof. exact (TRANS (@lem1541378) (@lem1541379)). Qed.
Lemma lem1541381 (x : real) (y : real) (z : real) (h1 : term143 x y z) : False.
Proof. exact (EQ_MP (@lem1541380) (@lem1541375 x y z h1)). Qed.
Lemma lem1541382 (x : real) (y : real) (z : real) (h1 : term63 x y z) : term63 x y z.
Proof. exact (h1). Qed.
Lemma lem1541383 (x : real) (y : real) (z : real) (h1 : term63 x y z) : term143 x y z.
Proof. exact (EQ_MP (@lem1541287 x y z) (@lem1541382 x y z h1)). Qed.
Lemma lem1541384 (x : real) (y : real) (z : real) (h1 : term63 x y z) : (term143 x y z) = False.
Proof. exact (prop_ext (fun h2 : term143 x y z => @lem1541381 x y z h2) (fun h2 : False => @lem1541383 x y z h1)). Qed.
Lemma lem1541385 (x : real) (y : real) (z : real) (h1 : term63 x y z) : False.
Proof. exact (EQ_MP (@lem1541384 x y z h1) (@lem1541383 x y z h1)). Qed.
Lemma lem1541386 (x : real) (y : real) (h1 : term65 x y) : term65 x y.
Proof. exact (h1). Qed.
Lemma lem1541387 (x : real) (y : real) (h1 : term65 x y) : False.
Proof. exact (ex_elim (@lem1541386 x y h1) (fun z : real => fun h0 : term64 x y z => @lem1541385 x y z h0)). Qed.
Lemma lem1541388 (x : real) (h1 : term67 x) : term67 x.
Proof. exact (h1). Qed.
Lemma lem1541389 (x : real) (h1 : term67 x) : False.
Proof. exact (ex_elim (@lem1541388 x h1) (fun y : real => fun h0 : term66 x y => @lem1541387 x y h0)). Qed.
Lemma lem1541390 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1541391 (h1 : term69) : False.
Proof. exact (ex_elim (@lem1541390 h1) (fun x : real => fun h0 : term68 x => @lem1541389 x h0)). Qed.
Lemma lem1541392 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1541393 (h1 : term23) : term69.
Proof. exact (EQ_MP (@lem1541123) (@lem1541392 h1)). Qed.
Lemma lem1541394 (h1 : term23) : term69 = False.
Proof. exact (prop_ext (fun h2 : term69 => @lem1541391 h2) (fun h2 : False => @lem1541393 h1)). Qed.
Lemma lem1541395 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1541394 h1) (@lem1541393 h1)). Qed.
Lemma lem1541396 : term171.
Proof. exact (fun h0 : term23 => @lem1541395 h0). Qed.
Lemma lem1541397 : term172.
Proof. exact (@lem1386578 term173). Qed.
Lemma lem1541398 : term173.
Proof. exact (@lem1541397 (@lem1541396)). Qed.
