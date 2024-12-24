Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LADD_term_abbrevs.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1491908 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17646 (term2 y x z) (real_lt y z)). Qed.
Lemma lem1491909 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491910 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (@lem1491909 (term7 x y)). Qed.
Lemma lem1491911 (x : real) (y : real) (z : real) : (term8 x y z) = ((term2 y x z) = (real_lt y z)).
Proof. exact (eq_refl (term8 x y z)). Qed.
Lemma lem1491912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491913 (x : real) (y : real) (z : real) : (term9 x y z) = (term0 x y z).
Proof. exact (MK_COMB (@lem1491912) (@lem1491911 x y z)). Qed.
Lemma lem1491914 (x : real) (y : real) (z : real) : (term9 x y z) = (term1 x y z).
Proof. exact (TRANS (@lem1491913 x y z) (@lem1491908 x y z)). Qed.
Lemma lem1491915 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1491914 x y z)). Qed.
Lemma lem1491916 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491917 (x : real) (y : real) : (term6 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1491916) (@lem1491915 x y)). Qed.
Lemma lem1491918 (x : real) (y : real) : (term5 x y) = (term12 x y).
Proof. exact (TRANS (@lem1491910 x y) (@lem1491917 x y)). Qed.
Lemma lem1491919 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491920 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1491919 (term15 x)). Qed.
Lemma lem1491921 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1491922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491923 (x : real) (y : real) : (term18 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1491922) (@lem1491921 x y)). Qed.
Lemma lem1491924 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1491923 x y) (@lem1491918 x y)). Qed.
Lemma lem1491925 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1491924 x y)). Qed.
Lemma lem1491926 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491927 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1491926) (@lem1491925 x)). Qed.
Lemma lem1491928 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1491920 x) (@lem1491927 x)). Qed.
Lemma lem1491929 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1491930 : term22 = term23.
Proof. exact (@lem1491929 term24). Qed.
Lemma lem1491931 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1491932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1491933 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1491932) (@lem1491931 x)). Qed.
Lemma lem1491934 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1491933 x) (@lem1491928 x)). Qed.
Lemma lem1491935 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1491934 x)). Qed.
Lemma lem1491936 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491937 : term23 = term30.
Proof. exact (MK_COMB (@lem1491936) (@lem1491935)). Qed.
Lemma lem1491939 : term22 = term30.
Proof. exact (TRANS (@lem1491930) (@lem1491937)). Qed.
Lemma lem1491956 (x : real) (y : real) (z : real) : (term1 x y z) = (term1 x y z).
Proof. exact (eq_refl (term1 x y z)). Qed.
Lemma lem1491957 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1491956 x y z)). Qed.
Lemma lem1491958 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491959 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1491958) (@lem1491957 x y)). Qed.
Lemma lem1491960 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1491959 x y)). Qed.
Lemma lem1491961 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491962 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1491961) (@lem1491960 x)). Qed.
Lemma lem1491963 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1491962 x)). Qed.
Lemma lem1491964 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1491965 : term30 = term30.
Proof. exact (MK_COMB (@lem1491964) (@lem1491963)). Qed.
Lemma lem1491966 : term22 = term30.
Proof. exact (TRANS (@lem1491939) (@lem1491965)). Qed.
Lemma lem1491967 (z : real) (x : real) (y : real) : (term2 y x z) = (term31 z x y).
Proof. exact (@lem1483521 (real_add x z) (real_add x y)). Qed.
Lemma lem1491985 (z : real) (x : real) (y : real) : (term32 z x y) = (term33 z x y).
Proof. exact (@lem1483519 (real_add x z) (real_add x y)). Qed.
Lemma lem1491992 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1483508 x term36 y). Qed.
Lemma lem1491993 (x : real) (z : real) : (term37 x z) = (term37 x z).
Proof. exact (eq_refl (term37 x z)). Qed.
Lemma lem1491994 (z : real) (x : real) (y : real) : (term33 z x y) = (term38 z x y).
Proof. exact (MK_COMB (@lem1491993 x z) (@lem1491992 x y)). Qed.
Lemma lem1491995 (x : real) (z : real) (y : real) : (term38 z x y) = (term39 x z y).
Proof. exact (@lem1483480 x (term40 x) z (term40 y)). Qed.
Lemma lem1491996 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483442 term36 x). Qed.
Lemma lem1491998 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1491999 : term45 = term44.
Proof. exact (@lem1491998 term46). Qed.
Lemma lem1492000 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492001 : term47 = term48.
Proof. exact (MK_COMB (@lem1492000) (@lem1491999)). Qed.
Lemma lem1492002 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1492003 (x : real) : (term42 x) = (term49 x).
Proof. exact (MK_COMB (@lem1492001) (@lem1492002 x)). Qed.
Lemma lem1492004 (x : real) : (term41 x) = (term49 x).
Proof. exact (TRANS (@lem1491996 x) (@lem1492003 x)). Qed.
Lemma lem1492005 (x : real) : (term49 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1492006 (x : real) : (term41 x) = term44.
Proof. exact (TRANS (@lem1492004 x) (@lem1492005 x)). Qed.
Lemma lem1492007 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1492008 (x : real) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem1492007) (@lem1492006 x)). Qed.
Lemma lem1492009 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1492010 (x : real) (y : real) (z : real) : (term39 x z y) = (term54 y z).
Proof. exact (MK_COMB (@lem1492008 x) (@lem1492009 y z)). Qed.
Lemma lem1492011 (x : real) (y : real) (z : real) : (term38 z x y) = (term54 y z).
Proof. exact (TRANS (@lem1491995 x z y) (@lem1492010 x y z)). Qed.
Lemma lem1492012 (y : real) (z : real) : (term54 y z) = (term53 y z).
Proof. exact (@lem1483448 (term53 y z)). Qed.
Lemma lem1492013 (x : real) (y : real) (z : real) : (term38 z x y) = (term53 y z).
Proof. exact (TRANS (@lem1492011 x y z) (@lem1492012 y z)). Qed.
Lemma lem1492014 (x : real) (y : real) (z : real) : (term33 z x y) = (term53 y z).
Proof. exact (TRANS (@lem1491994 z x y) (@lem1492013 x y z)). Qed.
Lemma lem1492016 (x : real) (y : real) (z : real) : (term32 z x y) = (term53 y z).
Proof. exact (TRANS (@lem1491985 z x y) (@lem1492014 x y z)). Qed.
Lemma lem1492017 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492018 (x : real) (y : real) (z : real) : (term55 z x y) = (term56 y z).
Proof. exact (MK_COMB (@lem1492017) (@lem1492016 x y z)). Qed.
Lemma lem1492019 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492020 (x : real) (y : real) (z : real) : (term31 z x y) = (term57 y z).
Proof. exact (MK_COMB (@lem1492018 x y z) (@lem1492019)). Qed.
Lemma lem1492021 (x : real) (y : real) (z : real) : (term2 y x z) = (term57 y z).
Proof. exact (TRANS (@lem1491967 z x y) (@lem1492020 x y z)). Qed.
Lemma lem1492022 (y : real) (z : real) : (term58 y z) = (term59 y z).
Proof. exact (@lem1483531 y z). Qed.
Lemma lem1492035 (y : real) (z : real) : (real_sub y z) = (term52 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1492036 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1492037 (y : real) (z : real) : (term60 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1492036) (@lem1492035 y z)). Qed.
Lemma lem1492038 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492039 (y : real) (z : real) : (term59 y z) = (term62 y z).
Proof. exact (MK_COMB (@lem1492037 y z) (@lem1492038)). Qed.
Lemma lem1492040 (y : real) (z : real) : (term58 y z) = (term62 y z).
Proof. exact (TRANS (@lem1492022 y z) (@lem1492039 y z)). Qed.
Lemma lem1492041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1492042 (x : real) (y : real) (z : real) : (term63 y x z) = (term64 y z).
Proof. exact (MK_COMB (@lem1492041) (@lem1492021 x y z)). Qed.
Lemma lem1492043 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 y z).
Proof. exact (MK_COMB (@lem1492042 x y z) (@lem1492040 y z)). Qed.
Lemma lem1492044 (y : real) (x : real) (z : real) : (term67 y x z) = (term68 y x z).
Proof. exact (@lem1483531 (real_add x y) (real_add x z)). Qed.
Lemma lem1492062 (y : real) (x : real) (z : real) : (term32 y x z) = (term33 y x z).
Proof. exact (@lem1483519 (real_add x y) (real_add x z)). Qed.
Lemma lem1492069 (x : real) (z : real) : (term34 x z) = (term35 x z).
Proof. exact (@lem1483508 x term36 z). Qed.
Lemma lem1492070 (x : real) (y : real) : (term37 x y) = (term37 x y).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem1492071 (y : real) (x : real) (z : real) : (term33 y x z) = (term38 y x z).
Proof. exact (MK_COMB (@lem1492070 x y) (@lem1492069 x z)). Qed.
Lemma lem1492072 (x : real) (y : real) (z : real) : (term38 y x z) = (term39 x y z).
Proof. exact (@lem1483480 x (term40 x) y (term40 z)). Qed.
Lemma lem1492073 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483442 term36 x). Qed.
Lemma lem1492075 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492076 : term45 = term44.
Proof. exact (@lem1492075 term46). Qed.
Lemma lem1492077 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492078 : term47 = term48.
Proof. exact (MK_COMB (@lem1492077) (@lem1492076)). Qed.
Lemma lem1492079 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1492080 (x : real) : (term42 x) = (term49 x).
Proof. exact (MK_COMB (@lem1492078) (@lem1492079 x)). Qed.
Lemma lem1492081 (x : real) : (term41 x) = (term49 x).
Proof. exact (TRANS (@lem1492073 x) (@lem1492080 x)). Qed.
Lemma lem1492082 (x : real) : (term49 x) = term44.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1492083 (x : real) : (term41 x) = term44.
Proof. exact (TRANS (@lem1492081 x) (@lem1492082 x)). Qed.
Lemma lem1492084 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1492085 (x : real) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem1492084) (@lem1492083 x)). Qed.
Lemma lem1492086 (y : real) (z : real) : (term52 y z) = (term52 y z).
Proof. exact (eq_refl (term52 y z)). Qed.
Lemma lem1492087 (x : real) (y : real) (z : real) : (term39 x y z) = (term69 y z).
Proof. exact (MK_COMB (@lem1492085 x) (@lem1492086 y z)). Qed.
Lemma lem1492088 (x : real) (y : real) (z : real) : (term38 y x z) = (term69 y z).
Proof. exact (TRANS (@lem1492072 x y z) (@lem1492087 x y z)). Qed.
Lemma lem1492089 (y : real) (z : real) : (term69 y z) = (term52 y z).
Proof. exact (@lem1483448 (term52 y z)). Qed.
Lemma lem1492090 (x : real) (y : real) (z : real) : (term38 y x z) = (term52 y z).
Proof. exact (TRANS (@lem1492088 x y z) (@lem1492089 y z)). Qed.
Lemma lem1492091 (x : real) (y : real) (z : real) : (term33 y x z) = (term52 y z).
Proof. exact (TRANS (@lem1492071 y x z) (@lem1492090 x y z)). Qed.
Lemma lem1492093 (x : real) (y : real) (z : real) : (term32 y x z) = (term52 y z).
Proof. exact (TRANS (@lem1492062 y x z) (@lem1492091 x y z)). Qed.
Lemma lem1492094 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1492095 (x : real) (y : real) (z : real) : (term70 y x z) = (term61 y z).
Proof. exact (MK_COMB (@lem1492094) (@lem1492093 x y z)). Qed.
Lemma lem1492096 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492097 (x : real) (y : real) (z : real) : (term68 y x z) = (term62 y z).
Proof. exact (MK_COMB (@lem1492095 x y z) (@lem1492096)). Qed.
Lemma lem1492098 (x : real) (y : real) (z : real) : (term67 y x z) = (term62 y z).
Proof. exact (TRANS (@lem1492044 y x z) (@lem1492097 x y z)). Qed.
Lemma lem1492099 (z : real) (y : real) : (real_lt y z) = (term71 z y).
Proof. exact (@lem1483521 z y). Qed.
Lemma lem1492105 (z : real) (y : real) : (real_sub z y) = (term52 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1492110 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term40 y) z). Qed.
Lemma lem1492112 (y : real) (z : real) : (real_sub z y) = (term53 y z).
Proof. exact (TRANS (@lem1492105 z y) (@lem1492110 y z)). Qed.
Lemma lem1492113 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492114 (y : real) (z : real) : (term72 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1492113) (@lem1492112 y z)). Qed.
Lemma lem1492115 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492116 (y : real) (z : real) : (term71 z y) = (term57 y z).
Proof. exact (MK_COMB (@lem1492114 y z) (@lem1492115)). Qed.
Lemma lem1492117 (y : real) (z : real) : (real_lt y z) = (term57 y z).
Proof. exact (TRANS (@lem1492099 z y) (@lem1492116 y z)). Qed.
Lemma lem1492118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1492119 (x : real) (y : real) (z : real) : (term73 y x z) = (term74 y z).
Proof. exact (MK_COMB (@lem1492118) (@lem1492098 x y z)). Qed.
Lemma lem1492120 (x : real) (y : real) (z : real) : (term75 x y z) = (term76 y z).
Proof. exact (MK_COMB (@lem1492119 x y z) (@lem1492117 y z)). Qed.
Lemma lem1492121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492122 (x : real) (y : real) (z : real) : (term77 x y z) = (term78 y z).
Proof. exact (MK_COMB (@lem1492121) (@lem1492043 x y z)). Qed.
Lemma lem1492123 (x : real) (y : real) (z : real) : (term1 x y z) = (term79 y z).
Proof. exact (MK_COMB (@lem1492122 x y z) (@lem1492120 x y z)). Qed.
Lemma lem1492124 (x : real) (y : real) : (term11 x y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1492123 x y z)). Qed.
Lemma lem1492125 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492126 (x : real) (y : real) : (term12 x y) = (term81 y).
Proof. exact (MK_COMB (@lem1492125) (@lem1492124 x y)). Qed.
Lemma lem1492127 (x : real) : (term20 x) = term82.
Proof. exact (fun_ext (fun y : real => @lem1492126 x y)). Qed.
Lemma lem1492128 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492129 (x : real) : (term21 x) = term83.
Proof. exact (MK_COMB (@lem1492128) (@lem1492127 x)). Qed.
Lemma lem1492130 : term29 = term84.
Proof. exact (fun_ext (fun x : real => @lem1492129 x)). Qed.
Lemma lem1492131 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492132 : term30 = term85.
Proof. exact (MK_COMB (@lem1492131) (@lem1492130)). Qed.
Lemma lem1492133 : term22 = term85.
Proof. exact (TRANS (@lem1491966) (@lem1492132)). Qed.
Lemma lem1492135 {A : Type'} (t : Prop) : (term86 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1492136 (t : Prop) : (term87 t) = t.
Proof. exact (@lem1492135 real t). Qed.
Lemma lem1492137 : term85 = term83.
Proof. exact (@lem1492136 term83). Qed.
Lemma lem1492143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1492144 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem1492143 real P Q). Qed.
Lemma lem1492145 (y : real) : (term92 y) = (term93 y).
Proof. exact (@lem1492144 (term94 y) (term95 y)). Qed.
Lemma lem1492146 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1492147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492148 (y : real) (z : real) : (term97 y z) = (term78 y z).
Proof. exact (MK_COMB (@lem1492147) (@lem1492146 y z)). Qed.
Lemma lem1492149 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1492150 (y : real) (z : real) : (term99 y z) = (term79 y z).
Proof. exact (MK_COMB (@lem1492148 y z) (@lem1492149 y z)). Qed.
Lemma lem1492151 (y : real) : (term100 y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1492150 y z)). Qed.
Lemma lem1492152 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492153 (y : real) : (term92 y) = (term81 y).
Proof. exact (MK_COMB (@lem1492152) (@lem1492151 y)). Qed.
Lemma lem1492154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1492155 (y : real) : (term101 y) = (term102 y).
Proof. exact (MK_COMB (@lem1492154) (@lem1492153 y)). Qed.
Lemma lem1492156 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1492157 (y : real) : (term103 y) = (term94 y).
Proof. exact (fun_ext (fun z : real => @lem1492156 y z)). Qed.
Lemma lem1492158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492159 (y : real) : (term104 y) = (term105 y).
Proof. exact (MK_COMB (@lem1492158) (@lem1492157 y)). Qed.
Lemma lem1492160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492161 (y : real) : (term106 y) = (term107 y).
Proof. exact (MK_COMB (@lem1492160) (@lem1492159 y)). Qed.
Lemma lem1492162 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1492163 (y : real) : (term108 y) = (term95 y).
Proof. exact (fun_ext (fun z : real => @lem1492162 y z)). Qed.
Lemma lem1492164 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492165 (y : real) : (term109 y) = (term110 y).
Proof. exact (MK_COMB (@lem1492164) (@lem1492163 y)). Qed.
Lemma lem1492166 (y : real) : (term93 y) = (term111 y).
Proof. exact (MK_COMB (@lem1492161 y) (@lem1492165 y)). Qed.
Lemma lem1492167 (y : real) : ((term92 y) = (term93 y)) = ((term81 y) = (term111 y)).
Proof. exact (MK_COMB (@lem1492155 y) (@lem1492166 y)). Qed.
Lemma lem1492168 (y : real) : (term81 y) = (term111 y).
Proof. exact (EQ_MP (@lem1492167 y) (@lem1492145 y)). Qed.
Lemma lem1492265 : term82 = term112.
Proof. exact (fun_ext (fun y : real => @lem1492168 y)). Qed.
Lemma lem1492266 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492267 : term83 = term113.
Proof. exact (MK_COMB (@lem1492266) (@lem1492265)). Qed.
Lemma lem1492269 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1492270 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term91 P Q).
Proof. exact (@lem1492269 real P Q). Qed.
Lemma lem1492271 : term114 = term115.
Proof. exact (@lem1492270 term116 term117). Qed.
Lemma lem1492272 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1492273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492274 (y : real) : (term119 y) = (term107 y).
Proof. exact (MK_COMB (@lem1492273) (@lem1492272 y)). Qed.
Lemma lem1492275 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1492276 (y : real) : (term121 y) = (term111 y).
Proof. exact (MK_COMB (@lem1492274 y) (@lem1492275 y)). Qed.
Lemma lem1492277 : term122 = term112.
Proof. exact (fun_ext (fun y : real => @lem1492276 y)). Qed.
Lemma lem1492278 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492279 : term114 = term113.
Proof. exact (MK_COMB (@lem1492278) (@lem1492277)). Qed.
Lemma lem1492280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1492281 : term123 = term124.
Proof. exact (MK_COMB (@lem1492280) (@lem1492279)). Qed.
Lemma lem1492282 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1492283 : term125 = term116.
Proof. exact (fun_ext (fun y : real => @lem1492282 y)). Qed.
Lemma lem1492284 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492285 : term126 = term127.
Proof. exact (MK_COMB (@lem1492284) (@lem1492283)). Qed.
Lemma lem1492286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492287 : term128 = term129.
Proof. exact (MK_COMB (@lem1492286) (@lem1492285)). Qed.
Lemma lem1492288 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1492289 : term130 = term117.
Proof. exact (fun_ext (fun y : real => @lem1492288 y)). Qed.
Lemma lem1492290 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492291 : term131 = term132.
Proof. exact (MK_COMB (@lem1492290) (@lem1492289)). Qed.
Lemma lem1492292 : term115 = term133.
Proof. exact (MK_COMB (@lem1492287) (@lem1492291)). Qed.
Lemma lem1492293 : (term114 = term115) = (term113 = term133).
Proof. exact (MK_COMB (@lem1492281) (@lem1492292)). Qed.
Lemma lem1492294 : term113 = term133.
Proof. exact (EQ_MP (@lem1492293) (@lem1492271)). Qed.
Lemma lem1492399 : term83 = term133.
Proof. exact (TRANS (@lem1492267) (@lem1492294)). Qed.
Lemma lem1492400 : term85 = term133.
Proof. exact (TRANS (@lem1492137) (@lem1492399)). Qed.
Lemma lem1492402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1492403 (P : real -> Prop) (Q : real -> Prop) : (term91 P Q) = (term90 P Q).
Proof. exact (@lem1492402 real P Q). Qed.
Lemma lem1492404 : term115 = term114.
Proof. exact (@lem1492403 term116 term117). Qed.
Lemma lem1492405 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1492406 : term125 = term116.
Proof. exact (fun_ext (fun y : real => @lem1492405 y)). Qed.
Lemma lem1492407 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492408 : term126 = term127.
Proof. exact (MK_COMB (@lem1492407) (@lem1492406)). Qed.
Lemma lem1492409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492410 : term128 = term129.
Proof. exact (MK_COMB (@lem1492409) (@lem1492408)). Qed.
Lemma lem1492411 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1492412 : term130 = term117.
Proof. exact (fun_ext (fun y : real => @lem1492411 y)). Qed.
Lemma lem1492413 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492414 : term131 = term132.
Proof. exact (MK_COMB (@lem1492413) (@lem1492412)). Qed.
Lemma lem1492415 : term115 = term133.
Proof. exact (MK_COMB (@lem1492410) (@lem1492414)). Qed.
Lemma lem1492416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1492417 : term134 = term135.
Proof. exact (MK_COMB (@lem1492416) (@lem1492415)). Qed.
Lemma lem1492418 (y : real) : (term118 y) = (term105 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem1492419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492420 (y : real) : (term119 y) = (term107 y).
Proof. exact (MK_COMB (@lem1492419) (@lem1492418 y)). Qed.
Lemma lem1492421 (y : real) : (term120 y) = (term110 y).
Proof. exact (eq_refl (term120 y)). Qed.
Lemma lem1492422 (y : real) : (term121 y) = (term111 y).
Proof. exact (MK_COMB (@lem1492420 y) (@lem1492421 y)). Qed.
Lemma lem1492423 : term122 = term112.
Proof. exact (fun_ext (fun y : real => @lem1492422 y)). Qed.
Lemma lem1492424 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492425 : term114 = term113.
Proof. exact (MK_COMB (@lem1492424) (@lem1492423)). Qed.
Lemma lem1492426 : (term115 = term114) = (term133 = term113).
Proof. exact (MK_COMB (@lem1492417) (@lem1492425)). Qed.
Lemma lem1492427 : term133 = term113.
Proof. exact (EQ_MP (@lem1492426) (@lem1492404)). Qed.
Lemma lem1492429 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1492430 (P : real -> Prop) (Q : real -> Prop) : (term91 P Q) = (term90 P Q).
Proof. exact (@lem1492429 real P Q). Qed.
Lemma lem1492431 (y : real) : (term93 y) = (term92 y).
Proof. exact (@lem1492430 (term94 y) (term95 y)). Qed.
Lemma lem1492432 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1492433 (y : real) : (term103 y) = (term94 y).
Proof. exact (fun_ext (fun z : real => @lem1492432 y z)). Qed.
Lemma lem1492434 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492435 (y : real) : (term104 y) = (term105 y).
Proof. exact (MK_COMB (@lem1492434) (@lem1492433 y)). Qed.
Lemma lem1492436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492437 (y : real) : (term106 y) = (term107 y).
Proof. exact (MK_COMB (@lem1492436) (@lem1492435 y)). Qed.
Lemma lem1492438 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1492439 (y : real) : (term108 y) = (term95 y).
Proof. exact (fun_ext (fun z : real => @lem1492438 y z)). Qed.
Lemma lem1492440 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492441 (y : real) : (term109 y) = (term110 y).
Proof. exact (MK_COMB (@lem1492440) (@lem1492439 y)). Qed.
Lemma lem1492442 (y : real) : (term93 y) = (term111 y).
Proof. exact (MK_COMB (@lem1492437 y) (@lem1492441 y)). Qed.
Lemma lem1492443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1492444 (y : real) : (term136 y) = (term137 y).
Proof. exact (MK_COMB (@lem1492443) (@lem1492442 y)). Qed.
Lemma lem1492445 (y : real) (z : real) : (term96 y z) = (term66 y z).
Proof. exact (eq_refl (term96 y z)). Qed.
Lemma lem1492446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1492447 (y : real) (z : real) : (term97 y z) = (term78 y z).
Proof. exact (MK_COMB (@lem1492446) (@lem1492445 y z)). Qed.
Lemma lem1492448 (y : real) (z : real) : (term98 y z) = (term76 y z).
Proof. exact (eq_refl (term98 y z)). Qed.
Lemma lem1492449 (y : real) (z : real) : (term99 y z) = (term79 y z).
Proof. exact (MK_COMB (@lem1492447 y z) (@lem1492448 y z)). Qed.
Lemma lem1492450 (y : real) : (term100 y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1492449 y z)). Qed.
Lemma lem1492451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492452 (y : real) : (term92 y) = (term81 y).
Proof. exact (MK_COMB (@lem1492451) (@lem1492450 y)). Qed.
Lemma lem1492453 (y : real) : ((term93 y) = (term92 y)) = ((term111 y) = (term81 y)).
Proof. exact (MK_COMB (@lem1492444 y) (@lem1492452 y)). Qed.
Lemma lem1492454 (y : real) : (term111 y) = (term81 y).
Proof. exact (EQ_MP (@lem1492453 y) (@lem1492431 y)). Qed.
Lemma lem1492455 : term112 = term82.
Proof. exact (fun_ext (fun y : real => @lem1492454 y)). Qed.
Lemma lem1492456 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492457 : term113 = term83.
Proof. exact (MK_COMB (@lem1492456) (@lem1492455)). Qed.
Lemma lem1492458 : term133 = term83.
Proof. exact (TRANS (@lem1492427) (@lem1492457)). Qed.
Lemma lem1492459 : term85 = term83.
Proof. exact (TRANS (@lem1492400) (@lem1492458)). Qed.
Lemma lem1492462 : term22 = term83.
Proof. exact (TRANS (@lem1492133) (@lem1492459)). Qed.
Lemma lem1492479 (y : real) (z : real) : (term79 y z) = (term79 y z).
Proof. exact (eq_refl (term79 y z)). Qed.
Lemma lem1492480 (y : real) : (term80 y) = (term80 y).
Proof. exact (fun_ext (fun z : real => @lem1492479 y z)). Qed.
Lemma lem1492481 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492482 (y : real) : (term81 y) = (term81 y).
Proof. exact (MK_COMB (@lem1492481) (@lem1492480 y)). Qed.
Lemma lem1492483 : term82 = term82.
Proof. exact (fun_ext (fun y : real => @lem1492482 y)). Qed.
Lemma lem1492484 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1492485 : term83 = term83.
Proof. exact (MK_COMB (@lem1492484) (@lem1492483)). Qed.
Lemma lem1492486 : term22 = term83.
Proof. exact (TRANS (@lem1492462) (@lem1492485)). Qed.
Lemma lem1492496 (y : real) (z : real) (h1 : term79 y z) : term79 y z.
Proof. exact (h1). Qed.
Lemma lem1492497 (y : real) (z : real) (h1 : term66 y z) : term66 y z.
Proof. exact (h1). Qed.
Lemma lem1492498 (y : real) (z : real) (h1 : term66 y z) : term62 y z.
Proof. exact (proj2 (@lem1492497 y z h1)). Qed.
Lemma lem1492499 (y : real) (z : real) (h1 : term66 y z) : term57 y z.
Proof. exact (proj1 (@lem1492497 y z h1)). Qed.
Lemma lem1492501 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1492502 : term139 = term140.
Proof. exact (@lem1492501 (NUMERAL 0) term46). Qed.
Lemma lem1492503 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1492504 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1492505 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1492504 h1) (fun h1 : term140 = True => @lem1492503)). Qed.
Lemma lem1492506 : term140 = True.
Proof. exact (EQ_MP (@lem1492505) (@lem1492503)). Qed.
Lemma lem1492507 : term139 = True.
Proof. exact (TRANS (@lem1492502) (@lem1492506)). Qed.
Lemma lem1492508 : True = term139.
Proof. exact (SYM (@lem1492507)). Qed.
Lemma lem1492509 : term139.
Proof. exact (EQ_MP (@lem1492508) (@lem0)). Qed.
Lemma lem1492510 (y : real) (z : real) (h1 : term66 y z) : term142 y z.
Proof. exact (conj (@lem1492509) (@lem1492498 y z h1)). Qed.
Lemma lem1492512 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1492513 (y : real) (z : real) : term144 y z.
Proof. exact (@lem1492512 term145 (term52 y z)). Qed.
Lemma lem1492514 (y : real) (z : real) (h1 : term66 y z) : term146 y z.
Proof. exact (@lem1492513 y z (@lem1492510 y z h1)). Qed.
Lemma lem1492515 (y : real) (z : real) : (term147 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1492516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1492517 (y : real) (z : real) : (term148 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1492516) (@lem1492515 y z)). Qed.
Lemma lem1492518 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492519 (y : real) (z : real) : (term146 y z) = (term62 y z).
Proof. exact (MK_COMB (@lem1492517 y z) (@lem1492518)). Qed.
Lemma lem1492520 (y : real) (z : real) (h1 : term66 y z) : term62 y z.
Proof. exact (EQ_MP (@lem1492519 y z) (@lem1492514 y z h1)). Qed.
Lemma lem1492522 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1492523 : term139 = term140.
Proof. exact (@lem1492522 (NUMERAL 0) term46). Qed.
Lemma lem1492524 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1492525 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1492526 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1492525 h1) (fun h1 : term140 = True => @lem1492524)). Qed.
Lemma lem1492527 : term140 = True.
Proof. exact (EQ_MP (@lem1492526) (@lem1492524)). Qed.
Lemma lem1492528 : term139 = True.
Proof. exact (TRANS (@lem1492523) (@lem1492527)). Qed.
Lemma lem1492529 : True = term139.
Proof. exact (SYM (@lem1492528)). Qed.
Lemma lem1492530 : term139.
Proof. exact (EQ_MP (@lem1492529) (@lem0)). Qed.
Lemma lem1492531 (y : real) (z : real) (h1 : term66 y z) : term149 y z.
Proof. exact (conj (@lem1492530) (@lem1492499 y z h1)). Qed.
Lemma lem1492533 (x : real) (y : real) : term150 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1492534 (y : real) (z : real) : term151 y z.
Proof. exact (@lem1492533 term145 (term53 y z)). Qed.
Lemma lem1492535 (y : real) (z : real) (h1 : term66 y z) : term152 y z.
Proof. exact (@lem1492534 y z (@lem1492531 y z h1)). Qed.
Lemma lem1492536 (y : real) (z : real) : (term153 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1492537 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492538 (y : real) (z : real) : (term154 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1492537) (@lem1492536 y z)). Qed.
Lemma lem1492539 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492540 (y : real) (z : real) : (term152 y z) = (term57 y z).
Proof. exact (MK_COMB (@lem1492538 y z) (@lem1492539)). Qed.
Lemma lem1492541 (y : real) (z : real) (h1 : term66 y z) : term57 y z.
Proof. exact (EQ_MP (@lem1492540 y z) (@lem1492535 y z h1)). Qed.
Lemma lem1492542 (y : real) (z : real) (h1 : term66 y z) : term66 y z.
Proof. exact (conj (@lem1492541 y z h1) (@lem1492520 y z h1)). Qed.
Lemma lem1492544 (x : real) (y : real) : term155 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1492545 (y : real) (z : real) : term156 y z.
Proof. exact (@lem1492544 (term53 y z) (term52 y z)). Qed.
Lemma lem1492546 (y : real) (z : real) (h1 : term66 y z) : term157 y z.
Proof. exact (@lem1492545 y z (@lem1492542 y z h1)). Qed.
Lemma lem1492547 (y : real) (z : real) : (term158 y z) = (term159 y z).
Proof. exact (@lem1483480 (term40 y) y z (term40 z)). Qed.
Lemma lem1492548 (y : real) : (term160 y) = (term42 y).
Proof. exact (@lem1483440 term36 y). Qed.
Lemma lem1492550 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492551 : term45 = term44.
Proof. exact (@lem1492550 term46). Qed.
Lemma lem1492552 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492553 : term47 = term48.
Proof. exact (MK_COMB (@lem1492552) (@lem1492551)). Qed.
Lemma lem1492554 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1492555 (y : real) : (term42 y) = (term49 y).
Proof. exact (MK_COMB (@lem1492553) (@lem1492554 y)). Qed.
Lemma lem1492556 (y : real) : (term160 y) = (term49 y).
Proof. exact (TRANS (@lem1492548 y) (@lem1492555 y)). Qed.
Lemma lem1492557 (y : real) : (term49 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1492558 (y : real) : (term160 y) = term44.
Proof. exact (TRANS (@lem1492556 y) (@lem1492557 y)). Qed.
Lemma lem1492559 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1492560 (y : real) : (term161 y) = term51.
Proof. exact (MK_COMB (@lem1492559) (@lem1492558 y)). Qed.
Lemma lem1492561 (z : real) : (term41 z) = (term42 z).
Proof. exact (@lem1483442 term36 z). Qed.
Lemma lem1492563 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492564 : term45 = term44.
Proof. exact (@lem1492563 term46). Qed.
Lemma lem1492565 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492566 : term47 = term48.
Proof. exact (MK_COMB (@lem1492565) (@lem1492564)). Qed.
Lemma lem1492567 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1492568 (z : real) : (term42 z) = (term49 z).
Proof. exact (MK_COMB (@lem1492566) (@lem1492567 z)). Qed.
Lemma lem1492569 (z : real) : (term41 z) = (term49 z).
Proof. exact (TRANS (@lem1492561 z) (@lem1492568 z)). Qed.
Lemma lem1492570 (z : real) : (term49 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1492571 (z : real) : (term41 z) = term44.
Proof. exact (TRANS (@lem1492569 z) (@lem1492570 z)). Qed.
Lemma lem1492572 (y : real) (z : real) : (term159 y z) = term162.
Proof. exact (MK_COMB (@lem1492560 y) (@lem1492571 z)). Qed.
Lemma lem1492573 (y : real) (z : real) : (term158 y z) = term162.
Proof. exact (TRANS (@lem1492547 y z) (@lem1492572 y z)). Qed.
Lemma lem1492574 : term162 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1492575 (y : real) (z : real) : (term158 y z) = term44.
Proof. exact (TRANS (@lem1492573 y z) (@lem1492574)). Qed.
Lemma lem1492576 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492577 (y : real) (z : real) : (term163 y z) = term164.
Proof. exact (MK_COMB (@lem1492576) (@lem1492575 y z)). Qed.
Lemma lem1492578 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492579 (y : real) (z : real) : (term157 y z) = term165.
Proof. exact (MK_COMB (@lem1492577 y z) (@lem1492578)). Qed.
Lemma lem1492580 (y : real) (z : real) (h1 : term66 y z) : term165.
Proof. exact (EQ_MP (@lem1492579 y z) (@lem1492546 y z h1)). Qed.
Lemma lem1492582 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1492583 : term165 = term166.
Proof. exact (@lem1492582 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1492584 : term166 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1492585 : term165 = False.
Proof. exact (TRANS (@lem1492583) (@lem1492584)). Qed.
Lemma lem1492586 (y : real) (z : real) (h1 : term66 y z) : False.
Proof. exact (EQ_MP (@lem1492585) (@lem1492580 y z h1)). Qed.
Lemma lem1492587 (y : real) (z : real) (h1 : term76 y z) : term76 y z.
Proof. exact (h1). Qed.
Lemma lem1492588 (y : real) (z : real) (h1 : term76 y z) : term57 y z.
Proof. exact (proj2 (@lem1492587 y z h1)). Qed.
Lemma lem1492589 (y : real) (z : real) (h1 : term76 y z) : term62 y z.
Proof. exact (proj1 (@lem1492587 y z h1)). Qed.
Lemma lem1492591 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1492592 : term139 = term140.
Proof. exact (@lem1492591 (NUMERAL 0) term46). Qed.
Lemma lem1492593 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1492594 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1492595 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1492594 h1) (fun h1 : term140 = True => @lem1492593)). Qed.
Lemma lem1492596 : term140 = True.
Proof. exact (EQ_MP (@lem1492595) (@lem1492593)). Qed.
Lemma lem1492597 : term139 = True.
Proof. exact (TRANS (@lem1492592) (@lem1492596)). Qed.
Lemma lem1492598 : True = term139.
Proof. exact (SYM (@lem1492597)). Qed.
Lemma lem1492599 : term139.
Proof. exact (EQ_MP (@lem1492598) (@lem0)). Qed.
Lemma lem1492600 (y : real) (z : real) (h1 : term76 y z) : term142 y z.
Proof. exact (conj (@lem1492599) (@lem1492589 y z h1)). Qed.
Lemma lem1492602 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1492603 (y : real) (z : real) : term144 y z.
Proof. exact (@lem1492602 term145 (term52 y z)). Qed.
Lemma lem1492604 (y : real) (z : real) (h1 : term76 y z) : term146 y z.
Proof. exact (@lem1492603 y z (@lem1492600 y z h1)). Qed.
Lemma lem1492605 (y : real) (z : real) : (term147 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1492606 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1492607 (y : real) (z : real) : (term148 y z) = (term61 y z).
Proof. exact (MK_COMB (@lem1492606) (@lem1492605 y z)). Qed.
Lemma lem1492608 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492609 (y : real) (z : real) : (term146 y z) = (term62 y z).
Proof. exact (MK_COMB (@lem1492607 y z) (@lem1492608)). Qed.
Lemma lem1492610 (y : real) (z : real) (h1 : term76 y z) : term62 y z.
Proof. exact (EQ_MP (@lem1492609 y z) (@lem1492604 y z h1)). Qed.
Lemma lem1492612 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1492613 : term139 = term140.
Proof. exact (@lem1492612 (NUMERAL 0) term46). Qed.
Lemma lem1492614 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1492615 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1492616 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1492615 h1) (fun h1 : term140 = True => @lem1492614)). Qed.
Lemma lem1492617 : term140 = True.
Proof. exact (EQ_MP (@lem1492616) (@lem1492614)). Qed.
Lemma lem1492618 : term139 = True.
Proof. exact (TRANS (@lem1492613) (@lem1492617)). Qed.
Lemma lem1492619 : True = term139.
Proof. exact (SYM (@lem1492618)). Qed.
Lemma lem1492620 : term139.
Proof. exact (EQ_MP (@lem1492619) (@lem0)). Qed.
Lemma lem1492621 (y : real) (z : real) (h1 : term76 y z) : term149 y z.
Proof. exact (conj (@lem1492620) (@lem1492588 y z h1)). Qed.
Lemma lem1492623 (x : real) (y : real) : term150 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1492624 (y : real) (z : real) : term151 y z.
Proof. exact (@lem1492623 term145 (term53 y z)). Qed.
Lemma lem1492625 (y : real) (z : real) (h1 : term76 y z) : term152 y z.
Proof. exact (@lem1492624 y z (@lem1492621 y z h1)). Qed.
Lemma lem1492626 (y : real) (z : real) : (term153 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1492627 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492628 (y : real) (z : real) : (term154 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1492627) (@lem1492626 y z)). Qed.
Lemma lem1492629 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492630 (y : real) (z : real) : (term152 y z) = (term57 y z).
Proof. exact (MK_COMB (@lem1492628 y z) (@lem1492629)). Qed.
Lemma lem1492631 (y : real) (z : real) (h1 : term76 y z) : term57 y z.
Proof. exact (EQ_MP (@lem1492630 y z) (@lem1492625 y z h1)). Qed.
Lemma lem1492632 (y : real) (z : real) (h1 : term76 y z) : term66 y z.
Proof. exact (conj (@lem1492631 y z h1) (@lem1492610 y z h1)). Qed.
Lemma lem1492634 (x : real) (y : real) : term155 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1492635 (y : real) (z : real) : term156 y z.
Proof. exact (@lem1492634 (term53 y z) (term52 y z)). Qed.
Lemma lem1492636 (y : real) (z : real) (h1 : term76 y z) : term157 y z.
Proof. exact (@lem1492635 y z (@lem1492632 y z h1)). Qed.
Lemma lem1492637 (y : real) (z : real) : (term158 y z) = (term159 y z).
Proof. exact (@lem1483480 (term40 y) y z (term40 z)). Qed.
Lemma lem1492638 (y : real) : (term160 y) = (term42 y).
Proof. exact (@lem1483440 term36 y). Qed.
Lemma lem1492640 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492641 : term45 = term44.
Proof. exact (@lem1492640 term46). Qed.
Lemma lem1492642 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492643 : term47 = term48.
Proof. exact (MK_COMB (@lem1492642) (@lem1492641)). Qed.
Lemma lem1492644 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1492645 (y : real) : (term42 y) = (term49 y).
Proof. exact (MK_COMB (@lem1492643) (@lem1492644 y)). Qed.
Lemma lem1492646 (y : real) : (term160 y) = (term49 y).
Proof. exact (TRANS (@lem1492638 y) (@lem1492645 y)). Qed.
Lemma lem1492647 (y : real) : (term49 y) = term44.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1492648 (y : real) : (term160 y) = term44.
Proof. exact (TRANS (@lem1492646 y) (@lem1492647 y)). Qed.
Lemma lem1492649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1492650 (y : real) : (term161 y) = term51.
Proof. exact (MK_COMB (@lem1492649) (@lem1492648 y)). Qed.
Lemma lem1492651 (z : real) : (term41 z) = (term42 z).
Proof. exact (@lem1483442 term36 z). Qed.
Lemma lem1492653 (m : nat) : (term43 m) = term44.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1492654 : term45 = term44.
Proof. exact (@lem1492653 term46). Qed.
Lemma lem1492655 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1492656 : term47 = term48.
Proof. exact (MK_COMB (@lem1492655) (@lem1492654)). Qed.
Lemma lem1492657 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1492658 (z : real) : (term42 z) = (term49 z).
Proof. exact (MK_COMB (@lem1492656) (@lem1492657 z)). Qed.
Lemma lem1492659 (z : real) : (term41 z) = (term49 z).
Proof. exact (TRANS (@lem1492651 z) (@lem1492658 z)). Qed.
Lemma lem1492660 (z : real) : (term49 z) = term44.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1492661 (z : real) : (term41 z) = term44.
Proof. exact (TRANS (@lem1492659 z) (@lem1492660 z)). Qed.
Lemma lem1492662 (y : real) (z : real) : (term159 y z) = term162.
Proof. exact (MK_COMB (@lem1492650 y) (@lem1492661 z)). Qed.
Lemma lem1492663 (y : real) (z : real) : (term158 y z) = term162.
Proof. exact (TRANS (@lem1492637 y z) (@lem1492662 y z)). Qed.
Lemma lem1492664 : term162 = term44.
Proof. exact (@lem1483448 term44). Qed.
Lemma lem1492665 (y : real) (z : real) : (term158 y z) = term44.
Proof. exact (TRANS (@lem1492663 y z) (@lem1492664)). Qed.
Lemma lem1492666 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1492667 (y : real) (z : real) : (term163 y z) = term164.
Proof. exact (MK_COMB (@lem1492666) (@lem1492665 y z)). Qed.
Lemma lem1492668 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1492669 (y : real) (z : real) : (term157 y z) = term165.
Proof. exact (MK_COMB (@lem1492667 y z) (@lem1492668)). Qed.
Lemma lem1492670 (y : real) (z : real) (h1 : term76 y z) : term165.
Proof. exact (EQ_MP (@lem1492669 y z) (@lem1492636 y z h1)). Qed.
Lemma lem1492672 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1492673 : term165 = term166.
Proof. exact (@lem1492672 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1492674 : term166 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1492675 : term165 = False.
Proof. exact (TRANS (@lem1492673) (@lem1492674)). Qed.
Lemma lem1492676 (y : real) (z : real) (h1 : term76 y z) : False.
Proof. exact (EQ_MP (@lem1492675) (@lem1492670 y z h1)). Qed.
Lemma lem1492677 (y : real) (z : real) (h1 : term79 y z) : False.
Proof. exact (or_elim (@lem1492496 y z h1) (fun h0 : term66 y z => @lem1492586 y z h0) (fun h0 : term76 y z => @lem1492676 y z h0)). Qed.
Lemma lem1492679 (y : real) (z : real) (h1 : term79 y z) : term79 y z.
Proof. exact (h1). Qed.
Lemma lem1492680 (y : real) (z : real) (h1 : term79 y z) : (term79 y z) = False.
Proof. exact (prop_ext (fun h2 : term79 y z => @lem1492677 y z h1) (fun h2 : False => @lem1492679 y z h1)). Qed.
Lemma lem1492681 (y : real) (z : real) (h1 : term79 y z) : False.
Proof. exact (EQ_MP (@lem1492680 y z h1) (@lem1492679 y z h1)). Qed.
Lemma lem1492682 (y : real) (h1 : term81 y) : term81 y.
Proof. exact (h1). Qed.
Lemma lem1492683 (y : real) (h1 : term81 y) : False.
Proof. exact (ex_elim (@lem1492682 y h1) (fun z : real => fun h0 : term80 y z => @lem1492681 y z h0)). Qed.
Lemma lem1492684 (h1 : term83) : term83.
Proof. exact (h1). Qed.
Lemma lem1492685 (h1 : term83) : False.
Proof. exact (ex_elim (@lem1492684 h1) (fun y : real => fun h0 : term82 y => @lem1492683 y h0)). Qed.
Lemma lem1492686 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1492687 (h1 : term22) : term83.
Proof. exact (EQ_MP (@lem1492486) (@lem1492686 h1)). Qed.
Lemma lem1492688 (h1 : term22) : term83 = False.
Proof. exact (prop_ext (fun h2 : term83 => @lem1492685 h2) (fun h2 : False => @lem1492687 h1)). Qed.
Lemma lem1492689 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1492688 h1) (@lem1492687 h1)). Qed.
Lemma lem1492690 : term167.
Proof. exact (fun h0 : term22 => @lem1492689 h0). Qed.
Lemma lem1492691 : term168.
Proof. exact (@lem1386578 term169). Qed.
Lemma lem1492692 : term169.
Proof. exact (@lem1492691 (@lem1492690)). Qed.
