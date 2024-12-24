Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_SUB2_term_abbrevs.
Require Import thm1008952_spec.
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
Require Import thm1483476_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1522962 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1522963 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1522962 (term4 x)). Qed.
Lemma lem1522964 (x : real) (y : real) : (term5 x y) = ((term6 x y) = y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1522965 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1522967 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1522965) (@lem1522964 x y)). Qed.
Lemma lem1522968 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1522967 x y)). Qed.
Lemma lem1522969 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522970 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1522969) (@lem1522968 x)). Qed.
Lemma lem1522971 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1522963 x) (@lem1522970 x)). Qed.
Lemma lem1522972 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1522973 : term12 = term13.
Proof. exact (@lem1522972 term14). Qed.
Lemma lem1522974 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1522975 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1522976 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1522975) (@lem1522974 x)). Qed.
Lemma lem1522977 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1522976 x) (@lem1522971 x)). Qed.
Lemma lem1522978 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1522977 x)). Qed.
Lemma lem1522979 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522980 : term13 = term20.
Proof. exact (MK_COMB (@lem1522979) (@lem1522978)). Qed.
Lemma lem1522982 : term12 = term20.
Proof. exact (TRANS (@lem1522973) (@lem1522980)). Qed.
Lemma lem1522985 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1522986 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1522985 x y)). Qed.
Lemma lem1522987 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522988 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1522987) (@lem1522986 x)). Qed.
Lemma lem1522989 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1522988 x)). Qed.
Lemma lem1522990 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1522991 : term20 = term20.
Proof. exact (MK_COMB (@lem1522990) (@lem1522989)). Qed.
Lemma lem1522992 : term12 = term20.
Proof. exact (TRANS (@lem1522982) (@lem1522991)). Qed.
Lemma lem1522993 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (term6 x y) y). Qed.
Lemma lem1522994 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523007 (x : real) (y : real) : (real_sub x y) = (term22 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1523010 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1523011 (x : real) (y : real) : (term6 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1523010 x) (@lem1523007 x y)). Qed.
Lemma lem1523012 (x : real) (y : real) : (term23 x y) = (term24 x y).
Proof. exact (@lem1483519 x (term22 x y)). Qed.
Lemma lem1523013 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (@lem1483508 x term27 (term28 y)). Qed.
Lemma lem1523014 (y : real) : (term29 y) = (term30 y).
Proof. exact (@lem1483476 term27 term27 y). Qed.
Lemma lem1523016 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1523017 : term33 = term34.
Proof. exact (@lem1523016 term35 term35). Qed.
Lemma lem1523018 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1523019 : term37 = term35.
Proof. exact (EQ_MP (@lem1523018) (@lem940073)). Qed.
Lemma lem1523020 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1523021 : term34 = term38.
Proof. exact (MK_COMB (@lem1523020) (@lem1523019)). Qed.
Lemma lem1523022 : term33 = term38.
Proof. exact (TRANS (@lem1523017) (@lem1523021)). Qed.
Lemma lem1523023 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523024 : term39 = term40.
Proof. exact (MK_COMB (@lem1523023) (@lem1523022)). Qed.
Lemma lem1523025 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523026 (y : real) : (term30 y) = (term41 y).
Proof. exact (MK_COMB (@lem1523024) (@lem1523025 y)). Qed.
Lemma lem1523027 (y : real) : (term29 y) = (term41 y).
Proof. exact (TRANS (@lem1523014 y) (@lem1523026 y)). Qed.
Lemma lem1523028 (y : real) : (term41 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1523029 (y : real) : (term29 y) = y.
Proof. exact (TRANS (@lem1523027 y) (@lem1523028 y)). Qed.
Lemma lem1523032 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1523033 (x : real) (y : real) : (term26 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1523032 x) (@lem1523029 y)). Qed.
Lemma lem1523034 (x : real) (y : real) : (term25 x y) = (term43 x y).
Proof. exact (TRANS (@lem1523013 x y) (@lem1523033 x y)). Qed.
Lemma lem1523035 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1523036 (x : real) (y : real) : (term24 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1523035 x) (@lem1523034 x y)). Qed.
Lemma lem1523037 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (@lem1483490 x (term28 x) y). Qed.
Lemma lem1523038 (x : real) : (term46 x) = (term47 x).
Proof. exact (@lem1483442 term27 x). Qed.
Lemma lem1523040 (m : nat) : (term48 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523041 : term50 = term49.
Proof. exact (@lem1523040 term35). Qed.
Lemma lem1523042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523043 : term51 = term52.
Proof. exact (MK_COMB (@lem1523042) (@lem1523041)). Qed.
Lemma lem1523044 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1523045 (x : real) : (term47 x) = (term53 x).
Proof. exact (MK_COMB (@lem1523043) (@lem1523044 x)). Qed.
Lemma lem1523046 (x : real) : (term46 x) = (term53 x).
Proof. exact (TRANS (@lem1523038 x) (@lem1523045 x)). Qed.
Lemma lem1523047 (x : real) : (term53 x) = term49.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1523048 (x : real) : (term46 x) = term49.
Proof. exact (TRANS (@lem1523046 x) (@lem1523047 x)). Qed.
Lemma lem1523049 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1523050 (x : real) : (term54 x) = term55.
Proof. exact (MK_COMB (@lem1523049) (@lem1523048 x)). Qed.
Lemma lem1523051 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523052 (x : real) (y : real) : (term45 x y) = (term56 y).
Proof. exact (MK_COMB (@lem1523050 x) (@lem1523051 y)). Qed.
Lemma lem1523053 (x : real) (y : real) : (term44 x y) = (term56 y).
Proof. exact (TRANS (@lem1523037 x y) (@lem1523052 x y)). Qed.
Lemma lem1523054 (y : real) : (term56 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1523055 (x : real) (y : real) : (term44 x y) = y.
Proof. exact (TRANS (@lem1523053 x y) (@lem1523054 y)). Qed.
Lemma lem1523056 (x : real) (y : real) : (term24 x y) = y.
Proof. exact (TRANS (@lem1523036 x y) (@lem1523055 x y)). Qed.
Lemma lem1523057 (x : real) (y : real) : (term23 x y) = y.
Proof. exact (TRANS (@lem1523012 x y) (@lem1523056 x y)). Qed.
Lemma lem1523058 (x : real) (y : real) : (term6 x y) = y.
Proof. exact (TRANS (@lem1523011 x y) (@lem1523057 x y)). Qed.
Lemma lem1523059 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1523060 (x : real) (y : real) : (term57 x y) = (real_sub y).
Proof. exact (MK_COMB (@lem1523059) (@lem1523058 x y)). Qed.
Lemma lem1523061 (x : real) (y : real) : (term58 x y) = (real_sub y y).
Proof. exact (MK_COMB (@lem1523060 x y) (@lem1522994 y)). Qed.
Lemma lem1523062 (y : real) : (real_sub y y) = (term46 y).
Proof. exact (@lem1483519 y y). Qed.
Lemma lem1523066 (y : real) : (term46 y) = (term47 y).
Proof. exact (@lem1483442 term27 y). Qed.
Lemma lem1523068 (m : nat) : (term48 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1523069 : term50 = term49.
Proof. exact (@lem1523068 term35). Qed.
Lemma lem1523070 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1523071 : term51 = term52.
Proof. exact (MK_COMB (@lem1523070) (@lem1523069)). Qed.
Lemma lem1523072 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1523073 (y : real) : (term47 y) = (term53 y).
Proof. exact (MK_COMB (@lem1523071) (@lem1523072 y)). Qed.
Lemma lem1523074 (y : real) : (term46 y) = (term53 y).
Proof. exact (TRANS (@lem1523066 y) (@lem1523073 y)). Qed.
Lemma lem1523075 (y : real) : (term53 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1523077 (y : real) : (term46 y) = term49.
Proof. exact (TRANS (@lem1523074 y) (@lem1523075 y)). Qed.
Lemma lem1523078 (y : real) : (real_sub y y) = term49.
Proof. exact (TRANS (@lem1523062 y) (@lem1523077 y)). Qed.
Lemma lem1523079 (x : real) (y : real) : (term58 x y) = term49.
Proof. exact (TRANS (@lem1523061 x y) (@lem1523078 y)). Qed.
Lemma lem1523080 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1523081 (x : real) (y : real) : (term59 x y) = term60.
Proof. exact (MK_COMB (@lem1523080) (@lem1523079 x y)). Qed.
Lemma lem1523082 : term60 = term61.
Proof. exact (@lem1483512 term49). Qed.
Lemma lem1523084 (x : nat) : (term62 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1523085 : term61 = term49.
Proof. exact (@lem1523084 term35). Qed.
Lemma lem1523086 : term60 = term49.
Proof. exact (TRANS (@lem1523082) (@lem1523085)). Qed.
Lemma lem1523087 (x : real) (y : real) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1523088 (x : real) (y : real) : ((term59 x y) = term60) = ((term59 x y) = term49).
Proof. exact (MK_COMB (@lem1523087 x y) (@lem1523086)). Qed.
Lemma lem1523089 (x : real) (y : real) : (term59 x y) = term49.
Proof. exact (EQ_MP (@lem1523088 x y) (@lem1523081 x y)). Qed.
Lemma lem1523090 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523091 (x : real) (y : real) : (term64 x y) = term65.
Proof. exact (MK_COMB (@lem1523090) (@lem1523089 x y)). Qed.
Lemma lem1523092 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1523093 (x : real) (y : real) : (term66 x y) = term67.
Proof. exact (MK_COMB (@lem1523091 x y) (@lem1523092)). Qed.
Lemma lem1523094 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1523095 (x : real) (y : real) : (term68 x y) = term65.
Proof. exact (MK_COMB (@lem1523094) (@lem1523079 x y)). Qed.
Lemma lem1523096 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1523097 (x : real) (y : real) : (term69 x y) = term67.
Proof. exact (MK_COMB (@lem1523095 x y) (@lem1523096)). Qed.
Lemma lem1523098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523099 (x : real) (y : real) : (term70 x y) = term71.
Proof. exact (MK_COMB (@lem1523098) (@lem1523097 x y)). Qed.
Lemma lem1523100 (x : real) (y : real) : (term21 x y) = term72.
Proof. exact (MK_COMB (@lem1523099 x y) (@lem1523093 x y)). Qed.
Lemma lem1523101 (x : real) (y : real) : (term8 x y) = term72.
Proof. exact (TRANS (@lem1522993 x y) (@lem1523100 x y)). Qed.
Lemma lem1523102 (x : real) : (term10 x) = term73.
Proof. exact (fun_ext (fun y : real => @lem1523101 x y)). Qed.
Lemma lem1523103 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523104 (x : real) : (term11 x) = term74.
Proof. exact (MK_COMB (@lem1523103) (@lem1523102 x)). Qed.
Lemma lem1523105 : term19 = term75.
Proof. exact (fun_ext (fun x : real => @lem1523104 x)). Qed.
Lemma lem1523106 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523107 : term20 = term76.
Proof. exact (MK_COMB (@lem1523106) (@lem1523105)). Qed.
Lemma lem1523108 : term12 = term76.
Proof. exact (TRANS (@lem1522992) (@lem1523107)). Qed.
Lemma lem1523110 {A : Type'} (t : Prop) : (term77 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1523111 (t : Prop) : (term78 t) = t.
Proof. exact (@lem1523110 real t). Qed.
Lemma lem1523112 : term76 = term74.
Proof. exact (@lem1523111 term74). Qed.
Lemma lem1523114 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1523115 (P : real -> Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1523114 real P Q). Qed.
Lemma lem1523116 : term83 = term84.
Proof. exact (@lem1523115 term85 term85). Qed.
Lemma lem1523117 (y : real) : (term86 y) = term67.
Proof. exact (eq_refl (term86 y)). Qed.
Lemma lem1523118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523119 (y : real) : (term87 y) = term71.
Proof. exact (MK_COMB (@lem1523118) (@lem1523117 y)). Qed.
Lemma lem1523120 (y : real) : (term86 y) = term67.
Proof. exact (eq_refl (term86 y)). Qed.
Lemma lem1523121 (y : real) : (term88 y) = term72.
Proof. exact (MK_COMB (@lem1523119 y) (@lem1523120 y)). Qed.
Lemma lem1523122 : term89 = term73.
Proof. exact (fun_ext (fun y : real => @lem1523121 y)). Qed.
Lemma lem1523123 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523124 : term83 = term74.
Proof. exact (MK_COMB (@lem1523123) (@lem1523122)). Qed.
Lemma lem1523125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1523126 : term90 = term91.
Proof. exact (MK_COMB (@lem1523125) (@lem1523124)). Qed.
Lemma lem1523127 (y : real) : (term86 y) = term67.
Proof. exact (eq_refl (term86 y)). Qed.
Lemma lem1523128 : term92 = term85.
Proof. exact (fun_ext (fun y : real => @lem1523127 y)). Qed.
Lemma lem1523129 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523130 : term93 = term94.
Proof. exact (MK_COMB (@lem1523129) (@lem1523128)). Qed.
Lemma lem1523131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523132 : term95 = term96.
Proof. exact (MK_COMB (@lem1523131) (@lem1523130)). Qed.
Lemma lem1523133 (y : real) : (term86 y) = term67.
Proof. exact (eq_refl (term86 y)). Qed.
Lemma lem1523134 : term92 = term85.
Proof. exact (fun_ext (fun y : real => @lem1523133 y)). Qed.
Lemma lem1523135 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1523136 : term93 = term94.
Proof. exact (MK_COMB (@lem1523135) (@lem1523134)). Qed.
Lemma lem1523137 : term84 = term97.
Proof. exact (MK_COMB (@lem1523132) (@lem1523136)). Qed.
Lemma lem1523138 : (term83 = term84) = (term74 = term97).
Proof. exact (MK_COMB (@lem1523126) (@lem1523137)). Qed.
Lemma lem1523139 : term74 = term97.
Proof. exact (EQ_MP (@lem1523138) (@lem1523116)). Qed.
Lemma lem1523140 : term76 = term97.
Proof. exact (TRANS (@lem1523112) (@lem1523139)). Qed.
Lemma lem1523142 {A : Type'} (t : Prop) : (term77 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1523143 (t : Prop) : (term78 t) = t.
Proof. exact (@lem1523142 real t). Qed.
Lemma lem1523144 : term94 = term67.
Proof. exact (@lem1523143 term67). Qed.
Lemma lem1523145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1523146 : term96 = term71.
Proof. exact (MK_COMB (@lem1523145) (@lem1523144)). Qed.
Lemma lem1523148 {A : Type'} (t : Prop) : (term77 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1523149 (t : Prop) : (term78 t) = t.
Proof. exact (@lem1523148 real t). Qed.
Lemma lem1523150 : term94 = term67.
Proof. exact (@lem1523149 term67). Qed.
Lemma lem1523151 : term97 = term72.
Proof. exact (MK_COMB (@lem1523146) (@lem1523150)). Qed.
Lemma lem1523154 : term76 = term72.
Proof. exact (TRANS (@lem1523140) (@lem1523151)). Qed.
Lemma lem1523163 : term12 = term72.
Proof. exact (TRANS (@lem1523108) (@lem1523154)). Qed.
Lemma lem1523173 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem1523174 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem1523176 (n : nat) (m : nat) : (term98 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523177 : term67 = term99.
Proof. exact (@lem1523176 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1523178 : term99 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1523179 : term67 = False.
Proof. exact (TRANS (@lem1523177) (@lem1523178)). Qed.
Lemma lem1523180 (h1 : term67) : False.
Proof. exact (EQ_MP (@lem1523179) (@lem1523174 h1)). Qed.
Lemma lem1523181 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem1523183 (n : nat) (m : nat) : (term98 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1523184 : term67 = term99.
Proof. exact (@lem1523183 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1523185 : term99 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1523186 : term67 = False.
Proof. exact (TRANS (@lem1523184) (@lem1523185)). Qed.
Lemma lem1523187 (h1 : term67) : False.
Proof. exact (EQ_MP (@lem1523186) (@lem1523181 h1)). Qed.
Lemma lem1523188 (h1 : term72) : False.
Proof. exact (or_elim (@lem1523173 h1) (fun h0 : term67 => @lem1523180 h0) (fun h0 : term67 => @lem1523187 h0)). Qed.
Lemma lem1523190 (h1 : term72) : term72.
Proof. exact (h1). Qed.
Lemma lem1523191 (h1 : term72) : term72 = False.
Proof. exact (prop_ext (fun h2 : term72 => @lem1523188 h1) (fun h2 : False => @lem1523190 h1)). Qed.
Lemma lem1523192 (h1 : term72) : False.
Proof. exact (EQ_MP (@lem1523191 h1) (@lem1523190 h1)). Qed.
Lemma lem1523193 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1523194 (h1 : term12) : term72.
Proof. exact (EQ_MP (@lem1523163) (@lem1523193 h1)). Qed.
Lemma lem1523195 (h1 : term12) : term72 = False.
Proof. exact (prop_ext (fun h2 : term72 => @lem1523192 h2) (fun h2 : False => @lem1523194 h1)). Qed.
Lemma lem1523196 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1523195 h1) (@lem1523194 h1)). Qed.
Lemma lem1523197 : term100.
Proof. exact (fun h0 : term12 => @lem1523196 h0). Qed.
Lemma lem1523198 : term101.
Proof. exact (@lem1386578 term102). Qed.
Lemma lem1523199 : term102.
Proof. exact (@lem1523198 (@lem1523197)). Qed.
