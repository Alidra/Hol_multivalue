Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_MIN_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482709_spec.
Require Import thm1482716_spec.
Require Import thm1483205_spec.
Require Import thm1483429_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1555979 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1555980 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1555979 (term4 x)). Qed.
Lemma lem1555981 (x : real) (y : real) : (term5 x y) = ((real_max x y) = (term6 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1555982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1555984 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1555982) (@lem1555981 x y)). Qed.
Lemma lem1555985 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1555984 x y)). Qed.
Lemma lem1555986 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555987 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1555986) (@lem1555985 x)). Qed.
Lemma lem1555988 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1555980 x) (@lem1555987 x)). Qed.
Lemma lem1555989 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1555990 : term12 = term13.
Proof. exact (@lem1555989 term14). Qed.
Lemma lem1555991 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1555992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1555993 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1555992) (@lem1555991 x)). Qed.
Lemma lem1555994 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1555993 x) (@lem1555988 x)). Qed.
Lemma lem1555995 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1555994 x)). Qed.
Lemma lem1555996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1555997 : term13 = term20.
Proof. exact (MK_COMB (@lem1555996) (@lem1555995)). Qed.
Lemma lem1555999 : term12 = term20.
Proof. exact (TRANS (@lem1555990) (@lem1555997)). Qed.
Lemma lem1556002 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1556003 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1556002 x y)). Qed.
Lemma lem1556004 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556005 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1556004) (@lem1556003 x)). Qed.
Lemma lem1556006 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1556005 x)). Qed.
Lemma lem1556007 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556008 : term20 = term20.
Proof. exact (MK_COMB (@lem1556007) (@lem1556006)). Qed.
Lemma lem1556009 : term12 = term20.
Proof. exact (TRANS (@lem1555999) (@lem1556008)). Qed.
Lemma lem1556010 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483554 (real_max x y) (term6 x y)). Qed.
Lemma lem1556017 (x : real) (y : real) : (term6 x y) = (term22 x y).
Proof. exact (@lem1483512 (term23 x y)). Qed.
Lemma lem1556020 (x : real) (y : real) : (term24 x y) = (term24 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1556021 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1556020 x y) (@lem1556017 x y)). Qed.
Lemma lem1556022 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483519 (real_max x y) (term22 x y)). Qed.
Lemma lem1556023 (x : real) (y : real) : (term28 x y) = (term29 x y).
Proof. exact (@lem1483476 term30 term30 (term23 x y)). Qed.
Lemma lem1556025 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556026 : term33 = term34.
Proof. exact (@lem1556025 term35 term35). Qed.
Lemma lem1556027 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556028 : term37 = term35.
Proof. exact (EQ_MP (@lem1556027) (@lem940073)). Qed.
Lemma lem1556029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556030 : term34 = term38.
Proof. exact (MK_COMB (@lem1556029) (@lem1556028)). Qed.
Lemma lem1556031 : term33 = term38.
Proof. exact (TRANS (@lem1556026) (@lem1556030)). Qed.
Lemma lem1556032 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556033 : term39 = term40.
Proof. exact (MK_COMB (@lem1556032) (@lem1556031)). Qed.
Lemma lem1556034 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1556035 (x : real) (y : real) : (term29 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1556033) (@lem1556034 x y)). Qed.
Lemma lem1556036 (x : real) (y : real) : (term28 x y) = (term41 x y).
Proof. exact (TRANS (@lem1556023 x y) (@lem1556035 x y)). Qed.
Lemma lem1556037 (x : real) (y : real) : (term41 x y) = (term23 x y).
Proof. exact (@lem1483436 (term23 x y)). Qed.
Lemma lem1556038 (x : real) (y : real) : (term28 x y) = (term23 x y).
Proof. exact (TRANS (@lem1556036 x y) (@lem1556037 x y)). Qed.
Lemma lem1556039 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1556042 (x : real) (y : real) : (term27 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1556039 x y) (@lem1556038 x y)). Qed.
Lemma lem1556043 (x : real) (y : real) : (term26 x y) = (term43 x y).
Proof. exact (TRANS (@lem1556022 x y) (@lem1556042 x y)). Qed.
Lemma lem1556044 (x : real) (y : real) : (term25 x y) = (term43 x y).
Proof. exact (TRANS (@lem1556021 x y) (@lem1556043 x y)). Qed.
Lemma lem1556045 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1556046 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1556045) (@lem1556044 x y)). Qed.
Lemma lem1556047 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (@lem1483512 (term43 x y)). Qed.
Lemma lem1556054 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem1483508 (real_max x y) term30 (term23 x y)). Qed.
Lemma lem1556055 (x : real) (y : real) : (term45 x y) = (term47 x y).
Proof. exact (TRANS (@lem1556047 x y) (@lem1556054 x y)). Qed.
Lemma lem1556056 (x : real) (y : real) : (term48 x y) = (term48 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1556057 (x : real) (y : real) : ((term44 x y) = (term45 x y)) = ((term44 x y) = (term47 x y)).
Proof. exact (MK_COMB (@lem1556056 x y) (@lem1556055 x y)). Qed.
Lemma lem1556058 (x : real) (y : real) : (term44 x y) = (term47 x y).
Proof. exact (EQ_MP (@lem1556057 x y) (@lem1556046 x y)). Qed.
Lemma lem1556059 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556060 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1556059) (@lem1556058 x y)). Qed.
Lemma lem1556061 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556062 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1556060 x y) (@lem1556061)). Qed.
Lemma lem1556063 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556064 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1556063) (@lem1556044 x y)). Qed.
Lemma lem1556065 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556066 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1556064 x y) (@lem1556065)). Qed.
Lemma lem1556067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556068 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1556067) (@lem1556066 x y)). Qed.
Lemma lem1556069 (x : real) (y : real) : (term21 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1556068 x y) (@lem1556062 x y)). Qed.
Lemma lem1556070 (x : real) (y : real) : (term8 x y) = (term60 x y).
Proof. exact (TRANS (@lem1556010 x y) (@lem1556069 x y)). Qed.
Lemma lem1556071 (x : real) : (term10 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1556070 x y)). Qed.
Lemma lem1556072 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556073 (x : real) : (term11 x) = (term62 x).
Proof. exact (MK_COMB (@lem1556072) (@lem1556071 x)). Qed.
Lemma lem1556074 : term19 = term63.
Proof. exact (fun_ext (fun x : real => @lem1556073 x)). Qed.
Lemma lem1556075 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556076 : term20 = term64.
Proof. exact (MK_COMB (@lem1556075) (@lem1556074)). Qed.
Lemma lem1556077 : term12 = term64.
Proof. exact (TRANS (@lem1556009) (@lem1556076)). Qed.
Lemma lem1556083 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1556084 (P : real -> Prop) (Q : real -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem1556083 real P Q). Qed.
Lemma lem1556085 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1556084 (term71 x) (term72 x)). Qed.
Lemma lem1556086 (x : real) (y : real) : (term73 x y) = (term57 x y).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem1556087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556088 (x : real) (y : real) : (term74 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1556087) (@lem1556086 x y)). Qed.
Lemma lem1556089 (x : real) (y : real) : (term75 x y) = (term53 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1556090 (x : real) (y : real) : (term76 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1556088 x y) (@lem1556089 x y)). Qed.
Lemma lem1556091 (x : real) : (term77 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1556090 x y)). Qed.
Lemma lem1556092 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556093 (x : real) : (term69 x) = (term62 x).
Proof. exact (MK_COMB (@lem1556092) (@lem1556091 x)). Qed.
Lemma lem1556094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1556095 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1556094) (@lem1556093 x)). Qed.
Lemma lem1556096 (x : real) (y : real) : (term73 x y) = (term57 x y).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem1556097 (x : real) : (term80 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1556096 x y)). Qed.
Lemma lem1556098 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556099 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1556098) (@lem1556097 x)). Qed.
Lemma lem1556100 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556101 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1556100) (@lem1556099 x)). Qed.
Lemma lem1556102 (x : real) (y : real) : (term75 x y) = (term53 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1556103 (x : real) : (term85 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1556102 x y)). Qed.
Lemma lem1556104 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556105 (x : real) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1556104) (@lem1556103 x)). Qed.
Lemma lem1556106 (x : real) : (term70 x) = (term88 x).
Proof. exact (MK_COMB (@lem1556101 x) (@lem1556105 x)). Qed.
Lemma lem1556107 (x : real) : ((term69 x) = (term70 x)) = ((term62 x) = (term88 x)).
Proof. exact (MK_COMB (@lem1556095 x) (@lem1556106 x)). Qed.
Lemma lem1556108 (x : real) : (term62 x) = (term88 x).
Proof. exact (EQ_MP (@lem1556107 x) (@lem1556085 x)). Qed.
Lemma lem1556117 : term63 = term89.
Proof. exact (fun_ext (fun x : real => @lem1556108 x)). Qed.
Lemma lem1556118 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556119 : term64 = term90.
Proof. exact (MK_COMB (@lem1556118) (@lem1556117)). Qed.
Lemma lem1556121 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1556122 (P : real -> Prop) (Q : real -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem1556121 real P Q). Qed.
Lemma lem1556123 : term91 = term92.
Proof. exact (@lem1556122 term93 term94). Qed.
Lemma lem1556124 (x : real) : (term95 x) = (term82 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1556125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556126 (x : real) : (term96 x) = (term84 x).
Proof. exact (MK_COMB (@lem1556125) (@lem1556124 x)). Qed.
Lemma lem1556127 (x : real) : (term97 x) = (term87 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1556128 (x : real) : (term98 x) = (term88 x).
Proof. exact (MK_COMB (@lem1556126 x) (@lem1556127 x)). Qed.
Lemma lem1556129 : term99 = term89.
Proof. exact (fun_ext (fun x : real => @lem1556128 x)). Qed.
Lemma lem1556130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556131 : term91 = term90.
Proof. exact (MK_COMB (@lem1556130) (@lem1556129)). Qed.
Lemma lem1556132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1556133 : term100 = term101.
Proof. exact (MK_COMB (@lem1556132) (@lem1556131)). Qed.
Lemma lem1556134 (x : real) : (term95 x) = (term82 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1556135 : term102 = term93.
Proof. exact (fun_ext (fun x : real => @lem1556134 x)). Qed.
Lemma lem1556136 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556137 : term103 = term104.
Proof. exact (MK_COMB (@lem1556136) (@lem1556135)). Qed.
Lemma lem1556138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556139 : term105 = term106.
Proof. exact (MK_COMB (@lem1556138) (@lem1556137)). Qed.
Lemma lem1556140 (x : real) : (term97 x) = (term87 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1556141 : term107 = term94.
Proof. exact (fun_ext (fun x : real => @lem1556140 x)). Qed.
Lemma lem1556142 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556143 : term108 = term109.
Proof. exact (MK_COMB (@lem1556142) (@lem1556141)). Qed.
Lemma lem1556144 : term92 = term110.
Proof. exact (MK_COMB (@lem1556139) (@lem1556143)). Qed.
Lemma lem1556145 : (term91 = term92) = (term90 = term110).
Proof. exact (MK_COMB (@lem1556133) (@lem1556144)). Qed.
Lemma lem1556146 : term90 = term110.
Proof. exact (EQ_MP (@lem1556145) (@lem1556123)). Qed.
Lemma lem1556163 : term64 = term110.
Proof. exact (TRANS (@lem1556119) (@lem1556146)). Qed.
Lemma lem1556165 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term65 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1556166 (P : real -> Prop) (Q : real -> Prop) : (term68 P Q) = (term67 P Q).
Proof. exact (@lem1556165 real P Q). Qed.
Lemma lem1556167 : term92 = term91.
Proof. exact (@lem1556166 term93 term94). Qed.
Lemma lem1556168 (x : real) : (term95 x) = (term82 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1556169 : term102 = term93.
Proof. exact (fun_ext (fun x : real => @lem1556168 x)). Qed.
Lemma lem1556170 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556171 : term103 = term104.
Proof. exact (MK_COMB (@lem1556170) (@lem1556169)). Qed.
Lemma lem1556172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556173 : term105 = term106.
Proof. exact (MK_COMB (@lem1556172) (@lem1556171)). Qed.
Lemma lem1556174 (x : real) : (term97 x) = (term87 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1556175 : term107 = term94.
Proof. exact (fun_ext (fun x : real => @lem1556174 x)). Qed.
Lemma lem1556176 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556177 : term108 = term109.
Proof. exact (MK_COMB (@lem1556176) (@lem1556175)). Qed.
Lemma lem1556178 : term92 = term110.
Proof. exact (MK_COMB (@lem1556173) (@lem1556177)). Qed.
Lemma lem1556179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1556180 : term111 = term112.
Proof. exact (MK_COMB (@lem1556179) (@lem1556178)). Qed.
Lemma lem1556181 (x : real) : (term95 x) = (term82 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1556182 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556183 (x : real) : (term96 x) = (term84 x).
Proof. exact (MK_COMB (@lem1556182) (@lem1556181 x)). Qed.
Lemma lem1556184 (x : real) : (term97 x) = (term87 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1556185 (x : real) : (term98 x) = (term88 x).
Proof. exact (MK_COMB (@lem1556183 x) (@lem1556184 x)). Qed.
Lemma lem1556186 : term99 = term89.
Proof. exact (fun_ext (fun x : real => @lem1556185 x)). Qed.
Lemma lem1556187 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556188 : term91 = term90.
Proof. exact (MK_COMB (@lem1556187) (@lem1556186)). Qed.
Lemma lem1556189 : (term92 = term91) = (term110 = term90).
Proof. exact (MK_COMB (@lem1556180) (@lem1556188)). Qed.
Lemma lem1556190 : term110 = term90.
Proof. exact (EQ_MP (@lem1556189) (@lem1556167)). Qed.
Lemma lem1556192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term66 A P Q) = (term65 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1556193 (P : real -> Prop) (Q : real -> Prop) : (term68 P Q) = (term67 P Q).
Proof. exact (@lem1556192 real P Q). Qed.
Lemma lem1556194 (x : real) : (term70 x) = (term69 x).
Proof. exact (@lem1556193 (term71 x) (term72 x)). Qed.
Lemma lem1556195 (x : real) (y : real) : (term73 x y) = (term57 x y).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem1556196 (x : real) : (term80 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1556195 x y)). Qed.
Lemma lem1556197 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556198 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1556197) (@lem1556196 x)). Qed.
Lemma lem1556199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556200 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1556199) (@lem1556198 x)). Qed.
Lemma lem1556201 (x : real) (y : real) : (term75 x y) = (term53 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1556202 (x : real) : (term85 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1556201 x y)). Qed.
Lemma lem1556203 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556204 (x : real) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1556203) (@lem1556202 x)). Qed.
Lemma lem1556205 (x : real) : (term70 x) = (term88 x).
Proof. exact (MK_COMB (@lem1556200 x) (@lem1556204 x)). Qed.
Lemma lem1556206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1556207 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1556206) (@lem1556205 x)). Qed.
Lemma lem1556208 (x : real) (y : real) : (term73 x y) = (term57 x y).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem1556209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556210 (x : real) (y : real) : (term74 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1556209) (@lem1556208 x y)). Qed.
Lemma lem1556211 (x : real) (y : real) : (term75 x y) = (term53 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1556212 (x : real) (y : real) : (term76 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1556210 x y) (@lem1556211 x y)). Qed.
Lemma lem1556213 (x : real) : (term77 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1556212 x y)). Qed.
Lemma lem1556214 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556215 (x : real) : (term69 x) = (term62 x).
Proof. exact (MK_COMB (@lem1556214) (@lem1556213 x)). Qed.
Lemma lem1556216 (x : real) : ((term70 x) = (term69 x)) = ((term88 x) = (term62 x)).
Proof. exact (MK_COMB (@lem1556207 x) (@lem1556215 x)). Qed.
Lemma lem1556217 (x : real) : (term88 x) = (term62 x).
Proof. exact (EQ_MP (@lem1556216 x) (@lem1556194 x)). Qed.
Lemma lem1556218 : term89 = term63.
Proof. exact (fun_ext (fun x : real => @lem1556217 x)). Qed.
Lemma lem1556219 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556220 : term90 = term64.
Proof. exact (MK_COMB (@lem1556219) (@lem1556218)). Qed.
Lemma lem1556221 : term110 = term64.
Proof. exact (TRANS (@lem1556190) (@lem1556220)). Qed.
Lemma lem1556222 : term64 = term64.
Proof. exact (TRANS (@lem1556163) (@lem1556221)). Qed.
Lemma lem1556225 : term12 = term64.
Proof. exact (TRANS (@lem1556077) (@lem1556222)). Qed.
Lemma lem1556230 (x : real) (y : real) : (term60 x y) = (term60 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1556231 (x : real) : (term61 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1556230 x y)). Qed.
Lemma lem1556232 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556233 (x : real) : (term62 x) = (term62 x).
Proof. exact (MK_COMB (@lem1556232) (@lem1556231 x)). Qed.
Lemma lem1556234 : term63 = term63.
Proof. exact (fun_ext (fun x : real => @lem1556233 x)). Qed.
Lemma lem1556235 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1556236 : term64 = term64.
Proof. exact (MK_COMB (@lem1556235) (@lem1556234)). Qed.
Lemma lem1556237 : term12 = term64.
Proof. exact (TRANS (@lem1556225) (@lem1556236)). Qed.
Lemma lem1556239 (x : real) (a : real) (y : real) (r : real) : (term115 a x y r) = (term116 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1556240 (x : real) (y : real) : (term57 x y) = (term117 x y).
Proof. exact (@lem1556239 (real_neg x) (real_max x y) (real_neg y) term51). Qed.
Lemma lem1556247 (y : real) : (real_neg y) = (term118 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1556250 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1556251 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1556250 x y) (@lem1556247 y)). Qed.
Lemma lem1556252 (x : real) (y : real) : (term120 x y) = (term121 x y).
Proof. exact (@lem1483488 (term118 y) (real_max x y)). Qed.
Lemma lem1556253 (x : real) (y : real) : (term119 x y) = (term121 x y).
Proof. exact (TRANS (@lem1556251 x y) (@lem1556252 x y)). Qed.
Lemma lem1556254 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556255 (x : real) (y : real) : (term122 x y) = (term123 x y).
Proof. exact (MK_COMB (@lem1556254) (@lem1556253 x y)). Qed.
Lemma lem1556256 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556257 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1556255 x y) (@lem1556256)). Qed.
Lemma lem1556264 (x : real) : (real_neg x) = (term118 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1556267 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1556268 (y : real) (x : real) : (term126 y x) = (term127 y x).
Proof. exact (MK_COMB (@lem1556267 x y) (@lem1556264 x)). Qed.
Lemma lem1556269 (x : real) (y : real) : (term127 y x) = (term128 x y).
Proof. exact (@lem1483488 (term118 x) (real_max x y)). Qed.
Lemma lem1556270 (x : real) (y : real) : (term126 y x) = (term128 x y).
Proof. exact (TRANS (@lem1556268 y x) (@lem1556269 x y)). Qed.
Lemma lem1556271 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556272 (x : real) (y : real) : (term129 y x) = (term130 x y).
Proof. exact (MK_COMB (@lem1556271) (@lem1556270 x y)). Qed.
Lemma lem1556273 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556274 (x : real) (y : real) : (term131 y x) = (term132 x y).
Proof. exact (MK_COMB (@lem1556272 x y) (@lem1556273)). Qed.
Lemma lem1556275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556276 (x : real) (y : real) : (term133 y x) = (term134 x y).
Proof. exact (MK_COMB (@lem1556275) (@lem1556274 x y)). Qed.
Lemma lem1556277 (x : real) (y : real) : (term117 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1556276 x y) (@lem1556257 x y)). Qed.
Lemma lem1556278 (x : real) (y : real) : (term57 x y) = (term135 x y).
Proof. exact (TRANS (@lem1556240 x y) (@lem1556277 x y)). Qed.
Lemma lem1556279 (x : real) (y : real) : (term136 x y) = (term135 x y).
Proof. exact (eq_refl (term136 x y)). Qed.
Lemma lem1556280 (x : real) (y : real) : (term135 x y) = (term136 x y).
Proof. exact (SYM (@lem1556279 x y)). Qed.
Lemma lem1556281 (y : real) (x : real) : (term136 x y) = (term137 y x).
Proof. exact (@lem1483205 y (term138 x y) x). Qed.
Lemma lem1556282 (y : real) (x : real) : (term135 x y) = (term137 y x).
Proof. exact (TRANS (@lem1556280 x y) (@lem1556281 y x)). Qed.
Lemma lem1556283 (y : real) (x : real) : (term139 y x) = (term140 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1556284 (x : real) (y : real) : (term141 x y) = (term141 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1556285 (y : real) (x : real) : (term142 y x) = (term143 y x).
Proof. exact (MK_COMB (@lem1556284 x y) (@lem1556283 y x)). Qed.
Lemma lem1556286 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (eq_refl (term144 x y)). Qed.
Lemma lem1556287 (y : real) (x : real) : (term146 y x) = (term146 y x).
Proof. exact (eq_refl (term146 y x)). Qed.
Lemma lem1556288 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (MK_COMB (@lem1556287 y x) (@lem1556286 x y)). Qed.
Lemma lem1556289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556290 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1556289) (@lem1556288 x y)). Qed.
Lemma lem1556291 (y : real) (x : real) : (term137 y x) = (term151 y x).
Proof. exact (MK_COMB (@lem1556290 x y) (@lem1556285 y x)). Qed.
Lemma lem1556292 (x : real) (y : real) : (term152 x y) = (term152 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1556293 (y : real) (x : real) : ((term135 x y) = (term137 y x)) = ((term135 x y) = (term151 y x)).
Proof. exact (MK_COMB (@lem1556292 x y) (@lem1556291 y x)). Qed.
Lemma lem1556294 (y : real) (x : real) : (term135 x y) = (term151 y x).
Proof. exact (EQ_MP (@lem1556293 y x) (@lem1556282 y x)). Qed.
Lemma lem1556295 (y : real) (x : real) : (real_ge y x) = (term153 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1556301 (y : real) (x : real) : (real_sub y x) = (term154 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1556306 (x : real) (y : real) : (term154 y x) = (term155 x y).
Proof. exact (@lem1483488 (term118 x) y). Qed.
Lemma lem1556308 (x : real) (y : real) : (real_sub y x) = (term155 x y).
Proof. exact (TRANS (@lem1556301 y x) (@lem1556306 x y)). Qed.
Lemma lem1556309 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1556310 (x : real) (y : real) : (term156 y x) = (term157 x y).
Proof. exact (MK_COMB (@lem1556309) (@lem1556308 x y)). Qed.
Lemma lem1556311 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556312 (x : real) (y : real) : (term153 y x) = (term158 x y).
Proof. exact (MK_COMB (@lem1556310 x y) (@lem1556311)). Qed.
Lemma lem1556313 (x : real) (y : real) : (real_ge y x) = (term158 x y).
Proof. exact (TRANS (@lem1556295 y x) (@lem1556312 x y)). Qed.
Lemma lem1556314 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (@lem1483525 (term155 x y) term51). Qed.
Lemma lem1556332 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (@lem1483519 (term155 x y) term51). Qed.
Lemma lem1556334 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556335 : term164 = term51.
Proof. exact (@lem1556334 term35). Qed.
Lemma lem1556336 (x : real) (y : real) : (term165 x y) = (term165 x y).
Proof. exact (eq_refl (term165 x y)). Qed.
Lemma lem1556337 (x : real) (y : real) : (term162 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1556336 x y) (@lem1556335)). Qed.
Lemma lem1556338 (x : real) (y : real) : (term166 x y) = (term155 x y).
Proof. exact (@lem1483450 (term155 x y)). Qed.
Lemma lem1556339 (x : real) (y : real) : (term162 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556337 x y) (@lem1556338 x y)). Qed.
Lemma lem1556341 (x : real) (y : real) : (term161 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556332 x y) (@lem1556339 x y)). Qed.
Lemma lem1556342 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556343 (x : real) (y : real) : (term167 x y) = (term168 x y).
Proof. exact (MK_COMB (@lem1556342) (@lem1556341 x y)). Qed.
Lemma lem1556344 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556345 (x : real) (y : real) : (term160 x y) = (term159 x y).
Proof. exact (MK_COMB (@lem1556343 x y) (@lem1556344)). Qed.
Lemma lem1556346 (x : real) (y : real) : (term159 x y) = (term159 x y).
Proof. exact (TRANS (@lem1556314 x y) (@lem1556345 x y)). Qed.
Lemma lem1556347 (y : real) : (term169 y) = (term170 y).
Proof. exact (@lem1483525 (term171 y) term51). Qed.
Lemma lem1556348 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556360 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1556362 (m : nat) : (term173 m) = term51.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1556363 : term174 = term51.
Proof. exact (@lem1556362 term35). Qed.
Lemma lem1556364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556365 : term175 = term176.
Proof. exact (MK_COMB (@lem1556364) (@lem1556363)). Qed.
Lemma lem1556366 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1556367 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1556365) (@lem1556366 y)). Qed.
Lemma lem1556368 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1556360 y) (@lem1556367 y)). Qed.
Lemma lem1556369 (y : real) : (term177 y) = term51.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1556371 (y : real) : (term171 y) = term51.
Proof. exact (TRANS (@lem1556368 y) (@lem1556369 y)). Qed.
Lemma lem1556372 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556373 (y : real) : (term178 y) = term179.
Proof. exact (MK_COMB (@lem1556372) (@lem1556371 y)). Qed.
Lemma lem1556374 (y : real) : (term180 y) = term181.
Proof. exact (MK_COMB (@lem1556373 y) (@lem1556348)). Qed.
Lemma lem1556375 : term181 = term182.
Proof. exact (@lem1483519 term51 term51). Qed.
Lemma lem1556377 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556378 : term164 = term51.
Proof. exact (@lem1556377 term35). Qed.
Lemma lem1556379 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1556380 : term182 = term184.
Proof. exact (MK_COMB (@lem1556379) (@lem1556378)). Qed.
Lemma lem1556381 : term184 = term51.
Proof. exact (@lem1483448 term51). Qed.
Lemma lem1556382 : term182 = term51.
Proof. exact (TRANS (@lem1556380) (@lem1556381)). Qed.
Lemma lem1556383 : term181 = term51.
Proof. exact (TRANS (@lem1556375) (@lem1556382)). Qed.
Lemma lem1556384 (y : real) : (term180 y) = term51.
Proof. exact (TRANS (@lem1556374 y) (@lem1556383)). Qed.
Lemma lem1556385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556386 (y : real) : (term185 y) = term186.
Proof. exact (MK_COMB (@lem1556385) (@lem1556384 y)). Qed.
Lemma lem1556387 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556388 (y : real) : (term170 y) = term187.
Proof. exact (MK_COMB (@lem1556386 y) (@lem1556387)). Qed.
Lemma lem1556389 (y : real) : (term169 y) = term187.
Proof. exact (TRANS (@lem1556347 y) (@lem1556388 y)). Qed.
Lemma lem1556390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556391 (x : real) (y : real) : (term188 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1556390) (@lem1556346 x y)). Qed.
Lemma lem1556392 (x : real) (y : real) : (term145 x y) = (term189 x y).
Proof. exact (MK_COMB (@lem1556391 x y) (@lem1556389 y)). Qed.
Lemma lem1556393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556394 (x : real) (y : real) : (term146 y x) = (term190 x y).
Proof. exact (MK_COMB (@lem1556393) (@lem1556313 x y)). Qed.
Lemma lem1556395 (x : real) (y : real) : (term148 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem1556394 x y) (@lem1556392 x y)). Qed.
Lemma lem1556396 (x : real) (y : real) : (real_gt x y) = (term192 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1556409 (x : real) (y : real) : (real_sub x y) = (term154 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1556410 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556411 (x : real) (y : real) : (term193 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem1556410) (@lem1556409 x y)). Qed.
Lemma lem1556412 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556413 (x : real) (y : real) : (term192 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1556411 x y) (@lem1556412)). Qed.
Lemma lem1556414 (x : real) (y : real) : (real_gt x y) = (term195 x y).
Proof. exact (TRANS (@lem1556396 x y) (@lem1556413 x y)). Qed.
Lemma lem1556415 (x : real) : (term169 x) = (term170 x).
Proof. exact (@lem1483525 (term171 x) term51). Qed.
Lemma lem1556416 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556428 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term30 x). Qed.
Lemma lem1556430 (m : nat) : (term173 m) = term51.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1556431 : term174 = term51.
Proof. exact (@lem1556430 term35). Qed.
Lemma lem1556432 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556433 : term175 = term176.
Proof. exact (MK_COMB (@lem1556432) (@lem1556431)). Qed.
Lemma lem1556434 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1556435 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1556433) (@lem1556434 x)). Qed.
Lemma lem1556436 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1556428 x) (@lem1556435 x)). Qed.
Lemma lem1556437 (x : real) : (term177 x) = term51.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1556439 (x : real) : (term171 x) = term51.
Proof. exact (TRANS (@lem1556436 x) (@lem1556437 x)). Qed.
Lemma lem1556440 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556441 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1556440) (@lem1556439 x)). Qed.
Lemma lem1556442 (x : real) : (term180 x) = term181.
Proof. exact (MK_COMB (@lem1556441 x) (@lem1556416)). Qed.
Lemma lem1556443 : term181 = term182.
Proof. exact (@lem1483519 term51 term51). Qed.
Lemma lem1556445 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556446 : term164 = term51.
Proof. exact (@lem1556445 term35). Qed.
Lemma lem1556447 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1556448 : term182 = term184.
Proof. exact (MK_COMB (@lem1556447) (@lem1556446)). Qed.
Lemma lem1556449 : term184 = term51.
Proof. exact (@lem1483448 term51). Qed.
Lemma lem1556450 : term182 = term51.
Proof. exact (TRANS (@lem1556448) (@lem1556449)). Qed.
Lemma lem1556451 : term181 = term51.
Proof. exact (TRANS (@lem1556443) (@lem1556450)). Qed.
Lemma lem1556452 (x : real) : (term180 x) = term51.
Proof. exact (TRANS (@lem1556442 x) (@lem1556451)). Qed.
Lemma lem1556453 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556454 (x : real) : (term185 x) = term186.
Proof. exact (MK_COMB (@lem1556453) (@lem1556452 x)). Qed.
Lemma lem1556455 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556456 (x : real) : (term170 x) = term187.
Proof. exact (MK_COMB (@lem1556454 x) (@lem1556455)). Qed.
Lemma lem1556457 (x : real) : (term169 x) = term187.
Proof. exact (TRANS (@lem1556415 x) (@lem1556456 x)). Qed.
Lemma lem1556458 (y : real) (x : real) : (term159 y x) = (term160 y x).
Proof. exact (@lem1483525 (term155 y x) term51). Qed.
Lemma lem1556459 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556472 (x : real) (y : real) : (term155 y x) = (term154 x y).
Proof. exact (@lem1483488 x (term118 y)). Qed.
Lemma lem1556473 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556474 (x : real) (y : real) : (term196 y x) = (term197 x y).
Proof. exact (MK_COMB (@lem1556473) (@lem1556472 x y)). Qed.
Lemma lem1556475 (x : real) (y : real) : (term161 y x) = (term198 x y).
Proof. exact (MK_COMB (@lem1556474 x y) (@lem1556459)). Qed.
Lemma lem1556476 (x : real) (y : real) : (term198 x y) = (term199 x y).
Proof. exact (@lem1483519 (term154 x y) term51). Qed.
Lemma lem1556478 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556479 : term164 = term51.
Proof. exact (@lem1556478 term35). Qed.
Lemma lem1556480 (x : real) (y : real) : (term200 x y) = (term200 x y).
Proof. exact (eq_refl (term200 x y)). Qed.
Lemma lem1556481 (x : real) (y : real) : (term199 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1556480 x y) (@lem1556479)). Qed.
Lemma lem1556482 (x : real) (y : real) : (term201 x y) = (term154 x y).
Proof. exact (@lem1483450 (term154 x y)). Qed.
Lemma lem1556483 (x : real) (y : real) : (term199 x y) = (term154 x y).
Proof. exact (TRANS (@lem1556481 x y) (@lem1556482 x y)). Qed.
Lemma lem1556484 (x : real) (y : real) : (term198 x y) = (term154 x y).
Proof. exact (TRANS (@lem1556476 x y) (@lem1556483 x y)). Qed.
Lemma lem1556485 (x : real) (y : real) : (term161 y x) = (term154 x y).
Proof. exact (TRANS (@lem1556475 x y) (@lem1556484 x y)). Qed.
Lemma lem1556486 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556487 (x : real) (y : real) : (term167 y x) = (term194 x y).
Proof. exact (MK_COMB (@lem1556486) (@lem1556485 x y)). Qed.
Lemma lem1556488 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556489 (x : real) (y : real) : (term160 y x) = (term195 x y).
Proof. exact (MK_COMB (@lem1556487 x y) (@lem1556488)). Qed.
Lemma lem1556490 (x : real) (y : real) : (term159 y x) = (term195 x y).
Proof. exact (TRANS (@lem1556458 y x) (@lem1556489 x y)). Qed.
Lemma lem1556491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556492 (x : real) : (term202 x) = term203.
Proof. exact (MK_COMB (@lem1556491) (@lem1556457 x)). Qed.
Lemma lem1556493 (x : real) (y : real) : (term140 y x) = (term204 x y).
Proof. exact (MK_COMB (@lem1556492 x) (@lem1556490 x y)). Qed.
Lemma lem1556494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556495 (x : real) (y : real) : (term141 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1556494) (@lem1556414 x y)). Qed.
Lemma lem1556496 (x : real) (y : real) : (term143 y x) = (term206 x y).
Proof. exact (MK_COMB (@lem1556495 x y) (@lem1556493 x y)). Qed.
Lemma lem1556497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556498 (x : real) (y : real) : (term150 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1556497) (@lem1556395 x y)). Qed.
Lemma lem1556499 (x : real) (y : real) : (term151 y x) = (term208 x y).
Proof. exact (MK_COMB (@lem1556498 x y) (@lem1556496 x y)). Qed.
Lemma lem1556510 (x : real) (y : real) : (term135 x y) = (term208 x y).
Proof. exact (TRANS (@lem1556294 y x) (@lem1556499 x y)). Qed.
Lemma lem1556511 (x : real) (y : real) : (term57 x y) = (term208 x y).
Proof. exact (TRANS (@lem1556278 x y) (@lem1556510 x y)). Qed.
Lemma lem1556513 (x : real) (a : real) (y : real) (r : real) : (term209 x y a r) = (term210 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1556514 (x : real) (y : real) : (term53 x y) = (term211 x y).
Proof. exact (@lem1556513 x (term22 x y) y term51). Qed.
Lemma lem1556533 (x : real) (y : real) : (term212 x y) = (term213 x y).
Proof. exact (@lem1483488 (term118 y) (term22 x y)). Qed.
Lemma lem1556534 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556535 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (MK_COMB (@lem1556534) (@lem1556533 x y)). Qed.
Lemma lem1556536 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556537 (x : real) (y : real) : (term216 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1556535 x y) (@lem1556536)). Qed.
Lemma lem1556556 (x : real) (y : real) : (term218 y x) = (term219 x y).
Proof. exact (@lem1483488 (term118 x) (term22 x y)). Qed.
Lemma lem1556557 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556558 (x : real) (y : real) : (term220 y x) = (term221 x y).
Proof. exact (MK_COMB (@lem1556557) (@lem1556556 x y)). Qed.
Lemma lem1556559 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556560 (x : real) (y : real) : (term222 y x) = (term223 x y).
Proof. exact (MK_COMB (@lem1556558 x y) (@lem1556559)). Qed.
Lemma lem1556561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556562 (x : real) (y : real) : (term224 y x) = (term225 x y).
Proof. exact (MK_COMB (@lem1556561) (@lem1556560 x y)). Qed.
Lemma lem1556563 (x : real) (y : real) : (term211 x y) = (term226 x y).
Proof. exact (MK_COMB (@lem1556562 x y) (@lem1556537 x y)). Qed.
Lemma lem1556564 (x : real) (y : real) : (term53 x y) = (term226 x y).
Proof. exact (TRANS (@lem1556514 x y) (@lem1556563 x y)). Qed.
Lemma lem1556565 (x : real) (y : real) : (term227 x y) = (term226 x y).
Proof. exact (eq_refl (term227 x y)). Qed.
Lemma lem1556566 (x : real) (y : real) : (term226 x y) = (term227 x y).
Proof. exact (SYM (@lem1556565 x y)). Qed.
Lemma lem1556567 (x : real) (y : real) : (term227 x y) = (term228 x y).
Proof. exact (@lem1483429 (real_neg x) (term229 x y) (real_neg y)). Qed.
Lemma lem1556568 (x : real) (y : real) : (term226 x y) = (term228 x y).
Proof. exact (TRANS (@lem1556566 x y) (@lem1556567 x y)). Qed.
Lemma lem1556569 (x : real) (y : real) : (term230 x y) = (term231 x y).
Proof. exact (eq_refl (term230 x y)). Qed.
Lemma lem1556570 (x : real) (y : real) : (term232 x y) = (term232 x y).
Proof. exact (eq_refl (term232 x y)). Qed.
Lemma lem1556571 (x : real) (y : real) : (term233 x y) = (term234 x y).
Proof. exact (MK_COMB (@lem1556570 x y) (@lem1556569 x y)). Qed.
Lemma lem1556572 (y : real) (x : real) : (term235 y x) = (term236 y x).
Proof. exact (eq_refl (term235 y x)). Qed.
Lemma lem1556573 (y : real) (x : real) : (term237 y x) = (term237 y x).
Proof. exact (eq_refl (term237 y x)). Qed.
Lemma lem1556574 (y : real) (x : real) : (term238 y x) = (term239 y x).
Proof. exact (MK_COMB (@lem1556573 y x) (@lem1556572 y x)). Qed.
Lemma lem1556575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556576 (y : real) (x : real) : (term240 y x) = (term241 y x).
Proof. exact (MK_COMB (@lem1556575) (@lem1556574 y x)). Qed.
Lemma lem1556577 (x : real) (y : real) : (term228 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1556576 y x) (@lem1556571 x y)). Qed.
Lemma lem1556578 (x : real) (y : real) : (term243 x y) = (term243 x y).
Proof. exact (eq_refl (term243 x y)). Qed.
Lemma lem1556579 (x : real) (y : real) : ((term226 x y) = (term228 x y)) = ((term226 x y) = (term242 x y)).
Proof. exact (MK_COMB (@lem1556578 x y) (@lem1556577 x y)). Qed.
Lemma lem1556580 (x : real) (y : real) : (term226 x y) = (term242 x y).
Proof. exact (EQ_MP (@lem1556579 x y) (@lem1556568 x y)). Qed.
Lemma lem1556581 (y : real) (x : real) : (term244 y x) = (term245 y x).
Proof. exact (@lem1483527 (real_neg y) (real_neg x)). Qed.
Lemma lem1556588 (x : real) : (real_neg x) = (term118 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1556595 (y : real) : (real_neg y) = (term118 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1556596 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556597 (y : real) : (term246 y) = (term247 y).
Proof. exact (MK_COMB (@lem1556596) (@lem1556595 y)). Qed.
Lemma lem1556598 (y : real) (x : real) : (term248 y x) = (term249 y x).
Proof. exact (MK_COMB (@lem1556597 y) (@lem1556588 x)). Qed.
Lemma lem1556599 (y : real) (x : real) : (term249 y x) = (term250 y x).
Proof. exact (@lem1483519 (term118 y) (term118 x)). Qed.
Lemma lem1556600 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1556602 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556603 : term33 = term34.
Proof. exact (@lem1556602 term35 term35). Qed.
Lemma lem1556604 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556605 : term37 = term35.
Proof. exact (EQ_MP (@lem1556604) (@lem940073)). Qed.
Lemma lem1556606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556607 : term34 = term38.
Proof. exact (MK_COMB (@lem1556606) (@lem1556605)). Qed.
Lemma lem1556608 : term33 = term38.
Proof. exact (TRANS (@lem1556603) (@lem1556607)). Qed.
Lemma lem1556609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556610 : term39 = term40.
Proof. exact (MK_COMB (@lem1556609) (@lem1556608)). Qed.
Lemma lem1556611 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1556612 (x : real) : (term252 x) = (term253 x).
Proof. exact (MK_COMB (@lem1556610) (@lem1556611 x)). Qed.
Lemma lem1556613 (x : real) : (term251 x) = (term253 x).
Proof. exact (TRANS (@lem1556600 x) (@lem1556612 x)). Qed.
Lemma lem1556614 (x : real) : (term253 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1556615 (x : real) : (term251 x) = x.
Proof. exact (TRANS (@lem1556613 x) (@lem1556614 x)). Qed.
Lemma lem1556616 (y : real) : (term254 y) = (term254 y).
Proof. exact (eq_refl (term254 y)). Qed.
Lemma lem1556617 (y : real) (x : real) : (term250 y x) = (term155 y x).
Proof. exact (MK_COMB (@lem1556616 y) (@lem1556615 x)). Qed.
Lemma lem1556618 (x : real) (y : real) : (term155 y x) = (term154 x y).
Proof. exact (@lem1483488 x (term118 y)). Qed.
Lemma lem1556619 (x : real) (y : real) : (term250 y x) = (term154 x y).
Proof. exact (TRANS (@lem1556617 y x) (@lem1556618 x y)). Qed.
Lemma lem1556620 (x : real) (y : real) : (term249 y x) = (term154 x y).
Proof. exact (TRANS (@lem1556599 y x) (@lem1556619 x y)). Qed.
Lemma lem1556621 (x : real) (y : real) : (term248 y x) = (term154 x y).
Proof. exact (TRANS (@lem1556598 y x) (@lem1556620 x y)). Qed.
Lemma lem1556622 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1556623 (x : real) (y : real) : (term255 y x) = (term256 x y).
Proof. exact (MK_COMB (@lem1556622) (@lem1556621 x y)). Qed.
Lemma lem1556624 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556625 (x : real) (y : real) : (term245 y x) = (term257 x y).
Proof. exact (MK_COMB (@lem1556623 x y) (@lem1556624)). Qed.
Lemma lem1556626 (x : real) (y : real) : (term244 y x) = (term257 x y).
Proof. exact (TRANS (@lem1556581 y x) (@lem1556625 x y)). Qed.
Lemma lem1556627 (x : real) : (term258 x) = (term259 x).
Proof. exact (@lem1483525 (term260 x) term51). Qed.
Lemma lem1556628 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556635 (x : real) : (real_neg x) = (term118 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1556638 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem1556639 (x : real) : (term262 x) = (term251 x).
Proof. exact (MK_COMB (@lem1556638) (@lem1556635 x)). Qed.
Lemma lem1556640 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1556642 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556643 : term33 = term34.
Proof. exact (@lem1556642 term35 term35). Qed.
Lemma lem1556644 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556645 : term37 = term35.
Proof. exact (EQ_MP (@lem1556644) (@lem940073)). Qed.
Lemma lem1556646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556647 : term34 = term38.
Proof. exact (MK_COMB (@lem1556646) (@lem1556645)). Qed.
Lemma lem1556648 : term33 = term38.
Proof. exact (TRANS (@lem1556643) (@lem1556647)). Qed.
Lemma lem1556649 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556650 : term39 = term40.
Proof. exact (MK_COMB (@lem1556649) (@lem1556648)). Qed.
Lemma lem1556651 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1556652 (x : real) : (term252 x) = (term253 x).
Proof. exact (MK_COMB (@lem1556650) (@lem1556651 x)). Qed.
Lemma lem1556653 (x : real) : (term251 x) = (term253 x).
Proof. exact (TRANS (@lem1556640 x) (@lem1556652 x)). Qed.
Lemma lem1556654 (x : real) : (term253 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1556655 (x : real) : (term251 x) = x.
Proof. exact (TRANS (@lem1556653 x) (@lem1556654 x)). Qed.
Lemma lem1556656 (x : real) : (term262 x) = x.
Proof. exact (TRANS (@lem1556639 x) (@lem1556655 x)). Qed.
Lemma lem1556665 (x : real) : (term254 x) = (term254 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem1556666 (x : real) : (term260 x) = (term171 x).
Proof. exact (MK_COMB (@lem1556665 x) (@lem1556656 x)). Qed.
Lemma lem1556667 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1483440 term30 x). Qed.
Lemma lem1556669 (m : nat) : (term173 m) = term51.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1556670 : term174 = term51.
Proof. exact (@lem1556669 term35). Qed.
Lemma lem1556671 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556672 : term175 = term176.
Proof. exact (MK_COMB (@lem1556671) (@lem1556670)). Qed.
Lemma lem1556673 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1556674 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1556672) (@lem1556673 x)). Qed.
Lemma lem1556675 (x : real) : (term171 x) = (term177 x).
Proof. exact (TRANS (@lem1556667 x) (@lem1556674 x)). Qed.
Lemma lem1556676 (x : real) : (term177 x) = term51.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1556677 (x : real) : (term171 x) = term51.
Proof. exact (TRANS (@lem1556675 x) (@lem1556676 x)). Qed.
Lemma lem1556678 (x : real) : (term260 x) = term51.
Proof. exact (TRANS (@lem1556666 x) (@lem1556677 x)). Qed.
Lemma lem1556679 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556680 (x : real) : (term263 x) = term179.
Proof. exact (MK_COMB (@lem1556679) (@lem1556678 x)). Qed.
Lemma lem1556681 (x : real) : (term264 x) = term181.
Proof. exact (MK_COMB (@lem1556680 x) (@lem1556628)). Qed.
Lemma lem1556682 : term181 = term182.
Proof. exact (@lem1483519 term51 term51). Qed.
Lemma lem1556684 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556685 : term164 = term51.
Proof. exact (@lem1556684 term35). Qed.
Lemma lem1556686 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1556687 : term182 = term184.
Proof. exact (MK_COMB (@lem1556686) (@lem1556685)). Qed.
Lemma lem1556688 : term184 = term51.
Proof. exact (@lem1483448 term51). Qed.
Lemma lem1556689 : term182 = term51.
Proof. exact (TRANS (@lem1556687) (@lem1556688)). Qed.
Lemma lem1556690 : term181 = term51.
Proof. exact (TRANS (@lem1556682) (@lem1556689)). Qed.
Lemma lem1556691 (x : real) : (term264 x) = term51.
Proof. exact (TRANS (@lem1556681 x) (@lem1556690)). Qed.
Lemma lem1556692 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556693 (x : real) : (term265 x) = term186.
Proof. exact (MK_COMB (@lem1556692) (@lem1556691 x)). Qed.
Lemma lem1556694 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556695 (x : real) : (term259 x) = term187.
Proof. exact (MK_COMB (@lem1556693 x) (@lem1556694)). Qed.
Lemma lem1556696 (x : real) : (term258 x) = term187.
Proof. exact (TRANS (@lem1556627 x) (@lem1556695 x)). Qed.
Lemma lem1556697 (y : real) (x : real) : (term266 y x) = (term267 y x).
Proof. exact (@lem1483525 (term268 y x) term51). Qed.
Lemma lem1556698 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556705 (x : real) : (real_neg x) = (term118 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1556708 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem1556709 (x : real) : (term262 x) = (term251 x).
Proof. exact (MK_COMB (@lem1556708) (@lem1556705 x)). Qed.
Lemma lem1556710 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483476 term30 term30 x). Qed.
Lemma lem1556712 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556713 : term33 = term34.
Proof. exact (@lem1556712 term35 term35). Qed.
Lemma lem1556714 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556715 : term37 = term35.
Proof. exact (EQ_MP (@lem1556714) (@lem940073)). Qed.
Lemma lem1556716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556717 : term34 = term38.
Proof. exact (MK_COMB (@lem1556716) (@lem1556715)). Qed.
Lemma lem1556718 : term33 = term38.
Proof. exact (TRANS (@lem1556713) (@lem1556717)). Qed.
Lemma lem1556719 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556720 : term39 = term40.
Proof. exact (MK_COMB (@lem1556719) (@lem1556718)). Qed.
Lemma lem1556721 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1556722 (x : real) : (term252 x) = (term253 x).
Proof. exact (MK_COMB (@lem1556720) (@lem1556721 x)). Qed.
Lemma lem1556723 (x : real) : (term251 x) = (term253 x).
Proof. exact (TRANS (@lem1556710 x) (@lem1556722 x)). Qed.
Lemma lem1556724 (x : real) : (term253 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1556725 (x : real) : (term251 x) = x.
Proof. exact (TRANS (@lem1556723 x) (@lem1556724 x)). Qed.
Lemma lem1556726 (x : real) : (term262 x) = x.
Proof. exact (TRANS (@lem1556709 x) (@lem1556725 x)). Qed.
Lemma lem1556735 (y : real) : (term254 y) = (term254 y).
Proof. exact (eq_refl (term254 y)). Qed.
Lemma lem1556736 (y : real) (x : real) : (term268 y x) = (term155 y x).
Proof. exact (MK_COMB (@lem1556735 y) (@lem1556726 x)). Qed.
Lemma lem1556737 (x : real) (y : real) : (term155 y x) = (term154 x y).
Proof. exact (@lem1483488 x (term118 y)). Qed.
Lemma lem1556738 (x : real) (y : real) : (term268 y x) = (term154 x y).
Proof. exact (TRANS (@lem1556736 y x) (@lem1556737 x y)). Qed.
Lemma lem1556739 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556740 (x : real) (y : real) : (term269 y x) = (term197 x y).
Proof. exact (MK_COMB (@lem1556739) (@lem1556738 x y)). Qed.
Lemma lem1556741 (x : real) (y : real) : (term270 y x) = (term198 x y).
Proof. exact (MK_COMB (@lem1556740 x y) (@lem1556698)). Qed.
Lemma lem1556742 (x : real) (y : real) : (term198 x y) = (term199 x y).
Proof. exact (@lem1483519 (term154 x y) term51). Qed.
Lemma lem1556744 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556745 : term164 = term51.
Proof. exact (@lem1556744 term35). Qed.
Lemma lem1556746 (x : real) (y : real) : (term200 x y) = (term200 x y).
Proof. exact (eq_refl (term200 x y)). Qed.
Lemma lem1556747 (x : real) (y : real) : (term199 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1556746 x y) (@lem1556745)). Qed.
Lemma lem1556748 (x : real) (y : real) : (term201 x y) = (term154 x y).
Proof. exact (@lem1483450 (term154 x y)). Qed.
Lemma lem1556749 (x : real) (y : real) : (term199 x y) = (term154 x y).
Proof. exact (TRANS (@lem1556747 x y) (@lem1556748 x y)). Qed.
Lemma lem1556750 (x : real) (y : real) : (term198 x y) = (term154 x y).
Proof. exact (TRANS (@lem1556742 x y) (@lem1556749 x y)). Qed.
Lemma lem1556751 (x : real) (y : real) : (term270 y x) = (term154 x y).
Proof. exact (TRANS (@lem1556741 x y) (@lem1556750 x y)). Qed.
Lemma lem1556752 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556753 (x : real) (y : real) : (term271 y x) = (term194 x y).
Proof. exact (MK_COMB (@lem1556752) (@lem1556751 x y)). Qed.
Lemma lem1556754 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556755 (x : real) (y : real) : (term267 y x) = (term195 x y).
Proof. exact (MK_COMB (@lem1556753 x y) (@lem1556754)). Qed.
Lemma lem1556756 (x : real) (y : real) : (term266 y x) = (term195 x y).
Proof. exact (TRANS (@lem1556697 y x) (@lem1556755 x y)). Qed.
Lemma lem1556757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556758 (x : real) : (term272 x) = term203.
Proof. exact (MK_COMB (@lem1556757) (@lem1556696 x)). Qed.
Lemma lem1556759 (x : real) (y : real) : (term236 y x) = (term204 x y).
Proof. exact (MK_COMB (@lem1556758 x) (@lem1556756 x y)). Qed.
Lemma lem1556760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556761 (x : real) (y : real) : (term237 y x) = (term273 x y).
Proof. exact (MK_COMB (@lem1556760) (@lem1556626 x y)). Qed.
Lemma lem1556762 (x : real) (y : real) : (term239 y x) = (term274 x y).
Proof. exact (MK_COMB (@lem1556761 x y) (@lem1556759 x y)). Qed.
Lemma lem1556763 (x : real) (y : real) : (term275 x y) = (term276 x y).
Proof. exact (@lem1483525 (real_neg x) (real_neg y)). Qed.
Lemma lem1556770 (y : real) : (real_neg y) = (term118 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1556777 (x : real) : (real_neg x) = (term118 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1556778 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556779 (x : real) : (term246 x) = (term247 x).
Proof. exact (MK_COMB (@lem1556778) (@lem1556777 x)). Qed.
Lemma lem1556780 (x : real) (y : real) : (term248 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1556779 x) (@lem1556770 y)). Qed.
Lemma lem1556781 (x : real) (y : real) : (term249 x y) = (term250 x y).
Proof. exact (@lem1483519 (term118 x) (term118 y)). Qed.
Lemma lem1556782 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1556784 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556785 : term33 = term34.
Proof. exact (@lem1556784 term35 term35). Qed.
Lemma lem1556786 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556787 : term37 = term35.
Proof. exact (EQ_MP (@lem1556786) (@lem940073)). Qed.
Lemma lem1556788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556789 : term34 = term38.
Proof. exact (MK_COMB (@lem1556788) (@lem1556787)). Qed.
Lemma lem1556790 : term33 = term38.
Proof. exact (TRANS (@lem1556785) (@lem1556789)). Qed.
Lemma lem1556791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556792 : term39 = term40.
Proof. exact (MK_COMB (@lem1556791) (@lem1556790)). Qed.
Lemma lem1556793 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1556794 (y : real) : (term252 y) = (term253 y).
Proof. exact (MK_COMB (@lem1556792) (@lem1556793 y)). Qed.
Lemma lem1556795 (y : real) : (term251 y) = (term253 y).
Proof. exact (TRANS (@lem1556782 y) (@lem1556794 y)). Qed.
Lemma lem1556796 (y : real) : (term253 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1556797 (y : real) : (term251 y) = y.
Proof. exact (TRANS (@lem1556795 y) (@lem1556796 y)). Qed.
Lemma lem1556798 (x : real) : (term254 x) = (term254 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem1556801 (x : real) (y : real) : (term250 x y) = (term155 x y).
Proof. exact (MK_COMB (@lem1556798 x) (@lem1556797 y)). Qed.
Lemma lem1556802 (x : real) (y : real) : (term249 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556781 x y) (@lem1556801 x y)). Qed.
Lemma lem1556803 (x : real) (y : real) : (term248 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556780 x y) (@lem1556802 x y)). Qed.
Lemma lem1556804 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556805 (x : real) (y : real) : (term277 x y) = (term168 x y).
Proof. exact (MK_COMB (@lem1556804) (@lem1556803 x y)). Qed.
Lemma lem1556806 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556807 (x : real) (y : real) : (term276 x y) = (term159 x y).
Proof. exact (MK_COMB (@lem1556805 x y) (@lem1556806)). Qed.
Lemma lem1556808 (x : real) (y : real) : (term275 x y) = (term159 x y).
Proof. exact (TRANS (@lem1556763 x y) (@lem1556807 x y)). Qed.
Lemma lem1556809 (x : real) (y : real) : (term266 x y) = (term267 x y).
Proof. exact (@lem1483525 (term268 x y) term51). Qed.
Lemma lem1556810 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556817 (y : real) : (real_neg y) = (term118 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1556820 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem1556821 (y : real) : (term262 y) = (term251 y).
Proof. exact (MK_COMB (@lem1556820) (@lem1556817 y)). Qed.
Lemma lem1556822 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1556824 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556825 : term33 = term34.
Proof. exact (@lem1556824 term35 term35). Qed.
Lemma lem1556826 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556827 : term37 = term35.
Proof. exact (EQ_MP (@lem1556826) (@lem940073)). Qed.
Lemma lem1556828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556829 : term34 = term38.
Proof. exact (MK_COMB (@lem1556828) (@lem1556827)). Qed.
Lemma lem1556830 : term33 = term38.
Proof. exact (TRANS (@lem1556825) (@lem1556829)). Qed.
Lemma lem1556831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556832 : term39 = term40.
Proof. exact (MK_COMB (@lem1556831) (@lem1556830)). Qed.
Lemma lem1556833 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1556834 (y : real) : (term252 y) = (term253 y).
Proof. exact (MK_COMB (@lem1556832) (@lem1556833 y)). Qed.
Lemma lem1556835 (y : real) : (term251 y) = (term253 y).
Proof. exact (TRANS (@lem1556822 y) (@lem1556834 y)). Qed.
Lemma lem1556836 (y : real) : (term253 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1556837 (y : real) : (term251 y) = y.
Proof. exact (TRANS (@lem1556835 y) (@lem1556836 y)). Qed.
Lemma lem1556838 (y : real) : (term262 y) = y.
Proof. exact (TRANS (@lem1556821 y) (@lem1556837 y)). Qed.
Lemma lem1556847 (x : real) : (term254 x) = (term254 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem1556850 (x : real) (y : real) : (term268 x y) = (term155 x y).
Proof. exact (MK_COMB (@lem1556847 x) (@lem1556838 y)). Qed.
Lemma lem1556851 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556852 (x : real) (y : real) : (term269 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1556851) (@lem1556850 x y)). Qed.
Lemma lem1556853 (x : real) (y : real) : (term270 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1556852 x y) (@lem1556810)). Qed.
Lemma lem1556854 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (@lem1483519 (term155 x y) term51). Qed.
Lemma lem1556856 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556857 : term164 = term51.
Proof. exact (@lem1556856 term35). Qed.
Lemma lem1556858 (x : real) (y : real) : (term165 x y) = (term165 x y).
Proof. exact (eq_refl (term165 x y)). Qed.
Lemma lem1556859 (x : real) (y : real) : (term162 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1556858 x y) (@lem1556857)). Qed.
Lemma lem1556860 (x : real) (y : real) : (term166 x y) = (term155 x y).
Proof. exact (@lem1483450 (term155 x y)). Qed.
Lemma lem1556861 (x : real) (y : real) : (term162 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556859 x y) (@lem1556860 x y)). Qed.
Lemma lem1556862 (x : real) (y : real) : (term161 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556854 x y) (@lem1556861 x y)). Qed.
Lemma lem1556863 (x : real) (y : real) : (term270 x y) = (term155 x y).
Proof. exact (TRANS (@lem1556853 x y) (@lem1556862 x y)). Qed.
Lemma lem1556864 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556865 (x : real) (y : real) : (term271 x y) = (term168 x y).
Proof. exact (MK_COMB (@lem1556864) (@lem1556863 x y)). Qed.
Lemma lem1556866 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556867 (x : real) (y : real) : (term267 x y) = (term159 x y).
Proof. exact (MK_COMB (@lem1556865 x y) (@lem1556866)). Qed.
Lemma lem1556868 (x : real) (y : real) : (term266 x y) = (term159 x y).
Proof. exact (TRANS (@lem1556809 x y) (@lem1556867 x y)). Qed.
Lemma lem1556869 (y : real) : (term258 y) = (term259 y).
Proof. exact (@lem1483525 (term260 y) term51). Qed.
Lemma lem1556870 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556877 (y : real) : (real_neg y) = (term118 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1556880 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem1556881 (y : real) : (term262 y) = (term251 y).
Proof. exact (MK_COMB (@lem1556880) (@lem1556877 y)). Qed.
Lemma lem1556882 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483476 term30 term30 y). Qed.
Lemma lem1556884 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1556885 : term33 = term34.
Proof. exact (@lem1556884 term35 term35). Qed.
Lemma lem1556886 : (term36 = (BIT1 0)) = (term37 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1556887 : term37 = term35.
Proof. exact (EQ_MP (@lem1556886) (@lem940073)). Qed.
Lemma lem1556888 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1556889 : term34 = term38.
Proof. exact (MK_COMB (@lem1556888) (@lem1556887)). Qed.
Lemma lem1556890 : term33 = term38.
Proof. exact (TRANS (@lem1556885) (@lem1556889)). Qed.
Lemma lem1556891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556892 : term39 = term40.
Proof. exact (MK_COMB (@lem1556891) (@lem1556890)). Qed.
Lemma lem1556893 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1556894 (y : real) : (term252 y) = (term253 y).
Proof. exact (MK_COMB (@lem1556892) (@lem1556893 y)). Qed.
Lemma lem1556895 (y : real) : (term251 y) = (term253 y).
Proof. exact (TRANS (@lem1556882 y) (@lem1556894 y)). Qed.
Lemma lem1556896 (y : real) : (term253 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1556897 (y : real) : (term251 y) = y.
Proof. exact (TRANS (@lem1556895 y) (@lem1556896 y)). Qed.
Lemma lem1556898 (y : real) : (term262 y) = y.
Proof. exact (TRANS (@lem1556881 y) (@lem1556897 y)). Qed.
Lemma lem1556907 (y : real) : (term254 y) = (term254 y).
Proof. exact (eq_refl (term254 y)). Qed.
Lemma lem1556908 (y : real) : (term260 y) = (term171 y).
Proof. exact (MK_COMB (@lem1556907 y) (@lem1556898 y)). Qed.
Lemma lem1556909 (y : real) : (term171 y) = (term172 y).
Proof. exact (@lem1483440 term30 y). Qed.
Lemma lem1556911 (m : nat) : (term173 m) = term51.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1556912 : term174 = term51.
Proof. exact (@lem1556911 term35). Qed.
Lemma lem1556913 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1556914 : term175 = term176.
Proof. exact (MK_COMB (@lem1556913) (@lem1556912)). Qed.
Lemma lem1556915 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1556916 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1556914) (@lem1556915 y)). Qed.
Lemma lem1556917 (y : real) : (term171 y) = (term177 y).
Proof. exact (TRANS (@lem1556909 y) (@lem1556916 y)). Qed.
Lemma lem1556918 (y : real) : (term177 y) = term51.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1556919 (y : real) : (term171 y) = term51.
Proof. exact (TRANS (@lem1556917 y) (@lem1556918 y)). Qed.
Lemma lem1556920 (y : real) : (term260 y) = term51.
Proof. exact (TRANS (@lem1556908 y) (@lem1556919 y)). Qed.
Lemma lem1556921 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1556922 (y : real) : (term263 y) = term179.
Proof. exact (MK_COMB (@lem1556921) (@lem1556920 y)). Qed.
Lemma lem1556923 (y : real) : (term264 y) = term181.
Proof. exact (MK_COMB (@lem1556922 y) (@lem1556870)). Qed.
Lemma lem1556924 : term181 = term182.
Proof. exact (@lem1483519 term51 term51). Qed.
Lemma lem1556926 (x : nat) : (term163 x) = term51.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1556927 : term164 = term51.
Proof. exact (@lem1556926 term35). Qed.
Lemma lem1556928 : term183 = term183.
Proof. exact (eq_refl term183). Qed.
Lemma lem1556929 : term182 = term184.
Proof. exact (MK_COMB (@lem1556928) (@lem1556927)). Qed.
Lemma lem1556930 : term184 = term51.
Proof. exact (@lem1483448 term51). Qed.
Lemma lem1556931 : term182 = term51.
Proof. exact (TRANS (@lem1556929) (@lem1556930)). Qed.
Lemma lem1556932 : term181 = term51.
Proof. exact (TRANS (@lem1556924) (@lem1556931)). Qed.
Lemma lem1556933 (y : real) : (term264 y) = term51.
Proof. exact (TRANS (@lem1556923 y) (@lem1556932)). Qed.
Lemma lem1556934 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1556935 (y : real) : (term265 y) = term186.
Proof. exact (MK_COMB (@lem1556934) (@lem1556933 y)). Qed.
Lemma lem1556936 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1556937 (y : real) : (term259 y) = term187.
Proof. exact (MK_COMB (@lem1556935 y) (@lem1556936)). Qed.
Lemma lem1556938 (y : real) : (term258 y) = term187.
Proof. exact (TRANS (@lem1556869 y) (@lem1556937 y)). Qed.
Lemma lem1556939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556940 (x : real) (y : real) : (term278 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1556939) (@lem1556868 x y)). Qed.
Lemma lem1556941 (x : real) (y : real) : (term231 x y) = (term189 x y).
Proof. exact (MK_COMB (@lem1556940 x y) (@lem1556938 y)). Qed.
Lemma lem1556942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1556943 (x : real) (y : real) : (term232 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1556942) (@lem1556808 x y)). Qed.
Lemma lem1556944 (x : real) (y : real) : (term234 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem1556943 x y) (@lem1556941 x y)). Qed.
Lemma lem1556945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556946 (x : real) (y : real) : (term241 y x) = (term280 x y).
Proof. exact (MK_COMB (@lem1556945) (@lem1556762 x y)). Qed.
Lemma lem1556947 (x : real) (y : real) : (term242 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem1556946 x y) (@lem1556944 x y)). Qed.
Lemma lem1556958 (x : real) (y : real) : (term226 x y) = (term281 x y).
Proof. exact (TRANS (@lem1556580 x y) (@lem1556947 x y)). Qed.
Lemma lem1556959 (x : real) (y : real) : (term53 x y) = (term281 x y).
Proof. exact (TRANS (@lem1556564 x y) (@lem1556958 x y)). Qed.
Lemma lem1556960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1556961 (x : real) (y : real) : (term59 x y) = (term282 x y).
Proof. exact (MK_COMB (@lem1556960) (@lem1556511 x y)). Qed.
Lemma lem1556962 (x : real) (y : real) : (term60 x y) = (term283 x y).
Proof. exact (MK_COMB (@lem1556961 x y) (@lem1556959 x y)). Qed.
Lemma lem1556963 (x : real) (y : real) (h1 : term283 x y) : term283 x y.
Proof. exact (h1). Qed.
Lemma lem1556964 (x : real) (y : real) (h1 : term208 x y) : term208 x y.
Proof. exact (h1). Qed.
Lemma lem1556965 (x : real) (y : real) (h1 : term191 x y) : term191 x y.
Proof. exact (h1). Qed.
Lemma lem1556966 (x : real) (y : real) (h1 : term191 x y) : term189 x y.
Proof. exact (proj2 (@lem1556965 x y h1)). Qed.
Lemma lem1556968 (x : real) (y : real) (h1 : term191 x y) : term187.
Proof. exact (proj2 (@lem1556966 x y h1)). Qed.
Lemma lem1556971 (n : nat) (m : nat) : (term284 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1556972 : term187 = term285.
Proof. exact (@lem1556971 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1556973 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1556974 : term187 = False.
Proof. exact (TRANS (@lem1556972) (@lem1556973)). Qed.
Lemma lem1556975 (x : real) (y : real) (h1 : term191 x y) : False.
Proof. exact (EQ_MP (@lem1556974) (@lem1556968 x y h1)). Qed.
Lemma lem1556976 (x : real) (y : real) (h1 : term206 x y) : term206 x y.
Proof. exact (h1). Qed.
Lemma lem1556977 (x : real) (y : real) (h1 : term206 x y) : term204 x y.
Proof. exact (proj2 (@lem1556976 x y h1)). Qed.
Lemma lem1556980 (x : real) (y : real) (h1 : term206 x y) : term187.
Proof. exact (proj1 (@lem1556977 x y h1)). Qed.
Lemma lem1556982 (n : nat) (m : nat) : (term284 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1556983 : term187 = term285.
Proof. exact (@lem1556982 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1556984 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1556985 : term187 = False.
Proof. exact (TRANS (@lem1556983) (@lem1556984)). Qed.
Lemma lem1556986 (x : real) (y : real) (h1 : term206 x y) : False.
Proof. exact (EQ_MP (@lem1556985) (@lem1556980 x y h1)). Qed.
Lemma lem1556987 (x : real) (y : real) (h1 : term208 x y) : False.
Proof. exact (or_elim (@lem1556964 x y h1) (fun h0 : term191 x y => @lem1556975 x y h0) (fun h0 : term206 x y => @lem1556986 x y h0)). Qed.
Lemma lem1556988 (x : real) (y : real) (h1 : term281 x y) : term281 x y.
Proof. exact (h1). Qed.
Lemma lem1556989 (x : real) (y : real) (h1 : term274 x y) : term274 x y.
Proof. exact (h1). Qed.
Lemma lem1556990 (x : real) (y : real) (h1 : term274 x y) : term204 x y.
Proof. exact (proj2 (@lem1556989 x y h1)). Qed.
Lemma lem1556993 (x : real) (y : real) (h1 : term274 x y) : term187.
Proof. exact (proj1 (@lem1556990 x y h1)). Qed.
Lemma lem1556995 (n : nat) (m : nat) : (term284 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1556996 : term187 = term285.
Proof. exact (@lem1556995 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1556997 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1556998 : term187 = False.
Proof. exact (TRANS (@lem1556996) (@lem1556997)). Qed.
Lemma lem1556999 (x : real) (y : real) (h1 : term274 x y) : False.
Proof. exact (EQ_MP (@lem1556998) (@lem1556993 x y h1)). Qed.
Lemma lem1557000 (x : real) (y : real) (h1 : term279 x y) : term279 x y.
Proof. exact (h1). Qed.
Lemma lem1557001 (x : real) (y : real) (h1 : term279 x y) : term189 x y.
Proof. exact (proj2 (@lem1557000 x y h1)). Qed.
Lemma lem1557003 (x : real) (y : real) (h1 : term279 x y) : term187.
Proof. exact (proj2 (@lem1557001 x y h1)). Qed.
Lemma lem1557006 (n : nat) (m : nat) : (term284 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1557007 : term187 = term285.
Proof. exact (@lem1557006 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1557008 : term285 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1557009 : term187 = False.
Proof. exact (TRANS (@lem1557007) (@lem1557008)). Qed.
Lemma lem1557010 (x : real) (y : real) (h1 : term279 x y) : False.
Proof. exact (EQ_MP (@lem1557009) (@lem1557003 x y h1)). Qed.
Lemma lem1557011 (x : real) (y : real) (h1 : term281 x y) : False.
Proof. exact (or_elim (@lem1556988 x y h1) (fun h0 : term274 x y => @lem1556999 x y h0) (fun h0 : term279 x y => @lem1557010 x y h0)). Qed.
Lemma lem1557012 (x : real) (y : real) (h1 : term283 x y) : False.
Proof. exact (or_elim (@lem1556963 x y h1) (fun h0 : term208 x y => @lem1556987 x y h0) (fun h0 : term281 x y => @lem1557011 x y h0)). Qed.
Lemma lem1557013 (x : real) (y : real) (h1 : term60 x y) : term60 x y.
Proof. exact (h1). Qed.
Lemma lem1557014 (x : real) (y : real) (h1 : term60 x y) : term283 x y.
Proof. exact (EQ_MP (@lem1556962 x y) (@lem1557013 x y h1)). Qed.
Lemma lem1557015 (x : real) (y : real) (h1 : term60 x y) : (term283 x y) = False.
Proof. exact (prop_ext (fun h2 : term283 x y => @lem1557012 x y h2) (fun h2 : False => @lem1557014 x y h1)). Qed.
Lemma lem1557016 (x : real) (y : real) (h1 : term60 x y) : False.
Proof. exact (EQ_MP (@lem1557015 x y h1) (@lem1557014 x y h1)). Qed.
Lemma lem1557017 (x : real) (h1 : term62 x) : term62 x.
Proof. exact (h1). Qed.
Lemma lem1557018 (x : real) (h1 : term62 x) : False.
Proof. exact (ex_elim (@lem1557017 x h1) (fun y : real => fun h0 : term61 x y => @lem1557016 x y h0)). Qed.
Lemma lem1557019 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem1557020 (h1 : term64) : False.
Proof. exact (ex_elim (@lem1557019 h1) (fun x : real => fun h0 : term63 x => @lem1557018 x h0)). Qed.
Lemma lem1557021 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1557022 (h1 : term12) : term64.
Proof. exact (EQ_MP (@lem1556237) (@lem1557021 h1)). Qed.
Lemma lem1557023 (h1 : term12) : term64 = False.
Proof. exact (prop_ext (fun h2 : term64 => @lem1557020 h2) (fun h2 : False => @lem1557022 h1)). Qed.
Lemma lem1557024 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1557023 h1) (@lem1557022 h1)). Qed.
Lemma lem1557025 : term286.
Proof. exact (fun h0 : term12 => @lem1557024 h0). Qed.
Lemma lem1557026 : term287.
Proof. exact (@lem1386578 term288). Qed.
Lemma lem1557027 : term288.
Proof. exact (@lem1557026 (@lem1557025)). Qed.
