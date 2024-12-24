Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MIN_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482716_spec.
Require Import thm1483429_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1566964 (x : real) (y : real) (z : real) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17160 (real_le x z) (real_le y z)). Qed.
Lemma lem1566970 (x : real) (y : real) (z : real) : (term2 x y z) = (term2 x y z).
Proof. exact (eq_refl (term2 x y z)). Qed.
Lemma lem1566972 (x : real) (y : real) (z : real) : (term3 x y z) = (term3 x y z).
Proof. exact (eq_refl (term3 x y z)). Qed.
Lemma lem1566973 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (MK_COMB (@lem1566972 x y z) (@lem1566964 x y z)). Qed.
Lemma lem1566974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1566975 (x : real) (y : real) (z : real) : (term6 x y z) = (term7 x y z).
Proof. exact (MK_COMB (@lem1566974) (@lem1566973 x y z)). Qed.
Lemma lem1566976 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1566975 x y z) (@lem1566970 x y z)). Qed.
Lemma lem1566977 (x : real) (y : real) (z : real) : (term10 x y z) = (term8 x y z).
Proof. exact (@lem17646 (term11 x y z) (term12 x y z)). Qed.
Lemma lem1566978 (x : real) (y : real) (z : real) : (term10 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1566977 x y z) (@lem1566976 x y z)). Qed.
Lemma lem1566979 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1566980 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1566979 (term17 x y)). Qed.
Lemma lem1566981 (x : real) (y : real) (z : real) : (term18 x y z) = ((term11 x y z) = (term12 x y z)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1566982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1566983 (x : real) (y : real) (z : real) : (term19 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem1566982) (@lem1566981 x y z)). Qed.
Lemma lem1566984 (x : real) (y : real) (z : real) : (term19 x y z) = (term9 x y z).
Proof. exact (TRANS (@lem1566983 x y z) (@lem1566978 x y z)). Qed.
Lemma lem1566985 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1566984 x y z)). Qed.
Lemma lem1566986 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566987 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1566986) (@lem1566985 x y)). Qed.
Lemma lem1566988 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1566980 x y) (@lem1566987 x y)). Qed.
Lemma lem1566989 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1566990 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1566989 (term25 x)). Qed.
Lemma lem1566991 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1566992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1566993 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1566992) (@lem1566991 x y)). Qed.
Lemma lem1566994 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1566993 x y) (@lem1566988 x y)). Qed.
Lemma lem1566995 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1566994 x y)). Qed.
Lemma lem1566996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1566997 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1566996) (@lem1566995 x)). Qed.
Lemma lem1566998 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1566990 x) (@lem1566997 x)). Qed.
Lemma lem1566999 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1567000 : term32 = term33.
Proof. exact (@lem1566999 term34). Qed.
Lemma lem1567001 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1567002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1567003 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1567002) (@lem1567001 x)). Qed.
Lemma lem1567004 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1567003 x) (@lem1566998 x)). Qed.
Lemma lem1567005 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1567004 x)). Qed.
Lemma lem1567006 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567007 : term33 = term40.
Proof. exact (MK_COMB (@lem1567006) (@lem1567005)). Qed.
Lemma lem1567009 : term32 = term40.
Proof. exact (TRANS (@lem1567000) (@lem1567007)). Qed.
Lemma lem1567036 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1567037 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1567036 x y z)). Qed.
Lemma lem1567038 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567039 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1567038) (@lem1567037 x y)). Qed.
Lemma lem1567040 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1567039 x y)). Qed.
Lemma lem1567041 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567042 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1567041) (@lem1567040 x)). Qed.
Lemma lem1567043 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1567042 x)). Qed.
Lemma lem1567044 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567045 : term40 = term40.
Proof. exact (MK_COMB (@lem1567044) (@lem1567043)). Qed.
Lemma lem1567046 : term32 = term40.
Proof. exact (TRANS (@lem1567009) (@lem1567045)). Qed.
Lemma lem1567047 (z : real) (x : real) (y : real) : (term11 x y z) = (term41 z x y).
Proof. exact (@lem1483523 z (real_min x y)). Qed.
Lemma lem1567060 (z : real) (x : real) (y : real) : (term42 z x y) = (term43 z x y).
Proof. exact (@lem1483519 z (real_min x y)). Qed.
Lemma lem1567061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1567062 (z : real) (x : real) (y : real) : (term44 z x y) = (term45 z x y).
Proof. exact (MK_COMB (@lem1567061) (@lem1567060 z x y)). Qed.
Lemma lem1567063 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567064 (z : real) (x : real) (y : real) : (term41 z x y) = (term47 z x y).
Proof. exact (MK_COMB (@lem1567062 z x y) (@lem1567063)). Qed.
Lemma lem1567065 (z : real) (x : real) (y : real) : (term11 x y z) = (term47 z x y).
Proof. exact (TRANS (@lem1567047 z x y) (@lem1567064 z x y)). Qed.
Lemma lem1567066 (x : real) (z : real) : (term48 x z) = (term49 x z).
Proof. exact (@lem1483533 x z). Qed.
Lemma lem1567079 (x : real) (z : real) : (real_sub x z) = (term50 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1567080 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567081 (x : real) (z : real) : (term51 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1567080) (@lem1567079 x z)). Qed.
Lemma lem1567082 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567083 (x : real) (z : real) : (term49 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1567081 x z) (@lem1567082)). Qed.
Lemma lem1567084 (x : real) (z : real) : (term48 x z) = (term53 x z).
Proof. exact (TRANS (@lem1567066 x z) (@lem1567083 x z)). Qed.
Lemma lem1567085 (y : real) (z : real) : (term48 y z) = (term49 y z).
Proof. exact (@lem1483533 y z). Qed.
Lemma lem1567098 (y : real) (z : real) : (real_sub y z) = (term50 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1567099 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567100 (y : real) (z : real) : (term51 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1567099) (@lem1567098 y z)). Qed.
Lemma lem1567101 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567102 (y : real) (z : real) : (term49 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1567100 y z) (@lem1567101)). Qed.
Lemma lem1567103 (y : real) (z : real) : (term48 y z) = (term53 y z).
Proof. exact (TRANS (@lem1567085 y z) (@lem1567102 y z)). Qed.
Lemma lem1567104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567105 (x : real) (z : real) : (term54 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1567104) (@lem1567084 x z)). Qed.
Lemma lem1567106 (x : real) (y : real) (z : real) : (term1 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1567105 x z) (@lem1567103 y z)). Qed.
Lemma lem1567107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567108 (z : real) (x : real) (y : real) : (term3 x y z) = (term57 z x y).
Proof. exact (MK_COMB (@lem1567107) (@lem1567065 z x y)). Qed.
Lemma lem1567109 (x : real) (y : real) (z : real) : (term5 x y z) = (term58 x y z).
Proof. exact (MK_COMB (@lem1567108 z x y) (@lem1567106 x y z)). Qed.
Lemma lem1567110 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (@lem1483533 (real_min x y) z). Qed.
Lemma lem1567116 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (@lem1483519 (real_min x y) z). Qed.
Lemma lem1567121 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (@lem1483488 (term64 z) (real_min x y)). Qed.
Lemma lem1567123 (z : real) (x : real) (y : real) : (term61 x y z) = (term63 z x y).
Proof. exact (TRANS (@lem1567116 x y z) (@lem1567121 z x y)). Qed.
Lemma lem1567124 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567125 (z : real) (x : real) (y : real) : (term65 x y z) = (term66 z x y).
Proof. exact (MK_COMB (@lem1567124) (@lem1567123 z x y)). Qed.
Lemma lem1567126 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567127 (z : real) (x : real) (y : real) : (term60 x y z) = (term67 z x y).
Proof. exact (MK_COMB (@lem1567125 z x y) (@lem1567126)). Qed.
Lemma lem1567128 (z : real) (x : real) (y : real) : (term59 x y z) = (term67 z x y).
Proof. exact (TRANS (@lem1567110 x y z) (@lem1567127 z x y)). Qed.
Lemma lem1567129 (z : real) (x : real) : (real_le x z) = (term68 z x).
Proof. exact (@lem1483523 z x). Qed.
Lemma lem1567135 (z : real) (x : real) : (real_sub z x) = (term50 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1567140 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1567142 (x : real) (z : real) : (real_sub z x) = (term69 x z).
Proof. exact (TRANS (@lem1567135 z x) (@lem1567140 x z)). Qed.
Lemma lem1567143 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1567144 (x : real) (z : real) : (term70 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1567143) (@lem1567142 x z)). Qed.
Lemma lem1567145 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567146 (x : real) (z : real) : (term68 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1567144 x z) (@lem1567145)). Qed.
Lemma lem1567147 (x : real) (z : real) : (real_le x z) = (term72 x z).
Proof. exact (TRANS (@lem1567129 z x) (@lem1567146 x z)). Qed.
Lemma lem1567148 (z : real) (y : real) : (real_le y z) = (term68 z y).
Proof. exact (@lem1483523 z y). Qed.
Lemma lem1567154 (z : real) (y : real) : (real_sub z y) = (term50 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1567159 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1567161 (y : real) (z : real) : (real_sub z y) = (term69 y z).
Proof. exact (TRANS (@lem1567154 z y) (@lem1567159 y z)). Qed.
Lemma lem1567162 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1567163 (y : real) (z : real) : (term70 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1567162) (@lem1567161 y z)). Qed.
Lemma lem1567164 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567165 (y : real) (z : real) : (term68 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1567163 y z) (@lem1567164)). Qed.
Lemma lem1567166 (y : real) (z : real) : (real_le y z) = (term72 y z).
Proof. exact (TRANS (@lem1567148 z y) (@lem1567165 y z)). Qed.
Lemma lem1567167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567168 (x : real) (z : real) : (term73 x z) = (term74 x z).
Proof. exact (MK_COMB (@lem1567167) (@lem1567147 x z)). Qed.
Lemma lem1567169 (x : real) (y : real) (z : real) : (term12 x y z) = (term75 x y z).
Proof. exact (MK_COMB (@lem1567168 x z) (@lem1567166 y z)). Qed.
Lemma lem1567170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567171 (z : real) (x : real) (y : real) : (term76 x y z) = (term77 z x y).
Proof. exact (MK_COMB (@lem1567170) (@lem1567128 z x y)). Qed.
Lemma lem1567172 (x : real) (y : real) (z : real) : (term2 x y z) = (term78 x y z).
Proof. exact (MK_COMB (@lem1567171 z x y) (@lem1567169 x y z)). Qed.
Lemma lem1567173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567174 (x : real) (y : real) (z : real) : (term7 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1567173) (@lem1567109 x y z)). Qed.
Lemma lem1567175 (x : real) (y : real) (z : real) : (term9 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1567174 x y z) (@lem1567172 x y z)). Qed.
Lemma lem1567176 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1567175 x y z)). Qed.
Lemma lem1567177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567178 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1567177) (@lem1567176 x y)). Qed.
Lemma lem1567179 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1567178 x y)). Qed.
Lemma lem1567180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567181 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1567180) (@lem1567179 x)). Qed.
Lemma lem1567182 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1567181 x)). Qed.
Lemma lem1567183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567184 : term40 = term86.
Proof. exact (MK_COMB (@lem1567183) (@lem1567182)). Qed.
Lemma lem1567185 : term32 = term86.
Proof. exact (TRANS (@lem1567046) (@lem1567184)). Qed.
Lemma lem1567195 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1567196 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1567195 real P Q). Qed.
Lemma lem1567197 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1567196 (term93 x y) (term94 x y)). Qed.
Lemma lem1567198 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1567199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567200 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1567199) (@lem1567198 x y z)). Qed.
Lemma lem1567201 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1567202 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1567200 x y z) (@lem1567201 x y z)). Qed.
Lemma lem1567203 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1567202 x y z)). Qed.
Lemma lem1567204 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567205 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1567204) (@lem1567203 x y)). Qed.
Lemma lem1567206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1567207 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1567206) (@lem1567205 x y)). Qed.
Lemma lem1567208 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1567209 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1567208 x y z)). Qed.
Lemma lem1567210 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567211 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1567210) (@lem1567209 x y)). Qed.
Lemma lem1567212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567213 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1567212) (@lem1567211 x y)). Qed.
Lemma lem1567214 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1567215 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1567214 x y z)). Qed.
Lemma lem1567216 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567217 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1567216) (@lem1567215 x y)). Qed.
Lemma lem1567218 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1567213 x y) (@lem1567217 x y)). Qed.
Lemma lem1567219 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1567207 x y) (@lem1567218 x y)). Qed.
Lemma lem1567220 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1567219 x y) (@lem1567197 x y)). Qed.
Lemma lem1567317 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1567220 x y)). Qed.
Lemma lem1567318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567319 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1567318) (@lem1567317 x)). Qed.
Lemma lem1567321 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1567322 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1567321 real P Q). Qed.
Lemma lem1567323 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1567322 (term115 x) (term116 x)). Qed.
Lemma lem1567324 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1567325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567326 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1567325) (@lem1567324 x y)). Qed.
Lemma lem1567327 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1567328 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1567326 x y) (@lem1567327 x y)). Qed.
Lemma lem1567329 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1567328 x y)). Qed.
Lemma lem1567330 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567331 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1567330) (@lem1567329 x)). Qed.
Lemma lem1567332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1567333 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1567332) (@lem1567331 x)). Qed.
Lemma lem1567334 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1567335 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1567334 x y)). Qed.
Lemma lem1567336 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567337 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1567336) (@lem1567335 x)). Qed.
Lemma lem1567338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567339 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1567338) (@lem1567337 x)). Qed.
Lemma lem1567340 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1567341 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1567340 x y)). Qed.
Lemma lem1567342 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567343 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1567342) (@lem1567341 x)). Qed.
Lemma lem1567344 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1567339 x) (@lem1567343 x)). Qed.
Lemma lem1567345 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1567333 x) (@lem1567344 x)). Qed.
Lemma lem1567346 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1567345 x) (@lem1567323 x)). Qed.
Lemma lem1567451 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1567319 x) (@lem1567346 x)). Qed.
Lemma lem1567452 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1567451 x)). Qed.
Lemma lem1567453 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567454 : term86 = term134.
Proof. exact (MK_COMB (@lem1567453) (@lem1567452)). Qed.
Lemma lem1567456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1567457 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1567456 real P Q). Qed.
Lemma lem1567458 : term135 = term136.
Proof. exact (@lem1567457 term137 term138). Qed.
Lemma lem1567459 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1567460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567461 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1567460) (@lem1567459 x)). Qed.
Lemma lem1567462 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1567463 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1567461 x) (@lem1567462 x)). Qed.
Lemma lem1567464 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1567463 x)). Qed.
Lemma lem1567465 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567466 : term135 = term134.
Proof. exact (MK_COMB (@lem1567465) (@lem1567464)). Qed.
Lemma lem1567467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1567468 : term144 = term145.
Proof. exact (MK_COMB (@lem1567467) (@lem1567466)). Qed.
Lemma lem1567469 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1567470 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1567469 x)). Qed.
Lemma lem1567471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567472 : term147 = term148.
Proof. exact (MK_COMB (@lem1567471) (@lem1567470)). Qed.
Lemma lem1567473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567474 : term149 = term150.
Proof. exact (MK_COMB (@lem1567473) (@lem1567472)). Qed.
Lemma lem1567475 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1567476 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1567475 x)). Qed.
Lemma lem1567477 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567478 : term152 = term153.
Proof. exact (MK_COMB (@lem1567477) (@lem1567476)). Qed.
Lemma lem1567479 : term136 = term154.
Proof. exact (MK_COMB (@lem1567474) (@lem1567478)). Qed.
Lemma lem1567480 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1567468) (@lem1567479)). Qed.
Lemma lem1567481 : term134 = term154.
Proof. exact (EQ_MP (@lem1567480) (@lem1567458)). Qed.
Lemma lem1567594 : term86 = term154.
Proof. exact (TRANS (@lem1567454) (@lem1567481)). Qed.
Lemma lem1567596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1567597 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1567596 real P Q). Qed.
Lemma lem1567598 : term136 = term135.
Proof. exact (@lem1567597 term137 term138). Qed.
Lemma lem1567599 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1567600 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1567599 x)). Qed.
Lemma lem1567601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567602 : term147 = term148.
Proof. exact (MK_COMB (@lem1567601) (@lem1567600)). Qed.
Lemma lem1567603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567604 : term149 = term150.
Proof. exact (MK_COMB (@lem1567603) (@lem1567602)). Qed.
Lemma lem1567605 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1567606 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1567605 x)). Qed.
Lemma lem1567607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567608 : term152 = term153.
Proof. exact (MK_COMB (@lem1567607) (@lem1567606)). Qed.
Lemma lem1567609 : term136 = term154.
Proof. exact (MK_COMB (@lem1567604) (@lem1567608)). Qed.
Lemma lem1567610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1567611 : term155 = term156.
Proof. exact (MK_COMB (@lem1567610) (@lem1567609)). Qed.
Lemma lem1567612 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1567613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567614 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1567613) (@lem1567612 x)). Qed.
Lemma lem1567615 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1567616 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1567614 x) (@lem1567615 x)). Qed.
Lemma lem1567617 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1567616 x)). Qed.
Lemma lem1567618 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567619 : term135 = term134.
Proof. exact (MK_COMB (@lem1567618) (@lem1567617)). Qed.
Lemma lem1567620 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1567611) (@lem1567619)). Qed.
Lemma lem1567621 : term154 = term134.
Proof. exact (EQ_MP (@lem1567620) (@lem1567598)). Qed.
Lemma lem1567623 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1567624 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1567623 real P Q). Qed.
Lemma lem1567625 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1567624 (term115 x) (term116 x)). Qed.
Lemma lem1567626 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1567627 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1567626 x y)). Qed.
Lemma lem1567628 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567629 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1567628) (@lem1567627 x)). Qed.
Lemma lem1567630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567631 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1567630) (@lem1567629 x)). Qed.
Lemma lem1567632 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1567633 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1567632 x y)). Qed.
Lemma lem1567634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567635 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1567634) (@lem1567633 x)). Qed.
Lemma lem1567636 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1567631 x) (@lem1567635 x)). Qed.
Lemma lem1567637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1567638 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1567637) (@lem1567636 x)). Qed.
Lemma lem1567639 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1567640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567641 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1567640) (@lem1567639 x y)). Qed.
Lemma lem1567642 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1567643 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1567641 x y) (@lem1567642 x y)). Qed.
Lemma lem1567644 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1567643 x y)). Qed.
Lemma lem1567645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567646 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1567645) (@lem1567644 x)). Qed.
Lemma lem1567647 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1567638 x) (@lem1567646 x)). Qed.
Lemma lem1567648 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1567647 x) (@lem1567625 x)). Qed.
Lemma lem1567650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1567651 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1567650 real P Q). Qed.
Lemma lem1567652 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1567651 (term93 x y) (term94 x y)). Qed.
Lemma lem1567653 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1567654 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1567653 x y z)). Qed.
Lemma lem1567655 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567656 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1567655) (@lem1567654 x y)). Qed.
Lemma lem1567657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567658 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1567657) (@lem1567656 x y)). Qed.
Lemma lem1567659 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1567660 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1567659 x y z)). Qed.
Lemma lem1567661 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567662 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1567661) (@lem1567660 x y)). Qed.
Lemma lem1567663 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1567658 x y) (@lem1567662 x y)). Qed.
Lemma lem1567664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1567665 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1567664) (@lem1567663 x y)). Qed.
Lemma lem1567666 (x : real) (y : real) (z : real) : (term95 x y z) = (term58 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1567667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567668 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1567667) (@lem1567666 x y z)). Qed.
Lemma lem1567669 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1567670 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1567668 x y z) (@lem1567669 x y z)). Qed.
Lemma lem1567671 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1567670 x y z)). Qed.
Lemma lem1567672 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567673 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1567672) (@lem1567671 x y)). Qed.
Lemma lem1567674 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1567665 x y) (@lem1567673 x y)). Qed.
Lemma lem1567675 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1567674 x y) (@lem1567652 x y)). Qed.
Lemma lem1567676 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1567675 x y)). Qed.
Lemma lem1567677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567678 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1567677) (@lem1567676 x)). Qed.
Lemma lem1567679 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1567648 x) (@lem1567678 x)). Qed.
Lemma lem1567680 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1567679 x)). Qed.
Lemma lem1567681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567682 : term134 = term86.
Proof. exact (MK_COMB (@lem1567681) (@lem1567680)). Qed.
Lemma lem1567683 : term154 = term86.
Proof. exact (TRANS (@lem1567621) (@lem1567682)). Qed.
Lemma lem1567684 : term86 = term86.
Proof. exact (TRANS (@lem1567594) (@lem1567683)). Qed.
Lemma lem1567687 : term32 = term86.
Proof. exact (TRANS (@lem1567185) (@lem1567684)). Qed.
Lemma lem1567704 (x : real) (y : real) (z : real) : (term78 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term72 x z) (term67 z x y) (term72 y z)). Qed.
Lemma lem1567719 (x : real) (y : real) (z : real) : (term79 x y z) = (term79 x y z).
Proof. exact (eq_refl (term79 x y z)). Qed.
Lemma lem1567720 (x : real) (y : real) (z : real) : (term80 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1567719 x y z) (@lem1567704 x y z)). Qed.
Lemma lem1567721 (x : real) (y : real) : (term81 x y) = (term163 x y).
Proof. exact (fun_ext (fun z : real => @lem1567720 x y z)). Qed.
Lemma lem1567722 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567723 (x : real) (y : real) : (term82 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1567722) (@lem1567721 x y)). Qed.
Lemma lem1567724 (x : real) : (term83 x) = (term165 x).
Proof. exact (fun_ext (fun y : real => @lem1567723 x y)). Qed.
Lemma lem1567725 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567726 (x : real) : (term84 x) = (term166 x).
Proof. exact (MK_COMB (@lem1567725) (@lem1567724 x)). Qed.
Lemma lem1567727 : term85 = term167.
Proof. exact (fun_ext (fun x : real => @lem1567726 x)). Qed.
Lemma lem1567728 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1567729 : term86 = term168.
Proof. exact (MK_COMB (@lem1567728) (@lem1567727)). Qed.
Lemma lem1567730 : term32 = term168.
Proof. exact (TRANS (@lem1567687) (@lem1567729)). Qed.
Lemma lem1567732 (x : real) (y : real) (z : real) : (term169 z x y) = (term58 x y z).
Proof. exact (eq_refl (term169 z x y)). Qed.
Lemma lem1567733 (z : real) (x : real) (y : real) : (term58 x y z) = (term169 z x y).
Proof. exact (SYM (@lem1567732 x y z)). Qed.
Lemma lem1567734 (x : real) (z : real) (y : real) : (term169 z x y) = (term170 x z y).
Proof. exact (@lem1483429 x (term171 x y z) y). Qed.
Lemma lem1567735 (x : real) (z : real) (y : real) : (term58 x y z) = (term170 x z y).
Proof. exact (TRANS (@lem1567733 z x y) (@lem1567734 x z y)). Qed.
Lemma lem1567736 (x : real) (y : real) (z : real) : (term172 x z y) = (term173 x y z).
Proof. exact (eq_refl (term172 x z y)). Qed.
Lemma lem1567737 (x : real) (y : real) : (term174 x y) = (term174 x y).
Proof. exact (eq_refl (term174 x y)). Qed.
Lemma lem1567738 (x : real) (y : real) (z : real) : (term175 x z y) = (term176 x y z).
Proof. exact (MK_COMB (@lem1567737 x y) (@lem1567736 x y z)). Qed.
Lemma lem1567739 (x : real) (y : real) (z : real) : (term177 y z x) = (term178 x y z).
Proof. exact (eq_refl (term177 y z x)). Qed.
Lemma lem1567740 (y : real) (x : real) : (term179 y x) = (term179 y x).
Proof. exact (eq_refl (term179 y x)). Qed.
Lemma lem1567741 (x : real) (y : real) (z : real) : (term180 y z x) = (term181 x y z).
Proof. exact (MK_COMB (@lem1567740 y x) (@lem1567739 x y z)). Qed.
Lemma lem1567742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567743 (x : real) (y : real) (z : real) : (term182 y z x) = (term183 x y z).
Proof. exact (MK_COMB (@lem1567742) (@lem1567741 x y z)). Qed.
Lemma lem1567744 (x : real) (y : real) (z : real) : (term170 x z y) = (term184 x y z).
Proof. exact (MK_COMB (@lem1567743 x y z) (@lem1567738 x y z)). Qed.
Lemma lem1567745 (x : real) (y : real) (z : real) : (term185 x y z) = (term185 x y z).
Proof. exact (eq_refl (term185 x y z)). Qed.
Lemma lem1567746 (x : real) (y : real) (z : real) : ((term58 x y z) = (term170 x z y)) = ((term58 x y z) = (term184 x y z)).
Proof. exact (MK_COMB (@lem1567745 x y z) (@lem1567744 x y z)). Qed.
Lemma lem1567747 (x : real) (y : real) (z : real) : (term58 x y z) = (term184 x y z).
Proof. exact (EQ_MP (@lem1567746 x y z) (@lem1567735 x z y)). Qed.
Lemma lem1567748 (y : real) (x : real) : (real_ge y x) = (term68 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1567754 (y : real) (x : real) : (real_sub y x) = (term50 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1567759 (x : real) (y : real) : (term50 y x) = (term69 x y).
Proof. exact (@lem1483488 (term64 x) y). Qed.
Lemma lem1567761 (x : real) (y : real) : (real_sub y x) = (term69 x y).
Proof. exact (TRANS (@lem1567754 y x) (@lem1567759 x y)). Qed.
Lemma lem1567762 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1567763 (x : real) (y : real) : (term70 y x) = (term71 x y).
Proof. exact (MK_COMB (@lem1567762) (@lem1567761 x y)). Qed.
Lemma lem1567764 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567765 (x : real) (y : real) : (term68 y x) = (term72 x y).
Proof. exact (MK_COMB (@lem1567763 x y) (@lem1567764)). Qed.
Lemma lem1567766 (x : real) (y : real) : (real_ge y x) = (term72 x y).
Proof. exact (TRANS (@lem1567748 y x) (@lem1567765 x y)). Qed.
Lemma lem1567767 (z : real) (x : real) : (term186 z x) = (term187 z x).
Proof. exact (@lem1483527 (term50 z x) term46). Qed.
Lemma lem1567768 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567781 (x : real) (z : real) : (term50 z x) = (term69 x z).
Proof. exact (@lem1483488 (term64 x) z). Qed.
Lemma lem1567782 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1567783 (x : real) (z : real) : (term188 z x) = (term189 x z).
Proof. exact (MK_COMB (@lem1567782) (@lem1567781 x z)). Qed.
Lemma lem1567784 (x : real) (z : real) : (term190 z x) = (term191 x z).
Proof. exact (MK_COMB (@lem1567783 x z) (@lem1567768)). Qed.
Lemma lem1567785 (x : real) (z : real) : (term191 x z) = (term192 x z).
Proof. exact (@lem1483519 (term69 x z) term46). Qed.
Lemma lem1567787 (x : nat) : (term193 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1567788 : term194 = term46.
Proof. exact (@lem1567787 term195). Qed.
Lemma lem1567789 (x : real) (z : real) : (term196 x z) = (term196 x z).
Proof. exact (eq_refl (term196 x z)). Qed.
Lemma lem1567790 (x : real) (z : real) : (term192 x z) = (term197 x z).
Proof. exact (MK_COMB (@lem1567789 x z) (@lem1567788)). Qed.
Lemma lem1567791 (x : real) (z : real) : (term197 x z) = (term69 x z).
Proof. exact (@lem1483450 (term69 x z)). Qed.
Lemma lem1567792 (x : real) (z : real) : (term192 x z) = (term69 x z).
Proof. exact (TRANS (@lem1567790 x z) (@lem1567791 x z)). Qed.
Lemma lem1567793 (x : real) (z : real) : (term191 x z) = (term69 x z).
Proof. exact (TRANS (@lem1567785 x z) (@lem1567792 x z)). Qed.
Lemma lem1567794 (x : real) (z : real) : (term190 z x) = (term69 x z).
Proof. exact (TRANS (@lem1567784 x z) (@lem1567793 x z)). Qed.
Lemma lem1567795 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1567796 (x : real) (z : real) : (term198 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1567795) (@lem1567794 x z)). Qed.
Lemma lem1567797 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567798 (x : real) (z : real) : (term187 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1567796 x z) (@lem1567797)). Qed.
Lemma lem1567799 (x : real) (z : real) : (term186 z x) = (term72 x z).
Proof. exact (TRANS (@lem1567767 z x) (@lem1567798 x z)). Qed.
Lemma lem1567800 (x : real) (z : real) : (term53 x z) = (term199 x z).
Proof. exact (@lem1483525 (term50 x z) term46). Qed.
Lemma lem1567818 (x : real) (z : real) : (term190 x z) = (term200 x z).
Proof. exact (@lem1483519 (term50 x z) term46). Qed.
Lemma lem1567820 (x : nat) : (term193 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1567821 : term194 = term46.
Proof. exact (@lem1567820 term195). Qed.
Lemma lem1567822 (x : real) (z : real) : (term201 x z) = (term201 x z).
Proof. exact (eq_refl (term201 x z)). Qed.
Lemma lem1567823 (x : real) (z : real) : (term200 x z) = (term202 x z).
Proof. exact (MK_COMB (@lem1567822 x z) (@lem1567821)). Qed.
Lemma lem1567824 (x : real) (z : real) : (term202 x z) = (term50 x z).
Proof. exact (@lem1483450 (term50 x z)). Qed.
Lemma lem1567825 (x : real) (z : real) : (term200 x z) = (term50 x z).
Proof. exact (TRANS (@lem1567823 x z) (@lem1567824 x z)). Qed.
Lemma lem1567827 (x : real) (z : real) : (term190 x z) = (term50 x z).
Proof. exact (TRANS (@lem1567818 x z) (@lem1567825 x z)). Qed.
Lemma lem1567828 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567829 (x : real) (z : real) : (term203 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1567828) (@lem1567827 x z)). Qed.
Lemma lem1567830 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567831 (x : real) (z : real) : (term199 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1567829 x z) (@lem1567830)). Qed.
Lemma lem1567832 (x : real) (z : real) : (term53 x z) = (term53 x z).
Proof. exact (TRANS (@lem1567800 x z) (@lem1567831 x z)). Qed.
Lemma lem1567833 (y : real) (z : real) : (term53 y z) = (term199 y z).
Proof. exact (@lem1483525 (term50 y z) term46). Qed.
Lemma lem1567851 (y : real) (z : real) : (term190 y z) = (term200 y z).
Proof. exact (@lem1483519 (term50 y z) term46). Qed.
Lemma lem1567853 (x : nat) : (term193 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1567854 : term194 = term46.
Proof. exact (@lem1567853 term195). Qed.
Lemma lem1567855 (y : real) (z : real) : (term201 y z) = (term201 y z).
Proof. exact (eq_refl (term201 y z)). Qed.
Lemma lem1567856 (y : real) (z : real) : (term200 y z) = (term202 y z).
Proof. exact (MK_COMB (@lem1567855 y z) (@lem1567854)). Qed.
Lemma lem1567857 (y : real) (z : real) : (term202 y z) = (term50 y z).
Proof. exact (@lem1483450 (term50 y z)). Qed.
Lemma lem1567858 (y : real) (z : real) : (term200 y z) = (term50 y z).
Proof. exact (TRANS (@lem1567856 y z) (@lem1567857 y z)). Qed.
Lemma lem1567860 (y : real) (z : real) : (term190 y z) = (term50 y z).
Proof. exact (TRANS (@lem1567851 y z) (@lem1567858 y z)). Qed.
Lemma lem1567861 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567862 (y : real) (z : real) : (term203 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1567861) (@lem1567860 y z)). Qed.
Lemma lem1567863 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567864 (y : real) (z : real) : (term199 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1567862 y z) (@lem1567863)). Qed.
Lemma lem1567865 (y : real) (z : real) : (term53 y z) = (term53 y z).
Proof. exact (TRANS (@lem1567833 y z) (@lem1567864 y z)). Qed.
Lemma lem1567866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567867 (x : real) (z : real) : (term55 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1567866) (@lem1567832 x z)). Qed.
Lemma lem1567868 (x : real) (y : real) (z : real) : (term56 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1567867 x z) (@lem1567865 y z)). Qed.
Lemma lem1567869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567870 (x : real) (z : real) : (term204 z x) = (term205 x z).
Proof. exact (MK_COMB (@lem1567869) (@lem1567799 x z)). Qed.
Lemma lem1567871 (x : real) (y : real) (z : real) : (term178 x y z) = (term206 x y z).
Proof. exact (MK_COMB (@lem1567870 x z) (@lem1567868 x y z)). Qed.
Lemma lem1567872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567873 (x : real) (y : real) : (term179 y x) = (term205 x y).
Proof. exact (MK_COMB (@lem1567872) (@lem1567766 x y)). Qed.
Lemma lem1567874 (x : real) (y : real) (z : real) : (term181 x y z) = (term207 x y z).
Proof. exact (MK_COMB (@lem1567873 x y) (@lem1567871 x y z)). Qed.
Lemma lem1567875 (x : real) (y : real) : (real_gt x y) = (term49 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1567888 (x : real) (y : real) : (real_sub x y) = (term50 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1567889 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567890 (x : real) (y : real) : (term51 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1567889) (@lem1567888 x y)). Qed.
Lemma lem1567891 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567892 (x : real) (y : real) : (term49 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1567890 x y) (@lem1567891)). Qed.
Lemma lem1567893 (x : real) (y : real) : (real_gt x y) = (term53 x y).
Proof. exact (TRANS (@lem1567875 x y) (@lem1567892 x y)). Qed.
Lemma lem1567894 (z : real) (y : real) : (term186 z y) = (term187 z y).
Proof. exact (@lem1483527 (term50 z y) term46). Qed.
Lemma lem1567895 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567908 (y : real) (z : real) : (term50 z y) = (term69 y z).
Proof. exact (@lem1483488 (term64 y) z). Qed.
Lemma lem1567909 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1567910 (y : real) (z : real) : (term188 z y) = (term189 y z).
Proof. exact (MK_COMB (@lem1567909) (@lem1567908 y z)). Qed.
Lemma lem1567911 (y : real) (z : real) : (term190 z y) = (term191 y z).
Proof. exact (MK_COMB (@lem1567910 y z) (@lem1567895)). Qed.
Lemma lem1567912 (y : real) (z : real) : (term191 y z) = (term192 y z).
Proof. exact (@lem1483519 (term69 y z) term46). Qed.
Lemma lem1567914 (x : nat) : (term193 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1567915 : term194 = term46.
Proof. exact (@lem1567914 term195). Qed.
Lemma lem1567916 (y : real) (z : real) : (term196 y z) = (term196 y z).
Proof. exact (eq_refl (term196 y z)). Qed.
Lemma lem1567917 (y : real) (z : real) : (term192 y z) = (term197 y z).
Proof. exact (MK_COMB (@lem1567916 y z) (@lem1567915)). Qed.
Lemma lem1567918 (y : real) (z : real) : (term197 y z) = (term69 y z).
Proof. exact (@lem1483450 (term69 y z)). Qed.
Lemma lem1567919 (y : real) (z : real) : (term192 y z) = (term69 y z).
Proof. exact (TRANS (@lem1567917 y z) (@lem1567918 y z)). Qed.
Lemma lem1567920 (y : real) (z : real) : (term191 y z) = (term69 y z).
Proof. exact (TRANS (@lem1567912 y z) (@lem1567919 y z)). Qed.
Lemma lem1567921 (y : real) (z : real) : (term190 z y) = (term69 y z).
Proof. exact (TRANS (@lem1567911 y z) (@lem1567920 y z)). Qed.
Lemma lem1567922 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1567923 (y : real) (z : real) : (term198 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1567922) (@lem1567921 y z)). Qed.
Lemma lem1567924 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567925 (y : real) (z : real) : (term187 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1567923 y z) (@lem1567924)). Qed.
Lemma lem1567926 (y : real) (z : real) : (term186 z y) = (term72 y z).
Proof. exact (TRANS (@lem1567894 z y) (@lem1567925 y z)). Qed.
Lemma lem1567927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567928 (x : real) (z : real) : (term55 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1567927) (@lem1567832 x z)). Qed.
Lemma lem1567929 (x : real) (y : real) (z : real) : (term56 x y z) = (term56 x y z).
Proof. exact (MK_COMB (@lem1567928 x z) (@lem1567865 y z)). Qed.
Lemma lem1567930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567931 (y : real) (z : real) : (term204 z y) = (term205 y z).
Proof. exact (MK_COMB (@lem1567930) (@lem1567926 y z)). Qed.
Lemma lem1567932 (x : real) (y : real) (z : real) : (term173 x y z) = (term208 x y z).
Proof. exact (MK_COMB (@lem1567931 y z) (@lem1567929 x y z)). Qed.
Lemma lem1567933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567934 (x : real) (y : real) : (term174 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1567933) (@lem1567893 x y)). Qed.
Lemma lem1567935 (x : real) (y : real) (z : real) : (term176 x y z) = (term209 x y z).
Proof. exact (MK_COMB (@lem1567934 x y) (@lem1567932 x y z)). Qed.
Lemma lem1567936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1567937 (x : real) (y : real) (z : real) : (term183 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem1567936) (@lem1567874 x y z)). Qed.
Lemma lem1567938 (x : real) (y : real) (z : real) : (term184 x y z) = (term211 x y z).
Proof. exact (MK_COMB (@lem1567937 x y z) (@lem1567935 x y z)). Qed.
Lemma lem1567950 (x : real) (y : real) (z : real) : (term58 x y z) = (term211 x y z).
Proof. exact (TRANS (@lem1567747 x y z) (@lem1567938 x y z)). Qed.
Lemma lem1567952 (x : real) (a : real) (y : real) (r : real) : (term212 a x y r) = (term213 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1567953 (x : real) (z : real) (y : real) : (term67 z x y) = (term214 x z y).
Proof. exact (@lem1567952 x (term64 z) y term46). Qed.
Lemma lem1567966 (y : real) (z : real) : (term69 z y) = (term50 y z).
Proof. exact (@lem1483488 y (term64 z)). Qed.
Lemma lem1567967 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567968 (y : real) (z : real) : (term215 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1567967) (@lem1567966 y z)). Qed.
Lemma lem1567969 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567970 (y : real) (z : real) : (term216 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1567968 y z) (@lem1567969)). Qed.
Lemma lem1567983 (x : real) (z : real) : (term69 z x) = (term50 x z).
Proof. exact (@lem1483488 x (term64 z)). Qed.
Lemma lem1567984 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1567985 (x : real) (z : real) : (term215 z x) = (term52 x z).
Proof. exact (MK_COMB (@lem1567984) (@lem1567983 x z)). Qed.
Lemma lem1567986 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1567987 (x : real) (z : real) : (term216 z x) = (term53 x z).
Proof. exact (MK_COMB (@lem1567985 x z) (@lem1567986)). Qed.
Lemma lem1567988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567989 (x : real) (z : real) : (term217 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1567988) (@lem1567987 x z)). Qed.
Lemma lem1567990 (x : real) (y : real) (z : real) : (term214 x z y) = (term56 x y z).
Proof. exact (MK_COMB (@lem1567989 x z) (@lem1567970 y z)). Qed.
Lemma lem1567991 (x : real) (y : real) (z : real) : (term67 z x y) = (term56 x y z).
Proof. exact (TRANS (@lem1567953 x z y) (@lem1567990 x y z)). Qed.
Lemma lem1567992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1567993 (x : real) (y : real) (z : real) : (term77 z x y) = (term218 x y z).
Proof. exact (MK_COMB (@lem1567992) (@lem1567991 x y z)). Qed.
Lemma lem1567994 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (eq_refl (term72 x z)). Qed.
Lemma lem1567997 (y : real) (x : real) (z : real) : (term219 y x z) = (term220 y x z).
Proof. exact (MK_COMB (@lem1567993 x y z) (@lem1567994 x z)). Qed.
Lemma lem1567999 (x : real) (a : real) (y : real) (r : real) : (term212 a x y r) = (term213 x a y r).
Proof. exact (proj1 (@lem1482716 x a (@el real) y (@el real) r)). Qed.
Lemma lem1568000 (x : real) (z : real) (y : real) : (term67 z x y) = (term214 x z y).
Proof. exact (@lem1567999 x (term64 z) y term46). Qed.
Lemma lem1568013 (y : real) (z : real) : (term69 z y) = (term50 y z).
Proof. exact (@lem1483488 y (term64 z)). Qed.
Lemma lem1568014 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568015 (y : real) (z : real) : (term215 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1568014) (@lem1568013 y z)). Qed.
Lemma lem1568016 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568017 (y : real) (z : real) : (term216 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1568015 y z) (@lem1568016)). Qed.
Lemma lem1568030 (x : real) (z : real) : (term69 z x) = (term50 x z).
Proof. exact (@lem1483488 x (term64 z)). Qed.
Lemma lem1568031 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568032 (x : real) (z : real) : (term215 z x) = (term52 x z).
Proof. exact (MK_COMB (@lem1568031) (@lem1568030 x z)). Qed.
Lemma lem1568033 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568034 (x : real) (z : real) : (term216 z x) = (term53 x z).
Proof. exact (MK_COMB (@lem1568032 x z) (@lem1568033)). Qed.
Lemma lem1568035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1568036 (x : real) (z : real) : (term217 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1568035) (@lem1568034 x z)). Qed.
Lemma lem1568037 (x : real) (y : real) (z : real) : (term214 x z y) = (term56 x y z).
Proof. exact (MK_COMB (@lem1568036 x z) (@lem1568017 y z)). Qed.
Lemma lem1568038 (x : real) (y : real) (z : real) : (term67 z x y) = (term56 x y z).
Proof. exact (TRANS (@lem1568000 x z y) (@lem1568037 x y z)). Qed.
Lemma lem1568039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1568040 (x : real) (y : real) (z : real) : (term77 z x y) = (term218 x y z).
Proof. exact (MK_COMB (@lem1568039) (@lem1568038 x y z)). Qed.
Lemma lem1568041 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (eq_refl (term72 y z)). Qed.
Lemma lem1568044 (x : real) (y : real) (z : real) : (term221 x y z) = (term222 x y z).
Proof. exact (MK_COMB (@lem1568040 x y z) (@lem1568041 y z)). Qed.
Lemma lem1568045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568046 (y : real) (x : real) (z : real) : (term223 y x z) = (term224 y x z).
Proof. exact (MK_COMB (@lem1568045) (@lem1567997 y x z)). Qed.
Lemma lem1568047 (x : real) (y : real) (z : real) : (term161 x y z) = (term225 x y z).
Proof. exact (MK_COMB (@lem1568046 y x z) (@lem1568044 x y z)). Qed.
Lemma lem1568048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1568049 (x : real) (y : real) (z : real) : (term79 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1568048) (@lem1567950 x y z)). Qed.
Lemma lem1568050 (x : real) (y : real) (z : real) : (term162 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1568049 x y z) (@lem1568047 x y z)). Qed.
Lemma lem1568051 (x : real) (y : real) (z : real) (h1 : term227 x y z) : term227 x y z.
Proof. exact (h1). Qed.
Lemma lem1568052 (x : real) (y : real) (z : real) (h1 : term211 x y z) : term211 x y z.
Proof. exact (h1). Qed.
Lemma lem1568053 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term207 x y z.
Proof. exact (h1). Qed.
Lemma lem1568054 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term206 x y z.
Proof. exact (proj2 (@lem1568053 x y z h1)). Qed.
Lemma lem1568056 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term56 x y z.
Proof. exact (proj2 (@lem1568054 x y z h1)). Qed.
Lemma lem1568057 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term72 x z.
Proof. exact (proj1 (@lem1568054 x y z h1)). Qed.
Lemma lem1568059 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term53 x z.
Proof. exact (proj1 (@lem1568056 x y z h1)). Qed.
Lemma lem1568061 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568062 : term229 = term230.
Proof. exact (@lem1568061 (NUMERAL 0) term195). Qed.
Lemma lem1568063 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568064 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568065 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568064 h1) (fun h1 : term230 = True => @lem1568063)). Qed.
Lemma lem1568066 : term230 = True.
Proof. exact (EQ_MP (@lem1568065) (@lem1568063)). Qed.
Lemma lem1568067 : term229 = True.
Proof. exact (TRANS (@lem1568062) (@lem1568066)). Qed.
Lemma lem1568068 : True = term229.
Proof. exact (SYM (@lem1568067)). Qed.
Lemma lem1568069 : term229.
Proof. exact (EQ_MP (@lem1568068) (@lem0)). Qed.
Lemma lem1568070 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term232 x z.
Proof. exact (conj (@lem1568069) (@lem1568057 x y z h1)). Qed.
Lemma lem1568072 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1568073 (x : real) (z : real) : term234 x z.
Proof. exact (@lem1568072 term235 (term69 x z)). Qed.
Lemma lem1568074 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term236 x z.
Proof. exact (@lem1568073 x z (@lem1568070 x y z h1)). Qed.
Lemma lem1568075 (x : real) (z : real) : (term237 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1568076 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568077 (x : real) (z : real) : (term238 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1568076) (@lem1568075 x z)). Qed.
Lemma lem1568078 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568079 (x : real) (z : real) : (term236 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1568077 x z) (@lem1568078)). Qed.
Lemma lem1568080 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1568079 x z) (@lem1568074 x y z h1)). Qed.
Lemma lem1568082 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568083 : term229 = term230.
Proof. exact (@lem1568082 (NUMERAL 0) term195). Qed.
Lemma lem1568084 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568085 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568086 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568085 h1) (fun h1 : term230 = True => @lem1568084)). Qed.
Lemma lem1568087 : term230 = True.
Proof. exact (EQ_MP (@lem1568086) (@lem1568084)). Qed.
Lemma lem1568088 : term229 = True.
Proof. exact (TRANS (@lem1568083) (@lem1568087)). Qed.
Lemma lem1568089 : True = term229.
Proof. exact (SYM (@lem1568088)). Qed.
Lemma lem1568090 : term229.
Proof. exact (EQ_MP (@lem1568089) (@lem0)). Qed.
Lemma lem1568091 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term239 x z.
Proof. exact (conj (@lem1568090) (@lem1568059 x y z h1)). Qed.
Lemma lem1568093 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1568094 (x : real) (z : real) : term241 x z.
Proof. exact (@lem1568093 term235 (term50 x z)). Qed.
Lemma lem1568095 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term242 x z.
Proof. exact (@lem1568094 x z (@lem1568091 x y z h1)). Qed.
Lemma lem1568096 (x : real) (z : real) : (term243 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1568097 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568098 (x : real) (z : real) : (term244 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1568097) (@lem1568096 x z)). Qed.
Lemma lem1568099 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568100 (x : real) (z : real) : (term242 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1568098 x z) (@lem1568099)). Qed.
Lemma lem1568101 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term53 x z.
Proof. exact (EQ_MP (@lem1568100 x z) (@lem1568095 x y z h1)). Qed.
Lemma lem1568102 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term245 x z.
Proof. exact (conj (@lem1568101 x y z h1) (@lem1568080 x y z h1)). Qed.
Lemma lem1568104 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1568105 (x : real) (z : real) : term247 x z.
Proof. exact (@lem1568104 (term50 x z) (term69 x z)). Qed.
Lemma lem1568106 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term248 x z.
Proof. exact (@lem1568105 x z (@lem1568102 x y z h1)). Qed.
Lemma lem1568107 (x : real) (z : real) : (term249 x z) = (term250 x z).
Proof. exact (@lem1483480 x (term64 x) (term64 z) z). Qed.
Lemma lem1568108 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483442 term253 x). Qed.
Lemma lem1568110 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568111 : term255 = term46.
Proof. exact (@lem1568110 term195). Qed.
Lemma lem1568112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568113 : term256 = term257.
Proof. exact (MK_COMB (@lem1568112) (@lem1568111)). Qed.
Lemma lem1568114 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1568115 (x : real) : (term252 x) = (term258 x).
Proof. exact (MK_COMB (@lem1568113) (@lem1568114 x)). Qed.
Lemma lem1568116 (x : real) : (term251 x) = (term258 x).
Proof. exact (TRANS (@lem1568108 x) (@lem1568115 x)). Qed.
Lemma lem1568117 (x : real) : (term258 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1568118 (x : real) : (term251 x) = term46.
Proof. exact (TRANS (@lem1568116 x) (@lem1568117 x)). Qed.
Lemma lem1568119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1568120 (x : real) : (term259 x) = term260.
Proof. exact (MK_COMB (@lem1568119) (@lem1568118 x)). Qed.
Lemma lem1568121 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1568123 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568124 : term255 = term46.
Proof. exact (@lem1568123 term195). Qed.
Lemma lem1568125 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568126 : term256 = term257.
Proof. exact (MK_COMB (@lem1568125) (@lem1568124)). Qed.
Lemma lem1568127 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1568128 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1568126) (@lem1568127 z)). Qed.
Lemma lem1568129 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1568121 z) (@lem1568128 z)). Qed.
Lemma lem1568130 (z : real) : (term258 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1568131 (z : real) : (term261 z) = term46.
Proof. exact (TRANS (@lem1568129 z) (@lem1568130 z)). Qed.
Lemma lem1568132 (x : real) (z : real) : (term250 x z) = term262.
Proof. exact (MK_COMB (@lem1568120 x) (@lem1568131 z)). Qed.
Lemma lem1568133 (x : real) (z : real) : (term249 x z) = term262.
Proof. exact (TRANS (@lem1568107 x z) (@lem1568132 x z)). Qed.
Lemma lem1568134 : term262 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1568135 (x : real) (z : real) : (term249 x z) = term46.
Proof. exact (TRANS (@lem1568133 x z) (@lem1568134)). Qed.
Lemma lem1568136 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568137 (x : real) (z : real) : (term263 x z) = term264.
Proof. exact (MK_COMB (@lem1568136) (@lem1568135 x z)). Qed.
Lemma lem1568138 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568139 (x : real) (z : real) : (term248 x z) = term265.
Proof. exact (MK_COMB (@lem1568137 x z) (@lem1568138)). Qed.
Lemma lem1568140 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term265.
Proof. exact (EQ_MP (@lem1568139 x z) (@lem1568106 x y z h1)). Qed.
Lemma lem1568142 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568143 : term265 = term266.
Proof. exact (@lem1568142 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1568144 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1568145 : term265 = False.
Proof. exact (TRANS (@lem1568143) (@lem1568144)). Qed.
Lemma lem1568146 (x : real) (y : real) (z : real) (h1 : term207 x y z) : False.
Proof. exact (EQ_MP (@lem1568145) (@lem1568140 x y z h1)). Qed.
Lemma lem1568147 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term209 x y z.
Proof. exact (h1). Qed.
Lemma lem1568148 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term208 x y z.
Proof. exact (proj2 (@lem1568147 x y z h1)). Qed.
Lemma lem1568150 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term56 x y z.
Proof. exact (proj2 (@lem1568148 x y z h1)). Qed.
Lemma lem1568151 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term72 y z.
Proof. exact (proj1 (@lem1568148 x y z h1)). Qed.
Lemma lem1568152 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term53 y z.
Proof. exact (proj2 (@lem1568150 x y z h1)). Qed.
Lemma lem1568155 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568156 : term229 = term230.
Proof. exact (@lem1568155 (NUMERAL 0) term195). Qed.
Lemma lem1568157 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568158 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568159 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568158 h1) (fun h1 : term230 = True => @lem1568157)). Qed.
Lemma lem1568160 : term230 = True.
Proof. exact (EQ_MP (@lem1568159) (@lem1568157)). Qed.
Lemma lem1568161 : term229 = True.
Proof. exact (TRANS (@lem1568156) (@lem1568160)). Qed.
Lemma lem1568162 : True = term229.
Proof. exact (SYM (@lem1568161)). Qed.
Lemma lem1568163 : term229.
Proof. exact (EQ_MP (@lem1568162) (@lem0)). Qed.
Lemma lem1568164 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term232 y z.
Proof. exact (conj (@lem1568163) (@lem1568151 x y z h1)). Qed.
Lemma lem1568166 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1568167 (y : real) (z : real) : term234 y z.
Proof. exact (@lem1568166 term235 (term69 y z)). Qed.
Lemma lem1568168 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term236 y z.
Proof. exact (@lem1568167 y z (@lem1568164 x y z h1)). Qed.
Lemma lem1568169 (y : real) (z : real) : (term237 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1568170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568171 (y : real) (z : real) : (term238 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1568170) (@lem1568169 y z)). Qed.
Lemma lem1568172 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568173 (y : real) (z : real) : (term236 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1568171 y z) (@lem1568172)). Qed.
Lemma lem1568174 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1568173 y z) (@lem1568168 x y z h1)). Qed.
Lemma lem1568176 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568177 : term229 = term230.
Proof. exact (@lem1568176 (NUMERAL 0) term195). Qed.
Lemma lem1568178 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568179 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568180 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568179 h1) (fun h1 : term230 = True => @lem1568178)). Qed.
Lemma lem1568181 : term230 = True.
Proof. exact (EQ_MP (@lem1568180) (@lem1568178)). Qed.
Lemma lem1568182 : term229 = True.
Proof. exact (TRANS (@lem1568177) (@lem1568181)). Qed.
Lemma lem1568183 : True = term229.
Proof. exact (SYM (@lem1568182)). Qed.
Lemma lem1568184 : term229.
Proof. exact (EQ_MP (@lem1568183) (@lem0)). Qed.
Lemma lem1568185 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term239 y z.
Proof. exact (conj (@lem1568184) (@lem1568152 x y z h1)). Qed.
Lemma lem1568187 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1568188 (y : real) (z : real) : term241 y z.
Proof. exact (@lem1568187 term235 (term50 y z)). Qed.
Lemma lem1568189 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term242 y z.
Proof. exact (@lem1568188 y z (@lem1568185 x y z h1)). Qed.
Lemma lem1568190 (y : real) (z : real) : (term243 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1568191 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568192 (y : real) (z : real) : (term244 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1568191) (@lem1568190 y z)). Qed.
Lemma lem1568193 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568194 (y : real) (z : real) : (term242 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1568192 y z) (@lem1568193)). Qed.
Lemma lem1568195 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1568194 y z) (@lem1568189 x y z h1)). Qed.
Lemma lem1568196 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term245 y z.
Proof. exact (conj (@lem1568195 x y z h1) (@lem1568174 x y z h1)). Qed.
Lemma lem1568198 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1568199 (y : real) (z : real) : term247 y z.
Proof. exact (@lem1568198 (term50 y z) (term69 y z)). Qed.
Lemma lem1568200 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term248 y z.
Proof. exact (@lem1568199 y z (@lem1568196 x y z h1)). Qed.
Lemma lem1568201 (y : real) (z : real) : (term249 y z) = (term250 y z).
Proof. exact (@lem1483480 y (term64 y) (term64 z) z). Qed.
Lemma lem1568202 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483442 term253 y). Qed.
Lemma lem1568204 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568205 : term255 = term46.
Proof. exact (@lem1568204 term195). Qed.
Lemma lem1568206 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568207 : term256 = term257.
Proof. exact (MK_COMB (@lem1568206) (@lem1568205)). Qed.
Lemma lem1568208 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1568209 (y : real) : (term252 y) = (term258 y).
Proof. exact (MK_COMB (@lem1568207) (@lem1568208 y)). Qed.
Lemma lem1568210 (y : real) : (term251 y) = (term258 y).
Proof. exact (TRANS (@lem1568202 y) (@lem1568209 y)). Qed.
Lemma lem1568211 (y : real) : (term258 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1568212 (y : real) : (term251 y) = term46.
Proof. exact (TRANS (@lem1568210 y) (@lem1568211 y)). Qed.
Lemma lem1568213 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1568214 (y : real) : (term259 y) = term260.
Proof. exact (MK_COMB (@lem1568213) (@lem1568212 y)). Qed.
Lemma lem1568215 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1568217 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568218 : term255 = term46.
Proof. exact (@lem1568217 term195). Qed.
Lemma lem1568219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568220 : term256 = term257.
Proof. exact (MK_COMB (@lem1568219) (@lem1568218)). Qed.
Lemma lem1568221 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1568222 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1568220) (@lem1568221 z)). Qed.
Lemma lem1568223 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1568215 z) (@lem1568222 z)). Qed.
Lemma lem1568224 (z : real) : (term258 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1568225 (z : real) : (term261 z) = term46.
Proof. exact (TRANS (@lem1568223 z) (@lem1568224 z)). Qed.
Lemma lem1568226 (y : real) (z : real) : (term250 y z) = term262.
Proof. exact (MK_COMB (@lem1568214 y) (@lem1568225 z)). Qed.
Lemma lem1568227 (y : real) (z : real) : (term249 y z) = term262.
Proof. exact (TRANS (@lem1568201 y z) (@lem1568226 y z)). Qed.
Lemma lem1568228 : term262 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1568229 (y : real) (z : real) : (term249 y z) = term46.
Proof. exact (TRANS (@lem1568227 y z) (@lem1568228)). Qed.
Lemma lem1568230 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568231 (y : real) (z : real) : (term263 y z) = term264.
Proof. exact (MK_COMB (@lem1568230) (@lem1568229 y z)). Qed.
Lemma lem1568232 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568233 (y : real) (z : real) : (term248 y z) = term265.
Proof. exact (MK_COMB (@lem1568231 y z) (@lem1568232)). Qed.
Lemma lem1568234 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term265.
Proof. exact (EQ_MP (@lem1568233 y z) (@lem1568200 x y z h1)). Qed.
Lemma lem1568236 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568237 : term265 = term266.
Proof. exact (@lem1568236 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1568238 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1568239 : term265 = False.
Proof. exact (TRANS (@lem1568237) (@lem1568238)). Qed.
Lemma lem1568240 (x : real) (y : real) (z : real) (h1 : term209 x y z) : False.
Proof. exact (EQ_MP (@lem1568239) (@lem1568234 x y z h1)). Qed.
Lemma lem1568241 (x : real) (y : real) (z : real) (h1 : term211 x y z) : False.
Proof. exact (or_elim (@lem1568052 x y z h1) (fun h0 : term207 x y z => @lem1568146 x y z h0) (fun h0 : term209 x y z => @lem1568240 x y z h0)). Qed.
Lemma lem1568242 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term225 x y z.
Proof. exact (h1). Qed.
Lemma lem1568243 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term220 y x z.
Proof. exact (h1). Qed.
Lemma lem1568244 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term72 x z.
Proof. exact (proj2 (@lem1568243 y x z h1)). Qed.
Lemma lem1568245 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term56 x y z.
Proof. exact (proj1 (@lem1568243 y x z h1)). Qed.
Lemma lem1568247 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term53 x z.
Proof. exact (proj1 (@lem1568245 y x z h1)). Qed.
Lemma lem1568249 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568250 : term229 = term230.
Proof. exact (@lem1568249 (NUMERAL 0) term195). Qed.
Lemma lem1568251 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568252 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568253 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568252 h1) (fun h1 : term230 = True => @lem1568251)). Qed.
Lemma lem1568254 : term230 = True.
Proof. exact (EQ_MP (@lem1568253) (@lem1568251)). Qed.
Lemma lem1568255 : term229 = True.
Proof. exact (TRANS (@lem1568250) (@lem1568254)). Qed.
Lemma lem1568256 : True = term229.
Proof. exact (SYM (@lem1568255)). Qed.
Lemma lem1568257 : term229.
Proof. exact (EQ_MP (@lem1568256) (@lem0)). Qed.
Lemma lem1568258 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term232 x z.
Proof. exact (conj (@lem1568257) (@lem1568244 y x z h1)). Qed.
Lemma lem1568260 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1568261 (x : real) (z : real) : term234 x z.
Proof. exact (@lem1568260 term235 (term69 x z)). Qed.
Lemma lem1568262 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term236 x z.
Proof. exact (@lem1568261 x z (@lem1568258 y x z h1)). Qed.
Lemma lem1568263 (x : real) (z : real) : (term237 x z) = (term69 x z).
Proof. exact (@lem1483460 (term69 x z)). Qed.
Lemma lem1568264 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568265 (x : real) (z : real) : (term238 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1568264) (@lem1568263 x z)). Qed.
Lemma lem1568266 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568267 (x : real) (z : real) : (term236 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1568265 x z) (@lem1568266)). Qed.
Lemma lem1568268 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1568267 x z) (@lem1568262 y x z h1)). Qed.
Lemma lem1568270 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568271 : term229 = term230.
Proof. exact (@lem1568270 (NUMERAL 0) term195). Qed.
Lemma lem1568272 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568273 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568274 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568273 h1) (fun h1 : term230 = True => @lem1568272)). Qed.
Lemma lem1568275 : term230 = True.
Proof. exact (EQ_MP (@lem1568274) (@lem1568272)). Qed.
Lemma lem1568276 : term229 = True.
Proof. exact (TRANS (@lem1568271) (@lem1568275)). Qed.
Lemma lem1568277 : True = term229.
Proof. exact (SYM (@lem1568276)). Qed.
Lemma lem1568278 : term229.
Proof. exact (EQ_MP (@lem1568277) (@lem0)). Qed.
Lemma lem1568279 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term239 x z.
Proof. exact (conj (@lem1568278) (@lem1568247 y x z h1)). Qed.
Lemma lem1568281 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1568282 (x : real) (z : real) : term241 x z.
Proof. exact (@lem1568281 term235 (term50 x z)). Qed.
Lemma lem1568283 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term242 x z.
Proof. exact (@lem1568282 x z (@lem1568279 y x z h1)). Qed.
Lemma lem1568284 (x : real) (z : real) : (term243 x z) = (term50 x z).
Proof. exact (@lem1483460 (term50 x z)). Qed.
Lemma lem1568285 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568286 (x : real) (z : real) : (term244 x z) = (term52 x z).
Proof. exact (MK_COMB (@lem1568285) (@lem1568284 x z)). Qed.
Lemma lem1568287 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568288 (x : real) (z : real) : (term242 x z) = (term53 x z).
Proof. exact (MK_COMB (@lem1568286 x z) (@lem1568287)). Qed.
Lemma lem1568289 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term53 x z.
Proof. exact (EQ_MP (@lem1568288 x z) (@lem1568283 y x z h1)). Qed.
Lemma lem1568290 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term245 x z.
Proof. exact (conj (@lem1568289 y x z h1) (@lem1568268 y x z h1)). Qed.
Lemma lem1568292 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1568293 (x : real) (z : real) : term247 x z.
Proof. exact (@lem1568292 (term50 x z) (term69 x z)). Qed.
Lemma lem1568294 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term248 x z.
Proof. exact (@lem1568293 x z (@lem1568290 y x z h1)). Qed.
Lemma lem1568295 (x : real) (z : real) : (term249 x z) = (term250 x z).
Proof. exact (@lem1483480 x (term64 x) (term64 z) z). Qed.
Lemma lem1568296 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483442 term253 x). Qed.
Lemma lem1568298 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568299 : term255 = term46.
Proof. exact (@lem1568298 term195). Qed.
Lemma lem1568300 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568301 : term256 = term257.
Proof. exact (MK_COMB (@lem1568300) (@lem1568299)). Qed.
Lemma lem1568302 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1568303 (x : real) : (term252 x) = (term258 x).
Proof. exact (MK_COMB (@lem1568301) (@lem1568302 x)). Qed.
Lemma lem1568304 (x : real) : (term251 x) = (term258 x).
Proof. exact (TRANS (@lem1568296 x) (@lem1568303 x)). Qed.
Lemma lem1568305 (x : real) : (term258 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1568306 (x : real) : (term251 x) = term46.
Proof. exact (TRANS (@lem1568304 x) (@lem1568305 x)). Qed.
Lemma lem1568307 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1568308 (x : real) : (term259 x) = term260.
Proof. exact (MK_COMB (@lem1568307) (@lem1568306 x)). Qed.
Lemma lem1568309 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1568311 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568312 : term255 = term46.
Proof. exact (@lem1568311 term195). Qed.
Lemma lem1568313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568314 : term256 = term257.
Proof. exact (MK_COMB (@lem1568313) (@lem1568312)). Qed.
Lemma lem1568315 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1568316 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1568314) (@lem1568315 z)). Qed.
Lemma lem1568317 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1568309 z) (@lem1568316 z)). Qed.
Lemma lem1568318 (z : real) : (term258 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1568319 (z : real) : (term261 z) = term46.
Proof. exact (TRANS (@lem1568317 z) (@lem1568318 z)). Qed.
Lemma lem1568320 (x : real) (z : real) : (term250 x z) = term262.
Proof. exact (MK_COMB (@lem1568308 x) (@lem1568319 z)). Qed.
Lemma lem1568321 (x : real) (z : real) : (term249 x z) = term262.
Proof. exact (TRANS (@lem1568295 x z) (@lem1568320 x z)). Qed.
Lemma lem1568322 : term262 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1568323 (x : real) (z : real) : (term249 x z) = term46.
Proof. exact (TRANS (@lem1568321 x z) (@lem1568322)). Qed.
Lemma lem1568324 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568325 (x : real) (z : real) : (term263 x z) = term264.
Proof. exact (MK_COMB (@lem1568324) (@lem1568323 x z)). Qed.
Lemma lem1568326 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568327 (x : real) (z : real) : (term248 x z) = term265.
Proof. exact (MK_COMB (@lem1568325 x z) (@lem1568326)). Qed.
Lemma lem1568328 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term265.
Proof. exact (EQ_MP (@lem1568327 x z) (@lem1568294 y x z h1)). Qed.
Lemma lem1568330 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568331 : term265 = term266.
Proof. exact (@lem1568330 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1568332 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1568333 : term265 = False.
Proof. exact (TRANS (@lem1568331) (@lem1568332)). Qed.
Lemma lem1568334 (y : real) (x : real) (z : real) (h1 : term220 y x z) : False.
Proof. exact (EQ_MP (@lem1568333) (@lem1568328 y x z h1)). Qed.
Lemma lem1568335 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1568336 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 y z.
Proof. exact (proj2 (@lem1568335 x y z h1)). Qed.
Lemma lem1568337 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 x y z.
Proof. exact (proj1 (@lem1568335 x y z h1)). Qed.
Lemma lem1568338 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term53 y z.
Proof. exact (proj2 (@lem1568337 x y z h1)). Qed.
Lemma lem1568341 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568342 : term229 = term230.
Proof. exact (@lem1568341 (NUMERAL 0) term195). Qed.
Lemma lem1568343 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568344 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568345 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568344 h1) (fun h1 : term230 = True => @lem1568343)). Qed.
Lemma lem1568346 : term230 = True.
Proof. exact (EQ_MP (@lem1568345) (@lem1568343)). Qed.
Lemma lem1568347 : term229 = True.
Proof. exact (TRANS (@lem1568342) (@lem1568346)). Qed.
Lemma lem1568348 : True = term229.
Proof. exact (SYM (@lem1568347)). Qed.
Lemma lem1568349 : term229.
Proof. exact (EQ_MP (@lem1568348) (@lem0)). Qed.
Lemma lem1568350 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term232 y z.
Proof. exact (conj (@lem1568349) (@lem1568336 x y z h1)). Qed.
Lemma lem1568352 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1568353 (y : real) (z : real) : term234 y z.
Proof. exact (@lem1568352 term235 (term69 y z)). Qed.
Lemma lem1568354 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term236 y z.
Proof. exact (@lem1568353 y z (@lem1568350 x y z h1)). Qed.
Lemma lem1568355 (y : real) (z : real) : (term237 y z) = (term69 y z).
Proof. exact (@lem1483460 (term69 y z)). Qed.
Lemma lem1568356 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1568357 (y : real) (z : real) : (term238 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1568356) (@lem1568355 y z)). Qed.
Lemma lem1568358 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568359 (y : real) (z : real) : (term236 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1568357 y z) (@lem1568358)). Qed.
Lemma lem1568360 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1568359 y z) (@lem1568354 x y z h1)). Qed.
Lemma lem1568362 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568363 : term229 = term230.
Proof. exact (@lem1568362 (NUMERAL 0) term195). Qed.
Lemma lem1568364 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1568365 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1568366 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1568365 h1) (fun h1 : term230 = True => @lem1568364)). Qed.
Lemma lem1568367 : term230 = True.
Proof. exact (EQ_MP (@lem1568366) (@lem1568364)). Qed.
Lemma lem1568368 : term229 = True.
Proof. exact (TRANS (@lem1568363) (@lem1568367)). Qed.
Lemma lem1568369 : True = term229.
Proof. exact (SYM (@lem1568368)). Qed.
Lemma lem1568370 : term229.
Proof. exact (EQ_MP (@lem1568369) (@lem0)). Qed.
Lemma lem1568371 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term239 y z.
Proof. exact (conj (@lem1568370) (@lem1568338 x y z h1)). Qed.
Lemma lem1568373 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1568374 (y : real) (z : real) : term241 y z.
Proof. exact (@lem1568373 term235 (term50 y z)). Qed.
Lemma lem1568375 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term242 y z.
Proof. exact (@lem1568374 y z (@lem1568371 x y z h1)). Qed.
Lemma lem1568376 (y : real) (z : real) : (term243 y z) = (term50 y z).
Proof. exact (@lem1483460 (term50 y z)). Qed.
Lemma lem1568377 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568378 (y : real) (z : real) : (term244 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1568377) (@lem1568376 y z)). Qed.
Lemma lem1568379 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568380 (y : real) (z : real) : (term242 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1568378 y z) (@lem1568379)). Qed.
Lemma lem1568381 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1568380 y z) (@lem1568375 x y z h1)). Qed.
Lemma lem1568382 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term245 y z.
Proof. exact (conj (@lem1568381 x y z h1) (@lem1568360 x y z h1)). Qed.
Lemma lem1568384 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1568385 (y : real) (z : real) : term247 y z.
Proof. exact (@lem1568384 (term50 y z) (term69 y z)). Qed.
Lemma lem1568386 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term248 y z.
Proof. exact (@lem1568385 y z (@lem1568382 x y z h1)). Qed.
Lemma lem1568387 (y : real) (z : real) : (term249 y z) = (term250 y z).
Proof. exact (@lem1483480 y (term64 y) (term64 z) z). Qed.
Lemma lem1568388 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483442 term253 y). Qed.
Lemma lem1568390 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568391 : term255 = term46.
Proof. exact (@lem1568390 term195). Qed.
Lemma lem1568392 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568393 : term256 = term257.
Proof. exact (MK_COMB (@lem1568392) (@lem1568391)). Qed.
Lemma lem1568394 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1568395 (y : real) : (term252 y) = (term258 y).
Proof. exact (MK_COMB (@lem1568393) (@lem1568394 y)). Qed.
Lemma lem1568396 (y : real) : (term251 y) = (term258 y).
Proof. exact (TRANS (@lem1568388 y) (@lem1568395 y)). Qed.
Lemma lem1568397 (y : real) : (term258 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1568398 (y : real) : (term251 y) = term46.
Proof. exact (TRANS (@lem1568396 y) (@lem1568397 y)). Qed.
Lemma lem1568399 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1568400 (y : real) : (term259 y) = term260.
Proof. exact (MK_COMB (@lem1568399) (@lem1568398 y)). Qed.
Lemma lem1568401 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1568403 (m : nat) : (term254 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1568404 : term255 = term46.
Proof. exact (@lem1568403 term195). Qed.
Lemma lem1568405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1568406 : term256 = term257.
Proof. exact (MK_COMB (@lem1568405) (@lem1568404)). Qed.
Lemma lem1568407 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1568408 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1568406) (@lem1568407 z)). Qed.
Lemma lem1568409 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1568401 z) (@lem1568408 z)). Qed.
Lemma lem1568410 (z : real) : (term258 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1568411 (z : real) : (term261 z) = term46.
Proof. exact (TRANS (@lem1568409 z) (@lem1568410 z)). Qed.
Lemma lem1568412 (y : real) (z : real) : (term250 y z) = term262.
Proof. exact (MK_COMB (@lem1568400 y) (@lem1568411 z)). Qed.
Lemma lem1568413 (y : real) (z : real) : (term249 y z) = term262.
Proof. exact (TRANS (@lem1568387 y z) (@lem1568412 y z)). Qed.
Lemma lem1568414 : term262 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1568415 (y : real) (z : real) : (term249 y z) = term46.
Proof. exact (TRANS (@lem1568413 y z) (@lem1568414)). Qed.
Lemma lem1568416 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1568417 (y : real) (z : real) : (term263 y z) = term264.
Proof. exact (MK_COMB (@lem1568416) (@lem1568415 y z)). Qed.
Lemma lem1568418 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1568419 (y : real) (z : real) : (term248 y z) = term265.
Proof. exact (MK_COMB (@lem1568417 y z) (@lem1568418)). Qed.
Lemma lem1568420 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term265.
Proof. exact (EQ_MP (@lem1568419 y z) (@lem1568386 x y z h1)). Qed.
Lemma lem1568422 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1568423 : term265 = term266.
Proof. exact (@lem1568422 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1568424 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1568425 : term265 = False.
Proof. exact (TRANS (@lem1568423) (@lem1568424)). Qed.
Lemma lem1568426 (x : real) (y : real) (z : real) (h1 : term222 x y z) : False.
Proof. exact (EQ_MP (@lem1568425) (@lem1568420 x y z h1)). Qed.
Lemma lem1568427 (x : real) (y : real) (z : real) (h1 : term225 x y z) : False.
Proof. exact (or_elim (@lem1568242 x y z h1) (fun h0 : term220 y x z => @lem1568334 y x z h0) (fun h0 : term222 x y z => @lem1568426 x y z h0)). Qed.
Lemma lem1568428 (x : real) (y : real) (z : real) (h1 : term227 x y z) : False.
Proof. exact (or_elim (@lem1568051 x y z h1) (fun h0 : term211 x y z => @lem1568241 x y z h0) (fun h0 : term225 x y z => @lem1568427 x y z h0)). Qed.
Lemma lem1568429 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term162 x y z.
Proof. exact (h1). Qed.
Lemma lem1568430 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term227 x y z.
Proof. exact (EQ_MP (@lem1568050 x y z) (@lem1568429 x y z h1)). Qed.
Lemma lem1568431 (x : real) (y : real) (z : real) (h1 : term162 x y z) : (term227 x y z) = False.
Proof. exact (prop_ext (fun h2 : term227 x y z => @lem1568428 x y z h2) (fun h2 : False => @lem1568430 x y z h1)). Qed.
Lemma lem1568432 (x : real) (y : real) (z : real) (h1 : term162 x y z) : False.
Proof. exact (EQ_MP (@lem1568431 x y z h1) (@lem1568430 x y z h1)). Qed.
Lemma lem1568433 (x : real) (y : real) (h1 : term164 x y) : term164 x y.
Proof. exact (h1). Qed.
Lemma lem1568434 (x : real) (y : real) (h1 : term164 x y) : False.
Proof. exact (ex_elim (@lem1568433 x y h1) (fun z : real => fun h0 : term163 x y z => @lem1568432 x y z h0)). Qed.
Lemma lem1568435 (x : real) (h1 : term166 x) : term166 x.
Proof. exact (h1). Qed.
Lemma lem1568436 (x : real) (h1 : term166 x) : False.
Proof. exact (ex_elim (@lem1568435 x h1) (fun y : real => fun h0 : term165 x y => @lem1568434 x y h0)). Qed.
Lemma lem1568437 (h1 : term168) : term168.
Proof. exact (h1). Qed.
Lemma lem1568438 (h1 : term168) : False.
Proof. exact (ex_elim (@lem1568437 h1) (fun x : real => fun h0 : term167 x => @lem1568436 x h0)). Qed.
Lemma lem1568439 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1568440 (h1 : term32) : term168.
Proof. exact (EQ_MP (@lem1567730) (@lem1568439 h1)). Qed.
Lemma lem1568441 (h1 : term32) : term168 = False.
Proof. exact (prop_ext (fun h2 : term168 => @lem1568438 h2) (fun h2 : False => @lem1568440 h1)). Qed.
Lemma lem1568442 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1568441 h1) (@lem1568440 h1)). Qed.
Lemma lem1568443 : term267.
Proof. exact (fun h0 : term32 => @lem1568442 h0). Qed.
Lemma lem1568444 : term268.
Proof. exact (@lem1386578 term269). Qed.
Lemma lem1568445 : term269.
Proof. exact (@lem1568444 (@lem1568443)). Qed.
