Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_BETWEEN_term_abbrevs.
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
Require Import thm1367770_spec.
Require Import thm1386578_spec.
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
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
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
Lemma lem1536922 (y : real) (x : real) (d : real) : (term0 y x d) = (term1 y x d).
Proof. exact (@lem17045 (term2 x d y) (term3 y x d)). Qed.
Lemma lem1536927 (d : real) : (term4 d) = (term4 d).
Proof. exact (eq_refl (term4 d)). Qed.
Lemma lem1536928 (y : real) (x : real) (d : real) : (term5 y x d) = (term6 y x d).
Proof. exact (MK_COMB (@lem1536927 d) (@lem1536922 y x d)). Qed.
Lemma lem1536929 (y : real) (x : real) (d : real) : (term7 y x d) = (term5 y x d).
Proof. exact (@lem17045 (term8 d) (term9 y x d)). Qed.
Lemma lem1536930 (y : real) (x : real) (d : real) : (term7 y x d) = (term6 y x d).
Proof. exact (TRANS (@lem1536929 y x d) (@lem1536928 y x d)). Qed.
Lemma lem1536935 (y : real) (x : real) (d : real) : (term10 y x d) = (term10 y x d).
Proof. exact (eq_refl (term10 y x d)). Qed.
Lemma lem1536936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1536937 (y : real) (x : real) (d : real) : (term11 y x d) = (term12 y x d).
Proof. exact (MK_COMB (@lem1536936) (@lem1536930 y x d)). Qed.
Lemma lem1536938 (y : real) (x : real) (d : real) : (term13 y x d) = (term14 y x d).
Proof. exact (MK_COMB (@lem1536937 y x d) (@lem1536935 y x d)). Qed.
Lemma lem1536943 (y : real) (x : real) (d : real) : (term15 y x d) = (term15 y x d).
Proof. exact (eq_refl (term15 y x d)). Qed.
Lemma lem1536944 (y : real) (x : real) (d : real) : (term16 y x d) = (term17 y x d).
Proof. exact (MK_COMB (@lem1536943 y x d) (@lem1536938 y x d)). Qed.
Lemma lem1536945 (y : real) (x : real) (d : real) : (term18 y x d) = (term16 y x d).
Proof. exact (@lem17646 (term19 y x d) (term10 y x d)). Qed.
Lemma lem1536946 (y : real) (x : real) (d : real) : (term18 y x d) = (term17 y x d).
Proof. exact (TRANS (@lem1536945 y x d) (@lem1536944 y x d)). Qed.
Lemma lem1536947 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1536948 (y : real) (x : real) : (term22 y x) = (term23 y x).
Proof. exact (@lem1536947 (term24 y x)). Qed.
Lemma lem1536949 (y : real) (x : real) (d : real) : (term25 y x d) = ((term19 y x d) = (term10 y x d)).
Proof. exact (eq_refl (term25 y x d)). Qed.
Lemma lem1536950 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1536951 (y : real) (x : real) (d : real) : (term26 y x d) = (term18 y x d).
Proof. exact (MK_COMB (@lem1536950) (@lem1536949 y x d)). Qed.
Lemma lem1536952 (y : real) (x : real) (d : real) : (term26 y x d) = (term17 y x d).
Proof. exact (TRANS (@lem1536951 y x d) (@lem1536946 y x d)). Qed.
Lemma lem1536953 (y : real) (x : real) : (term27 y x) = (term28 y x).
Proof. exact (fun_ext (fun d : real => @lem1536952 y x d)). Qed.
Lemma lem1536954 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536955 (y : real) (x : real) : (term23 y x) = (term29 y x).
Proof. exact (MK_COMB (@lem1536954) (@lem1536953 y x)). Qed.
Lemma lem1536956 (y : real) (x : real) : (term22 y x) = (term29 y x).
Proof. exact (TRANS (@lem1536948 y x) (@lem1536955 y x)). Qed.
Lemma lem1536957 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1536958 (x : real) : (term30 x) = (term31 x).
Proof. exact (@lem1536957 (term32 x)). Qed.
Lemma lem1536959 (y : real) (x : real) : (term33 x y) = (term34 y x).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1536960 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1536961 (y : real) (x : real) : (term35 x y) = (term22 y x).
Proof. exact (MK_COMB (@lem1536960) (@lem1536959 y x)). Qed.
Lemma lem1536962 (y : real) (x : real) : (term35 x y) = (term29 y x).
Proof. exact (TRANS (@lem1536961 y x) (@lem1536956 y x)). Qed.
Lemma lem1536963 (x : real) : (term36 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1536962 y x)). Qed.
Lemma lem1536964 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536965 (x : real) : (term31 x) = (term38 x).
Proof. exact (MK_COMB (@lem1536964) (@lem1536963 x)). Qed.
Lemma lem1536966 (x : real) : (term30 x) = (term38 x).
Proof. exact (TRANS (@lem1536958 x) (@lem1536965 x)). Qed.
Lemma lem1536967 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1536968 : term39 = term40.
Proof. exact (@lem1536967 term41). Qed.
Lemma lem1536969 (x : real) : (term42 x) = (term43 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1536970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1536971 (x : real) : (term44 x) = (term30 x).
Proof. exact (MK_COMB (@lem1536970) (@lem1536969 x)). Qed.
Lemma lem1536972 (x : real) : (term44 x) = (term38 x).
Proof. exact (TRANS (@lem1536971 x) (@lem1536966 x)). Qed.
Lemma lem1536973 : term45 = term46.
Proof. exact (fun_ext (fun x : real => @lem1536972 x)). Qed.
Lemma lem1536974 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1536975 : term40 = term47.
Proof. exact (MK_COMB (@lem1536974) (@lem1536973)). Qed.
Lemma lem1536977 : term39 = term47.
Proof. exact (TRANS (@lem1536968) (@lem1536975)). Qed.
Lemma lem1537014 (y : real) (x : real) (d : real) : (term17 y x d) = (term17 y x d).
Proof. exact (eq_refl (term17 y x d)). Qed.
Lemma lem1537015 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (fun_ext (fun d : real => @lem1537014 y x d)). Qed.
Lemma lem1537016 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537017 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (MK_COMB (@lem1537016) (@lem1537015 y x)). Qed.
Lemma lem1537018 (x : real) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1537017 y x)). Qed.
Lemma lem1537019 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537020 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1537019) (@lem1537018 x)). Qed.
Lemma lem1537021 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1537020 x)). Qed.
Lemma lem1537022 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537023 : term47 = term47.
Proof. exact (MK_COMB (@lem1537022) (@lem1537021)). Qed.
Lemma lem1537024 : term39 = term47.
Proof. exact (TRANS (@lem1536977) (@lem1537023)). Qed.
Lemma lem1537025 (d : real) : (term8 d) = (term48 d).
Proof. exact (@lem1483521 d term49). Qed.
Lemma lem1537031 (d : real) : (term50 d) = (term51 d).
Proof. exact (@lem1483519 d term49). Qed.
Lemma lem1537033 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1537034 : term53 = term49.
Proof. exact (@lem1537033 term54). Qed.
Lemma lem1537035 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1537036 (d : real) : (term51 d) = (term55 d).
Proof. exact (MK_COMB (@lem1537035 d) (@lem1537034)). Qed.
Lemma lem1537037 (d : real) : (term55 d) = d.
Proof. exact (@lem1483450 d). Qed.
Lemma lem1537038 (d : real) : (term51 d) = d.
Proof. exact (TRANS (@lem1537036 d) (@lem1537037 d)). Qed.
Lemma lem1537040 (d : real) : (term50 d) = d.
Proof. exact (TRANS (@lem1537031 d) (@lem1537038 d)). Qed.
Lemma lem1537041 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537042 (d : real) : (term56 d) = (real_gt d).
Proof. exact (MK_COMB (@lem1537041) (@lem1537040 d)). Qed.
Lemma lem1537043 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537044 (d : real) : (term48 d) = (term57 d).
Proof. exact (MK_COMB (@lem1537042 d) (@lem1537043)). Qed.
Lemma lem1537045 (d : real) : (term8 d) = (term57 d).
Proof. exact (TRANS (@lem1537025 d) (@lem1537044 d)). Qed.
Lemma lem1537046 (y : real) (x : real) (d : real) : (term2 x d y) = (term58 y x d).
Proof. exact (@lem1483521 y (real_sub x d)). Qed.
Lemma lem1537052 (x : real) (d : real) : (real_sub x d) = (term59 x d).
Proof. exact (@lem1483519 x d). Qed.
Lemma lem1537057 (d : real) (x : real) : (term59 x d) = (term60 d x).
Proof. exact (@lem1483488 (term61 d) x). Qed.
Lemma lem1537059 (d : real) (x : real) : (real_sub x d) = (term60 d x).
Proof. exact (TRANS (@lem1537052 x d) (@lem1537057 d x)). Qed.
Lemma lem1537062 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1537063 (y : real) (d : real) (x : real) : (term62 y x d) = (term63 y d x).
Proof. exact (MK_COMB (@lem1537062 y) (@lem1537059 d x)). Qed.
Lemma lem1537064 (y : real) (d : real) (x : real) : (term63 y d x) = (term64 y d x).
Proof. exact (@lem1483519 y (term60 d x)). Qed.
Lemma lem1537065 (d : real) (x : real) : (term65 d x) = (term66 d x).
Proof. exact (@lem1483508 (term61 d) term67 x). Qed.
Lemma lem1537066 (x : real) : (term61 x) = (term61 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1537067 (d : real) : (term68 d) = (term69 d).
Proof. exact (@lem1483476 term67 term67 d). Qed.
Lemma lem1537069 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1537070 : term72 = term73.
Proof. exact (@lem1537069 term54 term54). Qed.
Lemma lem1537071 : (term74 = (BIT1 0)) = (term75 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1537072 : term75 = term54.
Proof. exact (EQ_MP (@lem1537071) (@lem940073)). Qed.
Lemma lem1537073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1537074 : term73 = term76.
Proof. exact (MK_COMB (@lem1537073) (@lem1537072)). Qed.
Lemma lem1537075 : term72 = term76.
Proof. exact (TRANS (@lem1537070) (@lem1537074)). Qed.
Lemma lem1537076 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1537077 : term77 = term78.
Proof. exact (MK_COMB (@lem1537076) (@lem1537075)). Qed.
Lemma lem1537078 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1537079 (d : real) : (term69 d) = (term79 d).
Proof. exact (MK_COMB (@lem1537077) (@lem1537078 d)). Qed.
Lemma lem1537080 (d : real) : (term68 d) = (term79 d).
Proof. exact (TRANS (@lem1537067 d) (@lem1537079 d)). Qed.
Lemma lem1537081 (d : real) : (term79 d) = d.
Proof. exact (@lem1483436 d). Qed.
Lemma lem1537082 (d : real) : (term68 d) = d.
Proof. exact (TRANS (@lem1537080 d) (@lem1537081 d)). Qed.
Lemma lem1537083 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1537084 (d : real) : (term80 d) = (real_add d).
Proof. exact (MK_COMB (@lem1537083) (@lem1537082 d)). Qed.
Lemma lem1537085 (d : real) (x : real) : (term66 d x) = (term59 d x).
Proof. exact (MK_COMB (@lem1537084 d) (@lem1537066 x)). Qed.
Lemma lem1537086 (d : real) (x : real) : (term65 d x) = (term59 d x).
Proof. exact (TRANS (@lem1537065 d x) (@lem1537085 d x)). Qed.
Lemma lem1537087 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1537088 (y : real) (d : real) (x : real) : (term64 y d x) = (term81 y d x).
Proof. exact (MK_COMB (@lem1537087 y) (@lem1537086 d x)). Qed.
Lemma lem1537089 (d : real) (y : real) (x : real) : (term81 y d x) = (term81 d y x).
Proof. exact (@lem1483484 d y (term61 x)). Qed.
Lemma lem1537090 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1537091 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1537092 (d : real) (x : real) (y : real) : (term81 d y x) = (term82 d x y).
Proof. exact (MK_COMB (@lem1537091 d) (@lem1537090 x y)). Qed.
Lemma lem1537093 (d : real) (x : real) (y : real) : (term81 y d x) = (term82 d x y).
Proof. exact (TRANS (@lem1537089 d y x) (@lem1537092 d x y)). Qed.
Lemma lem1537094 (d : real) (x : real) (y : real) : (term64 y d x) = (term82 d x y).
Proof. exact (TRANS (@lem1537088 y d x) (@lem1537093 d x y)). Qed.
Lemma lem1537095 (d : real) (x : real) (y : real) : (term63 y d x) = (term82 d x y).
Proof. exact (TRANS (@lem1537064 y d x) (@lem1537094 d x y)). Qed.
Lemma lem1537096 (d : real) (x : real) (y : real) : (term62 y x d) = (term82 d x y).
Proof. exact (TRANS (@lem1537063 y d x) (@lem1537095 d x y)). Qed.
Lemma lem1537097 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537098 (d : real) (x : real) (y : real) : (term83 y x d) = (term84 d x y).
Proof. exact (MK_COMB (@lem1537097) (@lem1537096 d x y)). Qed.
Lemma lem1537099 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537100 (d : real) (x : real) (y : real) : (term58 y x d) = (term85 d x y).
Proof. exact (MK_COMB (@lem1537098 d x y) (@lem1537099)). Qed.
Lemma lem1537101 (d : real) (x : real) (y : real) : (term2 x d y) = (term85 d x y).
Proof. exact (TRANS (@lem1537046 y x d) (@lem1537100 d x y)). Qed.
Lemma lem1537102 (x : real) (d : real) (y : real) : (term3 y x d) = (term86 x d y).
Proof. exact (@lem1483521 (real_add x d) y). Qed.
Lemma lem1537103 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1537110 (d : real) (x : real) : (real_add x d) = (real_add d x).
Proof. exact (@lem1483488 d x). Qed.
Lemma lem1537111 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1537112 (d : real) (x : real) : (term87 x d) = (term87 d x).
Proof. exact (MK_COMB (@lem1537111) (@lem1537110 d x)). Qed.
Lemma lem1537113 (d : real) (x : real) (y : real) : (term88 x d y) = (term88 d x y).
Proof. exact (MK_COMB (@lem1537112 d x) (@lem1537103 y)). Qed.
Lemma lem1537114 (d : real) (x : real) (y : real) : (term88 d x y) = (term89 d x y).
Proof. exact (@lem1483519 (real_add d x) y). Qed.
Lemma lem1537123 (d : real) (x : real) (y : real) : (term89 d x y) = (term81 d x y).
Proof. exact (@lem1483482 d x (term61 y)). Qed.
Lemma lem1537124 (d : real) (x : real) (y : real) : (term88 d x y) = (term81 d x y).
Proof. exact (TRANS (@lem1537114 d x y) (@lem1537123 d x y)). Qed.
Lemma lem1537125 (d : real) (x : real) (y : real) : (term88 x d y) = (term81 d x y).
Proof. exact (TRANS (@lem1537113 d x y) (@lem1537124 d x y)). Qed.
Lemma lem1537126 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537127 (d : real) (x : real) (y : real) : (term90 x d y) = (term91 d x y).
Proof. exact (MK_COMB (@lem1537126) (@lem1537125 d x y)). Qed.
Lemma lem1537128 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537129 (d : real) (x : real) (y : real) : (term86 x d y) = (term92 d x y).
Proof. exact (MK_COMB (@lem1537127 d x y) (@lem1537128)). Qed.
Lemma lem1537130 (d : real) (x : real) (y : real) : (term3 y x d) = (term92 d x y).
Proof. exact (TRANS (@lem1537102 x d y) (@lem1537129 d x y)). Qed.
Lemma lem1537131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1537132 (d : real) (x : real) (y : real) : (term93 x d y) = (term94 d x y).
Proof. exact (MK_COMB (@lem1537131) (@lem1537101 d x y)). Qed.
Lemma lem1537133 (d : real) (x : real) (y : real) : (term9 y x d) = (term95 d x y).
Proof. exact (MK_COMB (@lem1537132 d x y) (@lem1537130 d x y)). Qed.
Lemma lem1537134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1537135 (d : real) : (term96 d) = (term97 d).
Proof. exact (MK_COMB (@lem1537134) (@lem1537045 d)). Qed.
Lemma lem1537136 (d : real) (x : real) (y : real) : (term19 y x d) = (term98 d x y).
Proof. exact (MK_COMB (@lem1537135 d) (@lem1537133 d x y)). Qed.
Lemma lem1537137 (y : real) (x : real) (d : real) : (term99 y x d) = (term100 y x d).
Proof. exact (@lem1483531 (term101 y x) d). Qed.
Lemma lem1537143 (y : real) (x : real) (d : real) : (term102 y x d) = (term103 y x d).
Proof. exact (@lem1483519 (term101 y x) d). Qed.
Lemma lem1537148 (d : real) (y : real) (x : real) : (term103 y x d) = (term104 d y x).
Proof. exact (@lem1483488 (term61 d) (term101 y x)). Qed.
Lemma lem1537150 (d : real) (y : real) (x : real) : (term102 y x d) = (term104 d y x).
Proof. exact (TRANS (@lem1537143 y x d) (@lem1537148 d y x)). Qed.
Lemma lem1537151 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1537152 (d : real) (y : real) (x : real) : (term105 y x d) = (term106 d y x).
Proof. exact (MK_COMB (@lem1537151) (@lem1537150 d y x)). Qed.
Lemma lem1537153 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537154 (d : real) (y : real) (x : real) : (term100 y x d) = (term107 d y x).
Proof. exact (MK_COMB (@lem1537152 d y x) (@lem1537153)). Qed.
Lemma lem1537155 (d : real) (y : real) (x : real) : (term99 y x d) = (term107 d y x).
Proof. exact (TRANS (@lem1537137 y x d) (@lem1537154 d y x)). Qed.
Lemma lem1537156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1537157 (d : real) (x : real) (y : real) : (term108 y x d) = (term109 d x y).
Proof. exact (MK_COMB (@lem1537156) (@lem1537136 d x y)). Qed.
Lemma lem1537158 (d : real) (y : real) (x : real) : (term110 y x d) = (term111 d y x).
Proof. exact (MK_COMB (@lem1537157 d x y) (@lem1537155 d y x)). Qed.
Lemma lem1537159 (d : real) : (term112 d) = (term113 d).
Proof. exact (@lem1483531 term49 d). Qed.
Lemma lem1537165 (d : real) : (term114 d) = (term115 d).
Proof. exact (@lem1483519 term49 d). Qed.
Lemma lem1537170 (d : real) : (term115 d) = (term61 d).
Proof. exact (@lem1483448 (term61 d)). Qed.
Lemma lem1537172 (d : real) : (term114 d) = (term61 d).
Proof. exact (TRANS (@lem1537165 d) (@lem1537170 d)). Qed.
Lemma lem1537173 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1537174 (d : real) : (term116 d) = (term117 d).
Proof. exact (MK_COMB (@lem1537173) (@lem1537172 d)). Qed.
Lemma lem1537175 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537176 (d : real) : (term113 d) = (term118 d).
Proof. exact (MK_COMB (@lem1537174 d) (@lem1537175)). Qed.
Lemma lem1537177 (d : real) : (term112 d) = (term118 d).
Proof. exact (TRANS (@lem1537159 d) (@lem1537176 d)). Qed.
Lemma lem1537178 (x : real) (d : real) (y : real) : (term119 x d y) = (term120 x d y).
Proof. exact (@lem1483531 (real_sub x d) y). Qed.
Lemma lem1537179 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1537185 (x : real) (d : real) : (real_sub x d) = (term59 x d).
Proof. exact (@lem1483519 x d). Qed.
Lemma lem1537190 (d : real) (x : real) : (term59 x d) = (term60 d x).
Proof. exact (@lem1483488 (term61 d) x). Qed.
Lemma lem1537192 (d : real) (x : real) : (real_sub x d) = (term60 d x).
Proof. exact (TRANS (@lem1537185 x d) (@lem1537190 d x)). Qed.
Lemma lem1537193 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1537194 (d : real) (x : real) : (term121 x d) = (term122 d x).
Proof. exact (MK_COMB (@lem1537193) (@lem1537192 d x)). Qed.
Lemma lem1537195 (d : real) (x : real) (y : real) : (term123 x d y) = (term124 d x y).
Proof. exact (MK_COMB (@lem1537194 d x) (@lem1537179 y)). Qed.
Lemma lem1537196 (d : real) (x : real) (y : real) : (term124 d x y) = (term125 d x y).
Proof. exact (@lem1483519 (term60 d x) y). Qed.
Lemma lem1537205 (d : real) (x : real) (y : real) : (term125 d x y) = (term126 d x y).
Proof. exact (@lem1483482 (term61 d) x (term61 y)). Qed.
Lemma lem1537206 (d : real) (x : real) (y : real) : (term124 d x y) = (term126 d x y).
Proof. exact (TRANS (@lem1537196 d x y) (@lem1537205 d x y)). Qed.
Lemma lem1537207 (d : real) (x : real) (y : real) : (term123 x d y) = (term126 d x y).
Proof. exact (TRANS (@lem1537195 d x y) (@lem1537206 d x y)). Qed.
Lemma lem1537208 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1537209 (d : real) (x : real) (y : real) : (term127 x d y) = (term128 d x y).
Proof. exact (MK_COMB (@lem1537208) (@lem1537207 d x y)). Qed.
Lemma lem1537210 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537211 (d : real) (x : real) (y : real) : (term120 x d y) = (term129 d x y).
Proof. exact (MK_COMB (@lem1537209 d x y) (@lem1537210)). Qed.
Lemma lem1537212 (d : real) (x : real) (y : real) : (term119 x d y) = (term129 d x y).
Proof. exact (TRANS (@lem1537178 x d y) (@lem1537211 d x y)). Qed.
Lemma lem1537213 (y : real) (x : real) (d : real) : (term130 y x d) = (term131 y x d).
Proof. exact (@lem1483531 y (real_add x d)). Qed.
Lemma lem1537220 (d : real) (x : real) : (real_add x d) = (real_add d x).
Proof. exact (@lem1483488 d x). Qed.
Lemma lem1537223 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1537224 (y : real) (d : real) (x : real) : (term132 y x d) = (term132 y d x).
Proof. exact (MK_COMB (@lem1537223 y) (@lem1537220 d x)). Qed.
Lemma lem1537225 (y : real) (d : real) (x : real) : (term132 y d x) = (term133 y d x).
Proof. exact (@lem1483519 y (real_add d x)). Qed.
Lemma lem1537232 (d : real) (x : real) : (term134 d x) = (term135 d x).
Proof. exact (@lem1483508 d term67 x). Qed.
Lemma lem1537233 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1537234 (y : real) (d : real) (x : real) : (term133 y d x) = (term136 y d x).
Proof. exact (MK_COMB (@lem1537233 y) (@lem1537232 d x)). Qed.
Lemma lem1537235 (d : real) (y : real) (x : real) : (term136 y d x) = (term126 d y x).
Proof. exact (@lem1483484 (term61 d) y (term61 x)). Qed.
Lemma lem1537236 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1537237 (d : real) : (term137 d) = (term137 d).
Proof. exact (eq_refl (term137 d)). Qed.
Lemma lem1537238 (d : real) (x : real) (y : real) : (term126 d y x) = (term138 d x y).
Proof. exact (MK_COMB (@lem1537237 d) (@lem1537236 x y)). Qed.
Lemma lem1537239 (d : real) (x : real) (y : real) : (term136 y d x) = (term138 d x y).
Proof. exact (TRANS (@lem1537235 d y x) (@lem1537238 d x y)). Qed.
Lemma lem1537240 (d : real) (x : real) (y : real) : (term133 y d x) = (term138 d x y).
Proof. exact (TRANS (@lem1537234 y d x) (@lem1537239 d x y)). Qed.
Lemma lem1537241 (d : real) (x : real) (y : real) : (term132 y d x) = (term138 d x y).
Proof. exact (TRANS (@lem1537225 y d x) (@lem1537240 d x y)). Qed.
Lemma lem1537242 (d : real) (x : real) (y : real) : (term132 y x d) = (term138 d x y).
Proof. exact (TRANS (@lem1537224 y d x) (@lem1537241 d x y)). Qed.
Lemma lem1537243 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1537244 (d : real) (x : real) (y : real) : (term139 y x d) = (term140 d x y).
Proof. exact (MK_COMB (@lem1537243) (@lem1537242 d x y)). Qed.
Lemma lem1537245 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537246 (d : real) (x : real) (y : real) : (term131 y x d) = (term141 d x y).
Proof. exact (MK_COMB (@lem1537244 d x y) (@lem1537245)). Qed.
Lemma lem1537247 (d : real) (x : real) (y : real) : (term130 y x d) = (term141 d x y).
Proof. exact (TRANS (@lem1537213 y x d) (@lem1537246 d x y)). Qed.
Lemma lem1537248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537249 (d : real) (x : real) (y : real) : (term142 x d y) = (term143 d x y).
Proof. exact (MK_COMB (@lem1537248) (@lem1537212 d x y)). Qed.
Lemma lem1537250 (d : real) (x : real) (y : real) : (term1 y x d) = (term144 d x y).
Proof. exact (MK_COMB (@lem1537249 d x y) (@lem1537247 d x y)). Qed.
Lemma lem1537251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537252 (d : real) : (term4 d) = (term145 d).
Proof. exact (MK_COMB (@lem1537251) (@lem1537177 d)). Qed.
Lemma lem1537253 (d : real) (x : real) (y : real) : (term6 y x d) = (term146 d x y).
Proof. exact (MK_COMB (@lem1537252 d) (@lem1537250 d x y)). Qed.
Lemma lem1537254 (d : real) (y : real) (x : real) : (term10 y x d) = (term147 d y x).
Proof. exact (@lem1483521 d (term101 y x)). Qed.
Lemma lem1537267 (d : real) (y : real) (x : real) : (term148 d y x) = (term149 d y x).
Proof. exact (@lem1483519 d (term101 y x)). Qed.
Lemma lem1537268 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537269 (d : real) (y : real) (x : real) : (term150 d y x) = (term151 d y x).
Proof. exact (MK_COMB (@lem1537268) (@lem1537267 d y x)). Qed.
Lemma lem1537270 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537271 (d : real) (y : real) (x : real) : (term147 d y x) = (term152 d y x).
Proof. exact (MK_COMB (@lem1537269 d y x) (@lem1537270)). Qed.
Lemma lem1537272 (d : real) (y : real) (x : real) : (term10 y x d) = (term152 d y x).
Proof. exact (TRANS (@lem1537254 d y x) (@lem1537271 d y x)). Qed.
Lemma lem1537273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1537274 (d : real) (x : real) (y : real) : (term12 y x d) = (term153 d x y).
Proof. exact (MK_COMB (@lem1537273) (@lem1537253 d x y)). Qed.
Lemma lem1537275 (d : real) (y : real) (x : real) : (term14 y x d) = (term154 d y x).
Proof. exact (MK_COMB (@lem1537274 d x y) (@lem1537272 d y x)). Qed.
Lemma lem1537276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537277 (d : real) (y : real) (x : real) : (term15 y x d) = (term155 d y x).
Proof. exact (MK_COMB (@lem1537276) (@lem1537158 d y x)). Qed.
Lemma lem1537278 (d : real) (y : real) (x : real) : (term17 y x d) = (term156 d y x).
Proof. exact (MK_COMB (@lem1537277 d y x) (@lem1537275 d y x)). Qed.
Lemma lem1537279 (y : real) (x : real) : (term28 y x) = (term157 y x).
Proof. exact (fun_ext (fun d : real => @lem1537278 d y x)). Qed.
Lemma lem1537280 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537281 (y : real) (x : real) : (term29 y x) = (term158 y x).
Proof. exact (MK_COMB (@lem1537280) (@lem1537279 y x)). Qed.
Lemma lem1537282 (x : real) : (term37 x) = (term159 x).
Proof. exact (fun_ext (fun y : real => @lem1537281 y x)). Qed.
Lemma lem1537283 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537284 (x : real) : (term38 x) = (term160 x).
Proof. exact (MK_COMB (@lem1537283) (@lem1537282 x)). Qed.
Lemma lem1537285 : term46 = term161.
Proof. exact (fun_ext (fun x : real => @lem1537284 x)). Qed.
Lemma lem1537286 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537287 : term47 = term162.
Proof. exact (MK_COMB (@lem1537286) (@lem1537285)). Qed.
Lemma lem1537288 : term39 = term162.
Proof. exact (TRANS (@lem1537024) (@lem1537287)). Qed.
Lemma lem1537298 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1537299 (P : real -> Prop) (Q : real -> Prop) : (term165 P Q) = (term166 P Q).
Proof. exact (@lem1537298 real P Q). Qed.
Lemma lem1537300 (y : real) (x : real) : (term167 y x) = (term168 y x).
Proof. exact (@lem1537299 (term169 y x) (term170 y x)). Qed.
Lemma lem1537301 (d : real) (y : real) (x : real) : (term171 y x d) = (term111 d y x).
Proof. exact (eq_refl (term171 y x d)). Qed.
Lemma lem1537302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537303 (d : real) (y : real) (x : real) : (term172 y x d) = (term155 d y x).
Proof. exact (MK_COMB (@lem1537302) (@lem1537301 d y x)). Qed.
Lemma lem1537304 (d : real) (y : real) (x : real) : (term173 y x d) = (term154 d y x).
Proof. exact (eq_refl (term173 y x d)). Qed.
Lemma lem1537305 (d : real) (y : real) (x : real) : (term174 y x d) = (term156 d y x).
Proof. exact (MK_COMB (@lem1537303 d y x) (@lem1537304 d y x)). Qed.
Lemma lem1537306 (y : real) (x : real) : (term175 y x) = (term157 y x).
Proof. exact (fun_ext (fun d : real => @lem1537305 d y x)). Qed.
Lemma lem1537307 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537308 (y : real) (x : real) : (term167 y x) = (term158 y x).
Proof. exact (MK_COMB (@lem1537307) (@lem1537306 y x)). Qed.
Lemma lem1537309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1537310 (y : real) (x : real) : (term176 y x) = (term177 y x).
Proof. exact (MK_COMB (@lem1537309) (@lem1537308 y x)). Qed.
Lemma lem1537311 (d : real) (y : real) (x : real) : (term171 y x d) = (term111 d y x).
Proof. exact (eq_refl (term171 y x d)). Qed.
Lemma lem1537312 (y : real) (x : real) : (term178 y x) = (term169 y x).
Proof. exact (fun_ext (fun d : real => @lem1537311 d y x)). Qed.
Lemma lem1537313 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537314 (y : real) (x : real) : (term179 y x) = (term180 y x).
Proof. exact (MK_COMB (@lem1537313) (@lem1537312 y x)). Qed.
Lemma lem1537315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537316 (y : real) (x : real) : (term181 y x) = (term182 y x).
Proof. exact (MK_COMB (@lem1537315) (@lem1537314 y x)). Qed.
Lemma lem1537317 (d : real) (y : real) (x : real) : (term173 y x d) = (term154 d y x).
Proof. exact (eq_refl (term173 y x d)). Qed.
Lemma lem1537318 (y : real) (x : real) : (term183 y x) = (term170 y x).
Proof. exact (fun_ext (fun d : real => @lem1537317 d y x)). Qed.
Lemma lem1537319 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537320 (y : real) (x : real) : (term184 y x) = (term185 y x).
Proof. exact (MK_COMB (@lem1537319) (@lem1537318 y x)). Qed.
Lemma lem1537321 (y : real) (x : real) : (term168 y x) = (term186 y x).
Proof. exact (MK_COMB (@lem1537316 y x) (@lem1537320 y x)). Qed.
Lemma lem1537322 (y : real) (x : real) : ((term167 y x) = (term168 y x)) = ((term158 y x) = (term186 y x)).
Proof. exact (MK_COMB (@lem1537310 y x) (@lem1537321 y x)). Qed.
Lemma lem1537323 (y : real) (x : real) : (term158 y x) = (term186 y x).
Proof. exact (EQ_MP (@lem1537322 y x) (@lem1537300 y x)). Qed.
Lemma lem1537420 (x : real) : (term159 x) = (term187 x).
Proof. exact (fun_ext (fun y : real => @lem1537323 y x)). Qed.
Lemma lem1537421 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537422 (x : real) : (term160 x) = (term188 x).
Proof. exact (MK_COMB (@lem1537421) (@lem1537420 x)). Qed.
Lemma lem1537424 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1537425 (P : real -> Prop) (Q : real -> Prop) : (term165 P Q) = (term166 P Q).
Proof. exact (@lem1537424 real P Q). Qed.
Lemma lem1537426 (x : real) : (term189 x) = (term190 x).
Proof. exact (@lem1537425 (term191 x) (term192 x)). Qed.
Lemma lem1537427 (y : real) (x : real) : (term193 x y) = (term180 y x).
Proof. exact (eq_refl (term193 x y)). Qed.
Lemma lem1537428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537429 (y : real) (x : real) : (term194 x y) = (term182 y x).
Proof. exact (MK_COMB (@lem1537428) (@lem1537427 y x)). Qed.
Lemma lem1537430 (y : real) (x : real) : (term195 x y) = (term185 y x).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1537431 (y : real) (x : real) : (term196 x y) = (term186 y x).
Proof. exact (MK_COMB (@lem1537429 y x) (@lem1537430 y x)). Qed.
Lemma lem1537432 (x : real) : (term197 x) = (term187 x).
Proof. exact (fun_ext (fun y : real => @lem1537431 y x)). Qed.
Lemma lem1537433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537434 (x : real) : (term189 x) = (term188 x).
Proof. exact (MK_COMB (@lem1537433) (@lem1537432 x)). Qed.
Lemma lem1537435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1537436 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1537435) (@lem1537434 x)). Qed.
Lemma lem1537437 (y : real) (x : real) : (term193 x y) = (term180 y x).
Proof. exact (eq_refl (term193 x y)). Qed.
Lemma lem1537438 (x : real) : (term200 x) = (term191 x).
Proof. exact (fun_ext (fun y : real => @lem1537437 y x)). Qed.
Lemma lem1537439 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537440 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1537439) (@lem1537438 x)). Qed.
Lemma lem1537441 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537442 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1537441) (@lem1537440 x)). Qed.
Lemma lem1537443 (y : real) (x : real) : (term195 x y) = (term185 y x).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1537444 (x : real) : (term205 x) = (term192 x).
Proof. exact (fun_ext (fun y : real => @lem1537443 y x)). Qed.
Lemma lem1537445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537446 (x : real) : (term206 x) = (term207 x).
Proof. exact (MK_COMB (@lem1537445) (@lem1537444 x)). Qed.
Lemma lem1537447 (x : real) : (term190 x) = (term208 x).
Proof. exact (MK_COMB (@lem1537442 x) (@lem1537446 x)). Qed.
Lemma lem1537448 (x : real) : ((term189 x) = (term190 x)) = ((term188 x) = (term208 x)).
Proof. exact (MK_COMB (@lem1537436 x) (@lem1537447 x)). Qed.
Lemma lem1537449 (x : real) : (term188 x) = (term208 x).
Proof. exact (EQ_MP (@lem1537448 x) (@lem1537426 x)). Qed.
Lemma lem1537554 (x : real) : (term160 x) = (term208 x).
Proof. exact (TRANS (@lem1537422 x) (@lem1537449 x)). Qed.
Lemma lem1537555 : term161 = term209.
Proof. exact (fun_ext (fun x : real => @lem1537554 x)). Qed.
Lemma lem1537556 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537557 : term162 = term210.
Proof. exact (MK_COMB (@lem1537556) (@lem1537555)). Qed.
Lemma lem1537559 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1537560 (P : real -> Prop) (Q : real -> Prop) : (term165 P Q) = (term166 P Q).
Proof. exact (@lem1537559 real P Q). Qed.
Lemma lem1537561 : term211 = term212.
Proof. exact (@lem1537560 term213 term214). Qed.
Lemma lem1537562 (x : real) : (term215 x) = (term202 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1537563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537564 (x : real) : (term216 x) = (term204 x).
Proof. exact (MK_COMB (@lem1537563) (@lem1537562 x)). Qed.
Lemma lem1537565 (x : real) : (term217 x) = (term207 x).
Proof. exact (eq_refl (term217 x)). Qed.
Lemma lem1537566 (x : real) : (term218 x) = (term208 x).
Proof. exact (MK_COMB (@lem1537564 x) (@lem1537565 x)). Qed.
Lemma lem1537567 : term219 = term209.
Proof. exact (fun_ext (fun x : real => @lem1537566 x)). Qed.
Lemma lem1537568 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537569 : term211 = term210.
Proof. exact (MK_COMB (@lem1537568) (@lem1537567)). Qed.
Lemma lem1537570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1537571 : term220 = term221.
Proof. exact (MK_COMB (@lem1537570) (@lem1537569)). Qed.
Lemma lem1537572 (x : real) : (term215 x) = (term202 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1537573 : term222 = term213.
Proof. exact (fun_ext (fun x : real => @lem1537572 x)). Qed.
Lemma lem1537574 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537575 : term223 = term224.
Proof. exact (MK_COMB (@lem1537574) (@lem1537573)). Qed.
Lemma lem1537576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537577 : term225 = term226.
Proof. exact (MK_COMB (@lem1537576) (@lem1537575)). Qed.
Lemma lem1537578 (x : real) : (term217 x) = (term207 x).
Proof. exact (eq_refl (term217 x)). Qed.
Lemma lem1537579 : term227 = term214.
Proof. exact (fun_ext (fun x : real => @lem1537578 x)). Qed.
Lemma lem1537580 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537581 : term228 = term229.
Proof. exact (MK_COMB (@lem1537580) (@lem1537579)). Qed.
Lemma lem1537582 : term212 = term230.
Proof. exact (MK_COMB (@lem1537577) (@lem1537581)). Qed.
Lemma lem1537583 : (term211 = term212) = (term210 = term230).
Proof. exact (MK_COMB (@lem1537571) (@lem1537582)). Qed.
Lemma lem1537584 : term210 = term230.
Proof. exact (EQ_MP (@lem1537583) (@lem1537561)). Qed.
Lemma lem1537697 : term162 = term230.
Proof. exact (TRANS (@lem1537557) (@lem1537584)). Qed.
Lemma lem1537699 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term164 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1537700 (P : real -> Prop) (Q : real -> Prop) : (term166 P Q) = (term165 P Q).
Proof. exact (@lem1537699 real P Q). Qed.
Lemma lem1537701 : term212 = term211.
Proof. exact (@lem1537700 term213 term214). Qed.
Lemma lem1537702 (x : real) : (term215 x) = (term202 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1537703 : term222 = term213.
Proof. exact (fun_ext (fun x : real => @lem1537702 x)). Qed.
Lemma lem1537704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537705 : term223 = term224.
Proof. exact (MK_COMB (@lem1537704) (@lem1537703)). Qed.
Lemma lem1537706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537707 : term225 = term226.
Proof. exact (MK_COMB (@lem1537706) (@lem1537705)). Qed.
Lemma lem1537708 (x : real) : (term217 x) = (term207 x).
Proof. exact (eq_refl (term217 x)). Qed.
Lemma lem1537709 : term227 = term214.
Proof. exact (fun_ext (fun x : real => @lem1537708 x)). Qed.
Lemma lem1537710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537711 : term228 = term229.
Proof. exact (MK_COMB (@lem1537710) (@lem1537709)). Qed.
Lemma lem1537712 : term212 = term230.
Proof. exact (MK_COMB (@lem1537707) (@lem1537711)). Qed.
Lemma lem1537713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1537714 : term231 = term232.
Proof. exact (MK_COMB (@lem1537713) (@lem1537712)). Qed.
Lemma lem1537715 (x : real) : (term215 x) = (term202 x).
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem1537716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537717 (x : real) : (term216 x) = (term204 x).
Proof. exact (MK_COMB (@lem1537716) (@lem1537715 x)). Qed.
Lemma lem1537718 (x : real) : (term217 x) = (term207 x).
Proof. exact (eq_refl (term217 x)). Qed.
Lemma lem1537719 (x : real) : (term218 x) = (term208 x).
Proof. exact (MK_COMB (@lem1537717 x) (@lem1537718 x)). Qed.
Lemma lem1537720 : term219 = term209.
Proof. exact (fun_ext (fun x : real => @lem1537719 x)). Qed.
Lemma lem1537721 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537722 : term211 = term210.
Proof. exact (MK_COMB (@lem1537721) (@lem1537720)). Qed.
Lemma lem1537723 : (term212 = term211) = (term230 = term210).
Proof. exact (MK_COMB (@lem1537714) (@lem1537722)). Qed.
Lemma lem1537724 : term230 = term210.
Proof. exact (EQ_MP (@lem1537723) (@lem1537701)). Qed.
Lemma lem1537726 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term164 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1537727 (P : real -> Prop) (Q : real -> Prop) : (term166 P Q) = (term165 P Q).
Proof. exact (@lem1537726 real P Q). Qed.
Lemma lem1537728 (x : real) : (term190 x) = (term189 x).
Proof. exact (@lem1537727 (term191 x) (term192 x)). Qed.
Lemma lem1537729 (y : real) (x : real) : (term193 x y) = (term180 y x).
Proof. exact (eq_refl (term193 x y)). Qed.
Lemma lem1537730 (x : real) : (term200 x) = (term191 x).
Proof. exact (fun_ext (fun y : real => @lem1537729 y x)). Qed.
Lemma lem1537731 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537732 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1537731) (@lem1537730 x)). Qed.
Lemma lem1537733 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537734 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1537733) (@lem1537732 x)). Qed.
Lemma lem1537735 (y : real) (x : real) : (term195 x y) = (term185 y x).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1537736 (x : real) : (term205 x) = (term192 x).
Proof. exact (fun_ext (fun y : real => @lem1537735 y x)). Qed.
Lemma lem1537737 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537738 (x : real) : (term206 x) = (term207 x).
Proof. exact (MK_COMB (@lem1537737) (@lem1537736 x)). Qed.
Lemma lem1537739 (x : real) : (term190 x) = (term208 x).
Proof. exact (MK_COMB (@lem1537734 x) (@lem1537738 x)). Qed.
Lemma lem1537740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1537741 (x : real) : (term233 x) = (term234 x).
Proof. exact (MK_COMB (@lem1537740) (@lem1537739 x)). Qed.
Lemma lem1537742 (y : real) (x : real) : (term193 x y) = (term180 y x).
Proof. exact (eq_refl (term193 x y)). Qed.
Lemma lem1537743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537744 (y : real) (x : real) : (term194 x y) = (term182 y x).
Proof. exact (MK_COMB (@lem1537743) (@lem1537742 y x)). Qed.
Lemma lem1537745 (y : real) (x : real) : (term195 x y) = (term185 y x).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1537746 (y : real) (x : real) : (term196 x y) = (term186 y x).
Proof. exact (MK_COMB (@lem1537744 y x) (@lem1537745 y x)). Qed.
Lemma lem1537747 (x : real) : (term197 x) = (term187 x).
Proof. exact (fun_ext (fun y : real => @lem1537746 y x)). Qed.
Lemma lem1537748 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537749 (x : real) : (term189 x) = (term188 x).
Proof. exact (MK_COMB (@lem1537748) (@lem1537747 x)). Qed.
Lemma lem1537750 (x : real) : ((term190 x) = (term189 x)) = ((term208 x) = (term188 x)).
Proof. exact (MK_COMB (@lem1537741 x) (@lem1537749 x)). Qed.
Lemma lem1537751 (x : real) : (term208 x) = (term188 x).
Proof. exact (EQ_MP (@lem1537750 x) (@lem1537728 x)). Qed.
Lemma lem1537753 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term164 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1537754 (P : real -> Prop) (Q : real -> Prop) : (term166 P Q) = (term165 P Q).
Proof. exact (@lem1537753 real P Q). Qed.
Lemma lem1537755 (y : real) (x : real) : (term168 y x) = (term167 y x).
Proof. exact (@lem1537754 (term169 y x) (term170 y x)). Qed.
Lemma lem1537756 (d : real) (y : real) (x : real) : (term171 y x d) = (term111 d y x).
Proof. exact (eq_refl (term171 y x d)). Qed.
Lemma lem1537757 (y : real) (x : real) : (term178 y x) = (term169 y x).
Proof. exact (fun_ext (fun d : real => @lem1537756 d y x)). Qed.
Lemma lem1537758 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537759 (y : real) (x : real) : (term179 y x) = (term180 y x).
Proof. exact (MK_COMB (@lem1537758) (@lem1537757 y x)). Qed.
Lemma lem1537760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537761 (y : real) (x : real) : (term181 y x) = (term182 y x).
Proof. exact (MK_COMB (@lem1537760) (@lem1537759 y x)). Qed.
Lemma lem1537762 (d : real) (y : real) (x : real) : (term173 y x d) = (term154 d y x).
Proof. exact (eq_refl (term173 y x d)). Qed.
Lemma lem1537763 (y : real) (x : real) : (term183 y x) = (term170 y x).
Proof. exact (fun_ext (fun d : real => @lem1537762 d y x)). Qed.
Lemma lem1537764 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537765 (y : real) (x : real) : (term184 y x) = (term185 y x).
Proof. exact (MK_COMB (@lem1537764) (@lem1537763 y x)). Qed.
Lemma lem1537766 (y : real) (x : real) : (term168 y x) = (term186 y x).
Proof. exact (MK_COMB (@lem1537761 y x) (@lem1537765 y x)). Qed.
Lemma lem1537767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1537768 (y : real) (x : real) : (term235 y x) = (term236 y x).
Proof. exact (MK_COMB (@lem1537767) (@lem1537766 y x)). Qed.
Lemma lem1537769 (d : real) (y : real) (x : real) : (term171 y x d) = (term111 d y x).
Proof. exact (eq_refl (term171 y x d)). Qed.
Lemma lem1537770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537771 (d : real) (y : real) (x : real) : (term172 y x d) = (term155 d y x).
Proof. exact (MK_COMB (@lem1537770) (@lem1537769 d y x)). Qed.
Lemma lem1537772 (d : real) (y : real) (x : real) : (term173 y x d) = (term154 d y x).
Proof. exact (eq_refl (term173 y x d)). Qed.
Lemma lem1537773 (d : real) (y : real) (x : real) : (term174 y x d) = (term156 d y x).
Proof. exact (MK_COMB (@lem1537771 d y x) (@lem1537772 d y x)). Qed.
Lemma lem1537774 (y : real) (x : real) : (term175 y x) = (term157 y x).
Proof. exact (fun_ext (fun d : real => @lem1537773 d y x)). Qed.
Lemma lem1537775 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537776 (y : real) (x : real) : (term167 y x) = (term158 y x).
Proof. exact (MK_COMB (@lem1537775) (@lem1537774 y x)). Qed.
Lemma lem1537777 (y : real) (x : real) : ((term168 y x) = (term167 y x)) = ((term186 y x) = (term158 y x)).
Proof. exact (MK_COMB (@lem1537768 y x) (@lem1537776 y x)). Qed.
Lemma lem1537778 (y : real) (x : real) : (term186 y x) = (term158 y x).
Proof. exact (EQ_MP (@lem1537777 y x) (@lem1537755 y x)). Qed.
Lemma lem1537779 (x : real) : (term187 x) = (term159 x).
Proof. exact (fun_ext (fun y : real => @lem1537778 y x)). Qed.
Lemma lem1537780 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537781 (x : real) : (term188 x) = (term160 x).
Proof. exact (MK_COMB (@lem1537780) (@lem1537779 x)). Qed.
Lemma lem1537782 (x : real) : (term208 x) = (term160 x).
Proof. exact (TRANS (@lem1537751 x) (@lem1537781 x)). Qed.
Lemma lem1537783 : term209 = term161.
Proof. exact (fun_ext (fun x : real => @lem1537782 x)). Qed.
Lemma lem1537784 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537785 : term210 = term162.
Proof. exact (MK_COMB (@lem1537784) (@lem1537783)). Qed.
Lemma lem1537786 : term230 = term162.
Proof. exact (TRANS (@lem1537724) (@lem1537785)). Qed.
Lemma lem1537787 : term162 = term162.
Proof. exact (TRANS (@lem1537697) (@lem1537786)). Qed.
Lemma lem1537790 : term39 = term162.
Proof. exact (TRANS (@lem1537288) (@lem1537787)). Qed.
Lemma lem1537804 (d : real) (y : real) (x : real) : (term154 d y x) = (term237 d y x).
Proof. exact (@lem19367 (term118 d) (term144 d x y) (term152 d y x)). Qed.
Lemma lem1537811 (d : real) (y : real) (x : real) : (term238 d y x) = (term239 d y x).
Proof. exact (@lem19367 (term129 d x y) (term141 d x y) (term152 d y x)). Qed.
Lemma lem1537814 (d : real) (y : real) (x : real) : (term240 d y x) = (term240 d y x).
Proof. exact (eq_refl (term240 d y x)). Qed.
Lemma lem1537815 (d : real) (y : real) (x : real) : (term237 d y x) = (term241 d y x).
Proof. exact (MK_COMB (@lem1537814 d y x) (@lem1537811 d y x)). Qed.
Lemma lem1537817 (d : real) (y : real) (x : real) : (term154 d y x) = (term241 d y x).
Proof. exact (TRANS (@lem1537804 d y x) (@lem1537815 d y x)). Qed.
Lemma lem1537838 (d : real) (y : real) (x : real) : (term155 d y x) = (term155 d y x).
Proof. exact (eq_refl (term155 d y x)). Qed.
Lemma lem1537839 (d : real) (y : real) (x : real) : (term156 d y x) = (term242 d y x).
Proof. exact (MK_COMB (@lem1537838 d y x) (@lem1537817 d y x)). Qed.
Lemma lem1537840 (y : real) (x : real) : (term157 y x) = (term243 y x).
Proof. exact (fun_ext (fun d : real => @lem1537839 d y x)). Qed.
Lemma lem1537841 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537842 (y : real) (x : real) : (term158 y x) = (term244 y x).
Proof. exact (MK_COMB (@lem1537841) (@lem1537840 y x)). Qed.
Lemma lem1537843 (x : real) : (term159 x) = (term245 x).
Proof. exact (fun_ext (fun y : real => @lem1537842 y x)). Qed.
Lemma lem1537844 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537845 (x : real) : (term160 x) = (term246 x).
Proof. exact (MK_COMB (@lem1537844) (@lem1537843 x)). Qed.
Lemma lem1537846 : term161 = term247.
Proof. exact (fun_ext (fun x : real => @lem1537845 x)). Qed.
Lemma lem1537847 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1537848 : term162 = term248.
Proof. exact (MK_COMB (@lem1537847) (@lem1537846)). Qed.
Lemma lem1537849 : term39 = term248.
Proof. exact (TRANS (@lem1537790) (@lem1537848)). Qed.
Lemma lem1537851 (d : real) (y : real) (x : real) : (term249 d y x) = (term111 d y x).
Proof. exact (eq_refl (term249 d y x)). Qed.
Lemma lem1537852 (d : real) (y : real) (x : real) : (term111 d y x) = (term249 d y x).
Proof. exact (SYM (@lem1537851 d y x)). Qed.
Lemma lem1537853 (d : real) (y : real) (x : real) : (term249 d y x) = (term250 d y x).
Proof. exact (@lem1482981 (term251 x y d) (real_sub y x)). Qed.
Lemma lem1537854 (d : real) (y : real) (x : real) : (term111 d y x) = (term250 d y x).
Proof. exact (TRANS (@lem1537852 d y x) (@lem1537853 d y x)). Qed.
Lemma lem1537855 (d : real) (y : real) (x : real) : (term252 d y x) = (term253 d y x).
Proof. exact (eq_refl (term252 d y x)). Qed.
Lemma lem1537856 (y : real) (x : real) : (term254 y x) = (term254 y x).
Proof. exact (eq_refl (term254 y x)). Qed.
Lemma lem1537857 (d : real) (y : real) (x : real) : (term255 d y x) = (term256 d y x).
Proof. exact (MK_COMB (@lem1537856 y x) (@lem1537855 d y x)). Qed.
Lemma lem1537858 (d : real) (y : real) (x : real) : (term257 d y x) = (term258 d y x).
Proof. exact (eq_refl (term257 d y x)). Qed.
Lemma lem1537859 (y : real) (x : real) : (term259 y x) = (term259 y x).
Proof. exact (eq_refl (term259 y x)). Qed.
Lemma lem1537860 (d : real) (y : real) (x : real) : (term260 d y x) = (term261 d y x).
Proof. exact (MK_COMB (@lem1537859 y x) (@lem1537858 d y x)). Qed.
Lemma lem1537861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1537862 (d : real) (y : real) (x : real) : (term262 d y x) = (term263 d y x).
Proof. exact (MK_COMB (@lem1537861) (@lem1537860 d y x)). Qed.
Lemma lem1537863 (d : real) (y : real) (x : real) : (term250 d y x) = (term264 d y x).
Proof. exact (MK_COMB (@lem1537862 d y x) (@lem1537857 d y x)). Qed.
Lemma lem1537864 (d : real) (y : real) (x : real) : (term265 d y x) = (term265 d y x).
Proof. exact (eq_refl (term265 d y x)). Qed.
Lemma lem1537865 (d : real) (y : real) (x : real) : ((term111 d y x) = (term250 d y x)) = ((term111 d y x) = (term264 d y x)).
Proof. exact (MK_COMB (@lem1537864 d y x) (@lem1537863 d y x)). Qed.
Lemma lem1537866 (d : real) (y : real) (x : real) : (term111 d y x) = (term264 d y x).
Proof. exact (EQ_MP (@lem1537865 d y x) (@lem1537854 d y x)). Qed.
Lemma lem1537867 (y : real) (x : real) : (term266 y x) = (term267 y x).
Proof. exact (@lem1483527 (real_sub y x) term49). Qed.
Lemma lem1537868 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537874 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1537879 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1537881 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1537874 y x) (@lem1537879 x y)). Qed.
Lemma lem1537882 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1537883 (x : real) (y : real) : (term121 y x) = (term122 x y).
Proof. exact (MK_COMB (@lem1537882) (@lem1537881 x y)). Qed.
Lemma lem1537884 (x : real) (y : real) : (term268 y x) = (term269 x y).
Proof. exact (MK_COMB (@lem1537883 x y) (@lem1537868)). Qed.
Lemma lem1537885 (x : real) (y : real) : (term269 x y) = (term270 x y).
Proof. exact (@lem1483519 (term60 x y) term49). Qed.
Lemma lem1537887 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1537888 : term53 = term49.
Proof. exact (@lem1537887 term54). Qed.
Lemma lem1537889 (x : real) (y : real) : (term271 x y) = (term271 x y).
Proof. exact (eq_refl (term271 x y)). Qed.
Lemma lem1537890 (x : real) (y : real) : (term270 x y) = (term272 x y).
Proof. exact (MK_COMB (@lem1537889 x y) (@lem1537888)). Qed.
Lemma lem1537891 (x : real) (y : real) : (term272 x y) = (term60 x y).
Proof. exact (@lem1483450 (term60 x y)). Qed.
Lemma lem1537892 (x : real) (y : real) : (term270 x y) = (term60 x y).
Proof. exact (TRANS (@lem1537890 x y) (@lem1537891 x y)). Qed.
Lemma lem1537893 (x : real) (y : real) : (term269 x y) = (term60 x y).
Proof. exact (TRANS (@lem1537885 x y) (@lem1537892 x y)). Qed.
Lemma lem1537894 (x : real) (y : real) : (term268 y x) = (term60 x y).
Proof. exact (TRANS (@lem1537884 x y) (@lem1537893 x y)). Qed.
Lemma lem1537895 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1537896 (x : real) (y : real) : (term273 y x) = (term274 x y).
Proof. exact (MK_COMB (@lem1537895) (@lem1537894 x y)). Qed.
Lemma lem1537897 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537898 (x : real) (y : real) : (term267 y x) = (term275 x y).
Proof. exact (MK_COMB (@lem1537896 x y) (@lem1537897)). Qed.
Lemma lem1537899 (x : real) (y : real) : (term266 y x) = (term275 x y).
Proof. exact (TRANS (@lem1537867 y x) (@lem1537898 x y)). Qed.
Lemma lem1537900 (d : real) : (term57 d) = (term48 d).
Proof. exact (@lem1483525 d term49). Qed.
Lemma lem1537906 (d : real) : (term50 d) = (term51 d).
Proof. exact (@lem1483519 d term49). Qed.
Lemma lem1537908 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1537909 : term53 = term49.
Proof. exact (@lem1537908 term54). Qed.
Lemma lem1537910 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1537911 (d : real) : (term51 d) = (term55 d).
Proof. exact (MK_COMB (@lem1537910 d) (@lem1537909)). Qed.
Lemma lem1537912 (d : real) : (term55 d) = d.
Proof. exact (@lem1483450 d). Qed.
Lemma lem1537913 (d : real) : (term51 d) = d.
Proof. exact (TRANS (@lem1537911 d) (@lem1537912 d)). Qed.
Lemma lem1537915 (d : real) : (term50 d) = d.
Proof. exact (TRANS (@lem1537906 d) (@lem1537913 d)). Qed.
Lemma lem1537916 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537917 (d : real) : (term56 d) = (real_gt d).
Proof. exact (MK_COMB (@lem1537916) (@lem1537915 d)). Qed.
Lemma lem1537918 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537919 (d : real) : (term48 d) = (term57 d).
Proof. exact (MK_COMB (@lem1537917 d) (@lem1537918)). Qed.
Lemma lem1537920 (d : real) : (term57 d) = (term57 d).
Proof. exact (TRANS (@lem1537900 d) (@lem1537919 d)). Qed.
Lemma lem1537921 (d : real) (x : real) (y : real) : (term85 d x y) = (term276 d x y).
Proof. exact (@lem1483525 (term82 d x y) term49). Qed.
Lemma lem1537945 (d : real) (x : real) (y : real) : (term277 d x y) = (term278 d x y).
Proof. exact (@lem1483519 (term82 d x y) term49). Qed.
Lemma lem1537947 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1537948 : term53 = term49.
Proof. exact (@lem1537947 term54). Qed.
Lemma lem1537949 (d : real) (x : real) (y : real) : (term279 d x y) = (term279 d x y).
Proof. exact (eq_refl (term279 d x y)). Qed.
Lemma lem1537950 (d : real) (x : real) (y : real) : (term278 d x y) = (term280 d x y).
Proof. exact (MK_COMB (@lem1537949 d x y) (@lem1537948)). Qed.
Lemma lem1537951 (d : real) (x : real) (y : real) : (term280 d x y) = (term82 d x y).
Proof. exact (@lem1483450 (term82 d x y)). Qed.
Lemma lem1537952 (d : real) (x : real) (y : real) : (term278 d x y) = (term82 d x y).
Proof. exact (TRANS (@lem1537950 d x y) (@lem1537951 d x y)). Qed.
Lemma lem1537954 (d : real) (x : real) (y : real) : (term277 d x y) = (term82 d x y).
Proof. exact (TRANS (@lem1537945 d x y) (@lem1537952 d x y)). Qed.
Lemma lem1537955 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537956 (d : real) (x : real) (y : real) : (term281 d x y) = (term84 d x y).
Proof. exact (MK_COMB (@lem1537955) (@lem1537954 d x y)). Qed.
Lemma lem1537957 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537958 (d : real) (x : real) (y : real) : (term276 d x y) = (term85 d x y).
Proof. exact (MK_COMB (@lem1537956 d x y) (@lem1537957)). Qed.
Lemma lem1537959 (d : real) (x : real) (y : real) : (term85 d x y) = (term85 d x y).
Proof. exact (TRANS (@lem1537921 d x y) (@lem1537958 d x y)). Qed.
Lemma lem1537960 (d : real) (x : real) (y : real) : (term92 d x y) = (term282 d x y).
Proof. exact (@lem1483525 (term81 d x y) term49). Qed.
Lemma lem1537984 (d : real) (x : real) (y : real) : (term283 d x y) = (term284 d x y).
Proof. exact (@lem1483519 (term81 d x y) term49). Qed.
Lemma lem1537986 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1537987 : term53 = term49.
Proof. exact (@lem1537986 term54). Qed.
Lemma lem1537988 (d : real) (x : real) (y : real) : (term285 d x y) = (term285 d x y).
Proof. exact (eq_refl (term285 d x y)). Qed.
Lemma lem1537989 (d : real) (x : real) (y : real) : (term284 d x y) = (term286 d x y).
Proof. exact (MK_COMB (@lem1537988 d x y) (@lem1537987)). Qed.
Lemma lem1537990 (d : real) (x : real) (y : real) : (term286 d x y) = (term81 d x y).
Proof. exact (@lem1483450 (term81 d x y)). Qed.
Lemma lem1537991 (d : real) (x : real) (y : real) : (term284 d x y) = (term81 d x y).
Proof. exact (TRANS (@lem1537989 d x y) (@lem1537990 d x y)). Qed.
Lemma lem1537993 (d : real) (x : real) (y : real) : (term283 d x y) = (term81 d x y).
Proof. exact (TRANS (@lem1537984 d x y) (@lem1537991 d x y)). Qed.
Lemma lem1537994 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1537995 (d : real) (x : real) (y : real) : (term287 d x y) = (term91 d x y).
Proof. exact (MK_COMB (@lem1537994) (@lem1537993 d x y)). Qed.
Lemma lem1537996 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1537997 (d : real) (x : real) (y : real) : (term282 d x y) = (term92 d x y).
Proof. exact (MK_COMB (@lem1537995 d x y) (@lem1537996)). Qed.
Lemma lem1537998 (d : real) (x : real) (y : real) : (term92 d x y) = (term92 d x y).
Proof. exact (TRANS (@lem1537960 d x y) (@lem1537997 d x y)). Qed.
Lemma lem1537999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538000 (d : real) (x : real) (y : real) : (term94 d x y) = (term94 d x y).
Proof. exact (MK_COMB (@lem1537999) (@lem1537959 d x y)). Qed.
Lemma lem1538001 (d : real) (x : real) (y : real) : (term95 d x y) = (term95 d x y).
Proof. exact (MK_COMB (@lem1538000 d x y) (@lem1537998 d x y)). Qed.
Lemma lem1538002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538003 (d : real) : (term97 d) = (term97 d).
Proof. exact (MK_COMB (@lem1538002) (@lem1537920 d)). Qed.
Lemma lem1538004 (d : real) (x : real) (y : real) : (term98 d x y) = (term98 d x y).
Proof. exact (MK_COMB (@lem1538003 d) (@lem1538001 d x y)). Qed.
Lemma lem1538005 (d : real) (y : real) (x : real) : (term288 d y x) = (term289 d y x).
Proof. exact (@lem1483527 (term290 d y x) term49). Qed.
Lemma lem1538006 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538012 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538017 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538019 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538012 y x) (@lem1538017 x y)). Qed.
Lemma lem1538028 (d : real) : (term137 d) = (term137 d).
Proof. exact (eq_refl (term137 d)). Qed.
Lemma lem1538031 (d : real) (x : real) (y : real) : (term290 d y x) = (term138 d x y).
Proof. exact (MK_COMB (@lem1538028 d) (@lem1538019 x y)). Qed.
Lemma lem1538032 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1538033 (d : real) (x : real) (y : real) : (term291 d y x) = (term292 d x y).
Proof. exact (MK_COMB (@lem1538032) (@lem1538031 d x y)). Qed.
Lemma lem1538034 (d : real) (x : real) (y : real) : (term293 d y x) = (term294 d x y).
Proof. exact (MK_COMB (@lem1538033 d x y) (@lem1538006)). Qed.
Lemma lem1538035 (d : real) (x : real) (y : real) : (term294 d x y) = (term295 d x y).
Proof. exact (@lem1483519 (term138 d x y) term49). Qed.
Lemma lem1538037 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1538038 : term53 = term49.
Proof. exact (@lem1538037 term54). Qed.
Lemma lem1538039 (d : real) (x : real) (y : real) : (term296 d x y) = (term296 d x y).
Proof. exact (eq_refl (term296 d x y)). Qed.
Lemma lem1538040 (d : real) (x : real) (y : real) : (term295 d x y) = (term297 d x y).
Proof. exact (MK_COMB (@lem1538039 d x y) (@lem1538038)). Qed.
Lemma lem1538041 (d : real) (x : real) (y : real) : (term297 d x y) = (term138 d x y).
Proof. exact (@lem1483450 (term138 d x y)). Qed.
Lemma lem1538042 (d : real) (x : real) (y : real) : (term295 d x y) = (term138 d x y).
Proof. exact (TRANS (@lem1538040 d x y) (@lem1538041 d x y)). Qed.
Lemma lem1538043 (d : real) (x : real) (y : real) : (term294 d x y) = (term138 d x y).
Proof. exact (TRANS (@lem1538035 d x y) (@lem1538042 d x y)). Qed.
Lemma lem1538044 (d : real) (x : real) (y : real) : (term293 d y x) = (term138 d x y).
Proof. exact (TRANS (@lem1538034 d x y) (@lem1538043 d x y)). Qed.
Lemma lem1538045 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1538046 (d : real) (x : real) (y : real) : (term298 d y x) = (term140 d x y).
Proof. exact (MK_COMB (@lem1538045) (@lem1538044 d x y)). Qed.
Lemma lem1538047 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538048 (d : real) (x : real) (y : real) : (term289 d y x) = (term141 d x y).
Proof. exact (MK_COMB (@lem1538046 d x y) (@lem1538047)). Qed.
Lemma lem1538049 (d : real) (x : real) (y : real) : (term288 d y x) = (term141 d x y).
Proof. exact (TRANS (@lem1538005 d y x) (@lem1538048 d x y)). Qed.
Lemma lem1538050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538051 (d : real) (x : real) (y : real) : (term109 d x y) = (term109 d x y).
Proof. exact (MK_COMB (@lem1538050) (@lem1538004 d x y)). Qed.
Lemma lem1538052 (d : real) (x : real) (y : real) : (term258 d y x) = (term299 d x y).
Proof. exact (MK_COMB (@lem1538051 d x y) (@lem1538049 d x y)). Qed.
Lemma lem1538053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538054 (x : real) (y : real) : (term259 y x) = (term300 x y).
Proof. exact (MK_COMB (@lem1538053) (@lem1537899 x y)). Qed.
Lemma lem1538055 (d : real) (x : real) (y : real) : (term261 d y x) = (term301 d x y).
Proof. exact (MK_COMB (@lem1538054 x y) (@lem1538052 d x y)). Qed.
Lemma lem1538056 (y : real) (x : real) : (term302 y x) = (term303 y x).
Proof. exact (@lem1483525 term49 (real_sub y x)). Qed.
Lemma lem1538062 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538067 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538069 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538062 y x) (@lem1538067 x y)). Qed.
Lemma lem1538072 : term304 = term304.
Proof. exact (eq_refl term304). Qed.
Lemma lem1538073 (x : real) (y : real) : (term305 y x) = (term306 x y).
Proof. exact (MK_COMB (@lem1538072) (@lem1538069 x y)). Qed.
Lemma lem1538074 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483519 term49 (term60 x y)). Qed.
Lemma lem1538075 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (@lem1483508 (term61 x) term67 y). Qed.
Lemma lem1538076 (y : real) : (term61 y) = (term61 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem1538077 (x : real) : (term68 x) = (term69 x).
Proof. exact (@lem1483476 term67 term67 x). Qed.
Lemma lem1538079 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1538080 : term72 = term73.
Proof. exact (@lem1538079 term54 term54). Qed.
Lemma lem1538081 : (term74 = (BIT1 0)) = (term75 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1538082 : term75 = term54.
Proof. exact (EQ_MP (@lem1538081) (@lem940073)). Qed.
Lemma lem1538083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538084 : term73 = term76.
Proof. exact (MK_COMB (@lem1538083) (@lem1538082)). Qed.
Lemma lem1538085 : term72 = term76.
Proof. exact (TRANS (@lem1538080) (@lem1538084)). Qed.
Lemma lem1538086 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538087 : term77 = term78.
Proof. exact (MK_COMB (@lem1538086) (@lem1538085)). Qed.
Lemma lem1538088 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538089 (x : real) : (term69 x) = (term79 x).
Proof. exact (MK_COMB (@lem1538087) (@lem1538088 x)). Qed.
Lemma lem1538090 (x : real) : (term68 x) = (term79 x).
Proof. exact (TRANS (@lem1538077 x) (@lem1538089 x)). Qed.
Lemma lem1538091 (x : real) : (term79 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1538092 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1538090 x) (@lem1538091 x)). Qed.
Lemma lem1538093 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538094 (x : real) : (term80 x) = (real_add x).
Proof. exact (MK_COMB (@lem1538093) (@lem1538092 x)). Qed.
Lemma lem1538095 (x : real) (y : real) : (term66 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1538094 x) (@lem1538076 y)). Qed.
Lemma lem1538096 (x : real) (y : real) : (term65 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538075 x y) (@lem1538095 x y)). Qed.
Lemma lem1538097 : term308 = term308.
Proof. exact (eq_refl term308). Qed.
Lemma lem1538098 (x : real) (y : real) : (term307 x y) = (term309 x y).
Proof. exact (MK_COMB (@lem1538097) (@lem1538096 x y)). Qed.
Lemma lem1538099 (x : real) (y : real) : (term309 x y) = (term59 x y).
Proof. exact (@lem1483448 (term59 x y)). Qed.
Lemma lem1538100 (x : real) (y : real) : (term307 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538098 x y) (@lem1538099 x y)). Qed.
Lemma lem1538101 (x : real) (y : real) : (term306 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538074 x y) (@lem1538100 x y)). Qed.
Lemma lem1538102 (x : real) (y : real) : (term305 y x) = (term59 x y).
Proof. exact (TRANS (@lem1538073 x y) (@lem1538101 x y)). Qed.
Lemma lem1538103 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538104 (x : real) (y : real) : (term310 y x) = (term311 x y).
Proof. exact (MK_COMB (@lem1538103) (@lem1538102 x y)). Qed.
Lemma lem1538105 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538106 (x : real) (y : real) : (term303 y x) = (term312 x y).
Proof. exact (MK_COMB (@lem1538104 x y) (@lem1538105)). Qed.
Lemma lem1538107 (x : real) (y : real) : (term302 y x) = (term312 x y).
Proof. exact (TRANS (@lem1538056 y x) (@lem1538106 x y)). Qed.
Lemma lem1538108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538109 (d : real) (x : real) (y : real) : (term94 d x y) = (term94 d x y).
Proof. exact (MK_COMB (@lem1538108) (@lem1537959 d x y)). Qed.
Lemma lem1538110 (d : real) (x : real) (y : real) : (term95 d x y) = (term95 d x y).
Proof. exact (MK_COMB (@lem1538109 d x y) (@lem1537998 d x y)). Qed.
Lemma lem1538111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538112 (d : real) : (term97 d) = (term97 d).
Proof. exact (MK_COMB (@lem1538111) (@lem1537920 d)). Qed.
Lemma lem1538113 (d : real) (x : real) (y : real) : (term98 d x y) = (term98 d x y).
Proof. exact (MK_COMB (@lem1538112 d) (@lem1538110 d x y)). Qed.
Lemma lem1538114 (d : real) (y : real) (x : real) : (term313 d y x) = (term314 d y x).
Proof. exact (@lem1483527 (term315 d y x) term49). Qed.
Lemma lem1538115 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538121 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538126 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538128 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538121 y x) (@lem1538126 x y)). Qed.
Lemma lem1538129 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1538130 (x : real) (y : real) : (term316 y x) = (term317 x y).
Proof. exact (MK_COMB (@lem1538129) (@lem1538128 x y)). Qed.
Lemma lem1538131 (x : real) (y : real) : (term317 x y) = (term65 x y).
Proof. exact (@lem1483512 (term60 x y)). Qed.
Lemma lem1538132 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (@lem1483508 (term61 x) term67 y). Qed.
Lemma lem1538133 (y : real) : (term61 y) = (term61 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem1538134 (x : real) : (term68 x) = (term69 x).
Proof. exact (@lem1483476 term67 term67 x). Qed.
Lemma lem1538136 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1538137 : term72 = term73.
Proof. exact (@lem1538136 term54 term54). Qed.
Lemma lem1538138 : (term74 = (BIT1 0)) = (term75 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1538139 : term75 = term54.
Proof. exact (EQ_MP (@lem1538138) (@lem940073)). Qed.
Lemma lem1538140 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538141 : term73 = term76.
Proof. exact (MK_COMB (@lem1538140) (@lem1538139)). Qed.
Lemma lem1538142 : term72 = term76.
Proof. exact (TRANS (@lem1538137) (@lem1538141)). Qed.
Lemma lem1538143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538144 : term77 = term78.
Proof. exact (MK_COMB (@lem1538143) (@lem1538142)). Qed.
Lemma lem1538145 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538146 (x : real) : (term69 x) = (term79 x).
Proof. exact (MK_COMB (@lem1538144) (@lem1538145 x)). Qed.
Lemma lem1538147 (x : real) : (term68 x) = (term79 x).
Proof. exact (TRANS (@lem1538134 x) (@lem1538146 x)). Qed.
Lemma lem1538148 (x : real) : (term79 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1538149 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1538147 x) (@lem1538148 x)). Qed.
Lemma lem1538150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538151 (x : real) : (term80 x) = (real_add x).
Proof. exact (MK_COMB (@lem1538150) (@lem1538149 x)). Qed.
Lemma lem1538152 (x : real) (y : real) : (term66 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1538151 x) (@lem1538133 y)). Qed.
Lemma lem1538153 (x : real) (y : real) : (term65 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538132 x y) (@lem1538152 x y)). Qed.
Lemma lem1538154 (x : real) (y : real) : (term317 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538131 x y) (@lem1538153 x y)). Qed.
Lemma lem1538155 (x : real) (y : real) : (term316 y x) = (term59 x y).
Proof. exact (TRANS (@lem1538130 x y) (@lem1538154 x y)). Qed.
Lemma lem1538164 (d : real) : (term137 d) = (term137 d).
Proof. exact (eq_refl (term137 d)). Qed.
Lemma lem1538167 (d : real) (x : real) (y : real) : (term315 d y x) = (term126 d x y).
Proof. exact (MK_COMB (@lem1538164 d) (@lem1538155 x y)). Qed.
Lemma lem1538168 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1538169 (d : real) (x : real) (y : real) : (term318 d y x) = (term319 d x y).
Proof. exact (MK_COMB (@lem1538168) (@lem1538167 d x y)). Qed.
Lemma lem1538170 (d : real) (x : real) (y : real) : (term320 d y x) = (term321 d x y).
Proof. exact (MK_COMB (@lem1538169 d x y) (@lem1538115)). Qed.
Lemma lem1538171 (d : real) (x : real) (y : real) : (term321 d x y) = (term322 d x y).
Proof. exact (@lem1483519 (term126 d x y) term49). Qed.
Lemma lem1538173 (x : nat) : (term52 x) = term49.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1538174 : term53 = term49.
Proof. exact (@lem1538173 term54). Qed.
Lemma lem1538175 (d : real) (x : real) (y : real) : (term323 d x y) = (term323 d x y).
Proof. exact (eq_refl (term323 d x y)). Qed.
Lemma lem1538176 (d : real) (x : real) (y : real) : (term322 d x y) = (term324 d x y).
Proof. exact (MK_COMB (@lem1538175 d x y) (@lem1538174)). Qed.
Lemma lem1538177 (d : real) (x : real) (y : real) : (term324 d x y) = (term126 d x y).
Proof. exact (@lem1483450 (term126 d x y)). Qed.
Lemma lem1538178 (d : real) (x : real) (y : real) : (term322 d x y) = (term126 d x y).
Proof. exact (TRANS (@lem1538176 d x y) (@lem1538177 d x y)). Qed.
Lemma lem1538179 (d : real) (x : real) (y : real) : (term321 d x y) = (term126 d x y).
Proof. exact (TRANS (@lem1538171 d x y) (@lem1538178 d x y)). Qed.
Lemma lem1538180 (d : real) (x : real) (y : real) : (term320 d y x) = (term126 d x y).
Proof. exact (TRANS (@lem1538170 d x y) (@lem1538179 d x y)). Qed.
Lemma lem1538181 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1538182 (d : real) (x : real) (y : real) : (term325 d y x) = (term128 d x y).
Proof. exact (MK_COMB (@lem1538181) (@lem1538180 d x y)). Qed.
Lemma lem1538183 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538184 (d : real) (x : real) (y : real) : (term314 d y x) = (term129 d x y).
Proof. exact (MK_COMB (@lem1538182 d x y) (@lem1538183)). Qed.
Lemma lem1538185 (d : real) (x : real) (y : real) : (term313 d y x) = (term129 d x y).
Proof. exact (TRANS (@lem1538114 d y x) (@lem1538184 d x y)). Qed.
Lemma lem1538186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538187 (d : real) (x : real) (y : real) : (term109 d x y) = (term109 d x y).
Proof. exact (MK_COMB (@lem1538186) (@lem1538113 d x y)). Qed.
Lemma lem1538188 (d : real) (x : real) (y : real) : (term253 d y x) = (term326 d x y).
Proof. exact (MK_COMB (@lem1538187 d x y) (@lem1538185 d x y)). Qed.
Lemma lem1538189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538190 (x : real) (y : real) : (term254 y x) = (term327 x y).
Proof. exact (MK_COMB (@lem1538189) (@lem1538107 x y)). Qed.
Lemma lem1538191 (d : real) (x : real) (y : real) : (term256 d y x) = (term328 d x y).
Proof. exact (MK_COMB (@lem1538190 x y) (@lem1538188 d x y)). Qed.
Lemma lem1538192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1538193 (d : real) (x : real) (y : real) : (term263 d y x) = (term329 d x y).
Proof. exact (MK_COMB (@lem1538192) (@lem1538055 d x y)). Qed.
Lemma lem1538194 (d : real) (x : real) (y : real) : (term264 d y x) = (term330 d x y).
Proof. exact (MK_COMB (@lem1538193 d x y) (@lem1538191 d x y)). Qed.
Lemma lem1538206 (d : real) (x : real) (y : real) : (term111 d y x) = (term330 d x y).
Proof. exact (TRANS (@lem1537866 d y x) (@lem1538194 d x y)). Qed.
Lemma lem1538208 (a : real) (x : real) (r : real) : (term331 a x r) = (term332 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1538209 (d : real) (y : real) (x : real) : (term152 d y x) = (term333 d y x).
Proof. exact (@lem1538208 d (real_sub y x) term49). Qed.
Lemma lem1538215 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538220 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538222 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538215 y x) (@lem1538220 x y)). Qed.
Lemma lem1538225 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1538226 (x : real) (y : real) : (term334 y x) = (term335 x y).
Proof. exact (MK_COMB (@lem1538225) (@lem1538222 x y)). Qed.
Lemma lem1538227 (x : real) (y : real) : (term335 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1538228 (x : real) (y : real) : (term334 y x) = (term60 x y).
Proof. exact (TRANS (@lem1538226 x y) (@lem1538227 x y)). Qed.
Lemma lem1538231 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1538234 (d : real) (x : real) (y : real) : (term336 d y x) = (term82 d x y).
Proof. exact (MK_COMB (@lem1538231 d) (@lem1538228 x y)). Qed.
Lemma lem1538235 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538236 (d : real) (x : real) (y : real) : (term337 d y x) = (term84 d x y).
Proof. exact (MK_COMB (@lem1538235) (@lem1538234 d x y)). Qed.
Lemma lem1538237 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538238 (d : real) (x : real) (y : real) : (term338 d y x) = (term85 d x y).
Proof. exact (MK_COMB (@lem1538236 d x y) (@lem1538237)). Qed.
Lemma lem1538244 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538249 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538251 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538244 y x) (@lem1538249 x y)). Qed.
Lemma lem1538254 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem1538255 (x : real) (y : real) : (term340 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1538254) (@lem1538251 x y)). Qed.
Lemma lem1538256 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (@lem1483508 (term61 x) term67 y). Qed.
Lemma lem1538257 (y : real) : (term61 y) = (term61 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem1538258 (x : real) : (term68 x) = (term69 x).
Proof. exact (@lem1483476 term67 term67 x). Qed.
Lemma lem1538260 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1538261 : term72 = term73.
Proof. exact (@lem1538260 term54 term54). Qed.
Lemma lem1538262 : (term74 = (BIT1 0)) = (term75 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1538263 : term75 = term54.
Proof. exact (EQ_MP (@lem1538262) (@lem940073)). Qed.
Lemma lem1538264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538265 : term73 = term76.
Proof. exact (MK_COMB (@lem1538264) (@lem1538263)). Qed.
Lemma lem1538266 : term72 = term76.
Proof. exact (TRANS (@lem1538261) (@lem1538265)). Qed.
Lemma lem1538267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538268 : term77 = term78.
Proof. exact (MK_COMB (@lem1538267) (@lem1538266)). Qed.
Lemma lem1538269 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538270 (x : real) : (term69 x) = (term79 x).
Proof. exact (MK_COMB (@lem1538268) (@lem1538269 x)). Qed.
Lemma lem1538271 (x : real) : (term68 x) = (term79 x).
Proof. exact (TRANS (@lem1538258 x) (@lem1538270 x)). Qed.
Lemma lem1538272 (x : real) : (term79 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1538273 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1538271 x) (@lem1538272 x)). Qed.
Lemma lem1538274 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538275 (x : real) : (term80 x) = (real_add x).
Proof. exact (MK_COMB (@lem1538274) (@lem1538273 x)). Qed.
Lemma lem1538276 (x : real) (y : real) : (term66 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1538275 x) (@lem1538257 y)). Qed.
Lemma lem1538277 (x : real) (y : real) : (term65 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538256 x y) (@lem1538276 x y)). Qed.
Lemma lem1538278 (x : real) (y : real) : (term340 y x) = (term59 x y).
Proof. exact (TRANS (@lem1538255 x y) (@lem1538277 x y)). Qed.
Lemma lem1538281 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1538284 (d : real) (x : real) (y : real) : (term341 d y x) = (term81 d x y).
Proof. exact (MK_COMB (@lem1538281 d) (@lem1538278 x y)). Qed.
Lemma lem1538285 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538286 (d : real) (x : real) (y : real) : (term342 d y x) = (term91 d x y).
Proof. exact (MK_COMB (@lem1538285) (@lem1538284 d x y)). Qed.
Lemma lem1538287 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538288 (d : real) (x : real) (y : real) : (term343 d y x) = (term92 d x y).
Proof. exact (MK_COMB (@lem1538286 d x y) (@lem1538287)). Qed.
Lemma lem1538289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538290 (d : real) (x : real) (y : real) : (term344 d y x) = (term345 d x y).
Proof. exact (MK_COMB (@lem1538289) (@lem1538288 d x y)). Qed.
Lemma lem1538291 (d : real) (x : real) (y : real) : (term333 d y x) = (term346 d x y).
Proof. exact (MK_COMB (@lem1538290 d x y) (@lem1538238 d x y)). Qed.
Lemma lem1538292 (d : real) (x : real) (y : real) : (term152 d y x) = (term346 d x y).
Proof. exact (TRANS (@lem1538209 d y x) (@lem1538291 d x y)). Qed.
Lemma lem1538293 (d : real) : (term347 d) = (term347 d).
Proof. exact (eq_refl (term347 d)). Qed.
Lemma lem1538296 (d : real) (x : real) (y : real) : (term348 d y x) = (term349 d x y).
Proof. exact (MK_COMB (@lem1538293 d) (@lem1538292 d x y)). Qed.
Lemma lem1538298 (a : real) (x : real) (r : real) : (term331 a x r) = (term332 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1538299 (d : real) (y : real) (x : real) : (term152 d y x) = (term333 d y x).
Proof. exact (@lem1538298 d (real_sub y x) term49). Qed.
Lemma lem1538305 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538310 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538312 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538305 y x) (@lem1538310 x y)). Qed.
Lemma lem1538315 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1538316 (x : real) (y : real) : (term334 y x) = (term335 x y).
Proof. exact (MK_COMB (@lem1538315) (@lem1538312 x y)). Qed.
Lemma lem1538317 (x : real) (y : real) : (term335 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1538318 (x : real) (y : real) : (term334 y x) = (term60 x y).
Proof. exact (TRANS (@lem1538316 x y) (@lem1538317 x y)). Qed.
Lemma lem1538321 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1538324 (d : real) (x : real) (y : real) : (term336 d y x) = (term82 d x y).
Proof. exact (MK_COMB (@lem1538321 d) (@lem1538318 x y)). Qed.
Lemma lem1538325 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538326 (d : real) (x : real) (y : real) : (term337 d y x) = (term84 d x y).
Proof. exact (MK_COMB (@lem1538325) (@lem1538324 d x y)). Qed.
Lemma lem1538327 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538328 (d : real) (x : real) (y : real) : (term338 d y x) = (term85 d x y).
Proof. exact (MK_COMB (@lem1538326 d x y) (@lem1538327)). Qed.
Lemma lem1538334 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538339 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538341 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538334 y x) (@lem1538339 x y)). Qed.
Lemma lem1538344 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem1538345 (x : real) (y : real) : (term340 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1538344) (@lem1538341 x y)). Qed.
Lemma lem1538346 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (@lem1483508 (term61 x) term67 y). Qed.
Lemma lem1538347 (y : real) : (term61 y) = (term61 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem1538348 (x : real) : (term68 x) = (term69 x).
Proof. exact (@lem1483476 term67 term67 x). Qed.
Lemma lem1538350 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1538351 : term72 = term73.
Proof. exact (@lem1538350 term54 term54). Qed.
Lemma lem1538352 : (term74 = (BIT1 0)) = (term75 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1538353 : term75 = term54.
Proof. exact (EQ_MP (@lem1538352) (@lem940073)). Qed.
Lemma lem1538354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538355 : term73 = term76.
Proof. exact (MK_COMB (@lem1538354) (@lem1538353)). Qed.
Lemma lem1538356 : term72 = term76.
Proof. exact (TRANS (@lem1538351) (@lem1538355)). Qed.
Lemma lem1538357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538358 : term77 = term78.
Proof. exact (MK_COMB (@lem1538357) (@lem1538356)). Qed.
Lemma lem1538359 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538360 (x : real) : (term69 x) = (term79 x).
Proof. exact (MK_COMB (@lem1538358) (@lem1538359 x)). Qed.
Lemma lem1538361 (x : real) : (term68 x) = (term79 x).
Proof. exact (TRANS (@lem1538348 x) (@lem1538360 x)). Qed.
Lemma lem1538362 (x : real) : (term79 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1538363 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1538361 x) (@lem1538362 x)). Qed.
Lemma lem1538364 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538365 (x : real) : (term80 x) = (real_add x).
Proof. exact (MK_COMB (@lem1538364) (@lem1538363 x)). Qed.
Lemma lem1538366 (x : real) (y : real) : (term66 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1538365 x) (@lem1538347 y)). Qed.
Lemma lem1538367 (x : real) (y : real) : (term65 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538346 x y) (@lem1538366 x y)). Qed.
Lemma lem1538368 (x : real) (y : real) : (term340 y x) = (term59 x y).
Proof. exact (TRANS (@lem1538345 x y) (@lem1538367 x y)). Qed.
Lemma lem1538371 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1538374 (d : real) (x : real) (y : real) : (term341 d y x) = (term81 d x y).
Proof. exact (MK_COMB (@lem1538371 d) (@lem1538368 x y)). Qed.
Lemma lem1538375 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538376 (d : real) (x : real) (y : real) : (term342 d y x) = (term91 d x y).
Proof. exact (MK_COMB (@lem1538375) (@lem1538374 d x y)). Qed.
Lemma lem1538377 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538378 (d : real) (x : real) (y : real) : (term343 d y x) = (term92 d x y).
Proof. exact (MK_COMB (@lem1538376 d x y) (@lem1538377)). Qed.
Lemma lem1538379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538380 (d : real) (x : real) (y : real) : (term344 d y x) = (term345 d x y).
Proof. exact (MK_COMB (@lem1538379) (@lem1538378 d x y)). Qed.
Lemma lem1538381 (d : real) (x : real) (y : real) : (term333 d y x) = (term346 d x y).
Proof. exact (MK_COMB (@lem1538380 d x y) (@lem1538328 d x y)). Qed.
Lemma lem1538382 (d : real) (x : real) (y : real) : (term152 d y x) = (term346 d x y).
Proof. exact (TRANS (@lem1538299 d y x) (@lem1538381 d x y)). Qed.
Lemma lem1538383 (d : real) (x : real) (y : real) : (term350 d x y) = (term350 d x y).
Proof. exact (eq_refl (term350 d x y)). Qed.
Lemma lem1538386 (d : real) (x : real) (y : real) : (term351 d y x) = (term352 d x y).
Proof. exact (MK_COMB (@lem1538383 d x y) (@lem1538382 d x y)). Qed.
Lemma lem1538388 (a : real) (x : real) (r : real) : (term331 a x r) = (term332 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1538389 (d : real) (y : real) (x : real) : (term152 d y x) = (term333 d y x).
Proof. exact (@lem1538388 d (real_sub y x) term49). Qed.
Lemma lem1538395 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538400 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538402 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538395 y x) (@lem1538400 x y)). Qed.
Lemma lem1538405 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1538406 (x : real) (y : real) : (term334 y x) = (term335 x y).
Proof. exact (MK_COMB (@lem1538405) (@lem1538402 x y)). Qed.
Lemma lem1538407 (x : real) (y : real) : (term335 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1538408 (x : real) (y : real) : (term334 y x) = (term60 x y).
Proof. exact (TRANS (@lem1538406 x y) (@lem1538407 x y)). Qed.
Lemma lem1538411 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1538414 (d : real) (x : real) (y : real) : (term336 d y x) = (term82 d x y).
Proof. exact (MK_COMB (@lem1538411 d) (@lem1538408 x y)). Qed.
Lemma lem1538415 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538416 (d : real) (x : real) (y : real) : (term337 d y x) = (term84 d x y).
Proof. exact (MK_COMB (@lem1538415) (@lem1538414 d x y)). Qed.
Lemma lem1538417 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538418 (d : real) (x : real) (y : real) : (term338 d y x) = (term85 d x y).
Proof. exact (MK_COMB (@lem1538416 d x y) (@lem1538417)). Qed.
Lemma lem1538424 (y : real) (x : real) : (real_sub y x) = (term59 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1538429 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (@lem1483488 (term61 x) y). Qed.
Lemma lem1538431 (x : real) (y : real) : (real_sub y x) = (term60 x y).
Proof. exact (TRANS (@lem1538424 y x) (@lem1538429 x y)). Qed.
Lemma lem1538434 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem1538435 (x : real) (y : real) : (term340 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1538434) (@lem1538431 x y)). Qed.
Lemma lem1538436 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (@lem1483508 (term61 x) term67 y). Qed.
Lemma lem1538437 (y : real) : (term61 y) = (term61 y).
Proof. exact (eq_refl (term61 y)). Qed.
Lemma lem1538438 (x : real) : (term68 x) = (term69 x).
Proof. exact (@lem1483476 term67 term67 x). Qed.
Lemma lem1538440 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1538441 : term72 = term73.
Proof. exact (@lem1538440 term54 term54). Qed.
Lemma lem1538442 : (term74 = (BIT1 0)) = (term75 = term54).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1538443 : term75 = term54.
Proof. exact (EQ_MP (@lem1538442) (@lem940073)). Qed.
Lemma lem1538444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538445 : term73 = term76.
Proof. exact (MK_COMB (@lem1538444) (@lem1538443)). Qed.
Lemma lem1538446 : term72 = term76.
Proof. exact (TRANS (@lem1538441) (@lem1538445)). Qed.
Lemma lem1538447 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538448 : term77 = term78.
Proof. exact (MK_COMB (@lem1538447) (@lem1538446)). Qed.
Lemma lem1538449 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538450 (x : real) : (term69 x) = (term79 x).
Proof. exact (MK_COMB (@lem1538448) (@lem1538449 x)). Qed.
Lemma lem1538451 (x : real) : (term68 x) = (term79 x).
Proof. exact (TRANS (@lem1538438 x) (@lem1538450 x)). Qed.
Lemma lem1538452 (x : real) : (term79 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1538453 (x : real) : (term68 x) = x.
Proof. exact (TRANS (@lem1538451 x) (@lem1538452 x)). Qed.
Lemma lem1538454 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538455 (x : real) : (term80 x) = (real_add x).
Proof. exact (MK_COMB (@lem1538454) (@lem1538453 x)). Qed.
Lemma lem1538456 (x : real) (y : real) : (term66 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1538455 x) (@lem1538437 y)). Qed.
Lemma lem1538457 (x : real) (y : real) : (term65 x y) = (term59 x y).
Proof. exact (TRANS (@lem1538436 x y) (@lem1538456 x y)). Qed.
Lemma lem1538458 (x : real) (y : real) : (term340 y x) = (term59 x y).
Proof. exact (TRANS (@lem1538435 x y) (@lem1538457 x y)). Qed.
Lemma lem1538461 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1538464 (d : real) (x : real) (y : real) : (term341 d y x) = (term81 d x y).
Proof. exact (MK_COMB (@lem1538461 d) (@lem1538458 x y)). Qed.
Lemma lem1538465 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538466 (d : real) (x : real) (y : real) : (term342 d y x) = (term91 d x y).
Proof. exact (MK_COMB (@lem1538465) (@lem1538464 d x y)). Qed.
Lemma lem1538467 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538468 (d : real) (x : real) (y : real) : (term343 d y x) = (term92 d x y).
Proof. exact (MK_COMB (@lem1538466 d x y) (@lem1538467)). Qed.
Lemma lem1538469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1538470 (d : real) (x : real) (y : real) : (term344 d y x) = (term345 d x y).
Proof. exact (MK_COMB (@lem1538469) (@lem1538468 d x y)). Qed.
Lemma lem1538471 (d : real) (x : real) (y : real) : (term333 d y x) = (term346 d x y).
Proof. exact (MK_COMB (@lem1538470 d x y) (@lem1538418 d x y)). Qed.
Lemma lem1538472 (d : real) (x : real) (y : real) : (term152 d y x) = (term346 d x y).
Proof. exact (TRANS (@lem1538389 d y x) (@lem1538471 d x y)). Qed.
Lemma lem1538473 (d : real) (x : real) (y : real) : (term353 d x y) = (term353 d x y).
Proof. exact (eq_refl (term353 d x y)). Qed.
Lemma lem1538476 (d : real) (x : real) (y : real) : (term354 d y x) = (term355 d x y).
Proof. exact (MK_COMB (@lem1538473 d x y) (@lem1538472 d x y)). Qed.
Lemma lem1538477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1538478 (d : real) (x : real) (y : real) : (term356 d y x) = (term357 d x y).
Proof. exact (MK_COMB (@lem1538477) (@lem1538386 d x y)). Qed.
Lemma lem1538479 (d : real) (x : real) (y : real) : (term239 d y x) = (term358 d x y).
Proof. exact (MK_COMB (@lem1538478 d x y) (@lem1538476 d x y)). Qed.
Lemma lem1538480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1538481 (d : real) (x : real) (y : real) : (term240 d y x) = (term359 d x y).
Proof. exact (MK_COMB (@lem1538480) (@lem1538296 d x y)). Qed.
Lemma lem1538482 (d : real) (x : real) (y : real) : (term241 d y x) = (term360 d x y).
Proof. exact (MK_COMB (@lem1538481 d x y) (@lem1538479 d x y)). Qed.
Lemma lem1538483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1538484 (d : real) (x : real) (y : real) : (term155 d y x) = (term361 d x y).
Proof. exact (MK_COMB (@lem1538483) (@lem1538206 d x y)). Qed.
Lemma lem1538485 (d : real) (x : real) (y : real) : (term242 d y x) = (term362 d x y).
Proof. exact (MK_COMB (@lem1538484 d x y) (@lem1538482 d x y)). Qed.
Lemma lem1538486 (d : real) (x : real) (y : real) (h1 : term362 d x y) : term362 d x y.
Proof. exact (h1). Qed.
Lemma lem1538487 (d : real) (x : real) (y : real) (h1 : term330 d x y) : term330 d x y.
Proof. exact (h1). Qed.
Lemma lem1538488 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term301 d x y.
Proof. exact (h1). Qed.
Lemma lem1538489 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term299 d x y.
Proof. exact (proj2 (@lem1538488 d x y h1)). Qed.
Lemma lem1538491 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term141 d x y.
Proof. exact (proj2 (@lem1538489 d x y h1)). Qed.
Lemma lem1538492 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term98 d x y.
Proof. exact (proj1 (@lem1538489 d x y h1)). Qed.
Lemma lem1538493 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term95 d x y.
Proof. exact (proj2 (@lem1538492 d x y h1)). Qed.
Lemma lem1538495 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term92 d x y.
Proof. exact (proj2 (@lem1538493 d x y h1)). Qed.
Lemma lem1538498 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538499 : term364 = term365.
Proof. exact (@lem1538498 (NUMERAL 0) term54). Qed.
Lemma lem1538500 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538501 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538502 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538501 h1) (fun h1 : term365 = True => @lem1538500)). Qed.
Lemma lem1538503 : term365 = True.
Proof. exact (EQ_MP (@lem1538502) (@lem1538500)). Qed.
Lemma lem1538504 : term364 = True.
Proof. exact (TRANS (@lem1538499) (@lem1538503)). Qed.
Lemma lem1538505 : True = term364.
Proof. exact (SYM (@lem1538504)). Qed.
Lemma lem1538506 : term364.
Proof. exact (EQ_MP (@lem1538505) (@lem0)). Qed.
Lemma lem1538507 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term367 d x y.
Proof. exact (conj (@lem1538506) (@lem1538491 d x y h1)). Qed.
Lemma lem1538509 (x : real) (y : real) : term368 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1538510 (d : real) (x : real) (y : real) : term369 d x y.
Proof. exact (@lem1538509 term76 (term138 d x y)). Qed.
Lemma lem1538511 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term370 d x y.
Proof. exact (@lem1538510 d x y (@lem1538507 d x y h1)). Qed.
Lemma lem1538512 (d : real) (x : real) (y : real) : (term371 d x y) = (term138 d x y).
Proof. exact (@lem1483460 (term138 d x y)). Qed.
Lemma lem1538513 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1538514 (d : real) (x : real) (y : real) : (term372 d x y) = (term140 d x y).
Proof. exact (MK_COMB (@lem1538513) (@lem1538512 d x y)). Qed.
Lemma lem1538515 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538516 (d : real) (x : real) (y : real) : (term370 d x y) = (term141 d x y).
Proof. exact (MK_COMB (@lem1538514 d x y) (@lem1538515)). Qed.
Lemma lem1538517 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term141 d x y.
Proof. exact (EQ_MP (@lem1538516 d x y) (@lem1538511 d x y h1)). Qed.
Lemma lem1538519 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538520 : term364 = term365.
Proof. exact (@lem1538519 (NUMERAL 0) term54). Qed.
Lemma lem1538521 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538522 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538523 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538522 h1) (fun h1 : term365 = True => @lem1538521)). Qed.
Lemma lem1538524 : term365 = True.
Proof. exact (EQ_MP (@lem1538523) (@lem1538521)). Qed.
Lemma lem1538525 : term364 = True.
Proof. exact (TRANS (@lem1538520) (@lem1538524)). Qed.
Lemma lem1538526 : True = term364.
Proof. exact (SYM (@lem1538525)). Qed.
Lemma lem1538527 : term364.
Proof. exact (EQ_MP (@lem1538526) (@lem0)). Qed.
Lemma lem1538528 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term373 d x y.
Proof. exact (conj (@lem1538527) (@lem1538495 d x y h1)). Qed.
Lemma lem1538530 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1538531 (d : real) (x : real) (y : real) : term375 d x y.
Proof. exact (@lem1538530 term76 (term81 d x y)). Qed.
Lemma lem1538532 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term376 d x y.
Proof. exact (@lem1538531 d x y (@lem1538528 d x y h1)). Qed.
Lemma lem1538533 (d : real) (x : real) (y : real) : (term377 d x y) = (term81 d x y).
Proof. exact (@lem1483460 (term81 d x y)). Qed.
Lemma lem1538534 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538535 (d : real) (x : real) (y : real) : (term378 d x y) = (term91 d x y).
Proof. exact (MK_COMB (@lem1538534) (@lem1538533 d x y)). Qed.
Lemma lem1538536 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538537 (d : real) (x : real) (y : real) : (term376 d x y) = (term92 d x y).
Proof. exact (MK_COMB (@lem1538535 d x y) (@lem1538536)). Qed.
Lemma lem1538538 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term92 d x y.
Proof. exact (EQ_MP (@lem1538537 d x y) (@lem1538532 d x y h1)). Qed.
Lemma lem1538539 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term379 d x y.
Proof. exact (conj (@lem1538538 d x y h1) (@lem1538517 d x y h1)). Qed.
Lemma lem1538541 (x : real) (y : real) : term380 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1538542 (d : real) (x : real) (y : real) : term381 d x y.
Proof. exact (@lem1538541 (term81 d x y) (term138 d x y)). Qed.
Lemma lem1538543 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term382 d x y.
Proof. exact (@lem1538542 d x y (@lem1538539 d x y h1)). Qed.
Lemma lem1538544 (d : real) (x : real) (y : real) : (term383 d x y) = (term384 d x y).
Proof. exact (@lem1483480 d (term61 d) (term59 x y) (term60 x y)). Qed.
Lemma lem1538545 (d : real) : (term385 d) = (term386 d).
Proof. exact (@lem1483442 term67 d). Qed.
Lemma lem1538547 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538548 : term388 = term49.
Proof. exact (@lem1538547 term54). Qed.
Lemma lem1538549 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538550 : term389 = term390.
Proof. exact (MK_COMB (@lem1538549) (@lem1538548)). Qed.
Lemma lem1538551 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1538552 (d : real) : (term386 d) = (term391 d).
Proof. exact (MK_COMB (@lem1538550) (@lem1538551 d)). Qed.
Lemma lem1538553 (d : real) : (term385 d) = (term391 d).
Proof. exact (TRANS (@lem1538545 d) (@lem1538552 d)). Qed.
Lemma lem1538554 (d : real) : (term391 d) = term49.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1538555 (d : real) : (term385 d) = term49.
Proof. exact (TRANS (@lem1538553 d) (@lem1538554 d)). Qed.
Lemma lem1538556 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538557 (d : real) : (term392 d) = term308.
Proof. exact (MK_COMB (@lem1538556) (@lem1538555 d)). Qed.
Lemma lem1538558 (x : real) (y : real) : (term393 x y) = (term394 x y).
Proof. exact (@lem1483480 x (term61 x) (term61 y) y). Qed.
Lemma lem1538559 (x : real) : (term385 x) = (term386 x).
Proof. exact (@lem1483442 term67 x). Qed.
Lemma lem1538561 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538562 : term388 = term49.
Proof. exact (@lem1538561 term54). Qed.
Lemma lem1538563 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538564 : term389 = term390.
Proof. exact (MK_COMB (@lem1538563) (@lem1538562)). Qed.
Lemma lem1538565 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538566 (x : real) : (term386 x) = (term391 x).
Proof. exact (MK_COMB (@lem1538564) (@lem1538565 x)). Qed.
Lemma lem1538567 (x : real) : (term385 x) = (term391 x).
Proof. exact (TRANS (@lem1538559 x) (@lem1538566 x)). Qed.
Lemma lem1538568 (x : real) : (term391 x) = term49.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1538569 (x : real) : (term385 x) = term49.
Proof. exact (TRANS (@lem1538567 x) (@lem1538568 x)). Qed.
Lemma lem1538570 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538571 (x : real) : (term392 x) = term308.
Proof. exact (MK_COMB (@lem1538570) (@lem1538569 x)). Qed.
Lemma lem1538572 (y : real) : (term395 y) = (term386 y).
Proof. exact (@lem1483440 term67 y). Qed.
Lemma lem1538574 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538575 : term388 = term49.
Proof. exact (@lem1538574 term54). Qed.
Lemma lem1538576 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538577 : term389 = term390.
Proof. exact (MK_COMB (@lem1538576) (@lem1538575)). Qed.
Lemma lem1538578 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1538579 (y : real) : (term386 y) = (term391 y).
Proof. exact (MK_COMB (@lem1538577) (@lem1538578 y)). Qed.
Lemma lem1538580 (y : real) : (term395 y) = (term391 y).
Proof. exact (TRANS (@lem1538572 y) (@lem1538579 y)). Qed.
Lemma lem1538581 (y : real) : (term391 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1538582 (y : real) : (term395 y) = term49.
Proof. exact (TRANS (@lem1538580 y) (@lem1538581 y)). Qed.
Lemma lem1538583 (x : real) (y : real) : (term394 x y) = term396.
Proof. exact (MK_COMB (@lem1538571 x) (@lem1538582 y)). Qed.
Lemma lem1538584 (x : real) (y : real) : (term393 x y) = term396.
Proof. exact (TRANS (@lem1538558 x y) (@lem1538583 x y)). Qed.
Lemma lem1538585 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1538586 (x : real) (y : real) : (term393 x y) = term49.
Proof. exact (TRANS (@lem1538584 x y) (@lem1538585)). Qed.
Lemma lem1538587 (d : real) (x : real) (y : real) : (term384 d x y) = term396.
Proof. exact (MK_COMB (@lem1538557 d) (@lem1538586 x y)). Qed.
Lemma lem1538588 (d : real) (x : real) (y : real) : (term383 d x y) = term396.
Proof. exact (TRANS (@lem1538544 d x y) (@lem1538587 d x y)). Qed.
Lemma lem1538589 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1538590 (d : real) (x : real) (y : real) : (term383 d x y) = term49.
Proof. exact (TRANS (@lem1538588 d x y) (@lem1538589)). Qed.
Lemma lem1538591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538592 (d : real) (x : real) (y : real) : (term397 d x y) = term398.
Proof. exact (MK_COMB (@lem1538591) (@lem1538590 d x y)). Qed.
Lemma lem1538593 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538594 (d : real) (x : real) (y : real) : (term382 d x y) = term399.
Proof. exact (MK_COMB (@lem1538592 d x y) (@lem1538593)). Qed.
Lemma lem1538595 (d : real) (x : real) (y : real) (h1 : term301 d x y) : term399.
Proof. exact (EQ_MP (@lem1538594 d x y) (@lem1538543 d x y h1)). Qed.
Lemma lem1538597 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538598 : term399 = term400.
Proof. exact (@lem1538597 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1538599 : term400 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1538600 : term399 = False.
Proof. exact (TRANS (@lem1538598) (@lem1538599)). Qed.
Lemma lem1538601 (d : real) (x : real) (y : real) (h1 : term301 d x y) : False.
Proof. exact (EQ_MP (@lem1538600) (@lem1538595 d x y h1)). Qed.
Lemma lem1538602 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term328 d x y.
Proof. exact (h1). Qed.
Lemma lem1538603 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term326 d x y.
Proof. exact (proj2 (@lem1538602 d x y h1)). Qed.
Lemma lem1538605 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term129 d x y.
Proof. exact (proj2 (@lem1538603 d x y h1)). Qed.
Lemma lem1538606 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term98 d x y.
Proof. exact (proj1 (@lem1538603 d x y h1)). Qed.
Lemma lem1538607 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term95 d x y.
Proof. exact (proj2 (@lem1538606 d x y h1)). Qed.
Lemma lem1538610 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term85 d x y.
Proof. exact (proj1 (@lem1538607 d x y h1)). Qed.
Lemma lem1538612 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538613 : term364 = term365.
Proof. exact (@lem1538612 (NUMERAL 0) term54). Qed.
Lemma lem1538614 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538615 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538616 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538615 h1) (fun h1 : term365 = True => @lem1538614)). Qed.
Lemma lem1538617 : term365 = True.
Proof. exact (EQ_MP (@lem1538616) (@lem1538614)). Qed.
Lemma lem1538618 : term364 = True.
Proof. exact (TRANS (@lem1538613) (@lem1538617)). Qed.
Lemma lem1538619 : True = term364.
Proof. exact (SYM (@lem1538618)). Qed.
Lemma lem1538620 : term364.
Proof. exact (EQ_MP (@lem1538619) (@lem0)). Qed.
Lemma lem1538621 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term401 d x y.
Proof. exact (conj (@lem1538620) (@lem1538605 d x y h1)). Qed.
Lemma lem1538623 (x : real) (y : real) : term368 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1538624 (d : real) (x : real) (y : real) : term402 d x y.
Proof. exact (@lem1538623 term76 (term126 d x y)). Qed.
Lemma lem1538625 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term403 d x y.
Proof. exact (@lem1538624 d x y (@lem1538621 d x y h1)). Qed.
Lemma lem1538626 (d : real) (x : real) (y : real) : (term404 d x y) = (term126 d x y).
Proof. exact (@lem1483460 (term126 d x y)). Qed.
Lemma lem1538627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1538628 (d : real) (x : real) (y : real) : (term405 d x y) = (term128 d x y).
Proof. exact (MK_COMB (@lem1538627) (@lem1538626 d x y)). Qed.
Lemma lem1538629 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538630 (d : real) (x : real) (y : real) : (term403 d x y) = (term129 d x y).
Proof. exact (MK_COMB (@lem1538628 d x y) (@lem1538629)). Qed.
Lemma lem1538631 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term129 d x y.
Proof. exact (EQ_MP (@lem1538630 d x y) (@lem1538625 d x y h1)). Qed.
Lemma lem1538633 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538634 : term364 = term365.
Proof. exact (@lem1538633 (NUMERAL 0) term54). Qed.
Lemma lem1538635 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538636 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538637 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538636 h1) (fun h1 : term365 = True => @lem1538635)). Qed.
Lemma lem1538638 : term365 = True.
Proof. exact (EQ_MP (@lem1538637) (@lem1538635)). Qed.
Lemma lem1538639 : term364 = True.
Proof. exact (TRANS (@lem1538634) (@lem1538638)). Qed.
Lemma lem1538640 : True = term364.
Proof. exact (SYM (@lem1538639)). Qed.
Lemma lem1538641 : term364.
Proof. exact (EQ_MP (@lem1538640) (@lem0)). Qed.
Lemma lem1538642 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term406 d x y.
Proof. exact (conj (@lem1538641) (@lem1538610 d x y h1)). Qed.
Lemma lem1538644 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1538645 (d : real) (x : real) (y : real) : term407 d x y.
Proof. exact (@lem1538644 term76 (term82 d x y)). Qed.
Lemma lem1538646 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term408 d x y.
Proof. exact (@lem1538645 d x y (@lem1538642 d x y h1)). Qed.
Lemma lem1538647 (d : real) (x : real) (y : real) : (term409 d x y) = (term82 d x y).
Proof. exact (@lem1483460 (term82 d x y)). Qed.
Lemma lem1538648 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538649 (d : real) (x : real) (y : real) : (term410 d x y) = (term84 d x y).
Proof. exact (MK_COMB (@lem1538648) (@lem1538647 d x y)). Qed.
Lemma lem1538650 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538651 (d : real) (x : real) (y : real) : (term408 d x y) = (term85 d x y).
Proof. exact (MK_COMB (@lem1538649 d x y) (@lem1538650)). Qed.
Lemma lem1538652 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term85 d x y.
Proof. exact (EQ_MP (@lem1538651 d x y) (@lem1538646 d x y h1)). Qed.
Lemma lem1538653 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term411 d x y.
Proof. exact (conj (@lem1538652 d x y h1) (@lem1538631 d x y h1)). Qed.
Lemma lem1538655 (x : real) (y : real) : term380 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1538656 (d : real) (x : real) (y : real) : term412 d x y.
Proof. exact (@lem1538655 (term82 d x y) (term126 d x y)). Qed.
Lemma lem1538657 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term413 d x y.
Proof. exact (@lem1538656 d x y (@lem1538653 d x y h1)). Qed.
Lemma lem1538658 (d : real) (x : real) (y : real) : (term414 d x y) = (term415 d x y).
Proof. exact (@lem1483480 d (term61 d) (term60 x y) (term59 x y)). Qed.
Lemma lem1538659 (d : real) : (term385 d) = (term386 d).
Proof. exact (@lem1483442 term67 d). Qed.
Lemma lem1538661 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538662 : term388 = term49.
Proof. exact (@lem1538661 term54). Qed.
Lemma lem1538663 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538664 : term389 = term390.
Proof. exact (MK_COMB (@lem1538663) (@lem1538662)). Qed.
Lemma lem1538665 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1538666 (d : real) : (term386 d) = (term391 d).
Proof. exact (MK_COMB (@lem1538664) (@lem1538665 d)). Qed.
Lemma lem1538667 (d : real) : (term385 d) = (term391 d).
Proof. exact (TRANS (@lem1538659 d) (@lem1538666 d)). Qed.
Lemma lem1538668 (d : real) : (term391 d) = term49.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1538669 (d : real) : (term385 d) = term49.
Proof. exact (TRANS (@lem1538667 d) (@lem1538668 d)). Qed.
Lemma lem1538670 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538671 (d : real) : (term392 d) = term308.
Proof. exact (MK_COMB (@lem1538670) (@lem1538669 d)). Qed.
Lemma lem1538672 (x : real) (y : real) : (term416 x y) = (term417 x y).
Proof. exact (@lem1483480 (term61 x) x y (term61 y)). Qed.
Lemma lem1538673 (x : real) : (term395 x) = (term386 x).
Proof. exact (@lem1483440 term67 x). Qed.
Lemma lem1538675 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538676 : term388 = term49.
Proof. exact (@lem1538675 term54). Qed.
Lemma lem1538677 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538678 : term389 = term390.
Proof. exact (MK_COMB (@lem1538677) (@lem1538676)). Qed.
Lemma lem1538679 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538680 (x : real) : (term386 x) = (term391 x).
Proof. exact (MK_COMB (@lem1538678) (@lem1538679 x)). Qed.
Lemma lem1538681 (x : real) : (term395 x) = (term391 x).
Proof. exact (TRANS (@lem1538673 x) (@lem1538680 x)). Qed.
Lemma lem1538682 (x : real) : (term391 x) = term49.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1538683 (x : real) : (term395 x) = term49.
Proof. exact (TRANS (@lem1538681 x) (@lem1538682 x)). Qed.
Lemma lem1538684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538685 (x : real) : (term418 x) = term308.
Proof. exact (MK_COMB (@lem1538684) (@lem1538683 x)). Qed.
Lemma lem1538686 (y : real) : (term385 y) = (term386 y).
Proof. exact (@lem1483442 term67 y). Qed.
Lemma lem1538688 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538689 : term388 = term49.
Proof. exact (@lem1538688 term54). Qed.
Lemma lem1538690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538691 : term389 = term390.
Proof. exact (MK_COMB (@lem1538690) (@lem1538689)). Qed.
Lemma lem1538692 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1538693 (y : real) : (term386 y) = (term391 y).
Proof. exact (MK_COMB (@lem1538691) (@lem1538692 y)). Qed.
Lemma lem1538694 (y : real) : (term385 y) = (term391 y).
Proof. exact (TRANS (@lem1538686 y) (@lem1538693 y)). Qed.
Lemma lem1538695 (y : real) : (term391 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1538696 (y : real) : (term385 y) = term49.
Proof. exact (TRANS (@lem1538694 y) (@lem1538695 y)). Qed.
Lemma lem1538697 (x : real) (y : real) : (term417 x y) = term396.
Proof. exact (MK_COMB (@lem1538685 x) (@lem1538696 y)). Qed.
Lemma lem1538698 (x : real) (y : real) : (term416 x y) = term396.
Proof. exact (TRANS (@lem1538672 x y) (@lem1538697 x y)). Qed.
Lemma lem1538699 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1538700 (x : real) (y : real) : (term416 x y) = term49.
Proof. exact (TRANS (@lem1538698 x y) (@lem1538699)). Qed.
Lemma lem1538701 (d : real) (x : real) (y : real) : (term415 d x y) = term396.
Proof. exact (MK_COMB (@lem1538671 d) (@lem1538700 x y)). Qed.
Lemma lem1538702 (d : real) (x : real) (y : real) : (term414 d x y) = term396.
Proof. exact (TRANS (@lem1538658 d x y) (@lem1538701 d x y)). Qed.
Lemma lem1538703 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1538704 (d : real) (x : real) (y : real) : (term414 d x y) = term49.
Proof. exact (TRANS (@lem1538702 d x y) (@lem1538703)). Qed.
Lemma lem1538705 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538706 (d : real) (x : real) (y : real) : (term419 d x y) = term398.
Proof. exact (MK_COMB (@lem1538705) (@lem1538704 d x y)). Qed.
Lemma lem1538707 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538708 (d : real) (x : real) (y : real) : (term413 d x y) = term399.
Proof. exact (MK_COMB (@lem1538706 d x y) (@lem1538707)). Qed.
Lemma lem1538709 (d : real) (x : real) (y : real) (h1 : term328 d x y) : term399.
Proof. exact (EQ_MP (@lem1538708 d x y) (@lem1538657 d x y h1)). Qed.
Lemma lem1538711 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538712 : term399 = term400.
Proof. exact (@lem1538711 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1538713 : term400 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1538714 : term399 = False.
Proof. exact (TRANS (@lem1538712) (@lem1538713)). Qed.
Lemma lem1538715 (d : real) (x : real) (y : real) (h1 : term328 d x y) : False.
Proof. exact (EQ_MP (@lem1538714) (@lem1538709 d x y h1)). Qed.
Lemma lem1538716 (d : real) (x : real) (y : real) (h1 : term330 d x y) : False.
Proof. exact (or_elim (@lem1538487 d x y h1) (fun h0 : term301 d x y => @lem1538601 d x y h0) (fun h0 : term328 d x y => @lem1538715 d x y h0)). Qed.
Lemma lem1538717 (d : real) (x : real) (y : real) (h1 : term360 d x y) : term360 d x y.
Proof. exact (h1). Qed.
Lemma lem1538718 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term349 d x y.
Proof. exact (h1). Qed.
Lemma lem1538719 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term346 d x y.
Proof. exact (proj2 (@lem1538718 d x y h1)). Qed.
Lemma lem1538720 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term118 d.
Proof. exact (proj1 (@lem1538718 d x y h1)). Qed.
Lemma lem1538721 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term85 d x y.
Proof. exact (proj2 (@lem1538719 d x y h1)). Qed.
Lemma lem1538722 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term92 d x y.
Proof. exact (proj1 (@lem1538719 d x y h1)). Qed.
Lemma lem1538724 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538725 : term420 = term421.
Proof. exact (@lem1538724 (NUMERAL 0) term422). Qed.
Lemma lem1538726 : term423 = term424.
Proof. exact (@lem912803). Qed.
Lemma lem1538727 (h1 : term423 = term424) : term421 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term424 h1). Qed.
Lemma lem1538728 : (term423 = term424) = (term421 = True).
Proof. exact (prop_ext (fun h1 : term423 = term424 => @lem1538727 h1) (fun h1 : term421 = True => @lem1538726)). Qed.
Lemma lem1538729 : term421 = True.
Proof. exact (EQ_MP (@lem1538728) (@lem1538726)). Qed.
Lemma lem1538730 : term420 = True.
Proof. exact (TRANS (@lem1538725) (@lem1538729)). Qed.
Lemma lem1538731 : True = term420.
Proof. exact (SYM (@lem1538730)). Qed.
Lemma lem1538732 : term420.
Proof. exact (EQ_MP (@lem1538731) (@lem0)). Qed.
Lemma lem1538733 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term425 d.
Proof. exact (conj (@lem1538732) (@lem1538720 d x y h1)). Qed.
Lemma lem1538735 (x : real) (y : real) : term368 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1538736 (d : real) : term426 d.
Proof. exact (@lem1538735 term427 (term61 d)). Qed.
Lemma lem1538737 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term428 d.
Proof. exact (@lem1538736 d (@lem1538733 d x y h1)). Qed.
Lemma lem1538738 (d : real) : (term429 d) = (term430 d).
Proof. exact (@lem1483476 term427 term67 d). Qed.
Lemma lem1538740 (m : nat) (n : nat) : (term431 m n) = (term432 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1538741 : term433 = term434.
Proof. exact (@lem1538740 term422 term54). Qed.
Lemma lem1538742 : term435 = term424.
Proof. exact (@lem996237 term424). Qed.
Lemma lem1538743 : (term435 = term424) = (term436 = term422).
Proof. exact (@lem1007663 term424 (BIT1 0) term424). Qed.
Lemma lem1538744 : term436 = term422.
Proof. exact (EQ_MP (@lem1538743) (@lem1538742)). Qed.
Lemma lem1538745 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538746 : term437 = term427.
Proof. exact (MK_COMB (@lem1538745) (@lem1538744)). Qed.
Lemma lem1538747 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1538748 : term434 = term438.
Proof. exact (MK_COMB (@lem1538747) (@lem1538746)). Qed.
Lemma lem1538749 : term433 = term438.
Proof. exact (TRANS (@lem1538741) (@lem1538748)). Qed.
Lemma lem1538750 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538751 : term439 = term440.
Proof. exact (MK_COMB (@lem1538750) (@lem1538749)). Qed.
Lemma lem1538752 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1538753 (d : real) : (term430 d) = (term441 d).
Proof. exact (MK_COMB (@lem1538751) (@lem1538752 d)). Qed.
Lemma lem1538754 (d : real) : (term429 d) = (term441 d).
Proof. exact (TRANS (@lem1538738 d) (@lem1538753 d)). Qed.
Lemma lem1538755 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1538756 (d : real) : (term442 d) = (term443 d).
Proof. exact (MK_COMB (@lem1538755) (@lem1538754 d)). Qed.
Lemma lem1538757 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538758 (d : real) : (term428 d) = (term444 d).
Proof. exact (MK_COMB (@lem1538756 d) (@lem1538757)). Qed.
Lemma lem1538759 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term444 d.
Proof. exact (EQ_MP (@lem1538758 d) (@lem1538737 d x y h1)). Qed.
Lemma lem1538761 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538762 : term364 = term365.
Proof. exact (@lem1538761 (NUMERAL 0) term54). Qed.
Lemma lem1538763 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538764 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538765 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538764 h1) (fun h1 : term365 = True => @lem1538763)). Qed.
Lemma lem1538766 : term365 = True.
Proof. exact (EQ_MP (@lem1538765) (@lem1538763)). Qed.
Lemma lem1538767 : term364 = True.
Proof. exact (TRANS (@lem1538762) (@lem1538766)). Qed.
Lemma lem1538768 : True = term364.
Proof. exact (SYM (@lem1538767)). Qed.
Lemma lem1538769 : term364.
Proof. exact (EQ_MP (@lem1538768) (@lem0)). Qed.
Lemma lem1538770 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term406 d x y.
Proof. exact (conj (@lem1538769) (@lem1538721 d x y h1)). Qed.
Lemma lem1538772 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1538773 (d : real) (x : real) (y : real) : term407 d x y.
Proof. exact (@lem1538772 term76 (term82 d x y)). Qed.
Lemma lem1538774 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term408 d x y.
Proof. exact (@lem1538773 d x y (@lem1538770 d x y h1)). Qed.
Lemma lem1538775 (d : real) (x : real) (y : real) : (term409 d x y) = (term82 d x y).
Proof. exact (@lem1483460 (term82 d x y)). Qed.
Lemma lem1538776 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538777 (d : real) (x : real) (y : real) : (term410 d x y) = (term84 d x y).
Proof. exact (MK_COMB (@lem1538776) (@lem1538775 d x y)). Qed.
Lemma lem1538778 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538779 (d : real) (x : real) (y : real) : (term408 d x y) = (term85 d x y).
Proof. exact (MK_COMB (@lem1538777 d x y) (@lem1538778)). Qed.
Lemma lem1538780 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term85 d x y.
Proof. exact (EQ_MP (@lem1538779 d x y) (@lem1538774 d x y h1)). Qed.
Lemma lem1538782 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538783 : term364 = term365.
Proof. exact (@lem1538782 (NUMERAL 0) term54). Qed.
Lemma lem1538784 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538785 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538786 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538785 h1) (fun h1 : term365 = True => @lem1538784)). Qed.
Lemma lem1538787 : term365 = True.
Proof. exact (EQ_MP (@lem1538786) (@lem1538784)). Qed.
Lemma lem1538788 : term364 = True.
Proof. exact (TRANS (@lem1538783) (@lem1538787)). Qed.
Lemma lem1538789 : True = term364.
Proof. exact (SYM (@lem1538788)). Qed.
Lemma lem1538790 : term364.
Proof. exact (EQ_MP (@lem1538789) (@lem0)). Qed.
Lemma lem1538791 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term373 d x y.
Proof. exact (conj (@lem1538790) (@lem1538722 d x y h1)). Qed.
Lemma lem1538793 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1538794 (d : real) (x : real) (y : real) : term375 d x y.
Proof. exact (@lem1538793 term76 (term81 d x y)). Qed.
Lemma lem1538795 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term376 d x y.
Proof. exact (@lem1538794 d x y (@lem1538791 d x y h1)). Qed.
Lemma lem1538796 (d : real) (x : real) (y : real) : (term377 d x y) = (term81 d x y).
Proof. exact (@lem1483460 (term81 d x y)). Qed.
Lemma lem1538797 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538798 (d : real) (x : real) (y : real) : (term378 d x y) = (term91 d x y).
Proof. exact (MK_COMB (@lem1538797) (@lem1538796 d x y)). Qed.
Lemma lem1538799 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538800 (d : real) (x : real) (y : real) : (term376 d x y) = (term92 d x y).
Proof. exact (MK_COMB (@lem1538798 d x y) (@lem1538799)). Qed.
Lemma lem1538801 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term92 d x y.
Proof. exact (EQ_MP (@lem1538800 d x y) (@lem1538795 d x y h1)). Qed.
Lemma lem1538802 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term346 d x y.
Proof. exact (conj (@lem1538801 d x y h1) (@lem1538780 d x y h1)). Qed.
Lemma lem1538804 (x : real) (y : real) : term445 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1538805 (d : real) (x : real) (y : real) : term446 d x y.
Proof. exact (@lem1538804 (term81 d x y) (term82 d x y)). Qed.
Lemma lem1538806 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term447 d x y.
Proof. exact (@lem1538805 d x y (@lem1538802 d x y h1)). Qed.
Lemma lem1538807 (d : real) (x : real) (y : real) : (term448 d x y) = (term449 d x y).
Proof. exact (@lem1483480 d d (term59 x y) (term60 x y)). Qed.
Lemma lem1538808 (d : real) : (real_add d d) = (term450 d).
Proof. exact (@lem1483444 d). Qed.
Lemma lem1538809 : term451 = term452.
Proof. exact (@lem1367770 term54 term54). Qed.
Lemma lem1538810 : term453 = term424.
Proof. exact (@lem706885). Qed.
Lemma lem1538811 : (term453 = term424) = (term454 = term422).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term424). Qed.
Lemma lem1538812 : term454 = term422.
Proof. exact (EQ_MP (@lem1538811) (@lem1538810)). Qed.
Lemma lem1538813 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1538814 : term452 = term427.
Proof. exact (MK_COMB (@lem1538813) (@lem1538812)). Qed.
Lemma lem1538815 : term451 = term427.
Proof. exact (TRANS (@lem1538809) (@lem1538814)). Qed.
Lemma lem1538816 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538817 : term455 = term456.
Proof. exact (MK_COMB (@lem1538816) (@lem1538815)). Qed.
Lemma lem1538818 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1538819 (d : real) : (term450 d) = (term457 d).
Proof. exact (MK_COMB (@lem1538817) (@lem1538818 d)). Qed.
Lemma lem1538820 (d : real) : (real_add d d) = (term457 d).
Proof. exact (TRANS (@lem1538808 d) (@lem1538819 d)). Qed.
Lemma lem1538821 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538822 (d : real) : (term458 d) = (term459 d).
Proof. exact (MK_COMB (@lem1538821) (@lem1538820 d)). Qed.
Lemma lem1538823 (x : real) (y : real) : (term393 x y) = (term394 x y).
Proof. exact (@lem1483480 x (term61 x) (term61 y) y). Qed.
Lemma lem1538824 (x : real) : (term385 x) = (term386 x).
Proof. exact (@lem1483442 term67 x). Qed.
Lemma lem1538826 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538827 : term388 = term49.
Proof. exact (@lem1538826 term54). Qed.
Lemma lem1538828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538829 : term389 = term390.
Proof. exact (MK_COMB (@lem1538828) (@lem1538827)). Qed.
Lemma lem1538830 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538831 (x : real) : (term386 x) = (term391 x).
Proof. exact (MK_COMB (@lem1538829) (@lem1538830 x)). Qed.
Lemma lem1538832 (x : real) : (term385 x) = (term391 x).
Proof. exact (TRANS (@lem1538824 x) (@lem1538831 x)). Qed.
Lemma lem1538833 (x : real) : (term391 x) = term49.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1538834 (x : real) : (term385 x) = term49.
Proof. exact (TRANS (@lem1538832 x) (@lem1538833 x)). Qed.
Lemma lem1538835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538836 (x : real) : (term392 x) = term308.
Proof. exact (MK_COMB (@lem1538835) (@lem1538834 x)). Qed.
Lemma lem1538837 (y : real) : (term395 y) = (term386 y).
Proof. exact (@lem1483440 term67 y). Qed.
Lemma lem1538839 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538840 : term388 = term49.
Proof. exact (@lem1538839 term54). Qed.
Lemma lem1538841 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538842 : term389 = term390.
Proof. exact (MK_COMB (@lem1538841) (@lem1538840)). Qed.
Lemma lem1538843 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1538844 (y : real) : (term386 y) = (term391 y).
Proof. exact (MK_COMB (@lem1538842) (@lem1538843 y)). Qed.
Lemma lem1538845 (y : real) : (term395 y) = (term391 y).
Proof. exact (TRANS (@lem1538837 y) (@lem1538844 y)). Qed.
Lemma lem1538846 (y : real) : (term391 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1538847 (y : real) : (term395 y) = term49.
Proof. exact (TRANS (@lem1538845 y) (@lem1538846 y)). Qed.
Lemma lem1538848 (x : real) (y : real) : (term394 x y) = term396.
Proof. exact (MK_COMB (@lem1538836 x) (@lem1538847 y)). Qed.
Lemma lem1538849 (x : real) (y : real) : (term393 x y) = term396.
Proof. exact (TRANS (@lem1538823 x y) (@lem1538848 x y)). Qed.
Lemma lem1538850 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1538851 (x : real) (y : real) : (term393 x y) = term49.
Proof. exact (TRANS (@lem1538849 x y) (@lem1538850)). Qed.
Lemma lem1538852 (x : real) (y : real) (d : real) : (term449 d x y) = (term460 d).
Proof. exact (MK_COMB (@lem1538822 d) (@lem1538851 x y)). Qed.
Lemma lem1538853 (x : real) (y : real) (d : real) : (term448 d x y) = (term460 d).
Proof. exact (TRANS (@lem1538807 d x y) (@lem1538852 x y d)). Qed.
Lemma lem1538854 (d : real) : (term460 d) = (term457 d).
Proof. exact (@lem1483450 (term457 d)). Qed.
Lemma lem1538855 (x : real) (y : real) (d : real) : (term448 d x y) = (term457 d).
Proof. exact (TRANS (@lem1538853 x y d) (@lem1538854 d)). Qed.
Lemma lem1538856 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538857 (x : real) (y : real) (d : real) : (term461 d x y) = (term462 d).
Proof. exact (MK_COMB (@lem1538856) (@lem1538855 x y d)). Qed.
Lemma lem1538858 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538859 (x : real) (y : real) (d : real) : (term447 d x y) = (term463 d).
Proof. exact (MK_COMB (@lem1538857 x y d) (@lem1538858)). Qed.
Lemma lem1538860 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term463 d.
Proof. exact (EQ_MP (@lem1538859 x y d) (@lem1538806 d x y h1)). Qed.
Lemma lem1538862 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538863 : term364 = term365.
Proof. exact (@lem1538862 (NUMERAL 0) term54). Qed.
Lemma lem1538864 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538865 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538866 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538865 h1) (fun h1 : term365 = True => @lem1538864)). Qed.
Lemma lem1538867 : term365 = True.
Proof. exact (EQ_MP (@lem1538866) (@lem1538864)). Qed.
Lemma lem1538868 : term364 = True.
Proof. exact (TRANS (@lem1538863) (@lem1538867)). Qed.
Lemma lem1538869 : True = term364.
Proof. exact (SYM (@lem1538868)). Qed.
Lemma lem1538870 : term364.
Proof. exact (EQ_MP (@lem1538869) (@lem0)). Qed.
Lemma lem1538871 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term464 d.
Proof. exact (conj (@lem1538870) (@lem1538860 d x y h1)). Qed.
Lemma lem1538873 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1538874 (d : real) : term465 d.
Proof. exact (@lem1538873 term76 (term457 d)). Qed.
Lemma lem1538875 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term466 d.
Proof. exact (@lem1538874 d (@lem1538871 d x y h1)). Qed.
Lemma lem1538876 (d : real) : (term467 d) = (term457 d).
Proof. exact (@lem1483460 (term457 d)). Qed.
Lemma lem1538877 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538878 (d : real) : (term468 d) = (term462 d).
Proof. exact (MK_COMB (@lem1538877) (@lem1538876 d)). Qed.
Lemma lem1538879 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538880 (d : real) : (term466 d) = (term463 d).
Proof. exact (MK_COMB (@lem1538878 d) (@lem1538879)). Qed.
Lemma lem1538881 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term463 d.
Proof. exact (EQ_MP (@lem1538880 d) (@lem1538875 d x y h1)). Qed.
Lemma lem1538882 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term469 d.
Proof. exact (conj (@lem1538881 d x y h1) (@lem1538759 d x y h1)). Qed.
Lemma lem1538884 (x : real) (y : real) : term380 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1538885 (d : real) : term470 d.
Proof. exact (@lem1538884 (term457 d) (term441 d)). Qed.
Lemma lem1538886 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term471 d.
Proof. exact (@lem1538885 d (@lem1538882 d x y h1)). Qed.
Lemma lem1538887 (d : real) : (term472 d) = (term473 d).
Proof. exact (@lem1483438 term427 term438 d). Qed.
Lemma lem1538889 (m : nat) : (term474 m) = term49.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1538890 : term475 = term49.
Proof. exact (@lem1538889 term422). Qed.
Lemma lem1538891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538892 : term476 = term390.
Proof. exact (MK_COMB (@lem1538891) (@lem1538890)). Qed.
Lemma lem1538893 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1538894 (d : real) : (term473 d) = (term391 d).
Proof. exact (MK_COMB (@lem1538892) (@lem1538893 d)). Qed.
Lemma lem1538895 (d : real) : (term472 d) = (term391 d).
Proof. exact (TRANS (@lem1538887 d) (@lem1538894 d)). Qed.
Lemma lem1538896 (d : real) : (term391 d) = term49.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1538897 (d : real) : (term472 d) = term49.
Proof. exact (TRANS (@lem1538895 d) (@lem1538896 d)). Qed.
Lemma lem1538898 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538899 (d : real) : (term477 d) = term398.
Proof. exact (MK_COMB (@lem1538898) (@lem1538897 d)). Qed.
Lemma lem1538900 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538901 (d : real) : (term471 d) = term399.
Proof. exact (MK_COMB (@lem1538899 d) (@lem1538900)). Qed.
Lemma lem1538902 (d : real) (x : real) (y : real) (h1 : term349 d x y) : term399.
Proof. exact (EQ_MP (@lem1538901 d) (@lem1538886 d x y h1)). Qed.
Lemma lem1538904 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538905 : term399 = term400.
Proof. exact (@lem1538904 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1538906 : term400 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1538907 : term399 = False.
Proof. exact (TRANS (@lem1538905) (@lem1538906)). Qed.
Lemma lem1538908 (d : real) (x : real) (y : real) (h1 : term349 d x y) : False.
Proof. exact (EQ_MP (@lem1538907) (@lem1538902 d x y h1)). Qed.
Lemma lem1538909 (d : real) (x : real) (y : real) (h1 : term358 d x y) : term358 d x y.
Proof. exact (h1). Qed.
Lemma lem1538910 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term352 d x y.
Proof. exact (h1). Qed.
Lemma lem1538911 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term346 d x y.
Proof. exact (proj2 (@lem1538910 d x y h1)). Qed.
Lemma lem1538912 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term129 d x y.
Proof. exact (proj1 (@lem1538910 d x y h1)). Qed.
Lemma lem1538913 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term85 d x y.
Proof. exact (proj2 (@lem1538911 d x y h1)). Qed.
Lemma lem1538916 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538917 : term364 = term365.
Proof. exact (@lem1538916 (NUMERAL 0) term54). Qed.
Lemma lem1538918 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538919 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538920 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538919 h1) (fun h1 : term365 = True => @lem1538918)). Qed.
Lemma lem1538921 : term365 = True.
Proof. exact (EQ_MP (@lem1538920) (@lem1538918)). Qed.
Lemma lem1538922 : term364 = True.
Proof. exact (TRANS (@lem1538917) (@lem1538921)). Qed.
Lemma lem1538923 : True = term364.
Proof. exact (SYM (@lem1538922)). Qed.
Lemma lem1538924 : term364.
Proof. exact (EQ_MP (@lem1538923) (@lem0)). Qed.
Lemma lem1538925 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term401 d x y.
Proof. exact (conj (@lem1538924) (@lem1538912 d x y h1)). Qed.
Lemma lem1538927 (x : real) (y : real) : term368 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1538928 (d : real) (x : real) (y : real) : term402 d x y.
Proof. exact (@lem1538927 term76 (term126 d x y)). Qed.
Lemma lem1538929 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term403 d x y.
Proof. exact (@lem1538928 d x y (@lem1538925 d x y h1)). Qed.
Lemma lem1538930 (d : real) (x : real) (y : real) : (term404 d x y) = (term126 d x y).
Proof. exact (@lem1483460 (term126 d x y)). Qed.
Lemma lem1538931 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1538932 (d : real) (x : real) (y : real) : (term405 d x y) = (term128 d x y).
Proof. exact (MK_COMB (@lem1538931) (@lem1538930 d x y)). Qed.
Lemma lem1538933 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538934 (d : real) (x : real) (y : real) : (term403 d x y) = (term129 d x y).
Proof. exact (MK_COMB (@lem1538932 d x y) (@lem1538933)). Qed.
Lemma lem1538935 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term129 d x y.
Proof. exact (EQ_MP (@lem1538934 d x y) (@lem1538929 d x y h1)). Qed.
Lemma lem1538937 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1538938 : term364 = term365.
Proof. exact (@lem1538937 (NUMERAL 0) term54). Qed.
Lemma lem1538939 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1538940 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1538941 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1538940 h1) (fun h1 : term365 = True => @lem1538939)). Qed.
Lemma lem1538942 : term365 = True.
Proof. exact (EQ_MP (@lem1538941) (@lem1538939)). Qed.
Lemma lem1538943 : term364 = True.
Proof. exact (TRANS (@lem1538938) (@lem1538942)). Qed.
Lemma lem1538944 : True = term364.
Proof. exact (SYM (@lem1538943)). Qed.
Lemma lem1538945 : term364.
Proof. exact (EQ_MP (@lem1538944) (@lem0)). Qed.
Lemma lem1538946 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term406 d x y.
Proof. exact (conj (@lem1538945) (@lem1538913 d x y h1)). Qed.
Lemma lem1538948 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1538949 (d : real) (x : real) (y : real) : term407 d x y.
Proof. exact (@lem1538948 term76 (term82 d x y)). Qed.
Lemma lem1538950 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term408 d x y.
Proof. exact (@lem1538949 d x y (@lem1538946 d x y h1)). Qed.
Lemma lem1538951 (d : real) (x : real) (y : real) : (term409 d x y) = (term82 d x y).
Proof. exact (@lem1483460 (term82 d x y)). Qed.
Lemma lem1538952 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1538953 (d : real) (x : real) (y : real) : (term410 d x y) = (term84 d x y).
Proof. exact (MK_COMB (@lem1538952) (@lem1538951 d x y)). Qed.
Lemma lem1538954 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1538955 (d : real) (x : real) (y : real) : (term408 d x y) = (term85 d x y).
Proof. exact (MK_COMB (@lem1538953 d x y) (@lem1538954)). Qed.
Lemma lem1538956 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term85 d x y.
Proof. exact (EQ_MP (@lem1538955 d x y) (@lem1538950 d x y h1)). Qed.
Lemma lem1538957 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term411 d x y.
Proof. exact (conj (@lem1538956 d x y h1) (@lem1538935 d x y h1)). Qed.
Lemma lem1538959 (x : real) (y : real) : term380 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1538960 (d : real) (x : real) (y : real) : term412 d x y.
Proof. exact (@lem1538959 (term82 d x y) (term126 d x y)). Qed.
Lemma lem1538961 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term413 d x y.
Proof. exact (@lem1538960 d x y (@lem1538957 d x y h1)). Qed.
Lemma lem1538962 (d : real) (x : real) (y : real) : (term414 d x y) = (term415 d x y).
Proof. exact (@lem1483480 d (term61 d) (term60 x y) (term59 x y)). Qed.
Lemma lem1538963 (d : real) : (term385 d) = (term386 d).
Proof. exact (@lem1483442 term67 d). Qed.
Lemma lem1538965 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538966 : term388 = term49.
Proof. exact (@lem1538965 term54). Qed.
Lemma lem1538967 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538968 : term389 = term390.
Proof. exact (MK_COMB (@lem1538967) (@lem1538966)). Qed.
Lemma lem1538969 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1538970 (d : real) : (term386 d) = (term391 d).
Proof. exact (MK_COMB (@lem1538968) (@lem1538969 d)). Qed.
Lemma lem1538971 (d : real) : (term385 d) = (term391 d).
Proof. exact (TRANS (@lem1538963 d) (@lem1538970 d)). Qed.
Lemma lem1538972 (d : real) : (term391 d) = term49.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1538973 (d : real) : (term385 d) = term49.
Proof. exact (TRANS (@lem1538971 d) (@lem1538972 d)). Qed.
Lemma lem1538974 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538975 (d : real) : (term392 d) = term308.
Proof. exact (MK_COMB (@lem1538974) (@lem1538973 d)). Qed.
Lemma lem1538976 (x : real) (y : real) : (term416 x y) = (term417 x y).
Proof. exact (@lem1483480 (term61 x) x y (term61 y)). Qed.
Lemma lem1538977 (x : real) : (term395 x) = (term386 x).
Proof. exact (@lem1483440 term67 x). Qed.
Lemma lem1538979 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538980 : term388 = term49.
Proof. exact (@lem1538979 term54). Qed.
Lemma lem1538981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538982 : term389 = term390.
Proof. exact (MK_COMB (@lem1538981) (@lem1538980)). Qed.
Lemma lem1538983 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1538984 (x : real) : (term386 x) = (term391 x).
Proof. exact (MK_COMB (@lem1538982) (@lem1538983 x)). Qed.
Lemma lem1538985 (x : real) : (term395 x) = (term391 x).
Proof. exact (TRANS (@lem1538977 x) (@lem1538984 x)). Qed.
Lemma lem1538986 (x : real) : (term391 x) = term49.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1538987 (x : real) : (term395 x) = term49.
Proof. exact (TRANS (@lem1538985 x) (@lem1538986 x)). Qed.
Lemma lem1538988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1538989 (x : real) : (term418 x) = term308.
Proof. exact (MK_COMB (@lem1538988) (@lem1538987 x)). Qed.
Lemma lem1538990 (y : real) : (term385 y) = (term386 y).
Proof. exact (@lem1483442 term67 y). Qed.
Lemma lem1538992 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1538993 : term388 = term49.
Proof. exact (@lem1538992 term54). Qed.
Lemma lem1538994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1538995 : term389 = term390.
Proof. exact (MK_COMB (@lem1538994) (@lem1538993)). Qed.
Lemma lem1538996 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1538997 (y : real) : (term386 y) = (term391 y).
Proof. exact (MK_COMB (@lem1538995) (@lem1538996 y)). Qed.
Lemma lem1538998 (y : real) : (term385 y) = (term391 y).
Proof. exact (TRANS (@lem1538990 y) (@lem1538997 y)). Qed.
Lemma lem1538999 (y : real) : (term391 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1539000 (y : real) : (term385 y) = term49.
Proof. exact (TRANS (@lem1538998 y) (@lem1538999 y)). Qed.
Lemma lem1539001 (x : real) (y : real) : (term417 x y) = term396.
Proof. exact (MK_COMB (@lem1538989 x) (@lem1539000 y)). Qed.
Lemma lem1539002 (x : real) (y : real) : (term416 x y) = term396.
Proof. exact (TRANS (@lem1538976 x y) (@lem1539001 x y)). Qed.
Lemma lem1539003 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1539004 (x : real) (y : real) : (term416 x y) = term49.
Proof. exact (TRANS (@lem1539002 x y) (@lem1539003)). Qed.
Lemma lem1539005 (d : real) (x : real) (y : real) : (term415 d x y) = term396.
Proof. exact (MK_COMB (@lem1538975 d) (@lem1539004 x y)). Qed.
Lemma lem1539006 (d : real) (x : real) (y : real) : (term414 d x y) = term396.
Proof. exact (TRANS (@lem1538962 d x y) (@lem1539005 d x y)). Qed.
Lemma lem1539007 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1539008 (d : real) (x : real) (y : real) : (term414 d x y) = term49.
Proof. exact (TRANS (@lem1539006 d x y) (@lem1539007)). Qed.
Lemma lem1539009 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539010 (d : real) (x : real) (y : real) : (term419 d x y) = term398.
Proof. exact (MK_COMB (@lem1539009) (@lem1539008 d x y)). Qed.
Lemma lem1539011 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1539012 (d : real) (x : real) (y : real) : (term413 d x y) = term399.
Proof. exact (MK_COMB (@lem1539010 d x y) (@lem1539011)). Qed.
Lemma lem1539013 (d : real) (x : real) (y : real) (h1 : term352 d x y) : term399.
Proof. exact (EQ_MP (@lem1539012 d x y) (@lem1538961 d x y h1)). Qed.
Lemma lem1539015 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539016 : term399 = term400.
Proof. exact (@lem1539015 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1539017 : term400 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1539018 : term399 = False.
Proof. exact (TRANS (@lem1539016) (@lem1539017)). Qed.
Lemma lem1539019 (d : real) (x : real) (y : real) (h1 : term352 d x y) : False.
Proof. exact (EQ_MP (@lem1539018) (@lem1539013 d x y h1)). Qed.
Lemma lem1539020 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term355 d x y.
Proof. exact (h1). Qed.
Lemma lem1539021 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term346 d x y.
Proof. exact (proj2 (@lem1539020 d x y h1)). Qed.
Lemma lem1539022 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term141 d x y.
Proof. exact (proj1 (@lem1539020 d x y h1)). Qed.
Lemma lem1539024 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term92 d x y.
Proof. exact (proj1 (@lem1539021 d x y h1)). Qed.
Lemma lem1539026 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539027 : term364 = term365.
Proof. exact (@lem1539026 (NUMERAL 0) term54). Qed.
Lemma lem1539028 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1539029 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1539030 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1539029 h1) (fun h1 : term365 = True => @lem1539028)). Qed.
Lemma lem1539031 : term365 = True.
Proof. exact (EQ_MP (@lem1539030) (@lem1539028)). Qed.
Lemma lem1539032 : term364 = True.
Proof. exact (TRANS (@lem1539027) (@lem1539031)). Qed.
Lemma lem1539033 : True = term364.
Proof. exact (SYM (@lem1539032)). Qed.
Lemma lem1539034 : term364.
Proof. exact (EQ_MP (@lem1539033) (@lem0)). Qed.
Lemma lem1539035 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term367 d x y.
Proof. exact (conj (@lem1539034) (@lem1539022 d x y h1)). Qed.
Lemma lem1539037 (x : real) (y : real) : term368 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1539038 (d : real) (x : real) (y : real) : term369 d x y.
Proof. exact (@lem1539037 term76 (term138 d x y)). Qed.
Lemma lem1539039 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term370 d x y.
Proof. exact (@lem1539038 d x y (@lem1539035 d x y h1)). Qed.
Lemma lem1539040 (d : real) (x : real) (y : real) : (term371 d x y) = (term138 d x y).
Proof. exact (@lem1483460 (term138 d x y)). Qed.
Lemma lem1539041 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1539042 (d : real) (x : real) (y : real) : (term372 d x y) = (term140 d x y).
Proof. exact (MK_COMB (@lem1539041) (@lem1539040 d x y)). Qed.
Lemma lem1539043 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1539044 (d : real) (x : real) (y : real) : (term370 d x y) = (term141 d x y).
Proof. exact (MK_COMB (@lem1539042 d x y) (@lem1539043)). Qed.
Lemma lem1539045 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term141 d x y.
Proof. exact (EQ_MP (@lem1539044 d x y) (@lem1539039 d x y h1)). Qed.
Lemma lem1539047 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539048 : term364 = term365.
Proof. exact (@lem1539047 (NUMERAL 0) term54). Qed.
Lemma lem1539049 : term366 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1539050 (h1 : term366 = (BIT1 0)) : term365 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1539051 : (term366 = (BIT1 0)) = (term365 = True).
Proof. exact (prop_ext (fun h1 : term366 = (BIT1 0) => @lem1539050 h1) (fun h1 : term365 = True => @lem1539049)). Qed.
Lemma lem1539052 : term365 = True.
Proof. exact (EQ_MP (@lem1539051) (@lem1539049)). Qed.
Lemma lem1539053 : term364 = True.
Proof. exact (TRANS (@lem1539048) (@lem1539052)). Qed.
Lemma lem1539054 : True = term364.
Proof. exact (SYM (@lem1539053)). Qed.
Lemma lem1539055 : term364.
Proof. exact (EQ_MP (@lem1539054) (@lem0)). Qed.
Lemma lem1539056 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term373 d x y.
Proof. exact (conj (@lem1539055) (@lem1539024 d x y h1)). Qed.
Lemma lem1539058 (x : real) (y : real) : term374 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1539059 (d : real) (x : real) (y : real) : term375 d x y.
Proof. exact (@lem1539058 term76 (term81 d x y)). Qed.
Lemma lem1539060 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term376 d x y.
Proof. exact (@lem1539059 d x y (@lem1539056 d x y h1)). Qed.
Lemma lem1539061 (d : real) (x : real) (y : real) : (term377 d x y) = (term81 d x y).
Proof. exact (@lem1483460 (term81 d x y)). Qed.
Lemma lem1539062 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539063 (d : real) (x : real) (y : real) : (term378 d x y) = (term91 d x y).
Proof. exact (MK_COMB (@lem1539062) (@lem1539061 d x y)). Qed.
Lemma lem1539064 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1539065 (d : real) (x : real) (y : real) : (term376 d x y) = (term92 d x y).
Proof. exact (MK_COMB (@lem1539063 d x y) (@lem1539064)). Qed.
Lemma lem1539066 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term92 d x y.
Proof. exact (EQ_MP (@lem1539065 d x y) (@lem1539060 d x y h1)). Qed.
Lemma lem1539067 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term379 d x y.
Proof. exact (conj (@lem1539066 d x y h1) (@lem1539045 d x y h1)). Qed.
Lemma lem1539069 (x : real) (y : real) : term380 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1539070 (d : real) (x : real) (y : real) : term381 d x y.
Proof. exact (@lem1539069 (term81 d x y) (term138 d x y)). Qed.
Lemma lem1539071 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term382 d x y.
Proof. exact (@lem1539070 d x y (@lem1539067 d x y h1)). Qed.
Lemma lem1539072 (d : real) (x : real) (y : real) : (term383 d x y) = (term384 d x y).
Proof. exact (@lem1483480 d (term61 d) (term59 x y) (term60 x y)). Qed.
Lemma lem1539073 (d : real) : (term385 d) = (term386 d).
Proof. exact (@lem1483442 term67 d). Qed.
Lemma lem1539075 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1539076 : term388 = term49.
Proof. exact (@lem1539075 term54). Qed.
Lemma lem1539077 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539078 : term389 = term390.
Proof. exact (MK_COMB (@lem1539077) (@lem1539076)). Qed.
Lemma lem1539079 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1539080 (d : real) : (term386 d) = (term391 d).
Proof. exact (MK_COMB (@lem1539078) (@lem1539079 d)). Qed.
Lemma lem1539081 (d : real) : (term385 d) = (term391 d).
Proof. exact (TRANS (@lem1539073 d) (@lem1539080 d)). Qed.
Lemma lem1539082 (d : real) : (term391 d) = term49.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1539083 (d : real) : (term385 d) = term49.
Proof. exact (TRANS (@lem1539081 d) (@lem1539082 d)). Qed.
Lemma lem1539084 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1539085 (d : real) : (term392 d) = term308.
Proof. exact (MK_COMB (@lem1539084) (@lem1539083 d)). Qed.
Lemma lem1539086 (x : real) (y : real) : (term393 x y) = (term394 x y).
Proof. exact (@lem1483480 x (term61 x) (term61 y) y). Qed.
Lemma lem1539087 (x : real) : (term385 x) = (term386 x).
Proof. exact (@lem1483442 term67 x). Qed.
Lemma lem1539089 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1539090 : term388 = term49.
Proof. exact (@lem1539089 term54). Qed.
Lemma lem1539091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539092 : term389 = term390.
Proof. exact (MK_COMB (@lem1539091) (@lem1539090)). Qed.
Lemma lem1539093 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1539094 (x : real) : (term386 x) = (term391 x).
Proof. exact (MK_COMB (@lem1539092) (@lem1539093 x)). Qed.
Lemma lem1539095 (x : real) : (term385 x) = (term391 x).
Proof. exact (TRANS (@lem1539087 x) (@lem1539094 x)). Qed.
Lemma lem1539096 (x : real) : (term391 x) = term49.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1539097 (x : real) : (term385 x) = term49.
Proof. exact (TRANS (@lem1539095 x) (@lem1539096 x)). Qed.
Lemma lem1539098 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1539099 (x : real) : (term392 x) = term308.
Proof. exact (MK_COMB (@lem1539098) (@lem1539097 x)). Qed.
Lemma lem1539100 (y : real) : (term395 y) = (term386 y).
Proof. exact (@lem1483440 term67 y). Qed.
Lemma lem1539102 (m : nat) : (term387 m) = term49.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1539103 : term388 = term49.
Proof. exact (@lem1539102 term54). Qed.
Lemma lem1539104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539105 : term389 = term390.
Proof. exact (MK_COMB (@lem1539104) (@lem1539103)). Qed.
Lemma lem1539106 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1539107 (y : real) : (term386 y) = (term391 y).
Proof. exact (MK_COMB (@lem1539105) (@lem1539106 y)). Qed.
Lemma lem1539108 (y : real) : (term395 y) = (term391 y).
Proof. exact (TRANS (@lem1539100 y) (@lem1539107 y)). Qed.
Lemma lem1539109 (y : real) : (term391 y) = term49.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1539110 (y : real) : (term395 y) = term49.
Proof. exact (TRANS (@lem1539108 y) (@lem1539109 y)). Qed.
Lemma lem1539111 (x : real) (y : real) : (term394 x y) = term396.
Proof. exact (MK_COMB (@lem1539099 x) (@lem1539110 y)). Qed.
Lemma lem1539112 (x : real) (y : real) : (term393 x y) = term396.
Proof. exact (TRANS (@lem1539086 x y) (@lem1539111 x y)). Qed.
Lemma lem1539113 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1539114 (x : real) (y : real) : (term393 x y) = term49.
Proof. exact (TRANS (@lem1539112 x y) (@lem1539113)). Qed.
Lemma lem1539115 (d : real) (x : real) (y : real) : (term384 d x y) = term396.
Proof. exact (MK_COMB (@lem1539085 d) (@lem1539114 x y)). Qed.
Lemma lem1539116 (d : real) (x : real) (y : real) : (term383 d x y) = term396.
Proof. exact (TRANS (@lem1539072 d x y) (@lem1539115 d x y)). Qed.
Lemma lem1539117 : term396 = term49.
Proof. exact (@lem1483448 term49). Qed.
Lemma lem1539118 (d : real) (x : real) (y : real) : (term383 d x y) = term49.
Proof. exact (TRANS (@lem1539116 d x y) (@lem1539117)). Qed.
Lemma lem1539119 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539120 (d : real) (x : real) (y : real) : (term397 d x y) = term398.
Proof. exact (MK_COMB (@lem1539119) (@lem1539118 d x y)). Qed.
Lemma lem1539121 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1539122 (d : real) (x : real) (y : real) : (term382 d x y) = term399.
Proof. exact (MK_COMB (@lem1539120 d x y) (@lem1539121)). Qed.
Lemma lem1539123 (d : real) (x : real) (y : real) (h1 : term355 d x y) : term399.
Proof. exact (EQ_MP (@lem1539122 d x y) (@lem1539071 d x y h1)). Qed.
Lemma lem1539125 (n : nat) (m : nat) : (term363 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539126 : term399 = term400.
Proof. exact (@lem1539125 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1539127 : term400 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1539128 : term399 = False.
Proof. exact (TRANS (@lem1539126) (@lem1539127)). Qed.
Lemma lem1539129 (d : real) (x : real) (y : real) (h1 : term355 d x y) : False.
Proof. exact (EQ_MP (@lem1539128) (@lem1539123 d x y h1)). Qed.
Lemma lem1539130 (d : real) (x : real) (y : real) (h1 : term358 d x y) : False.
Proof. exact (or_elim (@lem1538909 d x y h1) (fun h0 : term352 d x y => @lem1539019 d x y h0) (fun h0 : term355 d x y => @lem1539129 d x y h0)). Qed.
Lemma lem1539131 (d : real) (x : real) (y : real) (h1 : term360 d x y) : False.
Proof. exact (or_elim (@lem1538717 d x y h1) (fun h0 : term349 d x y => @lem1538908 d x y h0) (fun h0 : term358 d x y => @lem1539130 d x y h0)). Qed.
Lemma lem1539132 (d : real) (x : real) (y : real) (h1 : term362 d x y) : False.
Proof. exact (or_elim (@lem1538486 d x y h1) (fun h0 : term330 d x y => @lem1538716 d x y h0) (fun h0 : term360 d x y => @lem1539131 d x y h0)). Qed.
Lemma lem1539133 (d : real) (y : real) (x : real) (h1 : term242 d y x) : term242 d y x.
Proof. exact (h1). Qed.
Lemma lem1539134 (d : real) (y : real) (x : real) (h1 : term242 d y x) : term362 d x y.
Proof. exact (EQ_MP (@lem1538485 d x y) (@lem1539133 d y x h1)). Qed.
Lemma lem1539135 (d : real) (y : real) (x : real) (h1 : term242 d y x) : (term362 d x y) = False.
Proof. exact (prop_ext (fun h2 : term362 d x y => @lem1539132 d x y h2) (fun h2 : False => @lem1539134 d y x h1)). Qed.
Lemma lem1539136 (d : real) (y : real) (x : real) (h1 : term242 d y x) : False.
Proof. exact (EQ_MP (@lem1539135 d y x h1) (@lem1539134 d y x h1)). Qed.
Lemma lem1539137 (y : real) (x : real) (h1 : term244 y x) : term244 y x.
Proof. exact (h1). Qed.
Lemma lem1539138 (y : real) (x : real) (h1 : term244 y x) : False.
Proof. exact (ex_elim (@lem1539137 y x h1) (fun d : real => fun h0 : term243 y x d => @lem1539136 d y x h0)). Qed.
Lemma lem1539139 (x : real) (h1 : term246 x) : term246 x.
Proof. exact (h1). Qed.
Lemma lem1539140 (x : real) (h1 : term246 x) : False.
Proof. exact (ex_elim (@lem1539139 x h1) (fun y : real => fun h0 : term245 x y => @lem1539138 y x h0)). Qed.
Lemma lem1539141 (h1 : term248) : term248.
Proof. exact (h1). Qed.
Lemma lem1539142 (h1 : term248) : False.
Proof. exact (ex_elim (@lem1539141 h1) (fun x : real => fun h0 : term247 x => @lem1539140 x h0)). Qed.
Lemma lem1539143 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem1539144 (h1 : term39) : term248.
Proof. exact (EQ_MP (@lem1537849) (@lem1539143 h1)). Qed.
Lemma lem1539145 (h1 : term39) : term248 = False.
Proof. exact (prop_ext (fun h2 : term248 => @lem1539142 h2) (fun h2 : False => @lem1539144 h1)). Qed.
Lemma lem1539146 (h1 : term39) : False.
Proof. exact (EQ_MP (@lem1539145 h1) (@lem1539144 h1)). Qed.
Lemma lem1539147 : term478.
Proof. exact (fun h0 : term39 => @lem1539146 h0). Qed.
Lemma lem1539148 : term479.
Proof. exact (@lem1386578 term480). Qed.
Lemma lem1539149 : term480.
Proof. exact (@lem1539148 (@lem1539147)). Qed.
