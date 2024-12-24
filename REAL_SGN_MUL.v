Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_MUL_term_abbrevs.
Require Import REAL_ABS_MUL_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_SGN_spec.
Require Import real_div_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483466_spec.
Require Import thm1483478_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1733934 (x : real) : term0 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1733935 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1733936 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1733935 x) (@lem1733934 x)). Qed.
Lemma lem1733937 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1733936 x y). Qed.
Lemma lem1733938 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1733940 (x : real) : term5 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1733941 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1733942 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1733941 x) (@lem1733940 x)). Qed.
Lemma lem1733943 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1733942 x y). Qed.
Lemma lem1733944 (x : real) (y : real) : (term7 x y) = ((real_div x y) = (term8 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1733946 (x : real) : term9 x.
Proof. exact (@lem1582313 x). Qed.
Lemma lem1733947 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1733948 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1733947 x) (@lem1733946 x)). Qed.
Lemma lem1733949 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1733948 x y). Qed.
Lemma lem1733950 (x : real) (y : real) : (term11 x y) = ((term12 x y) = (term13 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1733952 (x : real) : term14 x.
Proof. exact (@lem1733933 x). Qed.
Lemma lem1733953 (x : real) : (term14 x) = ((real_sgn x) = (term15 x)).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1733966 (x : real) : (real_sgn x) = (term15 x).
Proof. exact (EQ_MP (@lem1733953 x) (@lem1733952 x)). Qed.
Lemma lem1733967 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (@lem1733966 (real_mul x y)). Qed.
Lemma lem1733969 (x : real) (y : real) : (real_div x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1733944 x y) (@lem1733943 x y)). Qed.
Lemma lem1733970 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (@lem1733969 (real_mul x y) (term12 x y)). Qed.
Lemma lem1733971 (x : real) (y : real) : (term16 x y) = (term18 x y).
Proof. exact (TRANS (@lem1733967 x y) (@lem1733970 x y)). Qed.
Lemma lem1733973 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1733950 x y) (@lem1733949 x y)). Qed.
Lemma lem1733974 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1733975 (x : real) (y : real) : (term19 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1733974) (@lem1733973 x y)). Qed.
Lemma lem1733977 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1733938 x y) (@lem1733937 x y)). Qed.
Lemma lem1733978 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (@lem1733977 (real_abs x) (real_abs y)). Qed.
Lemma lem1733979 (x : real) (y : real) : (term19 x y) = (term21 x y).
Proof. exact (TRANS (@lem1733975 x y) (@lem1733978 x y)). Qed.
Lemma lem1733980 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1733981 (x : real) (y : real) : (term18 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1733980 x y) (@lem1733979 x y)). Qed.
Lemma lem1733982 (x : real) (y : real) : (term16 x y) = (term23 x y).
Proof. exact (TRANS (@lem1733971 x y) (@lem1733981 x y)). Qed.
Lemma lem1733983 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1733984 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1733983) (@lem1733982 x y)). Qed.
Lemma lem1733986 (x : real) : (real_sgn x) = (term15 x).
Proof. exact (EQ_MP (@lem1733953 x) (@lem1733952 x)). Qed.
Lemma lem1733988 (x : real) (y : real) : (real_div x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1733944 x y) (@lem1733943 x y)). Qed.
Lemma lem1733989 (x : real) : (term15 x) = (term26 x).
Proof. exact (@lem1733988 x (real_abs x)). Qed.
Lemma lem1733990 (x : real) : (real_sgn x) = (term26 x).
Proof. exact (TRANS (@lem1733986 x) (@lem1733989 x)). Qed.
Lemma lem1733991 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1733992 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1733991) (@lem1733990 x)). Qed.
Lemma lem1733994 (x : real) : (real_sgn x) = (term15 x).
Proof. exact (EQ_MP (@lem1733953 x) (@lem1733952 x)). Qed.
Lemma lem1733995 (y : real) : (real_sgn y) = (term15 y).
Proof. exact (@lem1733994 y). Qed.
Lemma lem1733997 (x : real) (y : real) : (real_div x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1733944 x y) (@lem1733943 x y)). Qed.
Lemma lem1733998 (y : real) : (term15 y) = (term26 y).
Proof. exact (@lem1733997 y (real_abs y)). Qed.
Lemma lem1733999 (y : real) : (real_sgn y) = (term26 y).
Proof. exact (TRANS (@lem1733995 y) (@lem1733998 y)). Qed.
Lemma lem1734000 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1733992 x) (@lem1733999 y)). Qed.
Lemma lem1734001 (x : real) (y : real) : ((term16 x y) = (term29 x y)) = ((term23 x y) = (term30 x y)).
Proof. exact (MK_COMB (@lem1733984 x y) (@lem1734000 x y)). Qed.
Lemma lem1734004 (x : real) : (term31 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1734001 x y)). Qed.
Lemma lem1734005 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734006 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1734005) (@lem1734004 x)). Qed.
Lemma lem1734011 : term35 = term36.
Proof. exact (fun_ext (fun x : real => @lem1734006 x)). Qed.
Lemma lem1734012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1734013 : term37 = term38.
Proof. exact (MK_COMB (@lem1734012) (@lem1734011)). Qed.
Lemma lem1734018 : term38 = term37.
Proof. exact (SYM (@lem1734013)). Qed.
Lemma lem1734031 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1734032 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1734031 (term32 x)). Qed.
Lemma lem1734033 (x : real) (y : real) : (term43 x y) = ((term23 x y) = (term30 x y)).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1734034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1734036 (x : real) (y : real) : (term44 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1734034) (@lem1734033 x y)). Qed.
Lemma lem1734037 (x : real) : (term46 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem1734036 x y)). Qed.
Lemma lem1734038 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734039 (x : real) : (term42 x) = (term48 x).
Proof. exact (MK_COMB (@lem1734038) (@lem1734037 x)). Qed.
Lemma lem1734040 (x : real) : (term41 x) = (term48 x).
Proof. exact (TRANS (@lem1734032 x) (@lem1734039 x)). Qed.
Lemma lem1734041 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1734042 : term49 = term50.
Proof. exact (@lem1734041 term36). Qed.
Lemma lem1734043 (x : real) : (term51 x) = (term34 x).
Proof. exact (eq_refl (term51 x)). Qed.
Lemma lem1734044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1734045 (x : real) : (term52 x) = (term41 x).
Proof. exact (MK_COMB (@lem1734044) (@lem1734043 x)). Qed.
Lemma lem1734046 (x : real) : (term52 x) = (term48 x).
Proof. exact (TRANS (@lem1734045 x) (@lem1734040 x)). Qed.
Lemma lem1734047 : term53 = term54.
Proof. exact (fun_ext (fun x : real => @lem1734046 x)). Qed.
Lemma lem1734048 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734049 : term50 = term55.
Proof. exact (MK_COMB (@lem1734048) (@lem1734047)). Qed.
Lemma lem1734051 : term49 = term55.
Proof. exact (TRANS (@lem1734042) (@lem1734049)). Qed.
Lemma lem1734054 (x : real) (y : real) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1734055 (x : real) : (term47 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem1734054 x y)). Qed.
Lemma lem1734056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734057 (x : real) : (term48 x) = (term48 x).
Proof. exact (MK_COMB (@lem1734056) (@lem1734055 x)). Qed.
Lemma lem1734058 : term54 = term54.
Proof. exact (fun_ext (fun x : real => @lem1734057 x)). Qed.
Lemma lem1734059 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734060 : term55 = term55.
Proof. exact (MK_COMB (@lem1734059) (@lem1734058)). Qed.
Lemma lem1734061 : term49 = term55.
Proof. exact (TRANS (@lem1734051) (@lem1734060)). Qed.
Lemma lem1734062 (x : real) (y : real) : (term45 x y) = (term56 x y).
Proof. exact (@lem1483554 (term23 x y) (term30 x y)). Qed.
Lemma lem1734080 (x : real) (y : real) : (term30 x y) = (term57 x y).
Proof. exact (@lem1483466 x (term58 x) y (term58 y)). Qed.
Lemma lem1734085 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (@lem1483478 y (term58 x) (term58 y)). Qed.
Lemma lem1734086 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1734087 (x : real) (y : real) : (term57 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1734086 x) (@lem1734085 x y)). Qed.
Lemma lem1734089 (x : real) (y : real) : (term30 x y) = (term61 x y).
Proof. exact (TRANS (@lem1734080 x y) (@lem1734087 x y)). Qed.
Lemma lem1734112 (x : real) (y : real) : (term23 x y) = (term61 x y).
Proof. exact (@lem1483466 x y (term58 x) (term58 y)). Qed.
Lemma lem1734113 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1734114 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1734113) (@lem1734112 x y)). Qed.
Lemma lem1734115 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1734114 x y) (@lem1734089 x y)). Qed.
Lemma lem1734116 (x : real) (y : real) : (term65 x y) = (term66 x y).
Proof. exact (@lem1483519 (term61 x y) (term61 x y)). Qed.
Lemma lem1734120 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (@lem1483442 term68 (term61 x y)). Qed.
Lemma lem1734122 (m : nat) : (term69 m) = term70.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1734123 : term71 = term70.
Proof. exact (@lem1734122 term72). Qed.
Lemma lem1734124 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1734125 : term73 = term74.
Proof. exact (MK_COMB (@lem1734124) (@lem1734123)). Qed.
Lemma lem1734126 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1734127 (x : real) (y : real) : (term67 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1734125) (@lem1734126 x y)). Qed.
Lemma lem1734128 (x : real) (y : real) : (term66 x y) = (term75 x y).
Proof. exact (TRANS (@lem1734120 x y) (@lem1734127 x y)). Qed.
Lemma lem1734129 (x : real) (y : real) : (term75 x y) = term70.
Proof. exact (@lem1483446 (term61 x y)). Qed.
Lemma lem1734131 (x : real) (y : real) : (term66 x y) = term70.
Proof. exact (TRANS (@lem1734128 x y) (@lem1734129 x y)). Qed.
Lemma lem1734132 (x : real) (y : real) : (term65 x y) = term70.
Proof. exact (TRANS (@lem1734116 x y) (@lem1734131 x y)). Qed.
Lemma lem1734133 (x : real) (y : real) : (term64 x y) = term70.
Proof. exact (TRANS (@lem1734115 x y) (@lem1734132 x y)). Qed.
Lemma lem1734134 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1734135 (x : real) (y : real) : (term76 x y) = term77.
Proof. exact (MK_COMB (@lem1734134) (@lem1734133 x y)). Qed.
Lemma lem1734136 : term77 = term78.
Proof. exact (@lem1483512 term70). Qed.
Lemma lem1734138 (x : nat) : (term79 x) = term70.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1734139 : term78 = term70.
Proof. exact (@lem1734138 term72). Qed.
Lemma lem1734140 : term77 = term70.
Proof. exact (TRANS (@lem1734136) (@lem1734139)). Qed.
Lemma lem1734141 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1734142 (x : real) (y : real) : ((term76 x y) = term77) = ((term76 x y) = term70).
Proof. exact (MK_COMB (@lem1734141 x y) (@lem1734140)). Qed.
Lemma lem1734143 (x : real) (y : real) : (term76 x y) = term70.
Proof. exact (EQ_MP (@lem1734142 x y) (@lem1734135 x y)). Qed.
Lemma lem1734144 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734145 (x : real) (y : real) : (term81 x y) = term82.
Proof. exact (MK_COMB (@lem1734144) (@lem1734143 x y)). Qed.
Lemma lem1734146 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem1734147 (x : real) (y : real) : (term83 x y) = term84.
Proof. exact (MK_COMB (@lem1734145 x y) (@lem1734146)). Qed.
Lemma lem1734148 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1734149 (x : real) (y : real) : (term85 x y) = term82.
Proof. exact (MK_COMB (@lem1734148) (@lem1734133 x y)). Qed.
Lemma lem1734150 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem1734151 (x : real) (y : real) : (term86 x y) = term84.
Proof. exact (MK_COMB (@lem1734149 x y) (@lem1734150)). Qed.
Lemma lem1734152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734153 (x : real) (y : real) : (term87 x y) = term88.
Proof. exact (MK_COMB (@lem1734152) (@lem1734151 x y)). Qed.
Lemma lem1734154 (x : real) (y : real) : (term56 x y) = term89.
Proof. exact (MK_COMB (@lem1734153 x y) (@lem1734147 x y)). Qed.
Lemma lem1734155 (x : real) (y : real) : (term45 x y) = term89.
Proof. exact (TRANS (@lem1734062 x y) (@lem1734154 x y)). Qed.
Lemma lem1734156 (x : real) : (term47 x) = term90.
Proof. exact (fun_ext (fun y : real => @lem1734155 x y)). Qed.
Lemma lem1734157 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734158 (x : real) : (term48 x) = term91.
Proof. exact (MK_COMB (@lem1734157) (@lem1734156 x)). Qed.
Lemma lem1734159 : term54 = term92.
Proof. exact (fun_ext (fun x : real => @lem1734158 x)). Qed.
Lemma lem1734160 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734161 : term55 = term93.
Proof. exact (MK_COMB (@lem1734160) (@lem1734159)). Qed.
Lemma lem1734162 : term49 = term93.
Proof. exact (TRANS (@lem1734061) (@lem1734161)). Qed.
Lemma lem1734164 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1734165 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1734164 real t). Qed.
Lemma lem1734166 : term93 = term91.
Proof. exact (@lem1734165 term91). Qed.
Lemma lem1734168 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1734169 (P : real -> Prop) (Q : real -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem1734168 real P Q). Qed.
Lemma lem1734170 : term100 = term101.
Proof. exact (@lem1734169 term102 term102). Qed.
Lemma lem1734171 (y : real) : (term103 y) = term84.
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem1734172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734173 (y : real) : (term104 y) = term88.
Proof. exact (MK_COMB (@lem1734172) (@lem1734171 y)). Qed.
Lemma lem1734174 (y : real) : (term103 y) = term84.
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem1734175 (y : real) : (term105 y) = term89.
Proof. exact (MK_COMB (@lem1734173 y) (@lem1734174 y)). Qed.
Lemma lem1734176 : term106 = term90.
Proof. exact (fun_ext (fun y : real => @lem1734175 y)). Qed.
Lemma lem1734177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734178 : term100 = term91.
Proof. exact (MK_COMB (@lem1734177) (@lem1734176)). Qed.
Lemma lem1734179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1734180 : term107 = term108.
Proof. exact (MK_COMB (@lem1734179) (@lem1734178)). Qed.
Lemma lem1734181 (y : real) : (term103 y) = term84.
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem1734182 : term109 = term102.
Proof. exact (fun_ext (fun y : real => @lem1734181 y)). Qed.
Lemma lem1734183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734184 : term110 = term111.
Proof. exact (MK_COMB (@lem1734183) (@lem1734182)). Qed.
Lemma lem1734185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734186 : term112 = term113.
Proof. exact (MK_COMB (@lem1734185) (@lem1734184)). Qed.
Lemma lem1734187 (y : real) : (term103 y) = term84.
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem1734188 : term109 = term102.
Proof. exact (fun_ext (fun y : real => @lem1734187 y)). Qed.
Lemma lem1734189 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1734190 : term110 = term111.
Proof. exact (MK_COMB (@lem1734189) (@lem1734188)). Qed.
Lemma lem1734191 : term101 = term114.
Proof. exact (MK_COMB (@lem1734186) (@lem1734190)). Qed.
Lemma lem1734192 : (term100 = term101) = (term91 = term114).
Proof. exact (MK_COMB (@lem1734180) (@lem1734191)). Qed.
Lemma lem1734193 : term91 = term114.
Proof. exact (EQ_MP (@lem1734192) (@lem1734170)). Qed.
Lemma lem1734194 : term93 = term114.
Proof. exact (TRANS (@lem1734166) (@lem1734193)). Qed.
Lemma lem1734196 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1734197 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1734196 real t). Qed.
Lemma lem1734198 : term111 = term84.
Proof. exact (@lem1734197 term84). Qed.
Lemma lem1734199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1734200 : term113 = term88.
Proof. exact (MK_COMB (@lem1734199) (@lem1734198)). Qed.
Lemma lem1734202 {A : Type'} (t : Prop) : (term94 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1734203 (t : Prop) : (term95 t) = t.
Proof. exact (@lem1734202 real t). Qed.
Lemma lem1734204 : term111 = term84.
Proof. exact (@lem1734203 term84). Qed.
Lemma lem1734205 : term114 = term89.
Proof. exact (MK_COMB (@lem1734200) (@lem1734204)). Qed.
Lemma lem1734208 : term93 = term89.
Proof. exact (TRANS (@lem1734194) (@lem1734205)). Qed.
Lemma lem1734217 : term49 = term89.
Proof. exact (TRANS (@lem1734162) (@lem1734208)). Qed.
Lemma lem1734227 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1734228 (h1 : term84) : term84.
Proof. exact (h1). Qed.
Lemma lem1734230 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734231 : term84 = term116.
Proof. exact (@lem1734230 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1734232 : term116 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1734233 : term84 = False.
Proof. exact (TRANS (@lem1734231) (@lem1734232)). Qed.
Lemma lem1734234 (h1 : term84) : False.
Proof. exact (EQ_MP (@lem1734233) (@lem1734228 h1)). Qed.
Lemma lem1734235 (h1 : term84) : term84.
Proof. exact (h1). Qed.
Lemma lem1734237 (n : nat) (m : nat) : (term115 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1734238 : term84 = term116.
Proof. exact (@lem1734237 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1734239 : term116 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1734240 : term84 = False.
Proof. exact (TRANS (@lem1734238) (@lem1734239)). Qed.
Lemma lem1734241 (h1 : term84) : False.
Proof. exact (EQ_MP (@lem1734240) (@lem1734235 h1)). Qed.
Lemma lem1734242 (h1 : term89) : False.
Proof. exact (or_elim (@lem1734227 h1) (fun h0 : term84 => @lem1734234 h0) (fun h0 : term84 => @lem1734241 h0)). Qed.
Lemma lem1734244 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1734245 (h1 : term89) : term89 = False.
Proof. exact (prop_ext (fun h2 : term89 => @lem1734242 h1) (fun h2 : False => @lem1734244 h1)). Qed.
Lemma lem1734246 (h1 : term89) : False.
Proof. exact (EQ_MP (@lem1734245 h1) (@lem1734244 h1)). Qed.
Lemma lem1734247 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1734248 (h1 : term49) : term89.
Proof. exact (EQ_MP (@lem1734217) (@lem1734247 h1)). Qed.
Lemma lem1734249 (h1 : term49) : term89 = False.
Proof. exact (prop_ext (fun h2 : term89 => @lem1734246 h2) (fun h2 : False => @lem1734248 h1)). Qed.
Lemma lem1734250 (h1 : term49) : False.
Proof. exact (EQ_MP (@lem1734249 h1) (@lem1734248 h1)). Qed.
Lemma lem1734251 : term117.
Proof. exact (fun h0 : term49 => @lem1734250 h0). Qed.
Lemma lem1734252 : term118.
Proof. exact (@lem1386578 term38). Qed.
Lemma lem1734253 : term38.
Proof. exact (@lem1734252 (@lem1734251)). Qed.
Lemma lem1734254 : term37.
Proof. exact (EQ_MP (@lem1734018) (@lem1734253)). Qed.
