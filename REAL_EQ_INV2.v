Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_INV2_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_INV_INV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1587932 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1587933 : term1 = term2.
Proof. exact (@lem1587932 term1). Qed.
Lemma lem1587934 : term2 = term1.
Proof. exact (SYM (@lem1587933)). Qed.
Lemma lem1587935 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1587938 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1587939 : term5.
Proof. exact (fun h0 : term4 => @lem1587938 h0). Qed.
Lemma lem1587940 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1587941 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1587942 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1587940 h2 (@lem1587941 h1)). Qed.
Lemma lem1587943 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1587942 h1 h0). Qed.
Lemma lem1587944 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1587945 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1587943 h1 (@lem1587944 h2)). Qed.
Lemma lem1587946 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1587945 h0 h1). Qed.
Lemma lem1587947 : term7.
Proof. exact (fun h0 : term5 => @lem1587946 h0). Qed.
Lemma lem1587950 : term5.
Proof. exact (@lem1587947 (@lem1587939)). Qed.
Lemma lem1587962 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1587963 : term8 = term9.
Proof. exact (@lem1587962 term10). Qed.
Lemma lem1587968 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1587975 : term4 = term12.
Proof. exact (MK_COMB (@lem1587968) (@lem1587963)). Qed.
Lemma lem1587976 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1587977 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1587976 x)). Qed.
Lemma lem1587978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1587979 : term10 = term10.
Proof. exact (MK_COMB (@lem1587978) (@lem1587977)). Qed.
Lemma lem1587980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1587981 : term9 = term9.
Proof. exact (MK_COMB (@lem1587980) (@lem1587979)). Qed.
Lemma lem1587986 (x : real) (y : real) : (((real_inv x) = (real_inv y)) = (x = y)) = (((real_inv x) = (real_inv y)) = (x = y)).
Proof. exact (eq_refl (((real_inv x) = (real_inv y)) = (x = y))). Qed.
Lemma lem1587987 (x : real) : (term15 x) = (term15 x).
Proof. exact (fun_ext (fun y : real => @lem1587986 x y)). Qed.
Lemma lem1587988 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1587989 (x : real) : (term16 x) = (term16 x).
Proof. exact (MK_COMB (@lem1587988) (@lem1587987 x)). Qed.
Lemma lem1587990 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1587989 x)). Qed.
Lemma lem1587991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1587992 : term1 = term1.
Proof. exact (MK_COMB (@lem1587991) (@lem1587990)). Qed.
Lemma lem1587993 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1587994 : term3 = term3.
Proof. exact (MK_COMB (@lem1587993) (@lem1587992)). Qed.
Lemma lem1587995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1587996 : term11 = term11.
Proof. exact (MK_COMB (@lem1587995) (@lem1587994)). Qed.
Lemma lem1587997 : term12 = term12.
Proof. exact (MK_COMB (@lem1587996) (@lem1587981)). Qed.
Lemma lem1588020 : term4 = term12.
Proof. exact (TRANS (@lem1587975) (@lem1587997)). Qed.
Lemma lem1588021 : term12 = term4.
Proof. exact (SYM (@lem1588020)). Qed.
Lemma lem1588022 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1588023 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1588038 (x : real) (y : real) : (term18 x y) = (term19 x y).
Proof. exact (@lem17646 ((real_inv x) = (real_inv y)) (x = y)). Qed.
Lemma lem1588039 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1588040 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1588039 (term15 x)). Qed.
Lemma lem1588041 (x : real) (y : real) : (term24 x y) = (((real_inv x) = (real_inv y)) = (x = y)).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1588042 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1588043 (x : real) (y : real) : (term25 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1588042) (@lem1588041 x y)). Qed.
Lemma lem1588044 (x : real) (y : real) : (term25 x y) = (term19 x y).
Proof. exact (TRANS (@lem1588043 x y) (@lem1588038 x y)). Qed.
Lemma lem1588045 (x : real) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1588044 x y)). Qed.
Lemma lem1588046 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588047 (x : real) : (term23 x) = (term28 x).
Proof. exact (MK_COMB (@lem1588046) (@lem1588045 x)). Qed.
Lemma lem1588048 (x : real) : (term22 x) = (term28 x).
Proof. exact (TRANS (@lem1588040 x) (@lem1588047 x)). Qed.
Lemma lem1588049 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1588050 : term3 = term29.
Proof. exact (@lem1588049 term17). Qed.
Lemma lem1588051 (x : real) : (term30 x) = (term16 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1588052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1588053 (x : real) : (term31 x) = (term22 x).
Proof. exact (MK_COMB (@lem1588052) (@lem1588051 x)). Qed.
Lemma lem1588054 (x : real) : (term31 x) = (term28 x).
Proof. exact (TRANS (@lem1588053 x) (@lem1588048 x)). Qed.
Lemma lem1588055 : term32 = term33.
Proof. exact (fun_ext (fun x : real => @lem1588054 x)). Qed.
Lemma lem1588056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588057 : term29 = term34.
Proof. exact (MK_COMB (@lem1588056) (@lem1588055)). Qed.
Lemma lem1588058 : term3 = term34.
Proof. exact (TRANS (@lem1588050) (@lem1588057)). Qed.
Lemma lem1588064 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1588065 (P : real -> Prop) (Q : real -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem1588064 real P Q). Qed.
Lemma lem1588066 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1588065 (term41 x) (term42 x)). Qed.
Lemma lem1588067 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1588068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588069 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1588068) (@lem1588067 x y)). Qed.
Lemma lem1588070 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1588071 (x : real) (y : real) : (term49 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem1588069 x y) (@lem1588070 x y)). Qed.
Lemma lem1588072 (x : real) : (term50 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1588071 x y)). Qed.
Lemma lem1588073 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588074 (x : real) : (term39 x) = (term28 x).
Proof. exact (MK_COMB (@lem1588073) (@lem1588072 x)). Qed.
Lemma lem1588075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588076 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1588075) (@lem1588074 x)). Qed.
Lemma lem1588077 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1588078 (x : real) : (term53 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1588077 x y)). Qed.
Lemma lem1588079 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588080 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem1588079) (@lem1588078 x)). Qed.
Lemma lem1588081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588082 (x : real) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem1588081) (@lem1588080 x)). Qed.
Lemma lem1588083 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1588084 (x : real) : (term58 x) = (term42 x).
Proof. exact (fun_ext (fun y : real => @lem1588083 x y)). Qed.
Lemma lem1588085 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588086 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1588085) (@lem1588084 x)). Qed.
Lemma lem1588087 (x : real) : (term40 x) = (term61 x).
Proof. exact (MK_COMB (@lem1588082 x) (@lem1588086 x)). Qed.
Lemma lem1588088 (x : real) : ((term39 x) = (term40 x)) = ((term28 x) = (term61 x)).
Proof. exact (MK_COMB (@lem1588076 x) (@lem1588087 x)). Qed.
Lemma lem1588089 (x : real) : (term28 x) = (term61 x).
Proof. exact (EQ_MP (@lem1588088 x) (@lem1588066 x)). Qed.
Lemma lem1588186 : term33 = term62.
Proof. exact (fun_ext (fun x : real => @lem1588089 x)). Qed.
Lemma lem1588187 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588188 : term34 = term63.
Proof. exact (MK_COMB (@lem1588187) (@lem1588186)). Qed.
Lemma lem1588190 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1588191 (P : real -> Prop) (Q : real -> Prop) : (term37 P Q) = (term38 P Q).
Proof. exact (@lem1588190 real P Q). Qed.
Lemma lem1588192 : term64 = term65.
Proof. exact (@lem1588191 term66 term67). Qed.
Lemma lem1588193 (x : real) : (term68 x) = (term55 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1588194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588195 (x : real) : (term69 x) = (term57 x).
Proof. exact (MK_COMB (@lem1588194) (@lem1588193 x)). Qed.
Lemma lem1588196 (x : real) : (term70 x) = (term60 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1588197 (x : real) : (term71 x) = (term61 x).
Proof. exact (MK_COMB (@lem1588195 x) (@lem1588196 x)). Qed.
Lemma lem1588198 : term72 = term62.
Proof. exact (fun_ext (fun x : real => @lem1588197 x)). Qed.
Lemma lem1588199 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588200 : term64 = term63.
Proof. exact (MK_COMB (@lem1588199) (@lem1588198)). Qed.
Lemma lem1588201 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588202 : term73 = term74.
Proof. exact (MK_COMB (@lem1588201) (@lem1588200)). Qed.
Lemma lem1588203 (x : real) : (term68 x) = (term55 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1588204 : term75 = term66.
Proof. exact (fun_ext (fun x : real => @lem1588203 x)). Qed.
Lemma lem1588205 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588206 : term76 = term77.
Proof. exact (MK_COMB (@lem1588205) (@lem1588204)). Qed.
Lemma lem1588207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588208 : term78 = term79.
Proof. exact (MK_COMB (@lem1588207) (@lem1588206)). Qed.
Lemma lem1588209 (x : real) : (term70 x) = (term60 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1588210 : term80 = term67.
Proof. exact (fun_ext (fun x : real => @lem1588209 x)). Qed.
Lemma lem1588211 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588212 : term81 = term82.
Proof. exact (MK_COMB (@lem1588211) (@lem1588210)). Qed.
Lemma lem1588213 : term65 = term83.
Proof. exact (MK_COMB (@lem1588208) (@lem1588212)). Qed.
Lemma lem1588214 : (term64 = term65) = (term63 = term83).
Proof. exact (MK_COMB (@lem1588202) (@lem1588213)). Qed.
Lemma lem1588215 : term63 = term83.
Proof. exact (EQ_MP (@lem1588214) (@lem1588192)). Qed.
Lemma lem1588320 : term34 = term83.
Proof. exact (TRANS (@lem1588188) (@lem1588215)). Qed.
Lemma lem1588322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1588323 (P : real -> Prop) (Q : real -> Prop) : (term38 P Q) = (term37 P Q).
Proof. exact (@lem1588322 real P Q). Qed.
Lemma lem1588324 : term65 = term64.
Proof. exact (@lem1588323 term66 term67). Qed.
Lemma lem1588325 (x : real) : (term68 x) = (term55 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1588326 : term75 = term66.
Proof. exact (fun_ext (fun x : real => @lem1588325 x)). Qed.
Lemma lem1588327 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588328 : term76 = term77.
Proof. exact (MK_COMB (@lem1588327) (@lem1588326)). Qed.
Lemma lem1588329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588330 : term78 = term79.
Proof. exact (MK_COMB (@lem1588329) (@lem1588328)). Qed.
Lemma lem1588331 (x : real) : (term70 x) = (term60 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1588332 : term80 = term67.
Proof. exact (fun_ext (fun x : real => @lem1588331 x)). Qed.
Lemma lem1588333 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588334 : term81 = term82.
Proof. exact (MK_COMB (@lem1588333) (@lem1588332)). Qed.
Lemma lem1588335 : term65 = term83.
Proof. exact (MK_COMB (@lem1588330) (@lem1588334)). Qed.
Lemma lem1588336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588337 : term84 = term85.
Proof. exact (MK_COMB (@lem1588336) (@lem1588335)). Qed.
Lemma lem1588338 (x : real) : (term68 x) = (term55 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1588339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588340 (x : real) : (term69 x) = (term57 x).
Proof. exact (MK_COMB (@lem1588339) (@lem1588338 x)). Qed.
Lemma lem1588341 (x : real) : (term70 x) = (term60 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1588342 (x : real) : (term71 x) = (term61 x).
Proof. exact (MK_COMB (@lem1588340 x) (@lem1588341 x)). Qed.
Lemma lem1588343 : term72 = term62.
Proof. exact (fun_ext (fun x : real => @lem1588342 x)). Qed.
Lemma lem1588344 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588345 : term64 = term63.
Proof. exact (MK_COMB (@lem1588344) (@lem1588343)). Qed.
Lemma lem1588346 : (term65 = term64) = (term83 = term63).
Proof. exact (MK_COMB (@lem1588337) (@lem1588345)). Qed.
Lemma lem1588347 : term83 = term63.
Proof. exact (EQ_MP (@lem1588346) (@lem1588324)). Qed.
Lemma lem1588349 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term36 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1588350 (P : real -> Prop) (Q : real -> Prop) : (term38 P Q) = (term37 P Q).
Proof. exact (@lem1588349 real P Q). Qed.
Lemma lem1588351 (x : real) : (term40 x) = (term39 x).
Proof. exact (@lem1588350 (term41 x) (term42 x)). Qed.
Lemma lem1588352 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1588353 (x : real) : (term53 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1588352 x y)). Qed.
Lemma lem1588354 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588355 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem1588354) (@lem1588353 x)). Qed.
Lemma lem1588356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588357 (x : real) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem1588356) (@lem1588355 x)). Qed.
Lemma lem1588358 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1588359 (x : real) : (term58 x) = (term42 x).
Proof. exact (fun_ext (fun y : real => @lem1588358 x y)). Qed.
Lemma lem1588360 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588361 (x : real) : (term59 x) = (term60 x).
Proof. exact (MK_COMB (@lem1588360) (@lem1588359 x)). Qed.
Lemma lem1588362 (x : real) : (term40 x) = (term61 x).
Proof. exact (MK_COMB (@lem1588357 x) (@lem1588361 x)). Qed.
Lemma lem1588363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588364 (x : real) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1588363) (@lem1588362 x)). Qed.
Lemma lem1588365 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1588366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1588367 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1588366) (@lem1588365 x y)). Qed.
Lemma lem1588368 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1588369 (x : real) (y : real) : (term49 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem1588367 x y) (@lem1588368 x y)). Qed.
Lemma lem1588370 (x : real) : (term50 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1588369 x y)). Qed.
Lemma lem1588371 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588372 (x : real) : (term39 x) = (term28 x).
Proof. exact (MK_COMB (@lem1588371) (@lem1588370 x)). Qed.
Lemma lem1588373 (x : real) : ((term40 x) = (term39 x)) = ((term61 x) = (term28 x)).
Proof. exact (MK_COMB (@lem1588364 x) (@lem1588372 x)). Qed.
Lemma lem1588374 (x : real) : (term61 x) = (term28 x).
Proof. exact (EQ_MP (@lem1588373 x) (@lem1588351 x)). Qed.
Lemma lem1588375 : term62 = term33.
Proof. exact (fun_ext (fun x : real => @lem1588374 x)). Qed.
Lemma lem1588376 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1588377 : term63 = term34.
Proof. exact (MK_COMB (@lem1588376) (@lem1588375)). Qed.
Lemma lem1588378 : term83 = term34.
Proof. exact (TRANS (@lem1588347) (@lem1588377)). Qed.
Lemma lem1588379 : term34 = term34.
Proof. exact (TRANS (@lem1588320) (@lem1588378)). Qed.
Lemma lem1588380 : term3 = term34.
Proof. exact (TRANS (@lem1588058) (@lem1588379)). Qed.
Lemma lem1588381 (h1 : term3) : term34.
Proof. exact (EQ_MP (@lem1588380) (@lem1588022 h1)). Qed.
Lemma lem1588382 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1588383 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1588382 x)). Qed.
Lemma lem1588384 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1588393 : term10 = term10.
Proof. exact (MK_COMB (@lem1588384) (@lem1588383)). Qed.
Lemma lem1588394 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1588393) (@lem1588023 h1)). Qed.
Lemma lem1588395 (x : real) (h1 : term28 x) : term28 x.
Proof. exact (h1). Qed.
Lemma lem1588405 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1588406 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1588405 x)). Qed.
Lemma lem1588407 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1588408 : term10 = term10.
Proof. exact (MK_COMB (@lem1588407) (@lem1588406)). Qed.
Lemma lem1588409 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1588408) (@lem1588394 h1)). Qed.
Lemma lem1588451 (x : real) (y : real) (h1 : term19 x y) : term19 x y.
Proof. exact (h1). Qed.
Lemma lem1588452 (x : real) (y : real) (h1 : term44 x y) : term44 x y.
Proof. exact (h1). Qed.
Lemma lem1588453 (x : real) (y : real) (h1 : term48 x y) : term48 x y.
Proof. exact (h1). Qed.
Lemma lem1588459 (x : real) : ((term13 x) = x) = ((term13 x) = x).
Proof. exact (eq_refl ((term13 x) = x)). Qed.
Lemma lem1588460 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1588459 x)). Qed.
Lemma lem1588461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1588463 : term10 = term10.
Proof. exact (MK_COMB (@lem1588461) (@lem1588460)). Qed.
Lemma lem1588464 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1588463) (@lem1588409 h1)). Qed.
Lemma lem1588488 (_25085 : real) (h1 : term10) : term88 _25085.
Proof. exact (@lem1588464 h1 _25085). Qed.
Lemma lem1588489 (_25085 : real) : (term88 _25085) = ((term13 _25085) = _25085).
Proof. exact (eq_refl (term88 _25085)). Qed.
Lemma lem1588499 (x : real) (y : real) (h1 : term44 x y) : term89 x y.
Proof. exact (proj2 (@lem1588452 x y h1)). Qed.
Lemma lem1588503 (x : real) (y : real) (h1 : term48 x y) : term90 x y.
Proof. exact (proj1 (@lem1588453 x y h1)). Qed.
Lemma lem1588505 (x : real) (y : real) (h1 : term48 x y) : x = y.
Proof. exact (proj2 (@lem1588453 x y h1)). Qed.
Lemma lem1588534 (y : real) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1588535 (x : real) (y : real) (h1 : term48 x y) : (term92 y x) = (term93 y).
Proof. exact (MK_COMB (@lem1588534 y) (@lem1588505 x y h1)). Qed.
Lemma lem1588536 (y : real) : (term93 y) = (term94 y).
Proof. exact (eq_refl (term93 y)). Qed.
Lemma lem1588537 (y : real) (x : real) : (term95 y x) = (term95 y x).
Proof. exact (eq_refl (term95 y x)). Qed.
Lemma lem1588538 (x : real) (y : real) : ((term92 y x) = (term93 y)) = ((term92 y x) = (term94 y)).
Proof. exact (MK_COMB (@lem1588537 y x) (@lem1588536 y)). Qed.
Lemma lem1588539 (x : real) (y : real) : (term92 y x) = (term90 x y).
Proof. exact (eq_refl (term92 y x)). Qed.
Lemma lem1588540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588541 (x : real) (y : real) : (term95 y x) = (term96 x y).
Proof. exact (MK_COMB (@lem1588540) (@lem1588539 x y)). Qed.
Lemma lem1588542 (y : real) : (term94 y) = (term94 y).
Proof. exact (eq_refl (term94 y)). Qed.
Lemma lem1588543 (x : real) (y : real) : ((term92 y x) = (term94 y)) = ((term90 x y) = (term94 y)).
Proof. exact (MK_COMB (@lem1588541 x y) (@lem1588542 y)). Qed.
Lemma lem1588544 (x : real) (y : real) : ((term92 y x) = (term93 y)) = ((term90 x y) = (term94 y)).
Proof. exact (TRANS (@lem1588538 x y) (@lem1588543 x y)). Qed.
Lemma lem1588545 (x : real) (y : real) (h1 : term48 x y) : (term90 x y) = (term94 y).
Proof. exact (EQ_MP (@lem1588544 x y) (@lem1588535 x y h1)). Qed.
Lemma lem1588546 (x : real) (y : real) (h1 : term48 x y) : term94 y.
Proof. exact (EQ_MP (@lem1588545 x y h1) (@lem1588503 x y h1)). Qed.
Lemma lem1588547 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1588548 (_25093 : real) (_25094 : real) (h1 : _25093 = _25094) : _25093 = _25094.
Proof. exact (h1). Qed.
Lemma lem1588549 (_25093 : real) (_25094 : real) (h1 : _25093 = _25094) : (real_inv _25093) = (real_inv _25094).
Proof. exact (MK_COMB (@lem1588547) (@lem1588548 _25093 _25094 h1)). Qed.
Lemma lem1588550 (_25093 : real) (_25094 : real) : term97 _25093 _25094.
Proof. exact (fun h0 : _25093 = _25094 => @lem1588549 _25093 _25094 h0). Qed.
Lemma lem1588552 (a : Prop) (b : Prop) : (a -> b) = (term98 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1588553 (_25093 : real) (_25094 : real) : (term97 _25093 _25094) = (term99 _25093 _25094).
Proof. exact (@lem1588552 (_25093 = _25094) ((real_inv _25093) = (real_inv _25094))). Qed.
Lemma lem1588554 (_25093 : real) (_25094 : real) : term99 _25093 _25094.
Proof. exact (EQ_MP (@lem1588553 _25093 _25094) (@lem1588550 _25093 _25094)). Qed.
Lemma lem1588556 (x : real) (y : real) (z : real) : term100 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1588558 (x : real) (y : real) (h1 : term44 x y) : (real_inv x) = (real_inv y).
Proof. exact (proj1 (@lem1588452 x y h1)). Qed.
Lemma lem1588559 (x : real) (y : real) (h1 : term44 x y) : term101 x y.
Proof. exact (fun h0 : term90 x y => @lem1588558 x y h1). Qed.
Lemma lem1588561 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588562 (x : real) (y : real) : (term101 x y) = ((real_inv x) = (real_inv y)).
Proof. exact (@lem1588561 ((real_inv x) = (real_inv y))). Qed.
Lemma lem1588563 (x : real) (y : real) (h1 : term44 x y) : (real_inv x) = (real_inv y).
Proof. exact (EQ_MP (@lem1588562 x y) (@lem1588559 x y h1)). Qed.
Lemma lem1588569 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1588570 (_25093 : real) (_25094 : real) : (term99 _25093 _25094) = (term103 _25093 _25094).
Proof. exact (@lem1588569 ((real_inv _25093) = (real_inv _25094)) (term89 _25093 _25094)). Qed.
Lemma lem1588580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588581 (_25093 : real) (_25094 : real) : (term104 _25093 _25094) = (term105 _25093 _25094).
Proof. exact (MK_COMB (@lem1588580) (@lem1588570 _25093 _25094)). Qed.
Lemma lem1588591 (_25093 : real) (_25094 : real) : (term103 _25093 _25094) = (term103 _25093 _25094).
Proof. exact (eq_refl (term103 _25093 _25094)). Qed.
Lemma lem1588592 (_25093 : real) (_25094 : real) : ((term99 _25093 _25094) = (term103 _25093 _25094)) = ((term103 _25093 _25094) = (term103 _25093 _25094)).
Proof. exact (MK_COMB (@lem1588581 _25093 _25094) (@lem1588591 _25093 _25094)). Qed.
Lemma lem1588594 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1588595 (x : Prop) : (x = x) = True.
Proof. exact (@lem1588594 Prop x). Qed.
Lemma lem1588596 (_25093 : real) (_25094 : real) : ((term103 _25093 _25094) = (term103 _25093 _25094)) = True.
Proof. exact (@lem1588595 (term103 _25093 _25094)). Qed.
Lemma lem1588597 (_25093 : real) (_25094 : real) : ((term99 _25093 _25094) = (term103 _25093 _25094)) = True.
Proof. exact (TRANS (@lem1588592 _25093 _25094) (@lem1588596 _25093 _25094)). Qed.
Lemma lem1588598 (_25093 : real) (_25094 : real) : True = ((term99 _25093 _25094) = (term103 _25093 _25094)).
Proof. exact (SYM (@lem1588597 _25093 _25094)). Qed.
Lemma lem1588599 (_25093 : real) (_25094 : real) : (term99 _25093 _25094) = (term103 _25093 _25094).
Proof. exact (EQ_MP (@lem1588598 _25093 _25094) (@lem0)). Qed.
Lemma lem1588600 (_25093 : real) (_25094 : real) : term103 _25093 _25094.
Proof. exact (EQ_MP (@lem1588599 _25093 _25094) (@lem1588554 _25093 _25094)). Qed.
Lemma lem1588602 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1588603 (_25093 : real) (_25094 : real) : (term103 _25093 _25094) = (term107 _25093 _25094).
Proof. exact (@lem1588602 (term89 _25093 _25094) ((real_inv _25093) = (real_inv _25094))). Qed.
Lemma lem1588605 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1588606 (_25093 : real) (_25094 : real) : (term109 _25093 _25094) = (_25093 = _25094).
Proof. exact (@lem1588605 (_25093 = _25094)). Qed.
Lemma lem1588607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1588608 (_25093 : real) (_25094 : real) : (term110 _25093 _25094) = (term111 _25093 _25094).
Proof. exact (MK_COMB (@lem1588607) (@lem1588606 _25093 _25094)). Qed.
Lemma lem1588609 (_25093 : real) (_25094 : real) : ((real_inv _25093) = (real_inv _25094)) = ((real_inv _25093) = (real_inv _25094)).
Proof. exact (eq_refl ((real_inv _25093) = (real_inv _25094))). Qed.
Lemma lem1588610 (_25093 : real) (_25094 : real) : (term107 _25093 _25094) = (term97 _25093 _25094).
Proof. exact (MK_COMB (@lem1588608 _25093 _25094) (@lem1588609 _25093 _25094)). Qed.
Lemma lem1588611 (_25093 : real) (_25094 : real) : (term103 _25093 _25094) = (term97 _25093 _25094).
Proof. exact (TRANS (@lem1588603 _25093 _25094) (@lem1588610 _25093 _25094)). Qed.
Lemma lem1588614 (_25093 : real) (_25094 : real) : term97 _25093 _25094.
Proof. exact (EQ_MP (@lem1588611 _25093 _25094) (@lem1588600 _25093 _25094)). Qed.
Lemma lem1588615 (x : real) (y : real) : term112 x y.
Proof. exact (@lem1588614 (real_inv x) (real_inv y)). Qed.
Lemma lem1588618 (x : real) (y : real) (h1 : term44 x y) : (term13 x) = (term13 y).
Proof. exact (@lem1588615 x y (@lem1588563 x y h1)). Qed.
Lemma lem1588619 (x : real) (y : real) (h1 : term44 x y) : term113 x y.
Proof. exact (fun h0 : term114 x y => @lem1588618 x y h1). Qed.
Lemma lem1588621 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588622 (x : real) (y : real) : (term113 x y) = ((term13 x) = (term13 y)).
Proof. exact (@lem1588621 ((term13 x) = (term13 y))). Qed.
Lemma lem1588623 (x : real) (y : real) (h1 : term44 x y) : (term13 x) = (term13 y).
Proof. exact (EQ_MP (@lem1588622 x y) (@lem1588619 x y h1)). Qed.
Lemma lem1588625 (_25085 : real) (h1 : term10) : (term13 _25085) = _25085.
Proof. exact (EQ_MP (@lem1588489 _25085) (@lem1588488 _25085 h1)). Qed.
Lemma lem1588626 (x : real) (h1 : term10) : (term13 x) = x.
Proof. exact (@lem1588625 x h1). Qed.
Lemma lem1588627 (x : real) (h1 : term10) : term115 x.
Proof. exact (fun h0 : term116 x => @lem1588626 x h1). Qed.
Lemma lem1588629 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588630 (x : real) : (term115 x) = ((term13 x) = x).
Proof. exact (@lem1588629 ((term13 x) = x)). Qed.
Lemma lem1588631 (x : real) (h1 : term10) : (term13 x) = x.
Proof. exact (EQ_MP (@lem1588630 x) (@lem1588627 x h1)). Qed.
Lemma lem1588649 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1588650 (y : real) (x : real) (z : real) : (term117 x y z) = (term118 y x z).
Proof. exact (@lem1588649 (y = z) (term89 x z)). Qed.
Lemma lem1588660 (x : real) (y : real) : (term119 x y) = (term119 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1588661 (y : real) (x : real) (z : real) : (term100 x y z) = (term120 y x z).
Proof. exact (MK_COMB (@lem1588660 x y) (@lem1588650 y x z)). Qed.
Lemma lem1588665 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term121 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1588666 (y : real) (x : real) (z : real) : (term120 y x z) = (term122 y x z).
Proof. exact (@lem1588665 (y = z) (term89 x y) (term89 x z)). Qed.
Lemma lem1588688 (y : real) (x : real) (z : real) : (term100 x y z) = (term122 y x z).
Proof. exact (TRANS (@lem1588661 y x z) (@lem1588666 y x z)). Qed.
Lemma lem1588689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1588690 (y : real) (x : real) (z : real) : (term123 x y z) = (term124 y x z).
Proof. exact (MK_COMB (@lem1588689) (@lem1588688 y x z)). Qed.
Lemma lem1588712 (y : real) (x : real) (z : real) : (term122 y x z) = (term122 y x z).
Proof. exact (eq_refl (term122 y x z)). Qed.
Lemma lem1588713 (y : real) (x : real) (z : real) : ((term100 x y z) = (term122 y x z)) = ((term122 y x z) = (term122 y x z)).
Proof. exact (MK_COMB (@lem1588690 y x z) (@lem1588712 y x z)). Qed.
Lemma lem1588715 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1588716 (x : Prop) : (x = x) = True.
Proof. exact (@lem1588715 Prop x). Qed.
Lemma lem1588717 (y : real) (x : real) (z : real) : ((term122 y x z) = (term122 y x z)) = True.
Proof. exact (@lem1588716 (term122 y x z)). Qed.
Lemma lem1588718 (y : real) (x : real) (z : real) : ((term100 x y z) = (term122 y x z)) = True.
Proof. exact (TRANS (@lem1588713 y x z) (@lem1588717 y x z)). Qed.
Lemma lem1588719 (y : real) (x : real) (z : real) : True = ((term100 x y z) = (term122 y x z)).
Proof. exact (SYM (@lem1588718 y x z)). Qed.
Lemma lem1588720 (y : real) (x : real) (z : real) : (term100 x y z) = (term122 y x z).
Proof. exact (EQ_MP (@lem1588719 y x z) (@lem0)). Qed.
Lemma lem1588721 (y : real) (x : real) (z : real) : term122 y x z.
Proof. exact (EQ_MP (@lem1588720 y x z) (@lem1588556 x y z)). Qed.
Lemma lem1588723 (b : Prop) (a : Prop) : (a \/ b) = (term106 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1588724 (x : real) (y : real) (z : real) : (term122 y x z) = (term125 x y z).
Proof. exact (@lem1588723 (term126 y x z) (y = z)). Qed.
Lemma lem1588726 (a : Prop) (b : Prop) : (term127 a b) = (term128 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1588727 (y : real) (x : real) (z : real) : (term129 y x z) = (term130 y x z).
Proof. exact (@lem1588726 (term89 x y) (term89 x z)). Qed.
Lemma lem1588729 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1588730 (x : real) (y : real) : (term109 x y) = (x = y).
Proof. exact (@lem1588729 (x = y)). Qed.
Lemma lem1588731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1588732 (x : real) (y : real) : (term131 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1588731) (@lem1588730 x y)). Qed.
Lemma lem1588734 (a : Prop) : (term108 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1588735 (x : real) (z : real) : (term109 x z) = (x = z).
Proof. exact (@lem1588734 (x = z)). Qed.
Lemma lem1588736 (y : real) (x : real) (z : real) : (term130 y x z) = (term133 y x z).
Proof. exact (MK_COMB (@lem1588732 x y) (@lem1588735 x z)). Qed.
Lemma lem1588737 (y : real) (x : real) (z : real) : (term129 y x z) = (term133 y x z).
Proof. exact (TRANS (@lem1588727 y x z) (@lem1588736 y x z)). Qed.
Lemma lem1588738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1588739 (y : real) (x : real) (z : real) : (term134 y x z) = (term135 y x z).
Proof. exact (MK_COMB (@lem1588738) (@lem1588737 y x z)). Qed.
Lemma lem1588740 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1588741 (x : real) (y : real) (z : real) : (term125 x y z) = (term136 x y z).
Proof. exact (MK_COMB (@lem1588739 y x z) (@lem1588740 y z)). Qed.
Lemma lem1588742 (x : real) (y : real) (z : real) : (term122 y x z) = (term136 x y z).
Proof. exact (TRANS (@lem1588724 x y z) (@lem1588741 x y z)). Qed.
Lemma lem1588744 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : term137 y x.
Proof. exact (conj (@lem1588623 x y h2) (@lem1588631 x h1)). Qed.
Lemma lem1588746 (x : real) (y : real) (z : real) : term136 x y z.
Proof. exact (EQ_MP (@lem1588742 x y z) (@lem1588721 y x z)). Qed.
Lemma lem1588747 (y : real) (x : real) : term138 y x.
Proof. exact (@lem1588746 (term13 x) (term13 y) x). Qed.
Lemma lem1588750 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : (term13 y) = x.
Proof. exact (@lem1588747 y x (@lem1588744 x y h1 h2)). Qed.
Lemma lem1588751 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : term139 y x.
Proof. exact (fun h0 : term140 y x => @lem1588750 x y h1 h2). Qed.
Lemma lem1588753 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588754 (y : real) (x : real) : (term139 y x) = ((term13 y) = x).
Proof. exact (@lem1588753 ((term13 y) = x)). Qed.
Lemma lem1588755 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : (term13 y) = x.
Proof. exact (EQ_MP (@lem1588754 y x) (@lem1588751 x y h1 h2)). Qed.
Lemma lem1588757 (_25085 : real) (h1 : term10) : (term13 _25085) = _25085.
Proof. exact (EQ_MP (@lem1588489 _25085) (@lem1588488 _25085 h1)). Qed.
Lemma lem1588758 (y : real) (h1 : term10) : (term13 y) = y.
Proof. exact (@lem1588757 y h1). Qed.
Lemma lem1588759 (y : real) (h1 : term10) : term115 y.
Proof. exact (fun h0 : term116 y => @lem1588758 y h1). Qed.
Lemma lem1588761 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588762 (y : real) : (term115 y) = ((term13 y) = y).
Proof. exact (@lem1588761 ((term13 y) = y)). Qed.
Lemma lem1588763 (y : real) (h1 : term10) : (term13 y) = y.
Proof. exact (EQ_MP (@lem1588762 y) (@lem1588759 y h1)). Qed.
Lemma lem1588764 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : term141 x y.
Proof. exact (conj (@lem1588755 x y h1 h2) (@lem1588763 y h1)). Qed.
Lemma lem1588766 (x : real) (y : real) (z : real) : term136 x y z.
Proof. exact (EQ_MP (@lem1588742 x y z) (@lem1588721 y x z)). Qed.
Lemma lem1588767 (x : real) (y : real) : term142 x y.
Proof. exact (@lem1588766 (term13 y) x y). Qed.
Lemma lem1588770 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : x = y.
Proof. exact (@lem1588767 x y (@lem1588764 x y h1 h2)). Qed.
Lemma lem1588771 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : term143 x y.
Proof. exact (fun h0 : term89 x y => @lem1588770 x y h1 h2). Qed.
Lemma lem1588773 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588774 (x : real) (y : real) : (term143 x y) = (x = y).
Proof. exact (@lem1588773 (x = y)). Qed.
Lemma lem1588775 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : x = y.
Proof. exact (EQ_MP (@lem1588774 x y) (@lem1588771 x y h1 h2)). Qed.
Lemma lem1588778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1588780 (x : real) (y : real) : (term89 x y) = (term144 x y).
Proof. exact (@lem1588778 (x = y)). Qed.
Lemma lem1588783 (x : real) (y : real) (h1 : term44 x y) : term144 x y.
Proof. exact (EQ_MP (@lem1588780 x y) (@lem1588499 x y h1)). Qed.
Lemma lem1588786 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : False.
Proof. exact (@lem1588783 x y h2 (@lem1588775 x y h1 h2)). Qed.
Lemma lem1588787 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : term145.
Proof. exact (fun h0 : ~ False => @lem1588786 x y h1 h2). Qed.
Lemma lem1588789 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588790 : term145 = False.
Proof. exact (@lem1588789 False). Qed.
Lemma lem1588791 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : False.
Proof. exact (EQ_MP (@lem1588790) (@lem1588787 x y h1 h2)). Qed.
Lemma lem1588803 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1588804 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (@lem1588803 (real_inv y)). Qed.
Lemma lem1588805 (y : real) : term146 y.
Proof. exact (fun h0 : term94 y => @lem1588804 y). Qed.
Lemma lem1588807 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588808 (y : real) : (term146 y) = ((real_inv y) = (real_inv y)).
Proof. exact (@lem1588807 ((real_inv y) = (real_inv y))). Qed.
Lemma lem1588809 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (EQ_MP (@lem1588808 y) (@lem1588805 y)). Qed.
Lemma lem1588812 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1588814 (y : real) : (term94 y) = (term147 y).
Proof. exact (@lem1588812 ((real_inv y) = (real_inv y))). Qed.
Lemma lem1588817 (x : real) (y : real) (h1 : term48 x y) : term147 y.
Proof. exact (EQ_MP (@lem1588814 y) (@lem1588546 x y h1)). Qed.
Lemma lem1588820 (x : real) (y : real) (h1 : term48 x y) : False.
Proof. exact (@lem1588817 x y h1 (@lem1588809 y)). Qed.
Lemma lem1588821 (x : real) (y : real) (h1 : term48 x y) : term145.
Proof. exact (fun h0 : ~ False => @lem1588820 x y h1). Qed.
Lemma lem1588823 (p : Prop) : (term102 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1588824 : term145 = False.
Proof. exact (@lem1588823 False). Qed.
Lemma lem1588826 (x : real) (y : real) (h1 : term48 x y) : False.
Proof. exact (EQ_MP (@lem1588824) (@lem1588821 x y h1)). Qed.
Lemma lem1588827 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1588791 x y h1 h2) (fun h3 : False => @lem1588464 h1)). Qed.
Lemma lem1588828 (x : real) (y : real) (h1 : term10) (h2 : term44 x y) : False.
Proof. exact (EQ_MP (@lem1588827 x y h1 h2) (@lem1588464 h1)). Qed.
Lemma lem1588829 (x : real) (y : real) (h1 : term10) (h2 : term19 x y) : False.
Proof. exact (or_elim (@lem1588451 x y h2) (fun h0 : term44 x y => @lem1588828 x y h1 h0) (fun h0 : term48 x y => @lem1588826 x y h0)). Qed.
Lemma lem1588830 (x : real) (y : real) (h1 : term10) (h2 : term19 x y) : (term19 x y) = False.
Proof. exact (prop_ext (fun h3 : term19 x y => @lem1588829 x y h1 h2) (fun h3 : False => @lem1588451 x y h2)). Qed.
Lemma lem1588831 (x : real) (y : real) (h1 : term10) (h2 : term19 x y) : False.
Proof. exact (EQ_MP (@lem1588830 x y h1 h2) (@lem1588451 x y h2)). Qed.
Lemma lem1588832 (x : real) (y : real) (h1 : term10) (h2 : term19 x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1588831 x y h1 h2) (fun h3 : False => @lem1588409 h1)). Qed.
Lemma lem1588833 (x : real) (y : real) (h1 : term10) (h2 : term19 x y) : False.
Proof. exact (EQ_MP (@lem1588832 x y h1 h2) (@lem1588409 h1)). Qed.
Lemma lem1588834 (x : real) (h1 : term10) (h2 : term28 x) : False.
Proof. exact (ex_elim (@lem1588395 x h2) (fun y : real => fun h0 : term27 x y => @lem1588833 x y h1 h0)). Qed.
Lemma lem1588835 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem1588381 h2) (fun x : real => fun h0 : term33 x => @lem1588834 x h1 h0)). Qed.
Lemma lem1588836 (h1 : term10) (h2 : term3) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1588835 h1 h2) (fun h3 : False => @lem1588394 h1)). Qed.
Lemma lem1588837 (h1 : term10) (h2 : term3) : False.
Proof. exact (EQ_MP (@lem1588836 h1 h2) (@lem1588394 h1)). Qed.
Lemma lem1588838 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1588837 h0 h1). Qed.
Lemma lem1588839 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1588840 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem1588839) (@lem1588838 h1)). Qed.
Lemma lem1588841 : term12.
Proof. exact (fun h0 : term3 => @lem1588840 h0). Qed.
Lemma lem1588842 : term4.
Proof. exact (EQ_MP (@lem1588021) (@lem1588841)). Qed.
Lemma lem1588844 : term4.
Proof. exact (@lem1587950 (@lem1588842)). Qed.
Lemma lem1588845 (h1 : term3) : term8.
Proof. exact (@lem1588844 (@lem1587935 h1)). Qed.
Lemma lem1588846 (h1 : term3) : False.
Proof. exact (@lem1588845 h1 (@lem1587920)). Qed.
Lemma lem1588847 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1588846 h1) (fun h2 : False => @lem1587935 h1)). Qed.
Lemma lem1588848 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1588847 h1) (@lem1587935 h1)). Qed.
Lemma lem1588849 : term2.
Proof. exact (fun h0 : term3 => @lem1588848 h0). Qed.
Lemma lem1588850 : term1.
Proof. exact (EQ_MP (@lem1587934) (@lem1588849)). Qed.
