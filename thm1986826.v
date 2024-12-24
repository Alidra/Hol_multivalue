Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1986826_term_abbrevs.
Require Import REAL_ENTIRE_spec.
Require Import REAL_SUB_0_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483454_spec.
Require Import thm1483456_spec.
Require Import thm1483460_spec.
Require Import thm1483464_spec.
Require Import thm1483472_spec.
Require Import thm1483476_spec.
Require Import thm1483478_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1982801 (x : real) (y : real) (h1 : ((real_mul x y) = term0) = (term1 x y)) : ((real_mul x y) = term0) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem1982802 (x : real) (y : real) (h1 : ((real_mul x y) = term0) = (term1 x y)) : (term1 x y) = ((real_mul x y) = term0).
Proof. exact (SYM (@lem1982801 x y h1)). Qed.
Lemma lem1982803 (x : real) (y : real) (h1 : (term1 x y) = ((real_mul x y) = term0)) : (term1 x y) = ((real_mul x y) = term0).
Proof. exact (h1). Qed.
Lemma lem1982804 (x : real) (y : real) (h1 : (term1 x y) = ((real_mul x y) = term0)) : ((real_mul x y) = term0) = (term1 x y).
Proof. exact (SYM (@lem1982803 x y h1)). Qed.
Lemma lem1982805 (x : real) (y : real) : (((real_mul x y) = term0) = (term1 x y)) = ((term1 x y) = ((real_mul x y) = term0)).
Proof. exact (prop_ext (fun h1 : ((real_mul x y) = term0) = (term1 x y) => @lem1982802 x y h1) (fun h1 : (term1 x y) = ((real_mul x y) = term0) => @lem1982804 x y h1)). Qed.
Lemma lem1982806 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : real => @lem1982805 x y)). Qed.
Lemma lem1982807 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1982808 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1982807) (@lem1982806 x)). Qed.
Lemma lem1982809 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1982808 x)). Qed.
Lemma lem1982810 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1982811 : term8 = term9.
Proof. exact (MK_COMB (@lem1982810) (@lem1982809)). Qed.
Lemma lem1982812 : term9.
Proof. exact (EQ_MP (@lem1982811) (@lem1382769)). Qed.
Lemma lem1982813 (x : real) : term10 x.
Proof. exact (@lem1982812 x). Qed.
Lemma lem1982814 (x : real) : (term10 x) = (term5 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1982815 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1982814 x) (@lem1982813 x)). Qed.
Lemma lem1982816 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1982815 x y). Qed.
Lemma lem1982817 (x : real) (y : real) : (term11 x y) = ((term1 x y) = ((real_mul x y) = term0)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1982821 (x : real) (y : real) (h1 : ((real_sub x y) = term0) = (x = y)) : ((real_sub x y) = term0) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1982822 (x : real) (y : real) (h1 : ((real_sub x y) = term0) = (x = y)) : (x = y) = ((real_sub x y) = term0).
Proof. exact (SYM (@lem1982821 x y h1)). Qed.
Lemma lem1982823 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term0)) : (x = y) = ((real_sub x y) = term0).
Proof. exact (h1). Qed.
Lemma lem1982824 (x : real) (y : real) (h1 : (x = y) = ((real_sub x y) = term0)) : ((real_sub x y) = term0) = (x = y).
Proof. exact (SYM (@lem1982823 x y h1)). Qed.
Lemma lem1982825 (x : real) (y : real) : (((real_sub x y) = term0) = (x = y)) = ((x = y) = ((real_sub x y) = term0)).
Proof. exact (prop_ext (fun h1 : ((real_sub x y) = term0) = (x = y) => @lem1982822 x y h1) (fun h1 : (x = y) = ((real_sub x y) = term0) => @lem1982824 x y h1)). Qed.
Lemma lem1982826 (x : real) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1982825 x y)). Qed.
Lemma lem1982827 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1982828 (x : real) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1982827) (@lem1982826 x)). Qed.
Lemma lem1982829 : term16 = term17.
Proof. exact (fun_ext (fun x : real => @lem1982828 x)). Qed.
Lemma lem1982830 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1982831 : term18 = term19.
Proof. exact (MK_COMB (@lem1982830) (@lem1982829)). Qed.
Lemma lem1982832 : term19.
Proof. exact (EQ_MP (@lem1982831) (@lem1376695)). Qed.
Lemma lem1982833 (x : real) : term20 x.
Proof. exact (@lem1982832 x). Qed.
Lemma lem1982834 (x : real) : (term20 x) = (term15 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1982835 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1982834 x) (@lem1982833 x)). Qed.
Lemma lem1982836 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1982835 x y). Qed.
Lemma lem1982837 (x : real) (y : real) : (term21 x y) = ((x = y) = ((real_sub x y) = term0)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1983079 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (EQ_MP (@lem1982837 x y) (@lem1982836 x y)). Qed.
Lemma lem1983080 (x : real) : ((term22 x) = term0) = ((term23 x) = term0).
Proof. exact (@lem1983079 (term22 x) term0). Qed.
Lemma lem1983081 : term24 = term25.
Proof. exact (fun_ext (fun x : real => @lem1983080 x)). Qed.
Lemma lem1983082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983083 : term26 = term27.
Proof. exact (MK_COMB (@lem1983082) (@lem1983081)). Qed.
Lemma lem1983084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1983085 : term28 = term29.
Proof. exact (MK_COMB (@lem1983084) (@lem1983083)). Qed.
Lemma lem1983107 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (EQ_MP (@lem1982837 x y) (@lem1982836 x y)). Qed.
Lemma lem1983108 (y : real) (x : real) (z : real) : ((real_add x y) = (real_add x z)) = ((term30 y x z) = term0).
Proof. exact (@lem1983107 (real_add x y) (real_add x z)). Qed.
Lemma lem1983109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1983110 (y : real) (x : real) (z : real) : (term31 y x z) = (term32 y x z).
Proof. exact (MK_COMB (@lem1983109) (@lem1983108 y x z)). Qed.
Lemma lem1983114 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (EQ_MP (@lem1982837 x y) (@lem1982836 x y)). Qed.
Lemma lem1983115 (y : real) (z : real) : (y = z) = ((real_sub y z) = term0).
Proof. exact (@lem1983114 y z). Qed.
Lemma lem1983116 (x : real) (y : real) (z : real) : (((real_add x y) = (real_add x z)) = (y = z)) = (((term30 y x z) = term0) = ((real_sub y z) = term0)).
Proof. exact (MK_COMB (@lem1983110 y x z) (@lem1983115 y z)). Qed.
Lemma lem1983117 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (fun_ext (fun z : real => @lem1983116 x y z)). Qed.
Lemma lem1983118 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983119 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1983118) (@lem1983117 x y)). Qed.
Lemma lem1983120 (x : real) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1983119 x y)). Qed.
Lemma lem1983121 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983122 (x : real) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem1983121) (@lem1983120 x)). Qed.
Lemma lem1983123 : term41 = term42.
Proof. exact (fun_ext (fun x : real => @lem1983122 x)). Qed.
Lemma lem1983124 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983125 : term43 = term44.
Proof. exact (MK_COMB (@lem1983124) (@lem1983123)). Qed.
Lemma lem1983126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1983127 : term45 = term46.
Proof. exact (MK_COMB (@lem1983126) (@lem1983125)). Qed.
Lemma lem1983151 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (EQ_MP (@lem1982837 x y) (@lem1982836 x y)). Qed.
Lemma lem1983152 (w : real) (z : real) (x : real) (y : real) : ((term47 w y x z) = (term47 w z x y)) = ((term48 w z x y) = term0).
Proof. exact (@lem1983151 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem1983153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1983154 (w : real) (z : real) (x : real) (y : real) : (term49 w z x y) = (term50 w z x y).
Proof. exact (MK_COMB (@lem1983153) (@lem1983152 w z x y)). Qed.
Lemma lem1983160 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (EQ_MP (@lem1982837 x y) (@lem1982836 x y)). Qed.
Lemma lem1983161 (w : real) (x : real) : (w = x) = ((real_sub w x) = term0).
Proof. exact (@lem1983160 w x). Qed.
Lemma lem1983162 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983163 (w : real) (x : real) : (term51 w x) = (term52 w x).
Proof. exact (MK_COMB (@lem1983162) (@lem1983161 w x)). Qed.
Lemma lem1983167 (x : real) (y : real) : (x = y) = ((real_sub x y) = term0).
Proof. exact (EQ_MP (@lem1982837 x y) (@lem1982836 x y)). Qed.
Lemma lem1983168 (y : real) (z : real) : (y = z) = ((real_sub y z) = term0).
Proof. exact (@lem1983167 y z). Qed.
Lemma lem1983169 (w : real) (x : real) (y : real) (z : real) : (term53 w x y z) = (term54 w x y z).
Proof. exact (MK_COMB (@lem1983163 w x) (@lem1983168 y z)). Qed.
Lemma lem1983170 (w : real) (x : real) (y : real) (z : real) : (((term47 w y x z) = (term47 w z x y)) = (term53 w x y z)) = (((term48 w z x y) = term0) = (term54 w x y z)).
Proof. exact (MK_COMB (@lem1983154 w z x y) (@lem1983169 w x y z)). Qed.
Lemma lem1983171 (w : real) (x : real) (y : real) : (term55 w x y) = (term56 w x y).
Proof. exact (fun_ext (fun z : real => @lem1983170 w x y z)). Qed.
Lemma lem1983172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983173 (w : real) (x : real) (y : real) : (term57 w x y) = (term58 w x y).
Proof. exact (MK_COMB (@lem1983172) (@lem1983171 w x y)). Qed.
Lemma lem1983174 (w : real) (x : real) : (term59 w x) = (term60 w x).
Proof. exact (fun_ext (fun y : real => @lem1983173 w x y)). Qed.
Lemma lem1983175 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983176 (w : real) (x : real) : (term61 w x) = (term62 w x).
Proof. exact (MK_COMB (@lem1983175) (@lem1983174 w x)). Qed.
Lemma lem1983177 (w : real) : (term63 w) = (term64 w).
Proof. exact (fun_ext (fun x : real => @lem1983176 w x)). Qed.
Lemma lem1983178 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983179 (w : real) : (term65 w) = (term66 w).
Proof. exact (MK_COMB (@lem1983178) (@lem1983177 w)). Qed.
Lemma lem1983180 : term67 = term68.
Proof. exact (fun_ext (fun w : real => @lem1983179 w)). Qed.
Lemma lem1983181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983182 : term69 = term70.
Proof. exact (MK_COMB (@lem1983181) (@lem1983180)). Qed.
Lemma lem1983183 : term71 = term72.
Proof. exact (MK_COMB (@lem1983127) (@lem1983182)). Qed.
Lemma lem1983184 : term73 = term74.
Proof. exact (MK_COMB (@lem1983085) (@lem1983183)). Qed.
Lemma lem1983185 : term74 = term73.
Proof. exact (SYM (@lem1983184)). Qed.
Lemma lem1983235 (x : real) (y : real) : (term1 x y) = ((real_mul x y) = term0).
Proof. exact (EQ_MP (@lem1982817 x y) (@lem1982816 x y)). Qed.
Lemma lem1983236 (w : real) (x : real) (y : real) (z : real) : (term54 w x y z) = ((term75 w x y z) = term0).
Proof. exact (@lem1983235 (real_sub w x) (real_sub y z)). Qed.
Lemma lem1983239 (w : real) (z : real) (x : real) (y : real) : (term50 w z x y) = (term50 w z x y).
Proof. exact (eq_refl (term50 w z x y)). Qed.
Lemma lem1983240 (w : real) (x : real) (y : real) (z : real) : (((term48 w z x y) = term0) = (term54 w x y z)) = (((term48 w z x y) = term0) = ((term75 w x y z) = term0)).
Proof. exact (MK_COMB (@lem1983239 w z x y) (@lem1983236 w x y z)). Qed.
Lemma lem1983243 (w : real) (x : real) (y : real) : (term56 w x y) = (term76 w x y).
Proof. exact (fun_ext (fun z : real => @lem1983240 w x y z)). Qed.
Lemma lem1983244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983245 (w : real) (x : real) (y : real) : (term58 w x y) = (term77 w x y).
Proof. exact (MK_COMB (@lem1983244) (@lem1983243 w x y)). Qed.
Lemma lem1983250 (w : real) (x : real) : (term60 w x) = (term78 w x).
Proof. exact (fun_ext (fun y : real => @lem1983245 w x y)). Qed.
Lemma lem1983251 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983252 (w : real) (x : real) : (term62 w x) = (term79 w x).
Proof. exact (MK_COMB (@lem1983251) (@lem1983250 w x)). Qed.
Lemma lem1983257 (w : real) : (term64 w) = (term80 w).
Proof. exact (fun_ext (fun x : real => @lem1983252 w x)). Qed.
Lemma lem1983258 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983259 (w : real) : (term66 w) = (term81 w).
Proof. exact (MK_COMB (@lem1983258) (@lem1983257 w)). Qed.
Lemma lem1983264 : term68 = term82.
Proof. exact (fun_ext (fun w : real => @lem1983259 w)). Qed.
Lemma lem1983265 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1983266 : term70 = term83.
Proof. exact (MK_COMB (@lem1983265) (@lem1983264)). Qed.
Lemma lem1983271 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1983272 : term72 = term84.
Proof. exact (MK_COMB (@lem1983271) (@lem1983266)). Qed.
Lemma lem1983275 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1983276 : term74 = term85.
Proof. exact (MK_COMB (@lem1983275) (@lem1983272)). Qed.
Lemma lem1983279 : term85 = term74.
Proof. exact (SYM (@lem1983276)). Qed.
Lemma lem1983320 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983321 : term88 = term89.
Proof. exact (@lem1983320 term25). Qed.
Lemma lem1983322 (x : real) : (term90 x) = ((term23 x) = term0).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1983323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983325 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1983323) (@lem1983322 x)). Qed.
Lemma lem1983326 : term93 = term94.
Proof. exact (fun_ext (fun x : real => @lem1983325 x)). Qed.
Lemma lem1983327 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983328 : term89 = term95.
Proof. exact (MK_COMB (@lem1983327) (@lem1983326)). Qed.
Lemma lem1983329 : term88 = term95.
Proof. exact (TRANS (@lem1983321) (@lem1983328)). Qed.
Lemma lem1983344 (x : real) (y : real) (z : real) : (term96 x y z) = (term97 x y z).
Proof. exact (@lem17646 ((term30 y x z) = term0) ((real_sub y z) = term0)). Qed.
Lemma lem1983345 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983346 (x : real) (y : real) : (term98 x y) = (term99 x y).
Proof. exact (@lem1983345 (term34 x y)). Qed.
Lemma lem1983347 (x : real) (y : real) (z : real) : (term100 x y z) = (((term30 y x z) = term0) = ((real_sub y z) = term0)).
Proof. exact (eq_refl (term100 x y z)). Qed.
Lemma lem1983348 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983349 (x : real) (y : real) (z : real) : (term101 x y z) = (term96 x y z).
Proof. exact (MK_COMB (@lem1983348) (@lem1983347 x y z)). Qed.
Lemma lem1983350 (x : real) (y : real) (z : real) : (term101 x y z) = (term97 x y z).
Proof. exact (TRANS (@lem1983349 x y z) (@lem1983344 x y z)). Qed.
Lemma lem1983351 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1983350 x y z)). Qed.
Lemma lem1983352 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983353 (x : real) (y : real) : (term99 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1983352) (@lem1983351 x y)). Qed.
Lemma lem1983354 (x : real) (y : real) : (term98 x y) = (term104 x y).
Proof. exact (TRANS (@lem1983346 x y) (@lem1983353 x y)). Qed.
Lemma lem1983355 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983356 (x : real) : (term105 x) = (term106 x).
Proof. exact (@lem1983355 (term38 x)). Qed.
Lemma lem1983357 (x : real) (y : real) : (term107 x y) = (term36 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1983358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983359 (x : real) (y : real) : (term108 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1983358) (@lem1983357 x y)). Qed.
Lemma lem1983360 (x : real) (y : real) : (term108 x y) = (term104 x y).
Proof. exact (TRANS (@lem1983359 x y) (@lem1983354 x y)). Qed.
Lemma lem1983361 (x : real) : (term109 x) = (term110 x).
Proof. exact (fun_ext (fun y : real => @lem1983360 x y)). Qed.
Lemma lem1983362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983363 (x : real) : (term106 x) = (term111 x).
Proof. exact (MK_COMB (@lem1983362) (@lem1983361 x)). Qed.
Lemma lem1983364 (x : real) : (term105 x) = (term111 x).
Proof. exact (TRANS (@lem1983356 x) (@lem1983363 x)). Qed.
Lemma lem1983365 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983366 : term112 = term113.
Proof. exact (@lem1983365 term42). Qed.
Lemma lem1983367 (x : real) : (term114 x) = (term40 x).
Proof. exact (eq_refl (term114 x)). Qed.
Lemma lem1983368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983369 (x : real) : (term115 x) = (term105 x).
Proof. exact (MK_COMB (@lem1983368) (@lem1983367 x)). Qed.
Lemma lem1983370 (x : real) : (term115 x) = (term111 x).
Proof. exact (TRANS (@lem1983369 x) (@lem1983364 x)). Qed.
Lemma lem1983371 : term116 = term117.
Proof. exact (fun_ext (fun x : real => @lem1983370 x)). Qed.
Lemma lem1983372 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983373 : term113 = term118.
Proof. exact (MK_COMB (@lem1983372) (@lem1983371)). Qed.
Lemma lem1983374 : term112 = term118.
Proof. exact (TRANS (@lem1983366) (@lem1983373)). Qed.
Lemma lem1983389 (w : real) (x : real) (y : real) (z : real) : (term119 w x y z) = (term120 w x y z).
Proof. exact (@lem17646 ((term48 w z x y) = term0) ((term75 w x y z) = term0)). Qed.
Lemma lem1983390 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983391 (w : real) (x : real) (y : real) : (term121 w x y) = (term122 w x y).
Proof. exact (@lem1983390 (term76 w x y)). Qed.
Lemma lem1983392 (w : real) (x : real) (y : real) (z : real) : (term123 w x y z) = (((term48 w z x y) = term0) = ((term75 w x y z) = term0)).
Proof. exact (eq_refl (term123 w x y z)). Qed.
Lemma lem1983393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983394 (w : real) (x : real) (y : real) (z : real) : (term124 w x y z) = (term119 w x y z).
Proof. exact (MK_COMB (@lem1983393) (@lem1983392 w x y z)). Qed.
Lemma lem1983395 (w : real) (x : real) (y : real) (z : real) : (term124 w x y z) = (term120 w x y z).
Proof. exact (TRANS (@lem1983394 w x y z) (@lem1983389 w x y z)). Qed.
Lemma lem1983396 (w : real) (x : real) (y : real) : (term125 w x y) = (term126 w x y).
Proof. exact (fun_ext (fun z : real => @lem1983395 w x y z)). Qed.
Lemma lem1983397 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983398 (w : real) (x : real) (y : real) : (term122 w x y) = (term127 w x y).
Proof. exact (MK_COMB (@lem1983397) (@lem1983396 w x y)). Qed.
Lemma lem1983399 (w : real) (x : real) (y : real) : (term121 w x y) = (term127 w x y).
Proof. exact (TRANS (@lem1983391 w x y) (@lem1983398 w x y)). Qed.
Lemma lem1983400 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983401 (w : real) (x : real) : (term128 w x) = (term129 w x).
Proof. exact (@lem1983400 (term78 w x)). Qed.
Lemma lem1983402 (w : real) (x : real) (y : real) : (term130 w x y) = (term77 w x y).
Proof. exact (eq_refl (term130 w x y)). Qed.
Lemma lem1983403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983404 (w : real) (x : real) (y : real) : (term131 w x y) = (term121 w x y).
Proof. exact (MK_COMB (@lem1983403) (@lem1983402 w x y)). Qed.
Lemma lem1983405 (w : real) (x : real) (y : real) : (term131 w x y) = (term127 w x y).
Proof. exact (TRANS (@lem1983404 w x y) (@lem1983399 w x y)). Qed.
Lemma lem1983406 (w : real) (x : real) : (term132 w x) = (term133 w x).
Proof. exact (fun_ext (fun y : real => @lem1983405 w x y)). Qed.
Lemma lem1983407 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983408 (w : real) (x : real) : (term129 w x) = (term134 w x).
Proof. exact (MK_COMB (@lem1983407) (@lem1983406 w x)). Qed.
Lemma lem1983409 (w : real) (x : real) : (term128 w x) = (term134 w x).
Proof. exact (TRANS (@lem1983401 w x) (@lem1983408 w x)). Qed.
Lemma lem1983410 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983411 (w : real) : (term135 w) = (term136 w).
Proof. exact (@lem1983410 (term80 w)). Qed.
Lemma lem1983412 (w : real) (x : real) : (term137 w x) = (term79 w x).
Proof. exact (eq_refl (term137 w x)). Qed.
Lemma lem1983413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983414 (w : real) (x : real) : (term138 w x) = (term128 w x).
Proof. exact (MK_COMB (@lem1983413) (@lem1983412 w x)). Qed.
Lemma lem1983415 (w : real) (x : real) : (term138 w x) = (term134 w x).
Proof. exact (TRANS (@lem1983414 w x) (@lem1983409 w x)). Qed.
Lemma lem1983416 (w : real) : (term139 w) = (term140 w).
Proof. exact (fun_ext (fun x : real => @lem1983415 w x)). Qed.
Lemma lem1983417 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983418 (w : real) : (term136 w) = (term141 w).
Proof. exact (MK_COMB (@lem1983417) (@lem1983416 w)). Qed.
Lemma lem1983419 (w : real) : (term135 w) = (term141 w).
Proof. exact (TRANS (@lem1983411 w) (@lem1983418 w)). Qed.
Lemma lem1983420 (P : real -> Prop) : (term86 P) = (term87 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1983421 : term142 = term143.
Proof. exact (@lem1983420 term82). Qed.
Lemma lem1983422 (w : real) : (term144 w) = (term81 w).
Proof. exact (eq_refl (term144 w)). Qed.
Lemma lem1983423 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1983424 (w : real) : (term145 w) = (term135 w).
Proof. exact (MK_COMB (@lem1983423) (@lem1983422 w)). Qed.
Lemma lem1983425 (w : real) : (term145 w) = (term141 w).
Proof. exact (TRANS (@lem1983424 w) (@lem1983419 w)). Qed.
Lemma lem1983426 : term146 = term147.
Proof. exact (fun_ext (fun w : real => @lem1983425 w)). Qed.
Lemma lem1983427 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983428 : term143 = term148.
Proof. exact (MK_COMB (@lem1983427) (@lem1983426)). Qed.
Lemma lem1983429 : term142 = term148.
Proof. exact (TRANS (@lem1983421) (@lem1983428)). Qed.
Lemma lem1983430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983431 : term149 = term150.
Proof. exact (MK_COMB (@lem1983430) (@lem1983374)). Qed.
Lemma lem1983432 : term151 = term152.
Proof. exact (MK_COMB (@lem1983431) (@lem1983429)). Qed.
Lemma lem1983433 : term153 = term151.
Proof. exact (@lem17045 term44 term83). Qed.
Lemma lem1983434 : term153 = term152.
Proof. exact (TRANS (@lem1983433) (@lem1983432)). Qed.
Lemma lem1983435 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983436 : term154 = term155.
Proof. exact (MK_COMB (@lem1983435) (@lem1983329)). Qed.
Lemma lem1983437 : term156 = term157.
Proof. exact (MK_COMB (@lem1983436) (@lem1983434)). Qed.
Lemma lem1983438 : term158 = term156.
Proof. exact (@lem17045 term27 term84). Qed.
Lemma lem1983440 : term158 = term157.
Proof. exact (TRANS (@lem1983438) (@lem1983437)). Qed.
Lemma lem1983443 (x : real) : (term92 x) = (term92 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1983444 : term94 = term94.
Proof. exact (fun_ext (fun x : real => @lem1983443 x)). Qed.
Lemma lem1983445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983446 : term95 = term95.
Proof. exact (MK_COMB (@lem1983445) (@lem1983444)). Qed.
Lemma lem1983463 (x : real) (y : real) (z : real) : (term97 x y z) = (term97 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1983464 (x : real) (y : real) : (term103 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1983463 x y z)). Qed.
Lemma lem1983465 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983466 (x : real) (y : real) : (term104 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1983465) (@lem1983464 x y)). Qed.
Lemma lem1983467 (x : real) : (term110 x) = (term110 x).
Proof. exact (fun_ext (fun y : real => @lem1983466 x y)). Qed.
Lemma lem1983468 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983469 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem1983468) (@lem1983467 x)). Qed.
Lemma lem1983470 : term117 = term117.
Proof. exact (fun_ext (fun x : real => @lem1983469 x)). Qed.
Lemma lem1983471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983472 : term118 = term118.
Proof. exact (MK_COMB (@lem1983471) (@lem1983470)). Qed.
Lemma lem1983489 (w : real) (x : real) (y : real) (z : real) : (term120 w x y z) = (term120 w x y z).
Proof. exact (eq_refl (term120 w x y z)). Qed.
Lemma lem1983490 (w : real) (x : real) (y : real) : (term126 w x y) = (term126 w x y).
Proof. exact (fun_ext (fun z : real => @lem1983489 w x y z)). Qed.
Lemma lem1983491 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983492 (w : real) (x : real) (y : real) : (term127 w x y) = (term127 w x y).
Proof. exact (MK_COMB (@lem1983491) (@lem1983490 w x y)). Qed.
Lemma lem1983493 (w : real) (x : real) : (term133 w x) = (term133 w x).
Proof. exact (fun_ext (fun y : real => @lem1983492 w x y)). Qed.
Lemma lem1983494 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983495 (w : real) (x : real) : (term134 w x) = (term134 w x).
Proof. exact (MK_COMB (@lem1983494) (@lem1983493 w x)). Qed.
Lemma lem1983496 (w : real) : (term140 w) = (term140 w).
Proof. exact (fun_ext (fun x : real => @lem1983495 w x)). Qed.
Lemma lem1983497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983498 (w : real) : (term141 w) = (term141 w).
Proof. exact (MK_COMB (@lem1983497) (@lem1983496 w)). Qed.
Lemma lem1983499 : term147 = term147.
Proof. exact (fun_ext (fun w : real => @lem1983498 w)). Qed.
Lemma lem1983500 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983501 : term148 = term148.
Proof. exact (MK_COMB (@lem1983500) (@lem1983499)). Qed.
Lemma lem1983502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983503 : term150 = term150.
Proof. exact (MK_COMB (@lem1983502) (@lem1983472)). Qed.
Lemma lem1983504 : term152 = term152.
Proof. exact (MK_COMB (@lem1983503) (@lem1983501)). Qed.
Lemma lem1983505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983506 : term155 = term155.
Proof. exact (MK_COMB (@lem1983505) (@lem1983446)). Qed.
Lemma lem1983507 : term157 = term157.
Proof. exact (MK_COMB (@lem1983506) (@lem1983504)). Qed.
Lemma lem1983508 : term158 = term157.
Proof. exact (TRANS (@lem1983440) (@lem1983507)). Qed.
Lemma lem1983509 (x : real) : (term92 x) = (term159 x).
Proof. exact (@lem1483554 (term23 x) term0). Qed.
Lemma lem1983510 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983511 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983518 (x : real) : (term22 x) = term0.
Proof. exact (@lem1483456 x). Qed.
Lemma lem1983519 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983520 (x : real) : (term160 x) = term161.
Proof. exact (MK_COMB (@lem1983519) (@lem1983518 x)). Qed.
Lemma lem1983521 (x : real) : (term23 x) = term162.
Proof. exact (MK_COMB (@lem1983520 x) (@lem1983511)). Qed.
Lemma lem1983522 : term162 = term163.
Proof. exact (@lem1483519 term0 term0). Qed.
Lemma lem1983524 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983525 : term165 = term0.
Proof. exact (@lem1983524 term166). Qed.
Lemma lem1983526 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem1983527 : term163 = term168.
Proof. exact (MK_COMB (@lem1983526) (@lem1983525)). Qed.
Lemma lem1983528 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1983529 : term163 = term0.
Proof. exact (TRANS (@lem1983527) (@lem1983528)). Qed.
Lemma lem1983530 : term162 = term0.
Proof. exact (TRANS (@lem1983522) (@lem1983529)). Qed.
Lemma lem1983531 (x : real) : (term23 x) = term0.
Proof. exact (TRANS (@lem1983521 x) (@lem1983530)). Qed.
Lemma lem1983532 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983533 (x : real) : (term169 x) = term161.
Proof. exact (MK_COMB (@lem1983532) (@lem1983531 x)). Qed.
Lemma lem1983534 (x : real) : (term170 x) = term162.
Proof. exact (MK_COMB (@lem1983533 x) (@lem1983510)). Qed.
Lemma lem1983535 : term162 = term163.
Proof. exact (@lem1483519 term0 term0). Qed.
Lemma lem1983537 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983538 : term165 = term0.
Proof. exact (@lem1983537 term166). Qed.
Lemma lem1983539 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem1983540 : term163 = term168.
Proof. exact (MK_COMB (@lem1983539) (@lem1983538)). Qed.
Lemma lem1983541 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1983542 : term163 = term0.
Proof. exact (TRANS (@lem1983540) (@lem1983541)). Qed.
Lemma lem1983543 : term162 = term0.
Proof. exact (TRANS (@lem1983535) (@lem1983542)). Qed.
Lemma lem1983544 (x : real) : (term170 x) = term0.
Proof. exact (TRANS (@lem1983534 x) (@lem1983543)). Qed.
Lemma lem1983545 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1983546 (x : real) : (term171 x) = term172.
Proof. exact (MK_COMB (@lem1983545) (@lem1983544 x)). Qed.
Lemma lem1983547 : term172 = term165.
Proof. exact (@lem1483512 term0). Qed.
Lemma lem1983549 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983550 : term165 = term0.
Proof. exact (@lem1983549 term166). Qed.
Lemma lem1983551 : term172 = term0.
Proof. exact (TRANS (@lem1983547) (@lem1983550)). Qed.
Lemma lem1983552 (x : real) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem1983553 (x : real) : ((term171 x) = term172) = ((term171 x) = term0).
Proof. exact (MK_COMB (@lem1983552 x) (@lem1983551)). Qed.
Lemma lem1983554 (x : real) : (term171 x) = term0.
Proof. exact (EQ_MP (@lem1983553 x) (@lem1983546 x)). Qed.
Lemma lem1983555 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1983556 (x : real) : (term174 x) = term175.
Proof. exact (MK_COMB (@lem1983555) (@lem1983554 x)). Qed.
Lemma lem1983557 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983558 (x : real) : (term176 x) = term177.
Proof. exact (MK_COMB (@lem1983556 x) (@lem1983557)). Qed.
Lemma lem1983559 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1983560 (x : real) : (term178 x) = term175.
Proof. exact (MK_COMB (@lem1983559) (@lem1983544 x)). Qed.
Lemma lem1983561 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983562 (x : real) : (term179 x) = term177.
Proof. exact (MK_COMB (@lem1983560 x) (@lem1983561)). Qed.
Lemma lem1983563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983564 (x : real) : (term180 x) = term181.
Proof. exact (MK_COMB (@lem1983563) (@lem1983562 x)). Qed.
Lemma lem1983565 (x : real) : (term159 x) = term182.
Proof. exact (MK_COMB (@lem1983564 x) (@lem1983558 x)). Qed.
Lemma lem1983566 (x : real) : (term92 x) = term182.
Proof. exact (TRANS (@lem1983509 x) (@lem1983565 x)). Qed.
Lemma lem1983567 : term94 = term183.
Proof. exact (fun_ext (fun x : real => @lem1983566 x)). Qed.
Lemma lem1983568 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983569 : term95 = term184.
Proof. exact (MK_COMB (@lem1983568) (@lem1983567)). Qed.
Lemma lem1983570 (y : real) (x : real) (z : real) : ((term30 y x z) = term0) = ((term185 y x z) = term0).
Proof. exact (@lem1483529 (term30 y x z) term0). Qed.
Lemma lem1983571 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983589 (y : real) (x : real) (z : real) : (term30 y x z) = (term186 y x z).
Proof. exact (@lem1483519 (real_add x y) (real_add x z)). Qed.
Lemma lem1983596 (x : real) (z : real) : (term187 x z) = (term188 x z).
Proof. exact (@lem1483508 x term189 z). Qed.
Lemma lem1983597 (x : real) (y : real) : (term190 x y) = (term190 x y).
Proof. exact (eq_refl (term190 x y)). Qed.
Lemma lem1983598 (y : real) (x : real) (z : real) : (term186 y x z) = (term191 y x z).
Proof. exact (MK_COMB (@lem1983597 x y) (@lem1983596 x z)). Qed.
Lemma lem1983599 (x : real) (y : real) (z : real) : (term191 y x z) = (term192 x y z).
Proof. exact (@lem1483480 x (term193 x) y (term193 z)). Qed.
Lemma lem1983600 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483442 term189 x). Qed.
Lemma lem1983602 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1983603 : term197 = term0.
Proof. exact (@lem1983602 term166). Qed.
Lemma lem1983604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1983605 : term198 = term199.
Proof. exact (MK_COMB (@lem1983604) (@lem1983603)). Qed.
Lemma lem1983606 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1983607 (x : real) : (term195 x) = (term22 x).
Proof. exact (MK_COMB (@lem1983605) (@lem1983606 x)). Qed.
Lemma lem1983608 (x : real) : (term194 x) = (term22 x).
Proof. exact (TRANS (@lem1983600 x) (@lem1983607 x)). Qed.
Lemma lem1983609 (x : real) : (term22 x) = term0.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1983610 (x : real) : (term194 x) = term0.
Proof. exact (TRANS (@lem1983608 x) (@lem1983609 x)). Qed.
Lemma lem1983611 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1983612 (x : real) : (term200 x) = term167.
Proof. exact (MK_COMB (@lem1983611) (@lem1983610 x)). Qed.
Lemma lem1983613 (y : real) (z : real) : (term201 y z) = (term201 y z).
Proof. exact (eq_refl (term201 y z)). Qed.
Lemma lem1983614 (x : real) (y : real) (z : real) : (term192 x y z) = (term202 y z).
Proof. exact (MK_COMB (@lem1983612 x) (@lem1983613 y z)). Qed.
Lemma lem1983615 (x : real) (y : real) (z : real) : (term191 y x z) = (term202 y z).
Proof. exact (TRANS (@lem1983599 x y z) (@lem1983614 x y z)). Qed.
Lemma lem1983616 (y : real) (z : real) : (term202 y z) = (term201 y z).
Proof. exact (@lem1483448 (term201 y z)). Qed.
Lemma lem1983617 (x : real) (y : real) (z : real) : (term191 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983615 x y z) (@lem1983616 y z)). Qed.
Lemma lem1983618 (x : real) (y : real) (z : real) : (term186 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983598 y x z) (@lem1983617 x y z)). Qed.
Lemma lem1983620 (x : real) (y : real) (z : real) : (term30 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983589 y x z) (@lem1983618 x y z)). Qed.
Lemma lem1983621 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983622 (x : real) (y : real) (z : real) : (term203 y x z) = (term204 y z).
Proof. exact (MK_COMB (@lem1983621) (@lem1983620 x y z)). Qed.
Lemma lem1983623 (x : real) (y : real) (z : real) : (term185 y x z) = (term205 y z).
Proof. exact (MK_COMB (@lem1983622 x y z) (@lem1983571)). Qed.
Lemma lem1983624 (y : real) (z : real) : (term205 y z) = (term206 y z).
Proof. exact (@lem1483519 (term201 y z) term0). Qed.
Lemma lem1983626 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983627 : term165 = term0.
Proof. exact (@lem1983626 term166). Qed.
Lemma lem1983628 (y : real) (z : real) : (term207 y z) = (term207 y z).
Proof. exact (eq_refl (term207 y z)). Qed.
Lemma lem1983629 (y : real) (z : real) : (term206 y z) = (term208 y z).
Proof. exact (MK_COMB (@lem1983628 y z) (@lem1983627)). Qed.
Lemma lem1983630 (y : real) (z : real) : (term208 y z) = (term201 y z).
Proof. exact (@lem1483450 (term201 y z)). Qed.
Lemma lem1983631 (y : real) (z : real) : (term206 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983629 y z) (@lem1983630 y z)). Qed.
Lemma lem1983632 (y : real) (z : real) : (term205 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983624 y z) (@lem1983631 y z)). Qed.
Lemma lem1983633 (x : real) (y : real) (z : real) : (term185 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983623 x y z) (@lem1983632 y z)). Qed.
Lemma lem1983634 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1983635 (x : real) (y : real) (z : real) : (term209 y x z) = (term210 y z).
Proof. exact (MK_COMB (@lem1983634) (@lem1983633 x y z)). Qed.
Lemma lem1983636 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983637 (x : real) (y : real) (z : real) : ((term185 y x z) = term0) = ((term201 y z) = term0).
Proof. exact (MK_COMB (@lem1983635 x y z) (@lem1983636)). Qed.
Lemma lem1983638 (x : real) (y : real) (z : real) : ((term30 y x z) = term0) = ((term201 y z) = term0).
Proof. exact (TRANS (@lem1983570 y x z) (@lem1983637 x y z)). Qed.
Lemma lem1983639 (y : real) (z : real) : (term211 y z) = (term212 y z).
Proof. exact (@lem1483554 (real_sub y z) term0). Qed.
Lemma lem1983640 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983653 (y : real) (z : real) : (real_sub y z) = (term201 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1983654 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983655 (y : real) (z : real) : (term213 y z) = (term204 y z).
Proof. exact (MK_COMB (@lem1983654) (@lem1983653 y z)). Qed.
Lemma lem1983656 (y : real) (z : real) : (term214 y z) = (term205 y z).
Proof. exact (MK_COMB (@lem1983655 y z) (@lem1983640)). Qed.
Lemma lem1983657 (y : real) (z : real) : (term205 y z) = (term206 y z).
Proof. exact (@lem1483519 (term201 y z) term0). Qed.
Lemma lem1983659 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983660 : term165 = term0.
Proof. exact (@lem1983659 term166). Qed.
Lemma lem1983661 (y : real) (z : real) : (term207 y z) = (term207 y z).
Proof. exact (eq_refl (term207 y z)). Qed.
Lemma lem1983662 (y : real) (z : real) : (term206 y z) = (term208 y z).
Proof. exact (MK_COMB (@lem1983661 y z) (@lem1983660)). Qed.
Lemma lem1983663 (y : real) (z : real) : (term208 y z) = (term201 y z).
Proof. exact (@lem1483450 (term201 y z)). Qed.
Lemma lem1983664 (y : real) (z : real) : (term206 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983662 y z) (@lem1983663 y z)). Qed.
Lemma lem1983665 (y : real) (z : real) : (term205 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983657 y z) (@lem1983664 y z)). Qed.
Lemma lem1983666 (y : real) (z : real) : (term214 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983656 y z) (@lem1983665 y z)). Qed.
Lemma lem1983667 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1983668 (y : real) (z : real) : (term215 y z) = (term216 y z).
Proof. exact (MK_COMB (@lem1983667) (@lem1983666 y z)). Qed.
Lemma lem1983669 (y : real) (z : real) : (term216 y z) = (term217 y z).
Proof. exact (@lem1483512 (term201 y z)). Qed.
Lemma lem1983670 (y : real) (z : real) : (term217 y z) = (term218 y z).
Proof. exact (@lem1483508 y term189 (term193 z)). Qed.
Lemma lem1983671 (z : real) : (term219 z) = (term220 z).
Proof. exact (@lem1483476 term189 term189 z). Qed.
Lemma lem1983673 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1983674 : term223 = term224.
Proof. exact (@lem1983673 term166 term166). Qed.
Lemma lem1983675 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1983676 : term226 = term166.
Proof. exact (EQ_MP (@lem1983675) (@lem940073)). Qed.
Lemma lem1983677 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1983678 : term224 = term227.
Proof. exact (MK_COMB (@lem1983677) (@lem1983676)). Qed.
Lemma lem1983679 : term223 = term227.
Proof. exact (TRANS (@lem1983674) (@lem1983678)). Qed.
Lemma lem1983680 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1983681 : term228 = term229.
Proof. exact (MK_COMB (@lem1983680) (@lem1983679)). Qed.
Lemma lem1983682 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1983683 (z : real) : (term220 z) = (term230 z).
Proof. exact (MK_COMB (@lem1983681) (@lem1983682 z)). Qed.
Lemma lem1983684 (z : real) : (term219 z) = (term230 z).
Proof. exact (TRANS (@lem1983671 z) (@lem1983683 z)). Qed.
Lemma lem1983685 (z : real) : (term230 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1983686 (z : real) : (term219 z) = z.
Proof. exact (TRANS (@lem1983684 z) (@lem1983685 z)). Qed.
Lemma lem1983689 (y : real) : (term231 y) = (term231 y).
Proof. exact (eq_refl (term231 y)). Qed.
Lemma lem1983690 (y : real) (z : real) : (term218 y z) = (term232 y z).
Proof. exact (MK_COMB (@lem1983689 y) (@lem1983686 z)). Qed.
Lemma lem1983691 (y : real) (z : real) : (term217 y z) = (term232 y z).
Proof. exact (TRANS (@lem1983670 y z) (@lem1983690 y z)). Qed.
Lemma lem1983692 (y : real) (z : real) : (term216 y z) = (term232 y z).
Proof. exact (TRANS (@lem1983669 y z) (@lem1983691 y z)). Qed.
Lemma lem1983693 (y : real) (z : real) : (term233 y z) = (term233 y z).
Proof. exact (eq_refl (term233 y z)). Qed.
Lemma lem1983694 (y : real) (z : real) : ((term215 y z) = (term216 y z)) = ((term215 y z) = (term232 y z)).
Proof. exact (MK_COMB (@lem1983693 y z) (@lem1983692 y z)). Qed.
Lemma lem1983695 (y : real) (z : real) : (term215 y z) = (term232 y z).
Proof. exact (EQ_MP (@lem1983694 y z) (@lem1983668 y z)). Qed.
Lemma lem1983696 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1983697 (y : real) (z : real) : (term234 y z) = (term235 y z).
Proof. exact (MK_COMB (@lem1983696) (@lem1983695 y z)). Qed.
Lemma lem1983698 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983699 (y : real) (z : real) : (term236 y z) = (term237 y z).
Proof. exact (MK_COMB (@lem1983697 y z) (@lem1983698)). Qed.
Lemma lem1983700 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1983701 (y : real) (z : real) : (term238 y z) = (term239 y z).
Proof. exact (MK_COMB (@lem1983700) (@lem1983666 y z)). Qed.
Lemma lem1983702 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983703 (y : real) (z : real) : (term240 y z) = (term241 y z).
Proof. exact (MK_COMB (@lem1983701 y z) (@lem1983702)). Qed.
Lemma lem1983704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983705 (y : real) (z : real) : (term242 y z) = (term243 y z).
Proof. exact (MK_COMB (@lem1983704) (@lem1983703 y z)). Qed.
Lemma lem1983706 (y : real) (z : real) : (term212 y z) = (term244 y z).
Proof. exact (MK_COMB (@lem1983705 y z) (@lem1983699 y z)). Qed.
Lemma lem1983707 (y : real) (z : real) : (term211 y z) = (term244 y z).
Proof. exact (TRANS (@lem1983639 y z) (@lem1983706 y z)). Qed.
Lemma lem1983708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1983709 (x : real) (y : real) (z : real) : (term245 y x z) = (term246 y z).
Proof. exact (MK_COMB (@lem1983708) (@lem1983638 x y z)). Qed.
Lemma lem1983710 (x : real) (y : real) (z : real) : (term247 x y z) = (term248 y z).
Proof. exact (MK_COMB (@lem1983709 x y z) (@lem1983707 y z)). Qed.
Lemma lem1983711 (y : real) (x : real) (z : real) : (term249 y x z) = (term250 y x z).
Proof. exact (@lem1483554 (term30 y x z) term0). Qed.
Lemma lem1983712 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983730 (y : real) (x : real) (z : real) : (term30 y x z) = (term186 y x z).
Proof. exact (@lem1483519 (real_add x y) (real_add x z)). Qed.
Lemma lem1983737 (x : real) (z : real) : (term187 x z) = (term188 x z).
Proof. exact (@lem1483508 x term189 z). Qed.
Lemma lem1983738 (x : real) (y : real) : (term190 x y) = (term190 x y).
Proof. exact (eq_refl (term190 x y)). Qed.
Lemma lem1983739 (y : real) (x : real) (z : real) : (term186 y x z) = (term191 y x z).
Proof. exact (MK_COMB (@lem1983738 x y) (@lem1983737 x z)). Qed.
Lemma lem1983740 (x : real) (y : real) (z : real) : (term191 y x z) = (term192 x y z).
Proof. exact (@lem1483480 x (term193 x) y (term193 z)). Qed.
Lemma lem1983741 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483442 term189 x). Qed.
Lemma lem1983743 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1983744 : term197 = term0.
Proof. exact (@lem1983743 term166). Qed.
Lemma lem1983745 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1983746 : term198 = term199.
Proof. exact (MK_COMB (@lem1983745) (@lem1983744)). Qed.
Lemma lem1983747 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1983748 (x : real) : (term195 x) = (term22 x).
Proof. exact (MK_COMB (@lem1983746) (@lem1983747 x)). Qed.
Lemma lem1983749 (x : real) : (term194 x) = (term22 x).
Proof. exact (TRANS (@lem1983741 x) (@lem1983748 x)). Qed.
Lemma lem1983750 (x : real) : (term22 x) = term0.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1983751 (x : real) : (term194 x) = term0.
Proof. exact (TRANS (@lem1983749 x) (@lem1983750 x)). Qed.
Lemma lem1983752 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1983753 (x : real) : (term200 x) = term167.
Proof. exact (MK_COMB (@lem1983752) (@lem1983751 x)). Qed.
Lemma lem1983754 (y : real) (z : real) : (term201 y z) = (term201 y z).
Proof. exact (eq_refl (term201 y z)). Qed.
Lemma lem1983755 (x : real) (y : real) (z : real) : (term192 x y z) = (term202 y z).
Proof. exact (MK_COMB (@lem1983753 x) (@lem1983754 y z)). Qed.
Lemma lem1983756 (x : real) (y : real) (z : real) : (term191 y x z) = (term202 y z).
Proof. exact (TRANS (@lem1983740 x y z) (@lem1983755 x y z)). Qed.
Lemma lem1983757 (y : real) (z : real) : (term202 y z) = (term201 y z).
Proof. exact (@lem1483448 (term201 y z)). Qed.
Lemma lem1983758 (x : real) (y : real) (z : real) : (term191 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983756 x y z) (@lem1983757 y z)). Qed.
Lemma lem1983759 (x : real) (y : real) (z : real) : (term186 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983739 y x z) (@lem1983758 x y z)). Qed.
Lemma lem1983761 (x : real) (y : real) (z : real) : (term30 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983730 y x z) (@lem1983759 x y z)). Qed.
Lemma lem1983762 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983763 (x : real) (y : real) (z : real) : (term203 y x z) = (term204 y z).
Proof. exact (MK_COMB (@lem1983762) (@lem1983761 x y z)). Qed.
Lemma lem1983764 (x : real) (y : real) (z : real) : (term185 y x z) = (term205 y z).
Proof. exact (MK_COMB (@lem1983763 x y z) (@lem1983712)). Qed.
Lemma lem1983765 (y : real) (z : real) : (term205 y z) = (term206 y z).
Proof. exact (@lem1483519 (term201 y z) term0). Qed.
Lemma lem1983767 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983768 : term165 = term0.
Proof. exact (@lem1983767 term166). Qed.
Lemma lem1983769 (y : real) (z : real) : (term207 y z) = (term207 y z).
Proof. exact (eq_refl (term207 y z)). Qed.
Lemma lem1983770 (y : real) (z : real) : (term206 y z) = (term208 y z).
Proof. exact (MK_COMB (@lem1983769 y z) (@lem1983768)). Qed.
Lemma lem1983771 (y : real) (z : real) : (term208 y z) = (term201 y z).
Proof. exact (@lem1483450 (term201 y z)). Qed.
Lemma lem1983772 (y : real) (z : real) : (term206 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983770 y z) (@lem1983771 y z)). Qed.
Lemma lem1983773 (y : real) (z : real) : (term205 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983765 y z) (@lem1983772 y z)). Qed.
Lemma lem1983774 (x : real) (y : real) (z : real) : (term185 y x z) = (term201 y z).
Proof. exact (TRANS (@lem1983764 x y z) (@lem1983773 y z)). Qed.
Lemma lem1983775 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1983776 (x : real) (y : real) (z : real) : (term251 y x z) = (term216 y z).
Proof. exact (MK_COMB (@lem1983775) (@lem1983774 x y z)). Qed.
Lemma lem1983777 (y : real) (z : real) : (term216 y z) = (term217 y z).
Proof. exact (@lem1483512 (term201 y z)). Qed.
Lemma lem1983778 (y : real) (z : real) : (term217 y z) = (term218 y z).
Proof. exact (@lem1483508 y term189 (term193 z)). Qed.
Lemma lem1983779 (z : real) : (term219 z) = (term220 z).
Proof. exact (@lem1483476 term189 term189 z). Qed.
Lemma lem1983781 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1983782 : term223 = term224.
Proof. exact (@lem1983781 term166 term166). Qed.
Lemma lem1983783 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1983784 : term226 = term166.
Proof. exact (EQ_MP (@lem1983783) (@lem940073)). Qed.
Lemma lem1983785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1983786 : term224 = term227.
Proof. exact (MK_COMB (@lem1983785) (@lem1983784)). Qed.
Lemma lem1983787 : term223 = term227.
Proof. exact (TRANS (@lem1983782) (@lem1983786)). Qed.
Lemma lem1983788 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1983789 : term228 = term229.
Proof. exact (MK_COMB (@lem1983788) (@lem1983787)). Qed.
Lemma lem1983790 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1983791 (z : real) : (term220 z) = (term230 z).
Proof. exact (MK_COMB (@lem1983789) (@lem1983790 z)). Qed.
Lemma lem1983792 (z : real) : (term219 z) = (term230 z).
Proof. exact (TRANS (@lem1983779 z) (@lem1983791 z)). Qed.
Lemma lem1983793 (z : real) : (term230 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1983794 (z : real) : (term219 z) = z.
Proof. exact (TRANS (@lem1983792 z) (@lem1983793 z)). Qed.
Lemma lem1983797 (y : real) : (term231 y) = (term231 y).
Proof. exact (eq_refl (term231 y)). Qed.
Lemma lem1983798 (y : real) (z : real) : (term218 y z) = (term232 y z).
Proof. exact (MK_COMB (@lem1983797 y) (@lem1983794 z)). Qed.
Lemma lem1983799 (y : real) (z : real) : (term217 y z) = (term232 y z).
Proof. exact (TRANS (@lem1983778 y z) (@lem1983798 y z)). Qed.
Lemma lem1983800 (y : real) (z : real) : (term216 y z) = (term232 y z).
Proof. exact (TRANS (@lem1983777 y z) (@lem1983799 y z)). Qed.
Lemma lem1983801 (y : real) (x : real) (z : real) : (term252 y x z) = (term252 y x z).
Proof. exact (eq_refl (term252 y x z)). Qed.
Lemma lem1983802 (x : real) (y : real) (z : real) : ((term251 y x z) = (term216 y z)) = ((term251 y x z) = (term232 y z)).
Proof. exact (MK_COMB (@lem1983801 y x z) (@lem1983800 y z)). Qed.
Lemma lem1983803 (x : real) (y : real) (z : real) : (term251 y x z) = (term232 y z).
Proof. exact (EQ_MP (@lem1983802 x y z) (@lem1983776 x y z)). Qed.
Lemma lem1983804 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1983805 (x : real) (y : real) (z : real) : (term253 y x z) = (term235 y z).
Proof. exact (MK_COMB (@lem1983804) (@lem1983803 x y z)). Qed.
Lemma lem1983806 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983807 (x : real) (y : real) (z : real) : (term254 y x z) = (term237 y z).
Proof. exact (MK_COMB (@lem1983805 x y z) (@lem1983806)). Qed.
Lemma lem1983808 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1983809 (x : real) (y : real) (z : real) : (term255 y x z) = (term239 y z).
Proof. exact (MK_COMB (@lem1983808) (@lem1983774 x y z)). Qed.
Lemma lem1983810 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983811 (x : real) (y : real) (z : real) : (term256 y x z) = (term241 y z).
Proof. exact (MK_COMB (@lem1983809 x y z) (@lem1983810)). Qed.
Lemma lem1983812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983813 (x : real) (y : real) (z : real) : (term257 y x z) = (term243 y z).
Proof. exact (MK_COMB (@lem1983812) (@lem1983811 x y z)). Qed.
Lemma lem1983814 (x : real) (y : real) (z : real) : (term250 y x z) = (term244 y z).
Proof. exact (MK_COMB (@lem1983813 x y z) (@lem1983807 x y z)). Qed.
Lemma lem1983815 (x : real) (y : real) (z : real) : (term249 y x z) = (term244 y z).
Proof. exact (TRANS (@lem1983711 y x z) (@lem1983814 x y z)). Qed.
Lemma lem1983816 (y : real) (z : real) : ((real_sub y z) = term0) = ((term214 y z) = term0).
Proof. exact (@lem1483529 (real_sub y z) term0). Qed.
Lemma lem1983817 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983830 (y : real) (z : real) : (real_sub y z) = (term201 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1983831 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983832 (y : real) (z : real) : (term213 y z) = (term204 y z).
Proof. exact (MK_COMB (@lem1983831) (@lem1983830 y z)). Qed.
Lemma lem1983833 (y : real) (z : real) : (term214 y z) = (term205 y z).
Proof. exact (MK_COMB (@lem1983832 y z) (@lem1983817)). Qed.
Lemma lem1983834 (y : real) (z : real) : (term205 y z) = (term206 y z).
Proof. exact (@lem1483519 (term201 y z) term0). Qed.
Lemma lem1983836 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983837 : term165 = term0.
Proof. exact (@lem1983836 term166). Qed.
Lemma lem1983838 (y : real) (z : real) : (term207 y z) = (term207 y z).
Proof. exact (eq_refl (term207 y z)). Qed.
Lemma lem1983839 (y : real) (z : real) : (term206 y z) = (term208 y z).
Proof. exact (MK_COMB (@lem1983838 y z) (@lem1983837)). Qed.
Lemma lem1983840 (y : real) (z : real) : (term208 y z) = (term201 y z).
Proof. exact (@lem1483450 (term201 y z)). Qed.
Lemma lem1983841 (y : real) (z : real) : (term206 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983839 y z) (@lem1983840 y z)). Qed.
Lemma lem1983842 (y : real) (z : real) : (term205 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983834 y z) (@lem1983841 y z)). Qed.
Lemma lem1983843 (y : real) (z : real) : (term214 y z) = (term201 y z).
Proof. exact (TRANS (@lem1983833 y z) (@lem1983842 y z)). Qed.
Lemma lem1983844 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1983845 (y : real) (z : real) : (term258 y z) = (term210 y z).
Proof. exact (MK_COMB (@lem1983844) (@lem1983843 y z)). Qed.
Lemma lem1983846 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983847 (y : real) (z : real) : ((term214 y z) = term0) = ((term201 y z) = term0).
Proof. exact (MK_COMB (@lem1983845 y z) (@lem1983846)). Qed.
Lemma lem1983848 (y : real) (z : real) : ((real_sub y z) = term0) = ((term201 y z) = term0).
Proof. exact (TRANS (@lem1983816 y z) (@lem1983847 y z)). Qed.
Lemma lem1983849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1983850 (x : real) (y : real) (z : real) : (term259 y x z) = (term260 y z).
Proof. exact (MK_COMB (@lem1983849) (@lem1983815 x y z)). Qed.
Lemma lem1983851 (x : real) (y : real) (z : real) : (term261 x y z) = (term262 y z).
Proof. exact (MK_COMB (@lem1983850 x y z) (@lem1983848 y z)). Qed.
Lemma lem1983852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1983853 (x : real) (y : real) (z : real) : (term263 x y z) = (term264 y z).
Proof. exact (MK_COMB (@lem1983852) (@lem1983710 x y z)). Qed.
Lemma lem1983854 (x : real) (y : real) (z : real) : (term97 x y z) = (term265 y z).
Proof. exact (MK_COMB (@lem1983853 x y z) (@lem1983851 x y z)). Qed.
Lemma lem1983855 (x : real) (y : real) : (term103 x y) = (term266 y).
Proof. exact (fun_ext (fun z : real => @lem1983854 x y z)). Qed.
Lemma lem1983856 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983857 (x : real) (y : real) : (term104 x y) = (term267 y).
Proof. exact (MK_COMB (@lem1983856) (@lem1983855 x y)). Qed.
Lemma lem1983858 (x : real) : (term110 x) = term268.
Proof. exact (fun_ext (fun y : real => @lem1983857 x y)). Qed.
Lemma lem1983859 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983860 (x : real) : (term111 x) = term269.
Proof. exact (MK_COMB (@lem1983859) (@lem1983858 x)). Qed.
Lemma lem1983861 : term117 = term270.
Proof. exact (fun_ext (fun x : real => @lem1983860 x)). Qed.
Lemma lem1983862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1983863 : term118 = term271.
Proof. exact (MK_COMB (@lem1983862) (@lem1983861)). Qed.
Lemma lem1983864 (w : real) (z : real) (x : real) (y : real) : ((term48 w z x y) = term0) = ((term272 w z x y) = term0).
Proof. exact (@lem1483529 (term48 w z x y) term0). Qed.
Lemma lem1983865 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983907 (w : real) (z : real) (x : real) (y : real) : (term48 w z x y) = (term273 w z x y).
Proof. exact (@lem1483519 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem1983914 (w : real) (z : real) (x : real) (y : real) : (term274 w z x y) = (term275 w z x y).
Proof. exact (@lem1483508 (real_mul w z) term189 (real_mul x y)). Qed.
Lemma lem1983915 (w : real) (y : real) (x : real) (z : real) : (term276 w y x z) = (term276 w y x z).
Proof. exact (eq_refl (term276 w y x z)). Qed.
Lemma lem1983916 (w : real) (z : real) (x : real) (y : real) : (term273 w z x y) = (term277 w z x y).
Proof. exact (MK_COMB (@lem1983915 w y x z) (@lem1983914 w z x y)). Qed.
Lemma lem1983917 (w : real) (z : real) (x : real) (y : real) : (term277 w z x y) = (term278 w z x y).
Proof. exact (@lem1483482 (real_mul w y) (real_mul x z) (term275 w z x y)). Qed.
Lemma lem1983918 (w : real) (z : real) (x : real) (y : real) : (term279 w z x y) = (term280 w z x y).
Proof. exact (@lem1483484 (term281 w z) (real_mul x z) (term281 x y)). Qed.
Lemma lem1983919 (y : real) (x : real) (z : real) : (term282 z x y) = (term283 y x z).
Proof. exact (@lem1483488 (term281 x y) (real_mul x z)). Qed.
Lemma lem1983920 (w : real) (z : real) : (term284 w z) = (term284 w z).
Proof. exact (eq_refl (term284 w z)). Qed.
Lemma lem1983921 (w : real) (y : real) (x : real) (z : real) : (term280 w z x y) = (term285 w y x z).
Proof. exact (MK_COMB (@lem1983920 w z) (@lem1983919 y x z)). Qed.
Lemma lem1983922 (w : real) (y : real) (x : real) (z : real) : (term279 w z x y) = (term285 w y x z).
Proof. exact (TRANS (@lem1983918 w z x y) (@lem1983921 w y x z)). Qed.
Lemma lem1983923 (w : real) (y : real) : (term286 w y) = (term286 w y).
Proof. exact (eq_refl (term286 w y)). Qed.
Lemma lem1983924 (w : real) (y : real) (x : real) (z : real) : (term278 w z x y) = (term287 w y x z).
Proof. exact (MK_COMB (@lem1983923 w y) (@lem1983922 w y x z)). Qed.
Lemma lem1983925 (w : real) (y : real) (x : real) (z : real) : (term277 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1983917 w z x y) (@lem1983924 w y x z)). Qed.
Lemma lem1983926 (w : real) (y : real) (x : real) (z : real) : (term273 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1983916 w z x y) (@lem1983925 w y x z)). Qed.
Lemma lem1983928 (w : real) (y : real) (x : real) (z : real) : (term48 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1983907 w z x y) (@lem1983926 w y x z)). Qed.
Lemma lem1983929 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1983930 (w : real) (y : real) (x : real) (z : real) : (term288 w z x y) = (term289 w y x z).
Proof. exact (MK_COMB (@lem1983929) (@lem1983928 w y x z)). Qed.
Lemma lem1983931 (w : real) (y : real) (x : real) (z : real) : (term272 w z x y) = (term290 w y x z).
Proof. exact (MK_COMB (@lem1983930 w y x z) (@lem1983865)). Qed.
Lemma lem1983932 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term291 w y x z).
Proof. exact (@lem1483519 (term287 w y x z) term0). Qed.
Lemma lem1983934 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1983935 : term165 = term0.
Proof. exact (@lem1983934 term166). Qed.
Lemma lem1983936 (w : real) (y : real) (x : real) (z : real) : (term292 w y x z) = (term292 w y x z).
Proof. exact (eq_refl (term292 w y x z)). Qed.
Lemma lem1983937 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term293 w y x z).
Proof. exact (MK_COMB (@lem1983936 w y x z) (@lem1983935)). Qed.
Lemma lem1983938 (w : real) (y : real) (x : real) (z : real) : (term293 w y x z) = (term287 w y x z).
Proof. exact (@lem1483450 (term287 w y x z)). Qed.
Lemma lem1983939 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1983937 w y x z) (@lem1983938 w y x z)). Qed.
Lemma lem1983940 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1983932 w y x z) (@lem1983939 w y x z)). Qed.
Lemma lem1983941 (w : real) (y : real) (x : real) (z : real) : (term272 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1983931 w y x z) (@lem1983940 w y x z)). Qed.
Lemma lem1983942 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1983943 (w : real) (y : real) (x : real) (z : real) : (term294 w z x y) = (term295 w y x z).
Proof. exact (MK_COMB (@lem1983942) (@lem1983941 w y x z)). Qed.
Lemma lem1983944 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983945 (w : real) (y : real) (x : real) (z : real) : ((term272 w z x y) = term0) = ((term287 w y x z) = term0).
Proof. exact (MK_COMB (@lem1983943 w y x z) (@lem1983944)). Qed.
Lemma lem1983946 (w : real) (y : real) (x : real) (z : real) : ((term48 w z x y) = term0) = ((term287 w y x z) = term0).
Proof. exact (TRANS (@lem1983864 w z x y) (@lem1983945 w y x z)). Qed.
Lemma lem1983947 (w : real) (x : real) (y : real) (z : real) : (term296 w x y z) = (term297 w x y z).
Proof. exact (@lem1483554 (term75 w x y z) term0). Qed.
Lemma lem1983948 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1983961 (y : real) (z : real) : (real_sub y z) = (term201 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1983974 (w : real) (x : real) : (real_sub w x) = (term201 w x).
Proof. exact (@lem1483519 w x). Qed.
Lemma lem1983975 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1983976 (w : real) (x : real) : (term298 w x) = (term299 w x).
Proof. exact (MK_COMB (@lem1983975) (@lem1983974 w x)). Qed.
Lemma lem1983977 (w : real) (x : real) (y : real) (z : real) : (term75 w x y z) = (term300 w x y z).
Proof. exact (MK_COMB (@lem1983976 w x) (@lem1983961 y z)). Qed.
Lemma lem1983978 (w : real) (x : real) (y : real) (z : real) : (term300 w x y z) = (term301 w x y z).
Proof. exact (@lem1483454 w (term193 x) (term201 y z)). Qed.
Lemma lem1983979 (y : real) (w : real) (z : real) : (term302 w y z) = (term303 y w z).
Proof. exact (@lem1483508 y w (term193 z)). Qed.
Lemma lem1983984 (w : real) (z : real) : (term304 w z) = (term281 w z).
Proof. exact (@lem1483478 term189 w z). Qed.
Lemma lem1983987 (w : real) (y : real) : (term286 w y) = (term286 w y).
Proof. exact (eq_refl (term286 w y)). Qed.
Lemma lem1983988 (y : real) (w : real) (z : real) : (term303 y w z) = (term282 y w z).
Proof. exact (MK_COMB (@lem1983987 w y) (@lem1983984 w z)). Qed.
Lemma lem1983989 (y : real) (w : real) (z : real) : (term302 w y z) = (term282 y w z).
Proof. exact (TRANS (@lem1983979 y w z) (@lem1983988 y w z)). Qed.
Lemma lem1983990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1983991 (y : real) (w : real) (z : real) : (term305 w y z) = (term306 y w z).
Proof. exact (MK_COMB (@lem1983990) (@lem1983989 y w z)). Qed.
Lemma lem1983992 (y : real) (x : real) (z : real) : (term307 x y z) = (term308 y x z).
Proof. exact (@lem1483508 y (term193 x) (term193 z)). Qed.
Lemma lem1983993 (x : real) (z : real) : (term309 x z) = (term310 x z).
Proof. exact (@lem1483464 term189 term189 x z). Qed.
Lemma lem1983995 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1983996 : term223 = term224.
Proof. exact (@lem1983995 term166 term166). Qed.
Lemma lem1983997 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1983998 : term226 = term166.
Proof. exact (EQ_MP (@lem1983997) (@lem940073)). Qed.
Lemma lem1983999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1984000 : term224 = term227.
Proof. exact (MK_COMB (@lem1983999) (@lem1983998)). Qed.
Lemma lem1984001 : term223 = term227.
Proof. exact (TRANS (@lem1983996) (@lem1984000)). Qed.
Lemma lem1984002 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984003 : term228 = term229.
Proof. exact (MK_COMB (@lem1984002) (@lem1984001)). Qed.
Lemma lem1984004 (x : real) (z : real) : (real_mul x z) = (real_mul x z).
Proof. exact (eq_refl (real_mul x z)). Qed.
Lemma lem1984005 (x : real) (z : real) : (term310 x z) = (term311 x z).
Proof. exact (MK_COMB (@lem1984003) (@lem1984004 x z)). Qed.
Lemma lem1984010 (x : real) (z : real) : (term309 x z) = (term311 x z).
Proof. exact (TRANS (@lem1983993 x z) (@lem1984005 x z)). Qed.
Lemma lem1984011 (x : real) (z : real) : (term311 x z) = (real_mul x z).
Proof. exact (@lem1483436 (real_mul x z)). Qed.
Lemma lem1984012 (x : real) (z : real) : (term309 x z) = (real_mul x z).
Proof. exact (TRANS (@lem1984010 x z) (@lem1984011 x z)). Qed.
Lemma lem1984017 (x : real) (y : real) : (term312 x y) = (term281 x y).
Proof. exact (@lem1483472 term189 x y). Qed.
Lemma lem1984018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984019 (x : real) (y : real) : (term313 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1984018) (@lem1984017 x y)). Qed.
Lemma lem1984020 (y : real) (x : real) (z : real) : (term308 y x z) = (term283 y x z).
Proof. exact (MK_COMB (@lem1984019 x y) (@lem1984012 x z)). Qed.
Lemma lem1984021 (y : real) (x : real) (z : real) : (term307 x y z) = (term283 y x z).
Proof. exact (TRANS (@lem1983992 y x z) (@lem1984020 y x z)). Qed.
Lemma lem1984022 (w : real) (y : real) (x : real) (z : real) : (term301 w x y z) = (term314 w y x z).
Proof. exact (MK_COMB (@lem1983991 y w z) (@lem1984021 y x z)). Qed.
Lemma lem1984023 (w : real) (y : real) (x : real) (z : real) : (term300 w x y z) = (term314 w y x z).
Proof. exact (TRANS (@lem1983978 w x y z) (@lem1984022 w y x z)). Qed.
Lemma lem1984028 (w : real) (y : real) (x : real) (z : real) : (term314 w y x z) = (term287 w y x z).
Proof. exact (@lem1483482 (real_mul w y) (term281 w z) (term283 y x z)). Qed.
Lemma lem1984029 (w : real) (y : real) (x : real) (z : real) : (term300 w x y z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984023 w y x z) (@lem1984028 w y x z)). Qed.
Lemma lem1984030 (w : real) (y : real) (x : real) (z : real) : (term75 w x y z) = (term287 w y x z).
Proof. exact (TRANS (@lem1983977 w x y z) (@lem1984029 w y x z)). Qed.
Lemma lem1984031 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1984032 (w : real) (y : real) (x : real) (z : real) : (term315 w x y z) = (term289 w y x z).
Proof. exact (MK_COMB (@lem1984031) (@lem1984030 w y x z)). Qed.
Lemma lem1984033 (w : real) (y : real) (x : real) (z : real) : (term316 w x y z) = (term290 w y x z).
Proof. exact (MK_COMB (@lem1984032 w y x z) (@lem1983948)). Qed.
Lemma lem1984034 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term291 w y x z).
Proof. exact (@lem1483519 (term287 w y x z) term0). Qed.
Lemma lem1984036 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1984037 : term165 = term0.
Proof. exact (@lem1984036 term166). Qed.
Lemma lem1984038 (w : real) (y : real) (x : real) (z : real) : (term292 w y x z) = (term292 w y x z).
Proof. exact (eq_refl (term292 w y x z)). Qed.
Lemma lem1984039 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term293 w y x z).
Proof. exact (MK_COMB (@lem1984038 w y x z) (@lem1984037)). Qed.
Lemma lem1984040 (w : real) (y : real) (x : real) (z : real) : (term293 w y x z) = (term287 w y x z).
Proof. exact (@lem1483450 (term287 w y x z)). Qed.
Lemma lem1984041 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984039 w y x z) (@lem1984040 w y x z)). Qed.
Lemma lem1984042 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984034 w y x z) (@lem1984041 w y x z)). Qed.
Lemma lem1984043 (w : real) (y : real) (x : real) (z : real) : (term316 w x y z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984033 w y x z) (@lem1984042 w y x z)). Qed.
Lemma lem1984044 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1984045 (w : real) (y : real) (x : real) (z : real) : (term317 w x y z) = (term318 w y x z).
Proof. exact (MK_COMB (@lem1984044) (@lem1984043 w y x z)). Qed.
Lemma lem1984046 (w : real) (y : real) (x : real) (z : real) : (term318 w y x z) = (term319 w y x z).
Proof. exact (@lem1483512 (term287 w y x z)). Qed.
Lemma lem1984047 (w : real) (y : real) (x : real) (z : real) : (term319 w y x z) = (term320 w y x z).
Proof. exact (@lem1483508 (real_mul w y) term189 (term285 w y x z)). Qed.
Lemma lem1984048 (w : real) (y : real) (x : real) (z : real) : (term321 w y x z) = (term322 w y x z).
Proof. exact (@lem1483508 (term281 w z) term189 (term283 y x z)). Qed.
Lemma lem1984049 (y : real) (x : real) (z : real) : (term323 y x z) = (term324 y x z).
Proof. exact (@lem1483508 (term281 x y) term189 (real_mul x z)). Qed.
Lemma lem1984050 (x : real) (z : real) : (term281 x z) = (term281 x z).
Proof. exact (eq_refl (term281 x z)). Qed.
Lemma lem1984051 (x : real) (y : real) : (term325 x y) = (term310 x y).
Proof. exact (@lem1483476 term189 term189 (real_mul x y)). Qed.
Lemma lem1984053 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1984054 : term223 = term224.
Proof. exact (@lem1984053 term166 term166). Qed.
Lemma lem1984055 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1984056 : term226 = term166.
Proof. exact (EQ_MP (@lem1984055) (@lem940073)). Qed.
Lemma lem1984057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1984058 : term224 = term227.
Proof. exact (MK_COMB (@lem1984057) (@lem1984056)). Qed.
Lemma lem1984059 : term223 = term227.
Proof. exact (TRANS (@lem1984054) (@lem1984058)). Qed.
Lemma lem1984060 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984061 : term228 = term229.
Proof. exact (MK_COMB (@lem1984060) (@lem1984059)). Qed.
Lemma lem1984062 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1984063 (x : real) (y : real) : (term310 x y) = (term311 x y).
Proof. exact (MK_COMB (@lem1984061) (@lem1984062 x y)). Qed.
Lemma lem1984064 (x : real) (y : real) : (term325 x y) = (term311 x y).
Proof. exact (TRANS (@lem1984051 x y) (@lem1984063 x y)). Qed.
Lemma lem1984065 (x : real) (y : real) : (term311 x y) = (real_mul x y).
Proof. exact (@lem1483436 (real_mul x y)). Qed.
Lemma lem1984066 (x : real) (y : real) : (term325 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1984064 x y) (@lem1984065 x y)). Qed.
Lemma lem1984067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984068 (x : real) (y : real) : (term326 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1984067) (@lem1984066 x y)). Qed.
Lemma lem1984069 (y : real) (x : real) (z : real) : (term324 y x z) = (term282 y x z).
Proof. exact (MK_COMB (@lem1984068 x y) (@lem1984050 x z)). Qed.
Lemma lem1984070 (y : real) (x : real) (z : real) : (term323 y x z) = (term282 y x z).
Proof. exact (TRANS (@lem1984049 y x z) (@lem1984069 y x z)). Qed.
Lemma lem1984071 (w : real) (z : real) : (term325 w z) = (term310 w z).
Proof. exact (@lem1483476 term189 term189 (real_mul w z)). Qed.
Lemma lem1984073 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1984074 : term223 = term224.
Proof. exact (@lem1984073 term166 term166). Qed.
Lemma lem1984075 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1984076 : term226 = term166.
Proof. exact (EQ_MP (@lem1984075) (@lem940073)). Qed.
Lemma lem1984077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1984078 : term224 = term227.
Proof. exact (MK_COMB (@lem1984077) (@lem1984076)). Qed.
Lemma lem1984079 : term223 = term227.
Proof. exact (TRANS (@lem1984074) (@lem1984078)). Qed.
Lemma lem1984080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984081 : term228 = term229.
Proof. exact (MK_COMB (@lem1984080) (@lem1984079)). Qed.
Lemma lem1984082 (w : real) (z : real) : (real_mul w z) = (real_mul w z).
Proof. exact (eq_refl (real_mul w z)). Qed.
Lemma lem1984083 (w : real) (z : real) : (term310 w z) = (term311 w z).
Proof. exact (MK_COMB (@lem1984081) (@lem1984082 w z)). Qed.
Lemma lem1984084 (w : real) (z : real) : (term325 w z) = (term311 w z).
Proof. exact (TRANS (@lem1984071 w z) (@lem1984083 w z)). Qed.
Lemma lem1984085 (w : real) (z : real) : (term311 w z) = (real_mul w z).
Proof. exact (@lem1483436 (real_mul w z)). Qed.
Lemma lem1984086 (w : real) (z : real) : (term325 w z) = (real_mul w z).
Proof. exact (TRANS (@lem1984084 w z) (@lem1984085 w z)). Qed.
Lemma lem1984087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984088 (w : real) (z : real) : (term326 w z) = (term286 w z).
Proof. exact (MK_COMB (@lem1984087) (@lem1984086 w z)). Qed.
Lemma lem1984089 (w : real) (y : real) (x : real) (z : real) : (term322 w y x z) = (term327 w y x z).
Proof. exact (MK_COMB (@lem1984088 w z) (@lem1984070 y x z)). Qed.
Lemma lem1984090 (w : real) (y : real) (x : real) (z : real) : (term321 w y x z) = (term327 w y x z).
Proof. exact (TRANS (@lem1984048 w y x z) (@lem1984089 w y x z)). Qed.
Lemma lem1984093 (w : real) (y : real) : (term284 w y) = (term284 w y).
Proof. exact (eq_refl (term284 w y)). Qed.
Lemma lem1984094 (w : real) (y : real) (x : real) (z : real) : (term320 w y x z) = (term328 w y x z).
Proof. exact (MK_COMB (@lem1984093 w y) (@lem1984090 w y x z)). Qed.
Lemma lem1984095 (w : real) (y : real) (x : real) (z : real) : (term319 w y x z) = (term328 w y x z).
Proof. exact (TRANS (@lem1984047 w y x z) (@lem1984094 w y x z)). Qed.
Lemma lem1984096 (w : real) (y : real) (x : real) (z : real) : (term318 w y x z) = (term328 w y x z).
Proof. exact (TRANS (@lem1984046 w y x z) (@lem1984095 w y x z)). Qed.
Lemma lem1984097 (w : real) (x : real) (y : real) (z : real) : (term329 w x y z) = (term329 w x y z).
Proof. exact (eq_refl (term329 w x y z)). Qed.
Lemma lem1984098 (w : real) (y : real) (x : real) (z : real) : ((term317 w x y z) = (term318 w y x z)) = ((term317 w x y z) = (term328 w y x z)).
Proof. exact (MK_COMB (@lem1984097 w x y z) (@lem1984096 w y x z)). Qed.
Lemma lem1984099 (w : real) (y : real) (x : real) (z : real) : (term317 w x y z) = (term328 w y x z).
Proof. exact (EQ_MP (@lem1984098 w y x z) (@lem1984045 w y x z)). Qed.
Lemma lem1984100 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1984101 (w : real) (y : real) (x : real) (z : real) : (term330 w x y z) = (term331 w y x z).
Proof. exact (MK_COMB (@lem1984100) (@lem1984099 w y x z)). Qed.
Lemma lem1984102 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984103 (w : real) (y : real) (x : real) (z : real) : (term332 w x y z) = (term333 w y x z).
Proof. exact (MK_COMB (@lem1984101 w y x z) (@lem1984102)). Qed.
Lemma lem1984104 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1984105 (w : real) (y : real) (x : real) (z : real) : (term334 w x y z) = (term335 w y x z).
Proof. exact (MK_COMB (@lem1984104) (@lem1984043 w y x z)). Qed.
Lemma lem1984106 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984107 (w : real) (y : real) (x : real) (z : real) : (term336 w x y z) = (term337 w y x z).
Proof. exact (MK_COMB (@lem1984105 w y x z) (@lem1984106)). Qed.
Lemma lem1984108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984109 (w : real) (y : real) (x : real) (z : real) : (term338 w x y z) = (term339 w y x z).
Proof. exact (MK_COMB (@lem1984108) (@lem1984107 w y x z)). Qed.
Lemma lem1984110 (w : real) (y : real) (x : real) (z : real) : (term297 w x y z) = (term340 w y x z).
Proof. exact (MK_COMB (@lem1984109 w y x z) (@lem1984103 w y x z)). Qed.
Lemma lem1984111 (w : real) (y : real) (x : real) (z : real) : (term296 w x y z) = (term340 w y x z).
Proof. exact (TRANS (@lem1983947 w x y z) (@lem1984110 w y x z)). Qed.
Lemma lem1984112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1984113 (w : real) (y : real) (x : real) (z : real) : (term341 w z x y) = (term342 w y x z).
Proof. exact (MK_COMB (@lem1984112) (@lem1983946 w y x z)). Qed.
Lemma lem1984114 (w : real) (y : real) (x : real) (z : real) : (term343 w x y z) = (term344 w y x z).
Proof. exact (MK_COMB (@lem1984113 w y x z) (@lem1984111 w y x z)). Qed.
Lemma lem1984115 (w : real) (z : real) (x : real) (y : real) : (term345 w z x y) = (term346 w z x y).
Proof. exact (@lem1483554 (term48 w z x y) term0). Qed.
Lemma lem1984116 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984158 (w : real) (z : real) (x : real) (y : real) : (term48 w z x y) = (term273 w z x y).
Proof. exact (@lem1483519 (term47 w y x z) (term47 w z x y)). Qed.
Lemma lem1984165 (w : real) (z : real) (x : real) (y : real) : (term274 w z x y) = (term275 w z x y).
Proof. exact (@lem1483508 (real_mul w z) term189 (real_mul x y)). Qed.
Lemma lem1984166 (w : real) (y : real) (x : real) (z : real) : (term276 w y x z) = (term276 w y x z).
Proof. exact (eq_refl (term276 w y x z)). Qed.
Lemma lem1984167 (w : real) (z : real) (x : real) (y : real) : (term273 w z x y) = (term277 w z x y).
Proof. exact (MK_COMB (@lem1984166 w y x z) (@lem1984165 w z x y)). Qed.
Lemma lem1984168 (w : real) (z : real) (x : real) (y : real) : (term277 w z x y) = (term278 w z x y).
Proof. exact (@lem1483482 (real_mul w y) (real_mul x z) (term275 w z x y)). Qed.
Lemma lem1984169 (w : real) (z : real) (x : real) (y : real) : (term279 w z x y) = (term280 w z x y).
Proof. exact (@lem1483484 (term281 w z) (real_mul x z) (term281 x y)). Qed.
Lemma lem1984170 (y : real) (x : real) (z : real) : (term282 z x y) = (term283 y x z).
Proof. exact (@lem1483488 (term281 x y) (real_mul x z)). Qed.
Lemma lem1984171 (w : real) (z : real) : (term284 w z) = (term284 w z).
Proof. exact (eq_refl (term284 w z)). Qed.
Lemma lem1984172 (w : real) (y : real) (x : real) (z : real) : (term280 w z x y) = (term285 w y x z).
Proof. exact (MK_COMB (@lem1984171 w z) (@lem1984170 y x z)). Qed.
Lemma lem1984173 (w : real) (y : real) (x : real) (z : real) : (term279 w z x y) = (term285 w y x z).
Proof. exact (TRANS (@lem1984169 w z x y) (@lem1984172 w y x z)). Qed.
Lemma lem1984174 (w : real) (y : real) : (term286 w y) = (term286 w y).
Proof. exact (eq_refl (term286 w y)). Qed.
Lemma lem1984175 (w : real) (y : real) (x : real) (z : real) : (term278 w z x y) = (term287 w y x z).
Proof. exact (MK_COMB (@lem1984174 w y) (@lem1984173 w y x z)). Qed.
Lemma lem1984176 (w : real) (y : real) (x : real) (z : real) : (term277 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1984168 w z x y) (@lem1984175 w y x z)). Qed.
Lemma lem1984177 (w : real) (y : real) (x : real) (z : real) : (term273 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1984167 w z x y) (@lem1984176 w y x z)). Qed.
Lemma lem1984179 (w : real) (y : real) (x : real) (z : real) : (term48 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1984158 w z x y) (@lem1984177 w y x z)). Qed.
Lemma lem1984180 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1984181 (w : real) (y : real) (x : real) (z : real) : (term288 w z x y) = (term289 w y x z).
Proof. exact (MK_COMB (@lem1984180) (@lem1984179 w y x z)). Qed.
Lemma lem1984182 (w : real) (y : real) (x : real) (z : real) : (term272 w z x y) = (term290 w y x z).
Proof. exact (MK_COMB (@lem1984181 w y x z) (@lem1984116)). Qed.
Lemma lem1984183 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term291 w y x z).
Proof. exact (@lem1483519 (term287 w y x z) term0). Qed.
Lemma lem1984185 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1984186 : term165 = term0.
Proof. exact (@lem1984185 term166). Qed.
Lemma lem1984187 (w : real) (y : real) (x : real) (z : real) : (term292 w y x z) = (term292 w y x z).
Proof. exact (eq_refl (term292 w y x z)). Qed.
Lemma lem1984188 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term293 w y x z).
Proof. exact (MK_COMB (@lem1984187 w y x z) (@lem1984186)). Qed.
Lemma lem1984189 (w : real) (y : real) (x : real) (z : real) : (term293 w y x z) = (term287 w y x z).
Proof. exact (@lem1483450 (term287 w y x z)). Qed.
Lemma lem1984190 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984188 w y x z) (@lem1984189 w y x z)). Qed.
Lemma lem1984191 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984183 w y x z) (@lem1984190 w y x z)). Qed.
Lemma lem1984192 (w : real) (y : real) (x : real) (z : real) : (term272 w z x y) = (term287 w y x z).
Proof. exact (TRANS (@lem1984182 w y x z) (@lem1984191 w y x z)). Qed.
Lemma lem1984193 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1984194 (w : real) (y : real) (x : real) (z : real) : (term347 w z x y) = (term318 w y x z).
Proof. exact (MK_COMB (@lem1984193) (@lem1984192 w y x z)). Qed.
Lemma lem1984195 (w : real) (y : real) (x : real) (z : real) : (term318 w y x z) = (term319 w y x z).
Proof. exact (@lem1483512 (term287 w y x z)). Qed.
Lemma lem1984196 (w : real) (y : real) (x : real) (z : real) : (term319 w y x z) = (term320 w y x z).
Proof. exact (@lem1483508 (real_mul w y) term189 (term285 w y x z)). Qed.
Lemma lem1984197 (w : real) (y : real) (x : real) (z : real) : (term321 w y x z) = (term322 w y x z).
Proof. exact (@lem1483508 (term281 w z) term189 (term283 y x z)). Qed.
Lemma lem1984198 (y : real) (x : real) (z : real) : (term323 y x z) = (term324 y x z).
Proof. exact (@lem1483508 (term281 x y) term189 (real_mul x z)). Qed.
Lemma lem1984199 (x : real) (z : real) : (term281 x z) = (term281 x z).
Proof. exact (eq_refl (term281 x z)). Qed.
Lemma lem1984200 (x : real) (y : real) : (term325 x y) = (term310 x y).
Proof. exact (@lem1483476 term189 term189 (real_mul x y)). Qed.
Lemma lem1984202 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1984203 : term223 = term224.
Proof. exact (@lem1984202 term166 term166). Qed.
Lemma lem1984204 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1984205 : term226 = term166.
Proof. exact (EQ_MP (@lem1984204) (@lem940073)). Qed.
Lemma lem1984206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1984207 : term224 = term227.
Proof. exact (MK_COMB (@lem1984206) (@lem1984205)). Qed.
Lemma lem1984208 : term223 = term227.
Proof. exact (TRANS (@lem1984203) (@lem1984207)). Qed.
Lemma lem1984209 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984210 : term228 = term229.
Proof. exact (MK_COMB (@lem1984209) (@lem1984208)). Qed.
Lemma lem1984211 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (eq_refl (real_mul x y)). Qed.
Lemma lem1984212 (x : real) (y : real) : (term310 x y) = (term311 x y).
Proof. exact (MK_COMB (@lem1984210) (@lem1984211 x y)). Qed.
Lemma lem1984213 (x : real) (y : real) : (term325 x y) = (term311 x y).
Proof. exact (TRANS (@lem1984200 x y) (@lem1984212 x y)). Qed.
Lemma lem1984214 (x : real) (y : real) : (term311 x y) = (real_mul x y).
Proof. exact (@lem1483436 (real_mul x y)). Qed.
Lemma lem1984215 (x : real) (y : real) : (term325 x y) = (real_mul x y).
Proof. exact (TRANS (@lem1984213 x y) (@lem1984214 x y)). Qed.
Lemma lem1984216 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984217 (x : real) (y : real) : (term326 x y) = (term286 x y).
Proof. exact (MK_COMB (@lem1984216) (@lem1984215 x y)). Qed.
Lemma lem1984218 (y : real) (x : real) (z : real) : (term324 y x z) = (term282 y x z).
Proof. exact (MK_COMB (@lem1984217 x y) (@lem1984199 x z)). Qed.
Lemma lem1984219 (y : real) (x : real) (z : real) : (term323 y x z) = (term282 y x z).
Proof. exact (TRANS (@lem1984198 y x z) (@lem1984218 y x z)). Qed.
Lemma lem1984220 (w : real) (z : real) : (term325 w z) = (term310 w z).
Proof. exact (@lem1483476 term189 term189 (real_mul w z)). Qed.
Lemma lem1984222 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1984223 : term223 = term224.
Proof. exact (@lem1984222 term166 term166). Qed.
Lemma lem1984224 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1984225 : term226 = term166.
Proof. exact (EQ_MP (@lem1984224) (@lem940073)). Qed.
Lemma lem1984226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1984227 : term224 = term227.
Proof. exact (MK_COMB (@lem1984226) (@lem1984225)). Qed.
Lemma lem1984228 : term223 = term227.
Proof. exact (TRANS (@lem1984223) (@lem1984227)). Qed.
Lemma lem1984229 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984230 : term228 = term229.
Proof. exact (MK_COMB (@lem1984229) (@lem1984228)). Qed.
Lemma lem1984231 (w : real) (z : real) : (real_mul w z) = (real_mul w z).
Proof. exact (eq_refl (real_mul w z)). Qed.
Lemma lem1984232 (w : real) (z : real) : (term310 w z) = (term311 w z).
Proof. exact (MK_COMB (@lem1984230) (@lem1984231 w z)). Qed.
Lemma lem1984233 (w : real) (z : real) : (term325 w z) = (term311 w z).
Proof. exact (TRANS (@lem1984220 w z) (@lem1984232 w z)). Qed.
Lemma lem1984234 (w : real) (z : real) : (term311 w z) = (real_mul w z).
Proof. exact (@lem1483436 (real_mul w z)). Qed.
Lemma lem1984235 (w : real) (z : real) : (term325 w z) = (real_mul w z).
Proof. exact (TRANS (@lem1984233 w z) (@lem1984234 w z)). Qed.
Lemma lem1984236 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984237 (w : real) (z : real) : (term326 w z) = (term286 w z).
Proof. exact (MK_COMB (@lem1984236) (@lem1984235 w z)). Qed.
Lemma lem1984238 (w : real) (y : real) (x : real) (z : real) : (term322 w y x z) = (term327 w y x z).
Proof. exact (MK_COMB (@lem1984237 w z) (@lem1984219 y x z)). Qed.
Lemma lem1984239 (w : real) (y : real) (x : real) (z : real) : (term321 w y x z) = (term327 w y x z).
Proof. exact (TRANS (@lem1984197 w y x z) (@lem1984238 w y x z)). Qed.
Lemma lem1984242 (w : real) (y : real) : (term284 w y) = (term284 w y).
Proof. exact (eq_refl (term284 w y)). Qed.
Lemma lem1984243 (w : real) (y : real) (x : real) (z : real) : (term320 w y x z) = (term328 w y x z).
Proof. exact (MK_COMB (@lem1984242 w y) (@lem1984239 w y x z)). Qed.
Lemma lem1984244 (w : real) (y : real) (x : real) (z : real) : (term319 w y x z) = (term328 w y x z).
Proof. exact (TRANS (@lem1984196 w y x z) (@lem1984243 w y x z)). Qed.
Lemma lem1984245 (w : real) (y : real) (x : real) (z : real) : (term318 w y x z) = (term328 w y x z).
Proof. exact (TRANS (@lem1984195 w y x z) (@lem1984244 w y x z)). Qed.
Lemma lem1984246 (w : real) (z : real) (x : real) (y : real) : (term348 w z x y) = (term348 w z x y).
Proof. exact (eq_refl (term348 w z x y)). Qed.
Lemma lem1984247 (w : real) (y : real) (x : real) (z : real) : ((term347 w z x y) = (term318 w y x z)) = ((term347 w z x y) = (term328 w y x z)).
Proof. exact (MK_COMB (@lem1984246 w z x y) (@lem1984245 w y x z)). Qed.
Lemma lem1984248 (w : real) (y : real) (x : real) (z : real) : (term347 w z x y) = (term328 w y x z).
Proof. exact (EQ_MP (@lem1984247 w y x z) (@lem1984194 w y x z)). Qed.
Lemma lem1984249 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1984250 (w : real) (y : real) (x : real) (z : real) : (term349 w z x y) = (term331 w y x z).
Proof. exact (MK_COMB (@lem1984249) (@lem1984248 w y x z)). Qed.
Lemma lem1984251 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984252 (w : real) (y : real) (x : real) (z : real) : (term350 w z x y) = (term333 w y x z).
Proof. exact (MK_COMB (@lem1984250 w y x z) (@lem1984251)). Qed.
Lemma lem1984253 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1984254 (w : real) (y : real) (x : real) (z : real) : (term351 w z x y) = (term335 w y x z).
Proof. exact (MK_COMB (@lem1984253) (@lem1984192 w y x z)). Qed.
Lemma lem1984255 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984256 (w : real) (y : real) (x : real) (z : real) : (term352 w z x y) = (term337 w y x z).
Proof. exact (MK_COMB (@lem1984254 w y x z) (@lem1984255)). Qed.
Lemma lem1984257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984258 (w : real) (y : real) (x : real) (z : real) : (term353 w z x y) = (term339 w y x z).
Proof. exact (MK_COMB (@lem1984257) (@lem1984256 w y x z)). Qed.
Lemma lem1984259 (w : real) (y : real) (x : real) (z : real) : (term346 w z x y) = (term340 w y x z).
Proof. exact (MK_COMB (@lem1984258 w y x z) (@lem1984252 w y x z)). Qed.
Lemma lem1984260 (w : real) (y : real) (x : real) (z : real) : (term345 w z x y) = (term340 w y x z).
Proof. exact (TRANS (@lem1984115 w z x y) (@lem1984259 w y x z)). Qed.
Lemma lem1984261 (w : real) (x : real) (y : real) (z : real) : ((term75 w x y z) = term0) = ((term316 w x y z) = term0).
Proof. exact (@lem1483529 (term75 w x y z) term0). Qed.
Lemma lem1984262 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984275 (y : real) (z : real) : (real_sub y z) = (term201 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1984288 (w : real) (x : real) : (real_sub w x) = (term201 w x).
Proof. exact (@lem1483519 w x). Qed.
Lemma lem1984289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984290 (w : real) (x : real) : (term298 w x) = (term299 w x).
Proof. exact (MK_COMB (@lem1984289) (@lem1984288 w x)). Qed.
Lemma lem1984291 (w : real) (x : real) (y : real) (z : real) : (term75 w x y z) = (term300 w x y z).
Proof. exact (MK_COMB (@lem1984290 w x) (@lem1984275 y z)). Qed.
Lemma lem1984292 (w : real) (x : real) (y : real) (z : real) : (term300 w x y z) = (term301 w x y z).
Proof. exact (@lem1483454 w (term193 x) (term201 y z)). Qed.
Lemma lem1984293 (y : real) (w : real) (z : real) : (term302 w y z) = (term303 y w z).
Proof. exact (@lem1483508 y w (term193 z)). Qed.
Lemma lem1984298 (w : real) (z : real) : (term304 w z) = (term281 w z).
Proof. exact (@lem1483478 term189 w z). Qed.
Lemma lem1984301 (w : real) (y : real) : (term286 w y) = (term286 w y).
Proof. exact (eq_refl (term286 w y)). Qed.
Lemma lem1984302 (y : real) (w : real) (z : real) : (term303 y w z) = (term282 y w z).
Proof. exact (MK_COMB (@lem1984301 w y) (@lem1984298 w z)). Qed.
Lemma lem1984303 (y : real) (w : real) (z : real) : (term302 w y z) = (term282 y w z).
Proof. exact (TRANS (@lem1984293 y w z) (@lem1984302 y w z)). Qed.
Lemma lem1984304 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984305 (y : real) (w : real) (z : real) : (term305 w y z) = (term306 y w z).
Proof. exact (MK_COMB (@lem1984304) (@lem1984303 y w z)). Qed.
Lemma lem1984306 (y : real) (x : real) (z : real) : (term307 x y z) = (term308 y x z).
Proof. exact (@lem1483508 y (term193 x) (term193 z)). Qed.
Lemma lem1984307 (x : real) (z : real) : (term309 x z) = (term310 x z).
Proof. exact (@lem1483464 term189 term189 x z). Qed.
Lemma lem1984309 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1984310 : term223 = term224.
Proof. exact (@lem1984309 term166 term166). Qed.
Lemma lem1984311 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1984312 : term226 = term166.
Proof. exact (EQ_MP (@lem1984311) (@lem940073)). Qed.
Lemma lem1984313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1984314 : term224 = term227.
Proof. exact (MK_COMB (@lem1984313) (@lem1984312)). Qed.
Lemma lem1984315 : term223 = term227.
Proof. exact (TRANS (@lem1984310) (@lem1984314)). Qed.
Lemma lem1984316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1984317 : term228 = term229.
Proof. exact (MK_COMB (@lem1984316) (@lem1984315)). Qed.
Lemma lem1984318 (x : real) (z : real) : (real_mul x z) = (real_mul x z).
Proof. exact (eq_refl (real_mul x z)). Qed.
Lemma lem1984319 (x : real) (z : real) : (term310 x z) = (term311 x z).
Proof. exact (MK_COMB (@lem1984317) (@lem1984318 x z)). Qed.
Lemma lem1984324 (x : real) (z : real) : (term309 x z) = (term311 x z).
Proof. exact (TRANS (@lem1984307 x z) (@lem1984319 x z)). Qed.
Lemma lem1984325 (x : real) (z : real) : (term311 x z) = (real_mul x z).
Proof. exact (@lem1483436 (real_mul x z)). Qed.
Lemma lem1984326 (x : real) (z : real) : (term309 x z) = (real_mul x z).
Proof. exact (TRANS (@lem1984324 x z) (@lem1984325 x z)). Qed.
Lemma lem1984331 (x : real) (y : real) : (term312 x y) = (term281 x y).
Proof. exact (@lem1483472 term189 x y). Qed.
Lemma lem1984332 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1984333 (x : real) (y : real) : (term313 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1984332) (@lem1984331 x y)). Qed.
Lemma lem1984334 (y : real) (x : real) (z : real) : (term308 y x z) = (term283 y x z).
Proof. exact (MK_COMB (@lem1984333 x y) (@lem1984326 x z)). Qed.
Lemma lem1984335 (y : real) (x : real) (z : real) : (term307 x y z) = (term283 y x z).
Proof. exact (TRANS (@lem1984306 y x z) (@lem1984334 y x z)). Qed.
Lemma lem1984336 (w : real) (y : real) (x : real) (z : real) : (term301 w x y z) = (term314 w y x z).
Proof. exact (MK_COMB (@lem1984305 y w z) (@lem1984335 y x z)). Qed.
Lemma lem1984337 (w : real) (y : real) (x : real) (z : real) : (term300 w x y z) = (term314 w y x z).
Proof. exact (TRANS (@lem1984292 w x y z) (@lem1984336 w y x z)). Qed.
Lemma lem1984342 (w : real) (y : real) (x : real) (z : real) : (term314 w y x z) = (term287 w y x z).
Proof. exact (@lem1483482 (real_mul w y) (term281 w z) (term283 y x z)). Qed.
Lemma lem1984343 (w : real) (y : real) (x : real) (z : real) : (term300 w x y z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984337 w y x z) (@lem1984342 w y x z)). Qed.
Lemma lem1984344 (w : real) (y : real) (x : real) (z : real) : (term75 w x y z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984291 w x y z) (@lem1984343 w y x z)). Qed.
Lemma lem1984345 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1984346 (w : real) (y : real) (x : real) (z : real) : (term315 w x y z) = (term289 w y x z).
Proof. exact (MK_COMB (@lem1984345) (@lem1984344 w y x z)). Qed.
Lemma lem1984347 (w : real) (y : real) (x : real) (z : real) : (term316 w x y z) = (term290 w y x z).
Proof. exact (MK_COMB (@lem1984346 w y x z) (@lem1984262)). Qed.
Lemma lem1984348 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term291 w y x z).
Proof. exact (@lem1483519 (term287 w y x z) term0). Qed.
Lemma lem1984350 (x : nat) : (term164 x) = term0.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1984351 : term165 = term0.
Proof. exact (@lem1984350 term166). Qed.
Lemma lem1984352 (w : real) (y : real) (x : real) (z : real) : (term292 w y x z) = (term292 w y x z).
Proof. exact (eq_refl (term292 w y x z)). Qed.
Lemma lem1984353 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term293 w y x z).
Proof. exact (MK_COMB (@lem1984352 w y x z) (@lem1984351)). Qed.
Lemma lem1984354 (w : real) (y : real) (x : real) (z : real) : (term293 w y x z) = (term287 w y x z).
Proof. exact (@lem1483450 (term287 w y x z)). Qed.
Lemma lem1984355 (w : real) (y : real) (x : real) (z : real) : (term291 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984353 w y x z) (@lem1984354 w y x z)). Qed.
Lemma lem1984356 (w : real) (y : real) (x : real) (z : real) : (term290 w y x z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984348 w y x z) (@lem1984355 w y x z)). Qed.
Lemma lem1984357 (w : real) (y : real) (x : real) (z : real) : (term316 w x y z) = (term287 w y x z).
Proof. exact (TRANS (@lem1984347 w y x z) (@lem1984356 w y x z)). Qed.
Lemma lem1984358 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1984359 (w : real) (y : real) (x : real) (z : real) : (term354 w x y z) = (term295 w y x z).
Proof. exact (MK_COMB (@lem1984358) (@lem1984357 w y x z)). Qed.
Lemma lem1984360 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1984361 (w : real) (y : real) (x : real) (z : real) : ((term316 w x y z) = term0) = ((term287 w y x z) = term0).
Proof. exact (MK_COMB (@lem1984359 w y x z) (@lem1984360)). Qed.
Lemma lem1984362 (w : real) (y : real) (x : real) (z : real) : ((term75 w x y z) = term0) = ((term287 w y x z) = term0).
Proof. exact (TRANS (@lem1984261 w x y z) (@lem1984361 w y x z)). Qed.
Lemma lem1984363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1984364 (w : real) (y : real) (x : real) (z : real) : (term355 w z x y) = (term356 w y x z).
Proof. exact (MK_COMB (@lem1984363) (@lem1984260 w y x z)). Qed.
Lemma lem1984365 (w : real) (y : real) (x : real) (z : real) : (term357 w x y z) = (term358 w y x z).
Proof. exact (MK_COMB (@lem1984364 w y x z) (@lem1984362 w y x z)). Qed.
Lemma lem1984366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984367 (w : real) (y : real) (x : real) (z : real) : (term359 w x y z) = (term360 w y x z).
Proof. exact (MK_COMB (@lem1984366) (@lem1984114 w y x z)). Qed.
Lemma lem1984368 (w : real) (y : real) (x : real) (z : real) : (term120 w x y z) = (term361 w y x z).
Proof. exact (MK_COMB (@lem1984367 w y x z) (@lem1984365 w y x z)). Qed.
Lemma lem1984369 (w : real) (y : real) (x : real) : (term126 w x y) = (term362 w y x).
Proof. exact (fun_ext (fun z : real => @lem1984368 w y x z)). Qed.
Lemma lem1984370 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984371 (w : real) (y : real) (x : real) : (term127 w x y) = (term363 w y x).
Proof. exact (MK_COMB (@lem1984370) (@lem1984369 w y x)). Qed.
Lemma lem1984372 (w : real) (x : real) : (term133 w x) = (term364 w x).
Proof. exact (fun_ext (fun y : real => @lem1984371 w y x)). Qed.
Lemma lem1984373 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984374 (w : real) (x : real) : (term134 w x) = (term365 w x).
Proof. exact (MK_COMB (@lem1984373) (@lem1984372 w x)). Qed.
Lemma lem1984375 (w : real) : (term140 w) = (term366 w).
Proof. exact (fun_ext (fun x : real => @lem1984374 w x)). Qed.
Lemma lem1984376 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984377 (w : real) : (term141 w) = (term367 w).
Proof. exact (MK_COMB (@lem1984376) (@lem1984375 w)). Qed.
Lemma lem1984378 : term147 = term368.
Proof. exact (fun_ext (fun w : real => @lem1984377 w)). Qed.
Lemma lem1984379 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984380 : term148 = term369.
Proof. exact (MK_COMB (@lem1984379) (@lem1984378)). Qed.
Lemma lem1984381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984382 : term150 = term370.
Proof. exact (MK_COMB (@lem1984381) (@lem1983863)). Qed.
Lemma lem1984383 : term152 = term371.
Proof. exact (MK_COMB (@lem1984382) (@lem1984380)). Qed.
Lemma lem1984384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984385 : term155 = term372.
Proof. exact (MK_COMB (@lem1984384) (@lem1983569)). Qed.
Lemma lem1984386 : term157 = term373.
Proof. exact (MK_COMB (@lem1984385) (@lem1984383)). Qed.
Lemma lem1984387 : term158 = term373.
Proof. exact (TRANS (@lem1983508) (@lem1984386)). Qed.
Lemma lem1984389 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1984390 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1984389 real P Q). Qed.
Lemma lem1984391 : term378 = term379.
Proof. exact (@lem1984390 term380 term380). Qed.
Lemma lem1984392 (x : real) : (term381 x) = term177.
Proof. exact (eq_refl (term381 x)). Qed.
Lemma lem1984393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984394 (x : real) : (term382 x) = term181.
Proof. exact (MK_COMB (@lem1984393) (@lem1984392 x)). Qed.
Lemma lem1984395 (x : real) : (term381 x) = term177.
Proof. exact (eq_refl (term381 x)). Qed.
Lemma lem1984396 (x : real) : (term383 x) = term182.
Proof. exact (MK_COMB (@lem1984394 x) (@lem1984395 x)). Qed.
Lemma lem1984397 : term384 = term183.
Proof. exact (fun_ext (fun x : real => @lem1984396 x)). Qed.
Lemma lem1984398 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984399 : term378 = term184.
Proof. exact (MK_COMB (@lem1984398) (@lem1984397)). Qed.
Lemma lem1984400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1984401 : term385 = term386.
Proof. exact (MK_COMB (@lem1984400) (@lem1984399)). Qed.
Lemma lem1984402 (x : real) : (term381 x) = term177.
Proof. exact (eq_refl (term381 x)). Qed.
Lemma lem1984403 : term387 = term380.
Proof. exact (fun_ext (fun x : real => @lem1984402 x)). Qed.
Lemma lem1984404 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984405 : term388 = term389.
Proof. exact (MK_COMB (@lem1984404) (@lem1984403)). Qed.
Lemma lem1984406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984407 : term390 = term391.
Proof. exact (MK_COMB (@lem1984406) (@lem1984405)). Qed.
Lemma lem1984408 (x : real) : (term381 x) = term177.
Proof. exact (eq_refl (term381 x)). Qed.
Lemma lem1984409 : term387 = term380.
Proof. exact (fun_ext (fun x : real => @lem1984408 x)). Qed.
Lemma lem1984410 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984411 : term388 = term389.
Proof. exact (MK_COMB (@lem1984410) (@lem1984409)). Qed.
Lemma lem1984412 : term379 = term392.
Proof. exact (MK_COMB (@lem1984407) (@lem1984411)). Qed.
Lemma lem1984413 : (term378 = term379) = (term184 = term392).
Proof. exact (MK_COMB (@lem1984401) (@lem1984412)). Qed.
Lemma lem1984414 : term184 = term392.
Proof. exact (EQ_MP (@lem1984413) (@lem1984391)). Qed.
Lemma lem1984416 {A : Type'} (t : Prop) : (term393 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1984417 (t : Prop) : (term394 t) = t.
Proof. exact (@lem1984416 real t). Qed.
Lemma lem1984418 : term389 = term177.
Proof. exact (@lem1984417 term177). Qed.
Lemma lem1984419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984420 : term391 = term181.
Proof. exact (MK_COMB (@lem1984419) (@lem1984418)). Qed.
Lemma lem1984422 {A : Type'} (t : Prop) : (term393 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1984423 (t : Prop) : (term394 t) = t.
Proof. exact (@lem1984422 real t). Qed.
Lemma lem1984424 : term389 = term177.
Proof. exact (@lem1984423 term177). Qed.
Lemma lem1984425 : term392 = term182.
Proof. exact (MK_COMB (@lem1984420) (@lem1984424)). Qed.
Lemma lem1984426 : term184 = term182.
Proof. exact (TRANS (@lem1984414) (@lem1984425)). Qed.
Lemma lem1984427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984428 : term372 = term395.
Proof. exact (MK_COMB (@lem1984427) (@lem1984426)). Qed.
Lemma lem1984430 {A : Type'} (t : Prop) : (term393 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1984431 (t : Prop) : (term394 t) = t.
Proof. exact (@lem1984430 real t). Qed.
Lemma lem1984432 : term271 = term269.
Proof. exact (@lem1984431 term269). Qed.
Lemma lem1984438 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1984439 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1984438 real P Q). Qed.
Lemma lem1984440 (y : real) : (term396 y) = (term397 y).
Proof. exact (@lem1984439 (term398 y) (term399 y)). Qed.
Lemma lem1984441 (y : real) (z : real) : (term400 y z) = (term248 y z).
Proof. exact (eq_refl (term400 y z)). Qed.
Lemma lem1984442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984443 (y : real) (z : real) : (term401 y z) = (term264 y z).
Proof. exact (MK_COMB (@lem1984442) (@lem1984441 y z)). Qed.
Lemma lem1984444 (y : real) (z : real) : (term402 y z) = (term262 y z).
Proof. exact (eq_refl (term402 y z)). Qed.
Lemma lem1984445 (y : real) (z : real) : (term403 y z) = (term265 y z).
Proof. exact (MK_COMB (@lem1984443 y z) (@lem1984444 y z)). Qed.
Lemma lem1984446 (y : real) : (term404 y) = (term266 y).
Proof. exact (fun_ext (fun z : real => @lem1984445 y z)). Qed.
Lemma lem1984447 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984448 (y : real) : (term396 y) = (term267 y).
Proof. exact (MK_COMB (@lem1984447) (@lem1984446 y)). Qed.
Lemma lem1984449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1984450 (y : real) : (term405 y) = (term406 y).
Proof. exact (MK_COMB (@lem1984449) (@lem1984448 y)). Qed.
Lemma lem1984451 (y : real) (z : real) : (term400 y z) = (term248 y z).
Proof. exact (eq_refl (term400 y z)). Qed.
Lemma lem1984452 (y : real) : (term407 y) = (term398 y).
Proof. exact (fun_ext (fun z : real => @lem1984451 y z)). Qed.
Lemma lem1984453 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984454 (y : real) : (term408 y) = (term409 y).
Proof. exact (MK_COMB (@lem1984453) (@lem1984452 y)). Qed.
Lemma lem1984455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984456 (y : real) : (term410 y) = (term411 y).
Proof. exact (MK_COMB (@lem1984455) (@lem1984454 y)). Qed.
Lemma lem1984457 (y : real) (z : real) : (term402 y z) = (term262 y z).
Proof. exact (eq_refl (term402 y z)). Qed.
Lemma lem1984458 (y : real) : (term412 y) = (term399 y).
Proof. exact (fun_ext (fun z : real => @lem1984457 y z)). Qed.
Lemma lem1984459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984460 (y : real) : (term413 y) = (term414 y).
Proof. exact (MK_COMB (@lem1984459) (@lem1984458 y)). Qed.
Lemma lem1984461 (y : real) : (term397 y) = (term415 y).
Proof. exact (MK_COMB (@lem1984456 y) (@lem1984460 y)). Qed.
Lemma lem1984462 (y : real) : ((term396 y) = (term397 y)) = ((term267 y) = (term415 y)).
Proof. exact (MK_COMB (@lem1984450 y) (@lem1984461 y)). Qed.
Lemma lem1984463 (y : real) : (term267 y) = (term415 y).
Proof. exact (EQ_MP (@lem1984462 y) (@lem1984440 y)). Qed.
Lemma lem1984560 : term268 = term416.
Proof. exact (fun_ext (fun y : real => @lem1984463 y)). Qed.
Lemma lem1984561 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984562 : term269 = term417.
Proof. exact (MK_COMB (@lem1984561) (@lem1984560)). Qed.
Lemma lem1984564 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1984565 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1984564 real P Q). Qed.
Lemma lem1984566 : term418 = term419.
Proof. exact (@lem1984565 term420 term421). Qed.
Lemma lem1984567 (y : real) : (term422 y) = (term409 y).
Proof. exact (eq_refl (term422 y)). Qed.
Lemma lem1984568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984569 (y : real) : (term423 y) = (term411 y).
Proof. exact (MK_COMB (@lem1984568) (@lem1984567 y)). Qed.
Lemma lem1984570 (y : real) : (term424 y) = (term414 y).
Proof. exact (eq_refl (term424 y)). Qed.
Lemma lem1984571 (y : real) : (term425 y) = (term415 y).
Proof. exact (MK_COMB (@lem1984569 y) (@lem1984570 y)). Qed.
Lemma lem1984572 : term426 = term416.
Proof. exact (fun_ext (fun y : real => @lem1984571 y)). Qed.
Lemma lem1984573 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984574 : term418 = term417.
Proof. exact (MK_COMB (@lem1984573) (@lem1984572)). Qed.
Lemma lem1984575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1984576 : term427 = term428.
Proof. exact (MK_COMB (@lem1984575) (@lem1984574)). Qed.
Lemma lem1984577 (y : real) : (term422 y) = (term409 y).
Proof. exact (eq_refl (term422 y)). Qed.
Lemma lem1984578 : term429 = term420.
Proof. exact (fun_ext (fun y : real => @lem1984577 y)). Qed.
Lemma lem1984579 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984580 : term430 = term431.
Proof. exact (MK_COMB (@lem1984579) (@lem1984578)). Qed.
Lemma lem1984581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984582 : term432 = term433.
Proof. exact (MK_COMB (@lem1984581) (@lem1984580)). Qed.
Lemma lem1984583 (y : real) : (term424 y) = (term414 y).
Proof. exact (eq_refl (term424 y)). Qed.
Lemma lem1984584 : term434 = term421.
Proof. exact (fun_ext (fun y : real => @lem1984583 y)). Qed.
Lemma lem1984585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984586 : term435 = term436.
Proof. exact (MK_COMB (@lem1984585) (@lem1984584)). Qed.
Lemma lem1984587 : term419 = term437.
Proof. exact (MK_COMB (@lem1984582) (@lem1984586)). Qed.
Lemma lem1984588 : (term418 = term419) = (term417 = term437).
Proof. exact (MK_COMB (@lem1984576) (@lem1984587)). Qed.
Lemma lem1984589 : term417 = term437.
Proof. exact (EQ_MP (@lem1984588) (@lem1984566)). Qed.
Lemma lem1984694 : term269 = term437.
Proof. exact (TRANS (@lem1984562) (@lem1984589)). Qed.
Lemma lem1984695 : term271 = term437.
Proof. exact (TRANS (@lem1984432) (@lem1984694)). Qed.
Lemma lem1984696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984697 : term370 = term438.
Proof. exact (MK_COMB (@lem1984696) (@lem1984695)). Qed.
Lemma lem1984711 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1984712 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1984711 real P Q). Qed.
Lemma lem1984713 (w : real) (y : real) (x : real) : (term439 w y x) = (term440 w y x).
Proof. exact (@lem1984712 (term441 w y x) (term442 w y x)). Qed.
Lemma lem1984714 (w : real) (y : real) (x : real) (z : real) : (term443 w y x z) = (term344 w y x z).
Proof. exact (eq_refl (term443 w y x z)). Qed.
Lemma lem1984715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984716 (w : real) (y : real) (x : real) (z : real) : (term444 w y x z) = (term360 w y x z).
Proof. exact (MK_COMB (@lem1984715) (@lem1984714 w y x z)). Qed.
Lemma lem1984717 (w : real) (y : real) (x : real) (z : real) : (term445 w y x z) = (term358 w y x z).
Proof. exact (eq_refl (term445 w y x z)). Qed.
Lemma lem1984718 (w : real) (y : real) (x : real) (z : real) : (term446 w y x z) = (term361 w y x z).
Proof. exact (MK_COMB (@lem1984716 w y x z) (@lem1984717 w y x z)). Qed.
Lemma lem1984719 (w : real) (y : real) (x : real) : (term447 w y x) = (term362 w y x).
Proof. exact (fun_ext (fun z : real => @lem1984718 w y x z)). Qed.
Lemma lem1984720 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984721 (w : real) (y : real) (x : real) : (term439 w y x) = (term363 w y x).
Proof. exact (MK_COMB (@lem1984720) (@lem1984719 w y x)). Qed.
Lemma lem1984722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1984723 (w : real) (y : real) (x : real) : (term448 w y x) = (term449 w y x).
Proof. exact (MK_COMB (@lem1984722) (@lem1984721 w y x)). Qed.
Lemma lem1984724 (w : real) (y : real) (x : real) (z : real) : (term443 w y x z) = (term344 w y x z).
Proof. exact (eq_refl (term443 w y x z)). Qed.
Lemma lem1984725 (w : real) (y : real) (x : real) : (term450 w y x) = (term441 w y x).
Proof. exact (fun_ext (fun z : real => @lem1984724 w y x z)). Qed.
Lemma lem1984726 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984727 (w : real) (y : real) (x : real) : (term451 w y x) = (term452 w y x).
Proof. exact (MK_COMB (@lem1984726) (@lem1984725 w y x)). Qed.
Lemma lem1984728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984729 (w : real) (y : real) (x : real) : (term453 w y x) = (term454 w y x).
Proof. exact (MK_COMB (@lem1984728) (@lem1984727 w y x)). Qed.
Lemma lem1984730 (w : real) (y : real) (x : real) (z : real) : (term445 w y x z) = (term358 w y x z).
Proof. exact (eq_refl (term445 w y x z)). Qed.
Lemma lem1984731 (w : real) (y : real) (x : real) : (term455 w y x) = (term442 w y x).
Proof. exact (fun_ext (fun z : real => @lem1984730 w y x z)). Qed.
Lemma lem1984732 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984733 (w : real) (y : real) (x : real) : (term456 w y x) = (term457 w y x).
Proof. exact (MK_COMB (@lem1984732) (@lem1984731 w y x)). Qed.
Lemma lem1984734 (w : real) (y : real) (x : real) : (term440 w y x) = (term458 w y x).
Proof. exact (MK_COMB (@lem1984729 w y x) (@lem1984733 w y x)). Qed.
Lemma lem1984735 (w : real) (y : real) (x : real) : ((term439 w y x) = (term440 w y x)) = ((term363 w y x) = (term458 w y x)).
Proof. exact (MK_COMB (@lem1984723 w y x) (@lem1984734 w y x)). Qed.
Lemma lem1984736 (w : real) (y : real) (x : real) : (term363 w y x) = (term458 w y x).
Proof. exact (EQ_MP (@lem1984735 w y x) (@lem1984713 w y x)). Qed.
Lemma lem1984833 (w : real) (x : real) : (term364 w x) = (term459 w x).
Proof. exact (fun_ext (fun y : real => @lem1984736 w y x)). Qed.
Lemma lem1984834 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984835 (w : real) (x : real) : (term365 w x) = (term460 w x).
Proof. exact (MK_COMB (@lem1984834) (@lem1984833 w x)). Qed.
Lemma lem1984837 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1984838 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1984837 real P Q). Qed.
Lemma lem1984839 (w : real) (x : real) : (term461 w x) = (term462 w x).
Proof. exact (@lem1984838 (term463 w x) (term464 w x)). Qed.
Lemma lem1984840 (w : real) (y : real) (x : real) : (term465 w x y) = (term452 w y x).
Proof. exact (eq_refl (term465 w x y)). Qed.
Lemma lem1984841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984842 (w : real) (y : real) (x : real) : (term466 w x y) = (term454 w y x).
Proof. exact (MK_COMB (@lem1984841) (@lem1984840 w y x)). Qed.
Lemma lem1984843 (w : real) (y : real) (x : real) : (term467 w x y) = (term457 w y x).
Proof. exact (eq_refl (term467 w x y)). Qed.
Lemma lem1984844 (w : real) (y : real) (x : real) : (term468 w x y) = (term458 w y x).
Proof. exact (MK_COMB (@lem1984842 w y x) (@lem1984843 w y x)). Qed.
Lemma lem1984845 (w : real) (x : real) : (term469 w x) = (term459 w x).
Proof. exact (fun_ext (fun y : real => @lem1984844 w y x)). Qed.
Lemma lem1984846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984847 (w : real) (x : real) : (term461 w x) = (term460 w x).
Proof. exact (MK_COMB (@lem1984846) (@lem1984845 w x)). Qed.
Lemma lem1984848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1984849 (w : real) (x : real) : (term470 w x) = (term471 w x).
Proof. exact (MK_COMB (@lem1984848) (@lem1984847 w x)). Qed.
Lemma lem1984850 (w : real) (y : real) (x : real) : (term465 w x y) = (term452 w y x).
Proof. exact (eq_refl (term465 w x y)). Qed.
Lemma lem1984851 (w : real) (x : real) : (term472 w x) = (term463 w x).
Proof. exact (fun_ext (fun y : real => @lem1984850 w y x)). Qed.
Lemma lem1984852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984853 (w : real) (x : real) : (term473 w x) = (term474 w x).
Proof. exact (MK_COMB (@lem1984852) (@lem1984851 w x)). Qed.
Lemma lem1984854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984855 (w : real) (x : real) : (term475 w x) = (term476 w x).
Proof. exact (MK_COMB (@lem1984854) (@lem1984853 w x)). Qed.
Lemma lem1984856 (w : real) (y : real) (x : real) : (term467 w x y) = (term457 w y x).
Proof. exact (eq_refl (term467 w x y)). Qed.
Lemma lem1984857 (w : real) (x : real) : (term477 w x) = (term464 w x).
Proof. exact (fun_ext (fun y : real => @lem1984856 w y x)). Qed.
Lemma lem1984858 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984859 (w : real) (x : real) : (term478 w x) = (term479 w x).
Proof. exact (MK_COMB (@lem1984858) (@lem1984857 w x)). Qed.
Lemma lem1984860 (w : real) (x : real) : (term462 w x) = (term480 w x).
Proof. exact (MK_COMB (@lem1984855 w x) (@lem1984859 w x)). Qed.
Lemma lem1984861 (w : real) (x : real) : ((term461 w x) = (term462 w x)) = ((term460 w x) = (term480 w x)).
Proof. exact (MK_COMB (@lem1984849 w x) (@lem1984860 w x)). Qed.
Lemma lem1984862 (w : real) (x : real) : (term460 w x) = (term480 w x).
Proof. exact (EQ_MP (@lem1984861 w x) (@lem1984839 w x)). Qed.
Lemma lem1984967 (w : real) (x : real) : (term365 w x) = (term480 w x).
Proof. exact (TRANS (@lem1984835 w x) (@lem1984862 w x)). Qed.
Lemma lem1984968 (w : real) : (term366 w) = (term481 w).
Proof. exact (fun_ext (fun x : real => @lem1984967 w x)). Qed.
Lemma lem1984969 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984970 (w : real) : (term367 w) = (term482 w).
Proof. exact (MK_COMB (@lem1984969) (@lem1984968 w)). Qed.
Lemma lem1984972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1984973 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1984972 real P Q). Qed.
Lemma lem1984974 (w : real) : (term483 w) = (term484 w).
Proof. exact (@lem1984973 (term485 w) (term486 w)). Qed.
Lemma lem1984975 (w : real) (x : real) : (term487 w x) = (term474 w x).
Proof. exact (eq_refl (term487 w x)). Qed.
Lemma lem1984976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984977 (w : real) (x : real) : (term488 w x) = (term476 w x).
Proof. exact (MK_COMB (@lem1984976) (@lem1984975 w x)). Qed.
Lemma lem1984978 (w : real) (x : real) : (term489 w x) = (term479 w x).
Proof. exact (eq_refl (term489 w x)). Qed.
Lemma lem1984979 (w : real) (x : real) : (term490 w x) = (term480 w x).
Proof. exact (MK_COMB (@lem1984977 w x) (@lem1984978 w x)). Qed.
Lemma lem1984980 (w : real) : (term491 w) = (term481 w).
Proof. exact (fun_ext (fun x : real => @lem1984979 w x)). Qed.
Lemma lem1984981 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984982 (w : real) : (term483 w) = (term482 w).
Proof. exact (MK_COMB (@lem1984981) (@lem1984980 w)). Qed.
Lemma lem1984983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1984984 (w : real) : (term492 w) = (term493 w).
Proof. exact (MK_COMB (@lem1984983) (@lem1984982 w)). Qed.
Lemma lem1984985 (w : real) (x : real) : (term487 w x) = (term474 w x).
Proof. exact (eq_refl (term487 w x)). Qed.
Lemma lem1984986 (w : real) : (term494 w) = (term485 w).
Proof. exact (fun_ext (fun x : real => @lem1984985 w x)). Qed.
Lemma lem1984987 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984988 (w : real) : (term495 w) = (term496 w).
Proof. exact (MK_COMB (@lem1984987) (@lem1984986 w)). Qed.
Lemma lem1984989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1984990 (w : real) : (term497 w) = (term498 w).
Proof. exact (MK_COMB (@lem1984989) (@lem1984988 w)). Qed.
Lemma lem1984991 (w : real) (x : real) : (term489 w x) = (term479 w x).
Proof. exact (eq_refl (term489 w x)). Qed.
Lemma lem1984992 (w : real) : (term499 w) = (term486 w).
Proof. exact (fun_ext (fun x : real => @lem1984991 w x)). Qed.
Lemma lem1984993 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1984994 (w : real) : (term500 w) = (term501 w).
Proof. exact (MK_COMB (@lem1984993) (@lem1984992 w)). Qed.
Lemma lem1984995 (w : real) : (term484 w) = (term502 w).
Proof. exact (MK_COMB (@lem1984990 w) (@lem1984994 w)). Qed.
Lemma lem1984996 (w : real) : ((term483 w) = (term484 w)) = ((term482 w) = (term502 w)).
Proof. exact (MK_COMB (@lem1984984 w) (@lem1984995 w)). Qed.
Lemma lem1984997 (w : real) : (term482 w) = (term502 w).
Proof. exact (EQ_MP (@lem1984996 w) (@lem1984974 w)). Qed.
Lemma lem1985110 (w : real) : (term367 w) = (term502 w).
Proof. exact (TRANS (@lem1984970 w) (@lem1984997 w)). Qed.
Lemma lem1985111 : term368 = term503.
Proof. exact (fun_ext (fun w : real => @lem1985110 w)). Qed.
Lemma lem1985112 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985113 : term369 = term504.
Proof. exact (MK_COMB (@lem1985112) (@lem1985111)). Qed.
Lemma lem1985115 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term374 A P Q) = (term375 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1985116 (P : real -> Prop) (Q : real -> Prop) : (term376 P Q) = (term377 P Q).
Proof. exact (@lem1985115 real P Q). Qed.
Lemma lem1985117 : term505 = term506.
Proof. exact (@lem1985116 term507 term508). Qed.
Lemma lem1985118 (w : real) : (term509 w) = (term496 w).
Proof. exact (eq_refl (term509 w)). Qed.
Lemma lem1985119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985120 (w : real) : (term510 w) = (term498 w).
Proof. exact (MK_COMB (@lem1985119) (@lem1985118 w)). Qed.
Lemma lem1985121 (w : real) : (term511 w) = (term501 w).
Proof. exact (eq_refl (term511 w)). Qed.
Lemma lem1985122 (w : real) : (term512 w) = (term502 w).
Proof. exact (MK_COMB (@lem1985120 w) (@lem1985121 w)). Qed.
Lemma lem1985123 : term513 = term503.
Proof. exact (fun_ext (fun w : real => @lem1985122 w)). Qed.
Lemma lem1985124 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985125 : term505 = term504.
Proof. exact (MK_COMB (@lem1985124) (@lem1985123)). Qed.
Lemma lem1985126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985127 : term514 = term515.
Proof. exact (MK_COMB (@lem1985126) (@lem1985125)). Qed.
Lemma lem1985128 (w : real) : (term509 w) = (term496 w).
Proof. exact (eq_refl (term509 w)). Qed.
Lemma lem1985129 : term516 = term507.
Proof. exact (fun_ext (fun w : real => @lem1985128 w)). Qed.
Lemma lem1985130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985131 : term517 = term518.
Proof. exact (MK_COMB (@lem1985130) (@lem1985129)). Qed.
Lemma lem1985132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985133 : term519 = term520.
Proof. exact (MK_COMB (@lem1985132) (@lem1985131)). Qed.
Lemma lem1985134 (w : real) : (term511 w) = (term501 w).
Proof. exact (eq_refl (term511 w)). Qed.
Lemma lem1985135 : term521 = term508.
Proof. exact (fun_ext (fun w : real => @lem1985134 w)). Qed.
Lemma lem1985136 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985137 : term522 = term523.
Proof. exact (MK_COMB (@lem1985136) (@lem1985135)). Qed.
Lemma lem1985138 : term506 = term524.
Proof. exact (MK_COMB (@lem1985133) (@lem1985137)). Qed.
Lemma lem1985139 : (term505 = term506) = (term504 = term524).
Proof. exact (MK_COMB (@lem1985127) (@lem1985138)). Qed.
Lemma lem1985140 : term504 = term524.
Proof. exact (EQ_MP (@lem1985139) (@lem1985117)). Qed.
Lemma lem1985261 : term369 = term524.
Proof. exact (TRANS (@lem1985113) (@lem1985140)). Qed.
Lemma lem1985262 : term371 = term525.
Proof. exact (MK_COMB (@lem1984697) (@lem1985261)). Qed.
Lemma lem1985263 : term373 = term526.
Proof. exact (MK_COMB (@lem1984428) (@lem1985262)). Qed.
Lemma lem1985265 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985266 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985265 real P Q). Qed.
Lemma lem1985267 : term419 = term418.
Proof. exact (@lem1985266 term420 term421). Qed.
Lemma lem1985268 (y : real) : (term422 y) = (term409 y).
Proof. exact (eq_refl (term422 y)). Qed.
Lemma lem1985269 : term429 = term420.
Proof. exact (fun_ext (fun y : real => @lem1985268 y)). Qed.
Lemma lem1985270 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985271 : term430 = term431.
Proof. exact (MK_COMB (@lem1985270) (@lem1985269)). Qed.
Lemma lem1985272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985273 : term432 = term433.
Proof. exact (MK_COMB (@lem1985272) (@lem1985271)). Qed.
Lemma lem1985274 (y : real) : (term424 y) = (term414 y).
Proof. exact (eq_refl (term424 y)). Qed.
Lemma lem1985275 : term434 = term421.
Proof. exact (fun_ext (fun y : real => @lem1985274 y)). Qed.
Lemma lem1985276 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985277 : term435 = term436.
Proof. exact (MK_COMB (@lem1985276) (@lem1985275)). Qed.
Lemma lem1985278 : term419 = term437.
Proof. exact (MK_COMB (@lem1985273) (@lem1985277)). Qed.
Lemma lem1985279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985280 : term527 = term528.
Proof. exact (MK_COMB (@lem1985279) (@lem1985278)). Qed.
Lemma lem1985281 (y : real) : (term422 y) = (term409 y).
Proof. exact (eq_refl (term422 y)). Qed.
Lemma lem1985282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985283 (y : real) : (term423 y) = (term411 y).
Proof. exact (MK_COMB (@lem1985282) (@lem1985281 y)). Qed.
Lemma lem1985284 (y : real) : (term424 y) = (term414 y).
Proof. exact (eq_refl (term424 y)). Qed.
Lemma lem1985285 (y : real) : (term425 y) = (term415 y).
Proof. exact (MK_COMB (@lem1985283 y) (@lem1985284 y)). Qed.
Lemma lem1985286 : term426 = term416.
Proof. exact (fun_ext (fun y : real => @lem1985285 y)). Qed.
Lemma lem1985287 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985288 : term418 = term417.
Proof. exact (MK_COMB (@lem1985287) (@lem1985286)). Qed.
Lemma lem1985289 : (term419 = term418) = (term437 = term417).
Proof. exact (MK_COMB (@lem1985280) (@lem1985288)). Qed.
Lemma lem1985290 : term437 = term417.
Proof. exact (EQ_MP (@lem1985289) (@lem1985267)). Qed.
Lemma lem1985292 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985293 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985292 real P Q). Qed.
Lemma lem1985294 (y : real) : (term397 y) = (term396 y).
Proof. exact (@lem1985293 (term398 y) (term399 y)). Qed.
Lemma lem1985295 (y : real) (z : real) : (term400 y z) = (term248 y z).
Proof. exact (eq_refl (term400 y z)). Qed.
Lemma lem1985296 (y : real) : (term407 y) = (term398 y).
Proof. exact (fun_ext (fun z : real => @lem1985295 y z)). Qed.
Lemma lem1985297 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985298 (y : real) : (term408 y) = (term409 y).
Proof. exact (MK_COMB (@lem1985297) (@lem1985296 y)). Qed.
Lemma lem1985299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985300 (y : real) : (term410 y) = (term411 y).
Proof. exact (MK_COMB (@lem1985299) (@lem1985298 y)). Qed.
Lemma lem1985301 (y : real) (z : real) : (term402 y z) = (term262 y z).
Proof. exact (eq_refl (term402 y z)). Qed.
Lemma lem1985302 (y : real) : (term412 y) = (term399 y).
Proof. exact (fun_ext (fun z : real => @lem1985301 y z)). Qed.
Lemma lem1985303 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985304 (y : real) : (term413 y) = (term414 y).
Proof. exact (MK_COMB (@lem1985303) (@lem1985302 y)). Qed.
Lemma lem1985305 (y : real) : (term397 y) = (term415 y).
Proof. exact (MK_COMB (@lem1985300 y) (@lem1985304 y)). Qed.
Lemma lem1985306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985307 (y : real) : (term529 y) = (term530 y).
Proof. exact (MK_COMB (@lem1985306) (@lem1985305 y)). Qed.
Lemma lem1985308 (y : real) (z : real) : (term400 y z) = (term248 y z).
Proof. exact (eq_refl (term400 y z)). Qed.
Lemma lem1985309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985310 (y : real) (z : real) : (term401 y z) = (term264 y z).
Proof. exact (MK_COMB (@lem1985309) (@lem1985308 y z)). Qed.
Lemma lem1985311 (y : real) (z : real) : (term402 y z) = (term262 y z).
Proof. exact (eq_refl (term402 y z)). Qed.
Lemma lem1985312 (y : real) (z : real) : (term403 y z) = (term265 y z).
Proof. exact (MK_COMB (@lem1985310 y z) (@lem1985311 y z)). Qed.
Lemma lem1985313 (y : real) : (term404 y) = (term266 y).
Proof. exact (fun_ext (fun z : real => @lem1985312 y z)). Qed.
Lemma lem1985314 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985315 (y : real) : (term396 y) = (term267 y).
Proof. exact (MK_COMB (@lem1985314) (@lem1985313 y)). Qed.
Lemma lem1985316 (y : real) : ((term397 y) = (term396 y)) = ((term415 y) = (term267 y)).
Proof. exact (MK_COMB (@lem1985307 y) (@lem1985315 y)). Qed.
Lemma lem1985317 (y : real) : (term415 y) = (term267 y).
Proof. exact (EQ_MP (@lem1985316 y) (@lem1985294 y)). Qed.
Lemma lem1985318 : term416 = term268.
Proof. exact (fun_ext (fun y : real => @lem1985317 y)). Qed.
Lemma lem1985319 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985320 : term417 = term269.
Proof. exact (MK_COMB (@lem1985319) (@lem1985318)). Qed.
Lemma lem1985321 : term437 = term269.
Proof. exact (TRANS (@lem1985290) (@lem1985320)). Qed.
Lemma lem1985322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985323 : term438 = term531.
Proof. exact (MK_COMB (@lem1985322) (@lem1985321)). Qed.
Lemma lem1985325 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985326 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985325 real P Q). Qed.
Lemma lem1985327 : term506 = term505.
Proof. exact (@lem1985326 term507 term508). Qed.
Lemma lem1985328 (w : real) : (term509 w) = (term496 w).
Proof. exact (eq_refl (term509 w)). Qed.
Lemma lem1985329 : term516 = term507.
Proof. exact (fun_ext (fun w : real => @lem1985328 w)). Qed.
Lemma lem1985330 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985331 : term517 = term518.
Proof. exact (MK_COMB (@lem1985330) (@lem1985329)). Qed.
Lemma lem1985332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985333 : term519 = term520.
Proof. exact (MK_COMB (@lem1985332) (@lem1985331)). Qed.
Lemma lem1985334 (w : real) : (term511 w) = (term501 w).
Proof. exact (eq_refl (term511 w)). Qed.
Lemma lem1985335 : term521 = term508.
Proof. exact (fun_ext (fun w : real => @lem1985334 w)). Qed.
Lemma lem1985336 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985337 : term522 = term523.
Proof. exact (MK_COMB (@lem1985336) (@lem1985335)). Qed.
Lemma lem1985338 : term506 = term524.
Proof. exact (MK_COMB (@lem1985333) (@lem1985337)). Qed.
Lemma lem1985339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985340 : term532 = term533.
Proof. exact (MK_COMB (@lem1985339) (@lem1985338)). Qed.
Lemma lem1985341 (w : real) : (term509 w) = (term496 w).
Proof. exact (eq_refl (term509 w)). Qed.
Lemma lem1985342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985343 (w : real) : (term510 w) = (term498 w).
Proof. exact (MK_COMB (@lem1985342) (@lem1985341 w)). Qed.
Lemma lem1985344 (w : real) : (term511 w) = (term501 w).
Proof. exact (eq_refl (term511 w)). Qed.
Lemma lem1985345 (w : real) : (term512 w) = (term502 w).
Proof. exact (MK_COMB (@lem1985343 w) (@lem1985344 w)). Qed.
Lemma lem1985346 : term513 = term503.
Proof. exact (fun_ext (fun w : real => @lem1985345 w)). Qed.
Lemma lem1985347 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985348 : term505 = term504.
Proof. exact (MK_COMB (@lem1985347) (@lem1985346)). Qed.
Lemma lem1985349 : (term506 = term505) = (term524 = term504).
Proof. exact (MK_COMB (@lem1985340) (@lem1985348)). Qed.
Lemma lem1985350 : term524 = term504.
Proof. exact (EQ_MP (@lem1985349) (@lem1985327)). Qed.
Lemma lem1985352 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985353 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985352 real P Q). Qed.
Lemma lem1985354 (w : real) : (term484 w) = (term483 w).
Proof. exact (@lem1985353 (term485 w) (term486 w)). Qed.
Lemma lem1985355 (w : real) (x : real) : (term487 w x) = (term474 w x).
Proof. exact (eq_refl (term487 w x)). Qed.
Lemma lem1985356 (w : real) : (term494 w) = (term485 w).
Proof. exact (fun_ext (fun x : real => @lem1985355 w x)). Qed.
Lemma lem1985357 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985358 (w : real) : (term495 w) = (term496 w).
Proof. exact (MK_COMB (@lem1985357) (@lem1985356 w)). Qed.
Lemma lem1985359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985360 (w : real) : (term497 w) = (term498 w).
Proof. exact (MK_COMB (@lem1985359) (@lem1985358 w)). Qed.
Lemma lem1985361 (w : real) (x : real) : (term489 w x) = (term479 w x).
Proof. exact (eq_refl (term489 w x)). Qed.
Lemma lem1985362 (w : real) : (term499 w) = (term486 w).
Proof. exact (fun_ext (fun x : real => @lem1985361 w x)). Qed.
Lemma lem1985363 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985364 (w : real) : (term500 w) = (term501 w).
Proof. exact (MK_COMB (@lem1985363) (@lem1985362 w)). Qed.
Lemma lem1985365 (w : real) : (term484 w) = (term502 w).
Proof. exact (MK_COMB (@lem1985360 w) (@lem1985364 w)). Qed.
Lemma lem1985366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985367 (w : real) : (term534 w) = (term535 w).
Proof. exact (MK_COMB (@lem1985366) (@lem1985365 w)). Qed.
Lemma lem1985368 (w : real) (x : real) : (term487 w x) = (term474 w x).
Proof. exact (eq_refl (term487 w x)). Qed.
Lemma lem1985369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985370 (w : real) (x : real) : (term488 w x) = (term476 w x).
Proof. exact (MK_COMB (@lem1985369) (@lem1985368 w x)). Qed.
Lemma lem1985371 (w : real) (x : real) : (term489 w x) = (term479 w x).
Proof. exact (eq_refl (term489 w x)). Qed.
Lemma lem1985372 (w : real) (x : real) : (term490 w x) = (term480 w x).
Proof. exact (MK_COMB (@lem1985370 w x) (@lem1985371 w x)). Qed.
Lemma lem1985373 (w : real) : (term491 w) = (term481 w).
Proof. exact (fun_ext (fun x : real => @lem1985372 w x)). Qed.
Lemma lem1985374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985375 (w : real) : (term483 w) = (term482 w).
Proof. exact (MK_COMB (@lem1985374) (@lem1985373 w)). Qed.
Lemma lem1985376 (w : real) : ((term484 w) = (term483 w)) = ((term502 w) = (term482 w)).
Proof. exact (MK_COMB (@lem1985367 w) (@lem1985375 w)). Qed.
Lemma lem1985377 (w : real) : (term502 w) = (term482 w).
Proof. exact (EQ_MP (@lem1985376 w) (@lem1985354 w)). Qed.
Lemma lem1985379 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985380 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985379 real P Q). Qed.
Lemma lem1985381 (w : real) (x : real) : (term462 w x) = (term461 w x).
Proof. exact (@lem1985380 (term463 w x) (term464 w x)). Qed.
Lemma lem1985382 (w : real) (y : real) (x : real) : (term465 w x y) = (term452 w y x).
Proof. exact (eq_refl (term465 w x y)). Qed.
Lemma lem1985383 (w : real) (x : real) : (term472 w x) = (term463 w x).
Proof. exact (fun_ext (fun y : real => @lem1985382 w y x)). Qed.
Lemma lem1985384 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985385 (w : real) (x : real) : (term473 w x) = (term474 w x).
Proof. exact (MK_COMB (@lem1985384) (@lem1985383 w x)). Qed.
Lemma lem1985386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985387 (w : real) (x : real) : (term475 w x) = (term476 w x).
Proof. exact (MK_COMB (@lem1985386) (@lem1985385 w x)). Qed.
Lemma lem1985388 (w : real) (y : real) (x : real) : (term467 w x y) = (term457 w y x).
Proof. exact (eq_refl (term467 w x y)). Qed.
Lemma lem1985389 (w : real) (x : real) : (term477 w x) = (term464 w x).
Proof. exact (fun_ext (fun y : real => @lem1985388 w y x)). Qed.
Lemma lem1985390 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985391 (w : real) (x : real) : (term478 w x) = (term479 w x).
Proof. exact (MK_COMB (@lem1985390) (@lem1985389 w x)). Qed.
Lemma lem1985392 (w : real) (x : real) : (term462 w x) = (term480 w x).
Proof. exact (MK_COMB (@lem1985387 w x) (@lem1985391 w x)). Qed.
Lemma lem1985393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985394 (w : real) (x : real) : (term536 w x) = (term537 w x).
Proof. exact (MK_COMB (@lem1985393) (@lem1985392 w x)). Qed.
Lemma lem1985395 (w : real) (y : real) (x : real) : (term465 w x y) = (term452 w y x).
Proof. exact (eq_refl (term465 w x y)). Qed.
Lemma lem1985396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985397 (w : real) (y : real) (x : real) : (term466 w x y) = (term454 w y x).
Proof. exact (MK_COMB (@lem1985396) (@lem1985395 w y x)). Qed.
Lemma lem1985398 (w : real) (y : real) (x : real) : (term467 w x y) = (term457 w y x).
Proof. exact (eq_refl (term467 w x y)). Qed.
Lemma lem1985399 (w : real) (y : real) (x : real) : (term468 w x y) = (term458 w y x).
Proof. exact (MK_COMB (@lem1985397 w y x) (@lem1985398 w y x)). Qed.
Lemma lem1985400 (w : real) (x : real) : (term469 w x) = (term459 w x).
Proof. exact (fun_ext (fun y : real => @lem1985399 w y x)). Qed.
Lemma lem1985401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985402 (w : real) (x : real) : (term461 w x) = (term460 w x).
Proof. exact (MK_COMB (@lem1985401) (@lem1985400 w x)). Qed.
Lemma lem1985403 (w : real) (x : real) : ((term462 w x) = (term461 w x)) = ((term480 w x) = (term460 w x)).
Proof. exact (MK_COMB (@lem1985394 w x) (@lem1985402 w x)). Qed.
Lemma lem1985404 (w : real) (x : real) : (term480 w x) = (term460 w x).
Proof. exact (EQ_MP (@lem1985403 w x) (@lem1985381 w x)). Qed.
Lemma lem1985406 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985407 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985406 real P Q). Qed.
Lemma lem1985408 (w : real) (y : real) (x : real) : (term440 w y x) = (term439 w y x).
Proof. exact (@lem1985407 (term441 w y x) (term442 w y x)). Qed.
Lemma lem1985409 (w : real) (y : real) (x : real) (z : real) : (term443 w y x z) = (term344 w y x z).
Proof. exact (eq_refl (term443 w y x z)). Qed.
Lemma lem1985410 (w : real) (y : real) (x : real) : (term450 w y x) = (term441 w y x).
Proof. exact (fun_ext (fun z : real => @lem1985409 w y x z)). Qed.
Lemma lem1985411 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985412 (w : real) (y : real) (x : real) : (term451 w y x) = (term452 w y x).
Proof. exact (MK_COMB (@lem1985411) (@lem1985410 w y x)). Qed.
Lemma lem1985413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985414 (w : real) (y : real) (x : real) : (term453 w y x) = (term454 w y x).
Proof. exact (MK_COMB (@lem1985413) (@lem1985412 w y x)). Qed.
Lemma lem1985415 (w : real) (y : real) (x : real) (z : real) : (term445 w y x z) = (term358 w y x z).
Proof. exact (eq_refl (term445 w y x z)). Qed.
Lemma lem1985416 (w : real) (y : real) (x : real) : (term455 w y x) = (term442 w y x).
Proof. exact (fun_ext (fun z : real => @lem1985415 w y x z)). Qed.
Lemma lem1985417 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985418 (w : real) (y : real) (x : real) : (term456 w y x) = (term457 w y x).
Proof. exact (MK_COMB (@lem1985417) (@lem1985416 w y x)). Qed.
Lemma lem1985419 (w : real) (y : real) (x : real) : (term440 w y x) = (term458 w y x).
Proof. exact (MK_COMB (@lem1985414 w y x) (@lem1985418 w y x)). Qed.
Lemma lem1985420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985421 (w : real) (y : real) (x : real) : (term538 w y x) = (term539 w y x).
Proof. exact (MK_COMB (@lem1985420) (@lem1985419 w y x)). Qed.
Lemma lem1985422 (w : real) (y : real) (x : real) (z : real) : (term443 w y x z) = (term344 w y x z).
Proof. exact (eq_refl (term443 w y x z)). Qed.
Lemma lem1985423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985424 (w : real) (y : real) (x : real) (z : real) : (term444 w y x z) = (term360 w y x z).
Proof. exact (MK_COMB (@lem1985423) (@lem1985422 w y x z)). Qed.
Lemma lem1985425 (w : real) (y : real) (x : real) (z : real) : (term445 w y x z) = (term358 w y x z).
Proof. exact (eq_refl (term445 w y x z)). Qed.
Lemma lem1985426 (w : real) (y : real) (x : real) (z : real) : (term446 w y x z) = (term361 w y x z).
Proof. exact (MK_COMB (@lem1985424 w y x z) (@lem1985425 w y x z)). Qed.
Lemma lem1985427 (w : real) (y : real) (x : real) : (term447 w y x) = (term362 w y x).
Proof. exact (fun_ext (fun z : real => @lem1985426 w y x z)). Qed.
Lemma lem1985428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985429 (w : real) (y : real) (x : real) : (term439 w y x) = (term363 w y x).
Proof. exact (MK_COMB (@lem1985428) (@lem1985427 w y x)). Qed.
Lemma lem1985430 (w : real) (y : real) (x : real) : ((term440 w y x) = (term439 w y x)) = ((term458 w y x) = (term363 w y x)).
Proof. exact (MK_COMB (@lem1985421 w y x) (@lem1985429 w y x)). Qed.
Lemma lem1985431 (w : real) (y : real) (x : real) : (term458 w y x) = (term363 w y x).
Proof. exact (EQ_MP (@lem1985430 w y x) (@lem1985408 w y x)). Qed.
Lemma lem1985432 (w : real) (x : real) : (term459 w x) = (term364 w x).
Proof. exact (fun_ext (fun y : real => @lem1985431 w y x)). Qed.
Lemma lem1985433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985434 (w : real) (x : real) : (term460 w x) = (term365 w x).
Proof. exact (MK_COMB (@lem1985433) (@lem1985432 w x)). Qed.
Lemma lem1985435 (w : real) (x : real) : (term480 w x) = (term365 w x).
Proof. exact (TRANS (@lem1985404 w x) (@lem1985434 w x)). Qed.
Lemma lem1985436 (w : real) : (term481 w) = (term366 w).
Proof. exact (fun_ext (fun x : real => @lem1985435 w x)). Qed.
Lemma lem1985437 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985438 (w : real) : (term482 w) = (term367 w).
Proof. exact (MK_COMB (@lem1985437) (@lem1985436 w)). Qed.
Lemma lem1985439 (w : real) : (term502 w) = (term367 w).
Proof. exact (TRANS (@lem1985377 w) (@lem1985438 w)). Qed.
Lemma lem1985440 : term503 = term368.
Proof. exact (fun_ext (fun w : real => @lem1985439 w)). Qed.
Lemma lem1985441 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985442 : term504 = term369.
Proof. exact (MK_COMB (@lem1985441) (@lem1985440)). Qed.
Lemma lem1985443 : term524 = term369.
Proof. exact (TRANS (@lem1985350) (@lem1985442)). Qed.
Lemma lem1985444 : term525 = term540.
Proof. exact (MK_COMB (@lem1985323) (@lem1985443)). Qed.
Lemma lem1985446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985447 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985446 real P Q). Qed.
Lemma lem1985448 : term541 = term542.
Proof. exact (@lem1985447 term268 term368). Qed.
Lemma lem1985449 (y : real) : (term543 y) = (term267 y).
Proof. exact (eq_refl (term543 y)). Qed.
Lemma lem1985450 : term544 = term268.
Proof. exact (fun_ext (fun y : real => @lem1985449 y)). Qed.
Lemma lem1985451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985452 : term545 = term269.
Proof. exact (MK_COMB (@lem1985451) (@lem1985450)). Qed.
Lemma lem1985453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985454 : term546 = term531.
Proof. exact (MK_COMB (@lem1985453) (@lem1985452)). Qed.
Lemma lem1985455 (y : real) : (term547 y) = (term367 y).
Proof. exact (eq_refl (term547 y)). Qed.
Lemma lem1985456 : term548 = term368.
Proof. exact (fun_ext (fun y : real => @lem1985455 y)). Qed.
Lemma lem1985457 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985458 : term549 = term369.
Proof. exact (MK_COMB (@lem1985457) (@lem1985456)). Qed.
Lemma lem1985459 : term541 = term540.
Proof. exact (MK_COMB (@lem1985454) (@lem1985458)). Qed.
Lemma lem1985460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985461 : term550 = term551.
Proof. exact (MK_COMB (@lem1985460) (@lem1985459)). Qed.
Lemma lem1985462 (y : real) : (term543 y) = (term267 y).
Proof. exact (eq_refl (term543 y)). Qed.
Lemma lem1985463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985464 (y : real) : (term552 y) = (term553 y).
Proof. exact (MK_COMB (@lem1985463) (@lem1985462 y)). Qed.
Lemma lem1985465 (y : real) : (term547 y) = (term367 y).
Proof. exact (eq_refl (term547 y)). Qed.
Lemma lem1985466 (y : real) : (term554 y) = (term555 y).
Proof. exact (MK_COMB (@lem1985464 y) (@lem1985465 y)). Qed.
Lemma lem1985467 : term556 = term557.
Proof. exact (fun_ext (fun y : real => @lem1985466 y)). Qed.
Lemma lem1985468 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985469 : term542 = term558.
Proof. exact (MK_COMB (@lem1985468) (@lem1985467)). Qed.
Lemma lem1985470 : (term541 = term542) = (term540 = term558).
Proof. exact (MK_COMB (@lem1985461) (@lem1985469)). Qed.
Lemma lem1985471 : term540 = term558.
Proof. exact (EQ_MP (@lem1985470) (@lem1985448)). Qed.
Lemma lem1985474 : term559 = term559.
Proof. exact (eq_refl term559). Qed.
Lemma lem1985475 : term559 = (term540 = term558).
Proof. exact (eq_refl term559). Qed.
Lemma lem1985476 : term560 = term560.
Proof. exact (eq_refl term560). Qed.
Lemma lem1985477 : (term559 = term559) = (term559 = (term540 = term558)).
Proof. exact (MK_COMB (@lem1985476) (@lem1985475)). Qed.
Lemma lem1985478 : term559 = (term540 = term558).
Proof. exact (eq_refl term559). Qed.
Lemma lem1985479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985480 : term560 = term561.
Proof. exact (MK_COMB (@lem1985479) (@lem1985478)). Qed.
Lemma lem1985481 : (term540 = term558) = (term540 = term558).
Proof. exact (eq_refl (term540 = term558)). Qed.
Lemma lem1985482 : (term559 = (term540 = term558)) = ((term540 = term558) = (term540 = term558)).
Proof. exact (MK_COMB (@lem1985480) (@lem1985481)). Qed.
Lemma lem1985483 : (term559 = term559) = ((term540 = term558) = (term540 = term558)).
Proof. exact (TRANS (@lem1985477) (@lem1985482)). Qed.
Lemma lem1985484 : (term540 = term558) = (term540 = term558).
Proof. exact (EQ_MP (@lem1985483) (@lem1985474)). Qed.
Lemma lem1985485 : term540 = term558.
Proof. exact (EQ_MP (@lem1985484) (@lem1985471)). Qed.
Lemma lem1985487 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term375 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1985488 (P : real -> Prop) (Q : real -> Prop) : (term377 P Q) = (term376 P Q).
Proof. exact (@lem1985487 real P Q). Qed.
Lemma lem1985489 (y : real) : (term562 y) = (term563 y).
Proof. exact (@lem1985488 (term266 y) (term366 y)). Qed.
Lemma lem1985490 (y : real) (z : real) : (term564 y z) = (term265 y z).
Proof. exact (eq_refl (term564 y z)). Qed.
Lemma lem1985491 (y : real) : (term565 y) = (term266 y).
Proof. exact (fun_ext (fun z : real => @lem1985490 y z)). Qed.
Lemma lem1985492 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985493 (y : real) : (term566 y) = (term267 y).
Proof. exact (MK_COMB (@lem1985492) (@lem1985491 y)). Qed.
Lemma lem1985494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985495 (y : real) : (term567 y) = (term553 y).
Proof. exact (MK_COMB (@lem1985494) (@lem1985493 y)). Qed.
Lemma lem1985496 (y : real) (z : real) : (term568 y z) = (term365 y z).
Proof. exact (eq_refl (term568 y z)). Qed.
Lemma lem1985497 (y : real) : (term569 y) = (term366 y).
Proof. exact (fun_ext (fun z : real => @lem1985496 y z)). Qed.
Lemma lem1985498 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985499 (y : real) : (term570 y) = (term367 y).
Proof. exact (MK_COMB (@lem1985498) (@lem1985497 y)). Qed.
Lemma lem1985500 (y : real) : (term562 y) = (term555 y).
Proof. exact (MK_COMB (@lem1985495 y) (@lem1985499 y)). Qed.
Lemma lem1985501 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985502 (y : real) : (term571 y) = (term572 y).
Proof. exact (MK_COMB (@lem1985501) (@lem1985500 y)). Qed.
Lemma lem1985503 (y : real) (z : real) : (term564 y z) = (term265 y z).
Proof. exact (eq_refl (term564 y z)). Qed.
Lemma lem1985504 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985505 (y : real) (z : real) : (term573 y z) = (term574 y z).
Proof. exact (MK_COMB (@lem1985504) (@lem1985503 y z)). Qed.
Lemma lem1985506 (y : real) (z : real) : (term568 y z) = (term365 y z).
Proof. exact (eq_refl (term568 y z)). Qed.
Lemma lem1985507 (y : real) (z : real) : (term575 y z) = (term576 y z).
Proof. exact (MK_COMB (@lem1985505 y z) (@lem1985506 y z)). Qed.
Lemma lem1985508 (y : real) : (term577 y) = (term578 y).
Proof. exact (fun_ext (fun z : real => @lem1985507 y z)). Qed.
Lemma lem1985509 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985510 (y : real) : (term563 y) = (term579 y).
Proof. exact (MK_COMB (@lem1985509) (@lem1985508 y)). Qed.
Lemma lem1985511 (y : real) : ((term562 y) = (term563 y)) = ((term555 y) = (term579 y)).
Proof. exact (MK_COMB (@lem1985502 y) (@lem1985510 y)). Qed.
Lemma lem1985512 (y : real) : (term555 y) = (term579 y).
Proof. exact (EQ_MP (@lem1985511 y) (@lem1985489 y)). Qed.
Lemma lem1985515 (y : real) : (term580 y) = (term580 y).
Proof. exact (eq_refl (term580 y)). Qed.
Lemma lem1985516 (y : real) : (term580 y) = ((term555 y) = (term579 y)).
Proof. exact (eq_refl (term580 y)). Qed.
Lemma lem1985517 (y : real) : (term581 y) = (term581 y).
Proof. exact (eq_refl (term581 y)). Qed.
Lemma lem1985518 (y : real) : ((term580 y) = (term580 y)) = ((term580 y) = ((term555 y) = (term579 y))).
Proof. exact (MK_COMB (@lem1985517 y) (@lem1985516 y)). Qed.
Lemma lem1985519 (y : real) : (term580 y) = ((term555 y) = (term579 y)).
Proof. exact (eq_refl (term580 y)). Qed.
Lemma lem1985520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985521 (y : real) : (term581 y) = (term582 y).
Proof. exact (MK_COMB (@lem1985520) (@lem1985519 y)). Qed.
Lemma lem1985522 (y : real) : ((term555 y) = (term579 y)) = ((term555 y) = (term579 y)).
Proof. exact (eq_refl ((term555 y) = (term579 y))). Qed.
Lemma lem1985523 (y : real) : ((term580 y) = ((term555 y) = (term579 y))) = (((term555 y) = (term579 y)) = ((term555 y) = (term579 y))).
Proof. exact (MK_COMB (@lem1985521 y) (@lem1985522 y)). Qed.
Lemma lem1985524 (y : real) : ((term580 y) = (term580 y)) = (((term555 y) = (term579 y)) = ((term555 y) = (term579 y))).
Proof. exact (TRANS (@lem1985518 y) (@lem1985523 y)). Qed.
Lemma lem1985525 (y : real) : ((term555 y) = (term579 y)) = ((term555 y) = (term579 y)).
Proof. exact (EQ_MP (@lem1985524 y) (@lem1985515 y)). Qed.
Lemma lem1985526 (y : real) : (term555 y) = (term579 y).
Proof. exact (EQ_MP (@lem1985525 y) (@lem1985512 y)). Qed.
Lemma lem1985528 {A : Type'} (P : Prop) (Q : A -> Prop) : (term583 A P Q) = (term584 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1985529 (P : Prop) (Q : real -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem1985528 real P Q). Qed.
Lemma lem1985530 (y : real) (z : real) : (term587 y z) = (term588 y z).
Proof. exact (@lem1985529 (term265 y z) (term364 y z)). Qed.
Lemma lem1985531 (y : real) (y' : real) (z : real) : (term589 y z y') = (term363 y y' z).
Proof. exact (eq_refl (term589 y z y')). Qed.
Lemma lem1985532 (y : real) (z : real) : (term590 y z) = (term364 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985531 y y' z)). Qed.
Lemma lem1985533 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985534 (y : real) (z : real) : (term591 y z) = (term365 y z).
Proof. exact (MK_COMB (@lem1985533) (@lem1985532 y z)). Qed.
Lemma lem1985535 (y : real) (z : real) : (term574 y z) = (term574 y z).
Proof. exact (eq_refl (term574 y z)). Qed.
Lemma lem1985536 (y : real) (z : real) : (term587 y z) = (term576 y z).
Proof. exact (MK_COMB (@lem1985535 y z) (@lem1985534 y z)). Qed.
Lemma lem1985537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985538 (y : real) (z : real) : (term592 y z) = (term593 y z).
Proof. exact (MK_COMB (@lem1985537) (@lem1985536 y z)). Qed.
Lemma lem1985539 (y : real) (y' : real) (z : real) : (term589 y z y') = (term363 y y' z).
Proof. exact (eq_refl (term589 y z y')). Qed.
Lemma lem1985540 (y : real) (z : real) : (term574 y z) = (term574 y z).
Proof. exact (eq_refl (term574 y z)). Qed.
Lemma lem1985541 (y : real) (y' : real) (z : real) : (term594 y z y') = (term595 y y' z).
Proof. exact (MK_COMB (@lem1985540 y z) (@lem1985539 y y' z)). Qed.
Lemma lem1985542 (y : real) (z : real) : (term596 y z) = (term597 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985541 y y' z)). Qed.
Lemma lem1985543 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985544 (y : real) (z : real) : (term588 y z) = (term598 y z).
Proof. exact (MK_COMB (@lem1985543) (@lem1985542 y z)). Qed.
Lemma lem1985545 (y : real) (z : real) : ((term587 y z) = (term588 y z)) = ((term576 y z) = (term598 y z)).
Proof. exact (MK_COMB (@lem1985538 y z) (@lem1985544 y z)). Qed.
Lemma lem1985546 (y : real) (z : real) : (term576 y z) = (term598 y z).
Proof. exact (EQ_MP (@lem1985545 y z) (@lem1985530 y z)). Qed.
Lemma lem1985548 {A : Type'} (P : Prop) (Q : A -> Prop) : (term583 A P Q) = (term584 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1985549 (P : Prop) (Q : real -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem1985548 real P Q). Qed.
Lemma lem1985550 (y : real) (y' : real) (z : real) : (term599 y y' z) = (term600 y y' z).
Proof. exact (@lem1985549 (term265 y z) (term362 y y' z)). Qed.
Lemma lem1985551 (y : real) (y' : real) (z : real) (z' : real) : (term601 y y' z z') = (term361 y y' z z').
Proof. exact (eq_refl (term601 y y' z z')). Qed.
Lemma lem1985552 (y : real) (y' : real) (z : real) : (term602 y y' z) = (term362 y y' z).
Proof. exact (fun_ext (fun z' : real => @lem1985551 y y' z z')). Qed.
Lemma lem1985553 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985554 (y : real) (y' : real) (z : real) : (term603 y y' z) = (term363 y y' z).
Proof. exact (MK_COMB (@lem1985553) (@lem1985552 y y' z)). Qed.
Lemma lem1985555 (y : real) (z : real) : (term574 y z) = (term574 y z).
Proof. exact (eq_refl (term574 y z)). Qed.
Lemma lem1985556 (y : real) (y' : real) (z : real) : (term599 y y' z) = (term595 y y' z).
Proof. exact (MK_COMB (@lem1985555 y z) (@lem1985554 y y' z)). Qed.
Lemma lem1985557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985558 (y : real) (y' : real) (z : real) : (term604 y y' z) = (term605 y y' z).
Proof. exact (MK_COMB (@lem1985557) (@lem1985556 y y' z)). Qed.
Lemma lem1985559 (y : real) (y' : real) (z : real) (z' : real) : (term601 y y' z z') = (term361 y y' z z').
Proof. exact (eq_refl (term601 y y' z z')). Qed.
Lemma lem1985560 (y : real) (z : real) : (term574 y z) = (term574 y z).
Proof. exact (eq_refl (term574 y z)). Qed.
Lemma lem1985561 (y : real) (y' : real) (z : real) (z' : real) : (term606 y y' z z') = (term607 y y' z z').
Proof. exact (MK_COMB (@lem1985560 y z) (@lem1985559 y y' z z')). Qed.
Lemma lem1985562 (y : real) (y' : real) (z : real) : (term608 y y' z) = (term609 y y' z).
Proof. exact (fun_ext (fun z' : real => @lem1985561 y y' z z')). Qed.
Lemma lem1985563 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985564 (y : real) (y' : real) (z : real) : (term600 y y' z) = (term610 y y' z).
Proof. exact (MK_COMB (@lem1985563) (@lem1985562 y y' z)). Qed.
Lemma lem1985565 (y : real) (y' : real) (z : real) : ((term599 y y' z) = (term600 y y' z)) = ((term595 y y' z) = (term610 y y' z)).
Proof. exact (MK_COMB (@lem1985558 y y' z) (@lem1985564 y y' z)). Qed.
Lemma lem1985566 (y : real) (y' : real) (z : real) : (term595 y y' z) = (term610 y y' z).
Proof. exact (EQ_MP (@lem1985565 y y' z) (@lem1985550 y y' z)). Qed.
Lemma lem1985567 (y : real) (z : real) : (term597 y z) = (term611 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985566 y y' z)). Qed.
Lemma lem1985568 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985569 (y : real) (z : real) : (term598 y z) = (term612 y z).
Proof. exact (MK_COMB (@lem1985568) (@lem1985567 y z)). Qed.
Lemma lem1985570 (y : real) (z : real) : (term576 y z) = (term612 y z).
Proof. exact (TRANS (@lem1985546 y z) (@lem1985569 y z)). Qed.
Lemma lem1985571 (y : real) : (term578 y) = (term613 y).
Proof. exact (fun_ext (fun z : real => @lem1985570 y z)). Qed.
Lemma lem1985572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985573 (y : real) : (term579 y) = (term614 y).
Proof. exact (MK_COMB (@lem1985572) (@lem1985571 y)). Qed.
Lemma lem1985574 (y : real) : (term555 y) = (term614 y).
Proof. exact (TRANS (@lem1985526 y) (@lem1985573 y)). Qed.
Lemma lem1985575 : term557 = term615.
Proof. exact (fun_ext (fun y : real => @lem1985574 y)). Qed.
Lemma lem1985576 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985577 : term558 = term616.
Proof. exact (MK_COMB (@lem1985576) (@lem1985575)). Qed.
Lemma lem1985578 : term540 = term616.
Proof. exact (TRANS (@lem1985485) (@lem1985577)). Qed.
Lemma lem1985579 : term525 = term616.
Proof. exact (TRANS (@lem1985444) (@lem1985578)). Qed.
Lemma lem1985580 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985581 : term526 = term617.
Proof. exact (MK_COMB (@lem1985580) (@lem1985579)). Qed.
Lemma lem1985583 {A : Type'} (P : Prop) (Q : A -> Prop) : (term583 A P Q) = (term584 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1985584 (P : Prop) (Q : real -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem1985583 real P Q). Qed.
Lemma lem1985585 : term618 = term619.
Proof. exact (@lem1985584 term182 term615). Qed.
Lemma lem1985586 (y : real) : (term620 y) = (term614 y).
Proof. exact (eq_refl (term620 y)). Qed.
Lemma lem1985587 : term621 = term615.
Proof. exact (fun_ext (fun y : real => @lem1985586 y)). Qed.
Lemma lem1985588 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985589 : term622 = term616.
Proof. exact (MK_COMB (@lem1985588) (@lem1985587)). Qed.
Lemma lem1985590 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985591 : term618 = term617.
Proof. exact (MK_COMB (@lem1985590) (@lem1985589)). Qed.
Lemma lem1985592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985593 : term623 = term624.
Proof. exact (MK_COMB (@lem1985592) (@lem1985591)). Qed.
Lemma lem1985594 (y : real) : (term620 y) = (term614 y).
Proof. exact (eq_refl (term620 y)). Qed.
Lemma lem1985595 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985596 (y : real) : (term625 y) = (term626 y).
Proof. exact (MK_COMB (@lem1985595) (@lem1985594 y)). Qed.
Lemma lem1985597 : term627 = term628.
Proof. exact (fun_ext (fun y : real => @lem1985596 y)). Qed.
Lemma lem1985598 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985599 : term619 = term629.
Proof. exact (MK_COMB (@lem1985598) (@lem1985597)). Qed.
Lemma lem1985600 : (term618 = term619) = (term617 = term629).
Proof. exact (MK_COMB (@lem1985593) (@lem1985599)). Qed.
Lemma lem1985601 : term617 = term629.
Proof. exact (EQ_MP (@lem1985600) (@lem1985585)). Qed.
Lemma lem1985603 {A : Type'} (P : Prop) (Q : A -> Prop) : (term583 A P Q) = (term584 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1985604 (P : Prop) (Q : real -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem1985603 real P Q). Qed.
Lemma lem1985605 (y : real) : (term630 y) = (term631 y).
Proof. exact (@lem1985604 term182 (term613 y)). Qed.
Lemma lem1985606 (y : real) (z : real) : (term632 y z) = (term612 y z).
Proof. exact (eq_refl (term632 y z)). Qed.
Lemma lem1985607 (y : real) : (term633 y) = (term613 y).
Proof. exact (fun_ext (fun z : real => @lem1985606 y z)). Qed.
Lemma lem1985608 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985609 (y : real) : (term634 y) = (term614 y).
Proof. exact (MK_COMB (@lem1985608) (@lem1985607 y)). Qed.
Lemma lem1985610 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985611 (y : real) : (term630 y) = (term626 y).
Proof. exact (MK_COMB (@lem1985610) (@lem1985609 y)). Qed.
Lemma lem1985612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985613 (y : real) : (term635 y) = (term636 y).
Proof. exact (MK_COMB (@lem1985612) (@lem1985611 y)). Qed.
Lemma lem1985614 (y : real) (z : real) : (term632 y z) = (term612 y z).
Proof. exact (eq_refl (term632 y z)). Qed.
Lemma lem1985615 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985616 (y : real) (z : real) : (term637 y z) = (term638 y z).
Proof. exact (MK_COMB (@lem1985615) (@lem1985614 y z)). Qed.
Lemma lem1985617 (y : real) : (term639 y) = (term640 y).
Proof. exact (fun_ext (fun z : real => @lem1985616 y z)). Qed.
Lemma lem1985618 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985619 (y : real) : (term631 y) = (term641 y).
Proof. exact (MK_COMB (@lem1985618) (@lem1985617 y)). Qed.
Lemma lem1985620 (y : real) : ((term630 y) = (term631 y)) = ((term626 y) = (term641 y)).
Proof. exact (MK_COMB (@lem1985613 y) (@lem1985619 y)). Qed.
Lemma lem1985621 (y : real) : (term626 y) = (term641 y).
Proof. exact (EQ_MP (@lem1985620 y) (@lem1985605 y)). Qed.
Lemma lem1985623 {A : Type'} (P : Prop) (Q : A -> Prop) : (term583 A P Q) = (term584 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1985624 (P : Prop) (Q : real -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem1985623 real P Q). Qed.
Lemma lem1985625 (y : real) (z : real) : (term642 y z) = (term643 y z).
Proof. exact (@lem1985624 term182 (term611 y z)). Qed.
Lemma lem1985626 (y : real) (y' : real) (z : real) : (term644 y z y') = (term610 y y' z).
Proof. exact (eq_refl (term644 y z y')). Qed.
Lemma lem1985627 (y : real) (z : real) : (term645 y z) = (term611 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985626 y y' z)). Qed.
Lemma lem1985628 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985629 (y : real) (z : real) : (term646 y z) = (term612 y z).
Proof. exact (MK_COMB (@lem1985628) (@lem1985627 y z)). Qed.
Lemma lem1985630 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985631 (y : real) (z : real) : (term642 y z) = (term638 y z).
Proof. exact (MK_COMB (@lem1985630) (@lem1985629 y z)). Qed.
Lemma lem1985632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985633 (y : real) (z : real) : (term647 y z) = (term648 y z).
Proof. exact (MK_COMB (@lem1985632) (@lem1985631 y z)). Qed.
Lemma lem1985634 (y : real) (y' : real) (z : real) : (term644 y z y') = (term610 y y' z).
Proof. exact (eq_refl (term644 y z y')). Qed.
Lemma lem1985635 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985636 (y : real) (y' : real) (z : real) : (term649 y z y') = (term650 y y' z).
Proof. exact (MK_COMB (@lem1985635) (@lem1985634 y y' z)). Qed.
Lemma lem1985637 (y : real) (z : real) : (term651 y z) = (term652 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985636 y y' z)). Qed.
Lemma lem1985638 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985639 (y : real) (z : real) : (term643 y z) = (term653 y z).
Proof. exact (MK_COMB (@lem1985638) (@lem1985637 y z)). Qed.
Lemma lem1985640 (y : real) (z : real) : ((term642 y z) = (term643 y z)) = ((term638 y z) = (term653 y z)).
Proof. exact (MK_COMB (@lem1985633 y z) (@lem1985639 y z)). Qed.
Lemma lem1985641 (y : real) (z : real) : (term638 y z) = (term653 y z).
Proof. exact (EQ_MP (@lem1985640 y z) (@lem1985625 y z)). Qed.
Lemma lem1985643 {A : Type'} (P : Prop) (Q : A -> Prop) : (term583 A P Q) = (term584 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1985644 (P : Prop) (Q : real -> Prop) : (term585 P Q) = (term586 P Q).
Proof. exact (@lem1985643 real P Q). Qed.
Lemma lem1985645 (y : real) (y' : real) (z : real) : (term654 y y' z) = (term655 y y' z).
Proof. exact (@lem1985644 term182 (term609 y y' z)). Qed.
Lemma lem1985646 (y : real) (y' : real) (z : real) (z' : real) : (term656 y y' z z') = (term607 y y' z z').
Proof. exact (eq_refl (term656 y y' z z')). Qed.
Lemma lem1985647 (y : real) (y' : real) (z : real) : (term657 y y' z) = (term609 y y' z).
Proof. exact (fun_ext (fun z' : real => @lem1985646 y y' z z')). Qed.
Lemma lem1985648 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985649 (y : real) (y' : real) (z : real) : (term658 y y' z) = (term610 y y' z).
Proof. exact (MK_COMB (@lem1985648) (@lem1985647 y y' z)). Qed.
Lemma lem1985650 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985651 (y : real) (y' : real) (z : real) : (term654 y y' z) = (term650 y y' z).
Proof. exact (MK_COMB (@lem1985650) (@lem1985649 y y' z)). Qed.
Lemma lem1985652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1985653 (y : real) (y' : real) (z : real) : (term659 y y' z) = (term660 y y' z).
Proof. exact (MK_COMB (@lem1985652) (@lem1985651 y y' z)). Qed.
Lemma lem1985654 (y : real) (y' : real) (z : real) (z' : real) : (term656 y y' z z') = (term607 y y' z z').
Proof. exact (eq_refl (term656 y y' z z')). Qed.
Lemma lem1985655 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985656 (y : real) (y' : real) (z : real) (z' : real) : (term661 y y' z z') = (term662 y y' z z').
Proof. exact (MK_COMB (@lem1985655) (@lem1985654 y y' z z')). Qed.
Lemma lem1985657 (y : real) (y' : real) (z : real) : (term663 y y' z) = (term664 y y' z).
Proof. exact (fun_ext (fun z' : real => @lem1985656 y y' z z')). Qed.
Lemma lem1985658 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985659 (y : real) (y' : real) (z : real) : (term655 y y' z) = (term665 y y' z).
Proof. exact (MK_COMB (@lem1985658) (@lem1985657 y y' z)). Qed.
Lemma lem1985660 (y : real) (y' : real) (z : real) : ((term654 y y' z) = (term655 y y' z)) = ((term650 y y' z) = (term665 y y' z)).
Proof. exact (MK_COMB (@lem1985653 y y' z) (@lem1985659 y y' z)). Qed.
Lemma lem1985661 (y : real) (y' : real) (z : real) : (term650 y y' z) = (term665 y y' z).
Proof. exact (EQ_MP (@lem1985660 y y' z) (@lem1985645 y y' z)). Qed.
Lemma lem1985662 (y : real) (z : real) : (term652 y z) = (term666 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985661 y y' z)). Qed.
Lemma lem1985663 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985664 (y : real) (z : real) : (term653 y z) = (term667 y z).
Proof. exact (MK_COMB (@lem1985663) (@lem1985662 y z)). Qed.
Lemma lem1985665 (y : real) (z : real) : (term638 y z) = (term667 y z).
Proof. exact (TRANS (@lem1985641 y z) (@lem1985664 y z)). Qed.
Lemma lem1985666 (y : real) : (term640 y) = (term668 y).
Proof. exact (fun_ext (fun z : real => @lem1985665 y z)). Qed.
Lemma lem1985667 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985668 (y : real) : (term641 y) = (term669 y).
Proof. exact (MK_COMB (@lem1985667) (@lem1985666 y)). Qed.
Lemma lem1985669 (y : real) : (term626 y) = (term669 y).
Proof. exact (TRANS (@lem1985621 y) (@lem1985668 y)). Qed.
Lemma lem1985670 : term628 = term670.
Proof. exact (fun_ext (fun y : real => @lem1985669 y)). Qed.
Lemma lem1985671 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985672 : term629 = term671.
Proof. exact (MK_COMB (@lem1985671) (@lem1985670)). Qed.
Lemma lem1985673 : term617 = term671.
Proof. exact (TRANS (@lem1985601) (@lem1985672)). Qed.
Lemma lem1985674 : term526 = term671.
Proof. exact (TRANS (@lem1985581) (@lem1985673)). Qed.
Lemma lem1985675 : term373 = term671.
Proof. exact (TRANS (@lem1985263) (@lem1985674)). Qed.
Lemma lem1985678 : term158 = term671.
Proof. exact (TRANS (@lem1984387) (@lem1985675)). Qed.
Lemma lem1985695 (y : real) (y' : real) (z : real) (z' : real) : (term358 y y' z z') = (term672 y y' z z').
Proof. exact (@lem19367 (term337 y y' z z') (term333 y y' z z') ((term287 y y' z z') = term0)). Qed.
Lemma lem1985712 (y : real) (y' : real) (z : real) (z' : real) : (term344 y y' z z') = (term673 y y' z z').
Proof. exact (@lem19158 (term337 y y' z z') ((term287 y y' z z') = term0) (term333 y y' z z')). Qed.
Lemma lem1985713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985714 (y : real) (y' : real) (z : real) (z' : real) : (term360 y y' z z') = (term674 y y' z z').
Proof. exact (MK_COMB (@lem1985713) (@lem1985712 y y' z z')). Qed.
Lemma lem1985715 (y : real) (y' : real) (z : real) (z' : real) : (term361 y y' z z') = (term675 y y' z z').
Proof. exact (MK_COMB (@lem1985714 y y' z z') (@lem1985695 y y' z z')). Qed.
Lemma lem1985732 (y : real) (z : real) : (term262 y z) = (term676 y z).
Proof. exact (@lem19367 (term241 y z) (term237 y z) ((term201 y z) = term0)). Qed.
Lemma lem1985749 (y : real) (z : real) : (term248 y z) = (term677 y z).
Proof. exact (@lem19158 (term241 y z) ((term201 y z) = term0) (term237 y z)). Qed.
Lemma lem1985750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985751 (y : real) (z : real) : (term264 y z) = (term678 y z).
Proof. exact (MK_COMB (@lem1985750) (@lem1985749 y z)). Qed.
Lemma lem1985752 (y : real) (z : real) : (term265 y z) = (term679 y z).
Proof. exact (MK_COMB (@lem1985751 y z) (@lem1985732 y z)). Qed.
Lemma lem1985753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1985754 (y : real) (z : real) : (term574 y z) = (term680 y z).
Proof. exact (MK_COMB (@lem1985753) (@lem1985752 y z)). Qed.
Lemma lem1985755 (y : real) (y' : real) (z : real) (z' : real) : (term607 y y' z z') = (term681 y y' z z').
Proof. exact (MK_COMB (@lem1985754 y z) (@lem1985715 y y' z z')). Qed.
Lemma lem1985762 : term395 = term395.
Proof. exact (eq_refl term395). Qed.
Lemma lem1985763 (y : real) (y' : real) (z : real) (z' : real) : (term662 y y' z z') = (term682 y y' z z').
Proof. exact (MK_COMB (@lem1985762) (@lem1985755 y y' z z')). Qed.
Lemma lem1985764 (y : real) (y' : real) (z : real) : (term664 y y' z) = (term683 y y' z).
Proof. exact (fun_ext (fun z' : real => @lem1985763 y y' z z')). Qed.
Lemma lem1985765 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985766 (y : real) (y' : real) (z : real) : (term665 y y' z) = (term684 y y' z).
Proof. exact (MK_COMB (@lem1985765) (@lem1985764 y y' z)). Qed.
Lemma lem1985767 (y : real) (z : real) : (term666 y z) = (term685 y z).
Proof. exact (fun_ext (fun y' : real => @lem1985766 y y' z)). Qed.
Lemma lem1985768 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985769 (y : real) (z : real) : (term667 y z) = (term686 y z).
Proof. exact (MK_COMB (@lem1985768) (@lem1985767 y z)). Qed.
Lemma lem1985770 (y : real) : (term668 y) = (term687 y).
Proof. exact (fun_ext (fun z : real => @lem1985769 y z)). Qed.
Lemma lem1985771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985772 (y : real) : (term669 y) = (term688 y).
Proof. exact (MK_COMB (@lem1985771) (@lem1985770 y)). Qed.
Lemma lem1985773 : term670 = term689.
Proof. exact (fun_ext (fun y : real => @lem1985772 y)). Qed.
Lemma lem1985774 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1985775 : term671 = term690.
Proof. exact (MK_COMB (@lem1985774) (@lem1985773)). Qed.
Lemma lem1985776 : term158 = term690.
Proof. exact (TRANS (@lem1985678) (@lem1985775)). Qed.
Lemma lem1985834 (y : real) (y' : real) (z : real) (z' : real) (h1 : term682 y y' z z') : term682 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1985835 (h1 : term182) : term182.
Proof. exact (h1). Qed.
Lemma lem1985836 (h1 : term177) : term177.
Proof. exact (h1). Qed.
Lemma lem1985838 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1985839 : term177 = term692.
Proof. exact (@lem1985838 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1985840 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1985841 : term177 = False.
Proof. exact (TRANS (@lem1985839) (@lem1985840)). Qed.
Lemma lem1985842 (h1 : term177) : False.
Proof. exact (EQ_MP (@lem1985841) (@lem1985836 h1)). Qed.
Lemma lem1985843 (h1 : term177) : term177.
Proof. exact (h1). Qed.
Lemma lem1985845 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1985846 : term177 = term692.
Proof. exact (@lem1985845 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1985847 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1985848 : term177 = False.
Proof. exact (TRANS (@lem1985846) (@lem1985847)). Qed.
Lemma lem1985849 (h1 : term177) : False.
Proof. exact (EQ_MP (@lem1985848) (@lem1985843 h1)). Qed.
Lemma lem1985850 (h1 : term182) : False.
Proof. exact (or_elim (@lem1985835 h1) (fun h0 : term177 => @lem1985842 h0) (fun h0 : term177 => @lem1985849 h0)). Qed.
Lemma lem1985851 (y : real) (y' : real) (z : real) (z' : real) (h1 : term681 y y' z z') : term681 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1985852 (y : real) (z : real) (h1 : term679 y z) : term679 y z.
Proof. exact (h1). Qed.
Lemma lem1985853 (y : real) (z : real) (h1 : term677 y z) : term677 y z.
Proof. exact (h1). Qed.
Lemma lem1985854 (y : real) (z : real) (h1 : term693 y z) : term693 y z.
Proof. exact (h1). Qed.
Lemma lem1985855 (y : real) (z : real) (h1 : term693 y z) : term241 y z.
Proof. exact (proj2 (@lem1985854 y z h1)). Qed.
Lemma lem1985856 (y : real) (z : real) (h1 : term693 y z) : (term201 y z) = term0.
Proof. exact (proj1 (@lem1985854 y z h1)). Qed.
Lemma lem1985858 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1985859 : term694 = term695.
Proof. exact (@lem1985858 (NUMERAL 0) term166). Qed.
Lemma lem1985860 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1985861 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1985862 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1985861 h1) (fun h1 : term695 = True => @lem1985860)). Qed.
Lemma lem1985863 : term695 = True.
Proof. exact (EQ_MP (@lem1985862) (@lem1985860)). Qed.
Lemma lem1985864 : term694 = True.
Proof. exact (TRANS (@lem1985859) (@lem1985863)). Qed.
Lemma lem1985865 : True = term694.
Proof. exact (SYM (@lem1985864)). Qed.
Lemma lem1985866 : term694.
Proof. exact (EQ_MP (@lem1985865) (@lem0)). Qed.
Lemma lem1985867 (y : real) (z : real) (h1 : term693 y z) : term697 y z.
Proof. exact (conj (@lem1985866) (@lem1985855 y z h1)). Qed.
Lemma lem1985869 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1985870 (y : real) (z : real) : term699 y z.
Proof. exact (@lem1985869 term227 (term201 y z)). Qed.
Lemma lem1985871 (y : real) (z : real) (h1 : term693 y z) : term700 y z.
Proof. exact (@lem1985870 y z (@lem1985867 y z h1)). Qed.
Lemma lem1985872 (y : real) (z : real) : (term701 y z) = (term201 y z).
Proof. exact (@lem1483460 (term201 y z)). Qed.
Lemma lem1985873 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1985874 (y : real) (z : real) : (term702 y z) = (term239 y z).
Proof. exact (MK_COMB (@lem1985873) (@lem1985872 y z)). Qed.
Lemma lem1985875 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1985876 (y : real) (z : real) : (term700 y z) = (term241 y z).
Proof. exact (MK_COMB (@lem1985874 y z) (@lem1985875)). Qed.
Lemma lem1985877 (y : real) (z : real) (h1 : term693 y z) : term241 y z.
Proof. exact (EQ_MP (@lem1985876 y z) (@lem1985871 y z h1)). Qed.
Lemma lem1985879 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1985880 (y : real) (z : real) : term704 y z.
Proof. exact (@lem1985879 (term201 y z)). Qed.
Lemma lem1985881 (y : real) (z : real) (h1 : term693 y z) : term705 y z.
Proof. exact (@lem1985880 y z (@lem1985856 y z h1)). Qed.
Lemma lem1985882 (y : real) (z : real) (h1 : term693 y z) : term706 y z.
Proof. exact (@lem1985881 y z h1 term189). Qed.
Lemma lem1985883 (y : real) (z : real) : (term706 y z) = ((term217 y z) = term0).
Proof. exact (eq_refl (term706 y z)). Qed.
Lemma lem1985884 (y : real) (z : real) (h1 : term693 y z) : (term217 y z) = term0.
Proof. exact (EQ_MP (@lem1985883 y z) (@lem1985882 y z h1)). Qed.
Lemma lem1985885 (y : real) (z : real) : (term217 y z) = (term218 y z).
Proof. exact (@lem1483508 y term189 (term193 z)). Qed.
Lemma lem1985886 (z : real) : (term219 z) = (term220 z).
Proof. exact (@lem1483476 term189 term189 z). Qed.
Lemma lem1985888 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1985889 : term223 = term224.
Proof. exact (@lem1985888 term166 term166). Qed.
Lemma lem1985890 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1985891 : term226 = term166.
Proof. exact (EQ_MP (@lem1985890) (@lem940073)). Qed.
Lemma lem1985892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1985893 : term224 = term227.
Proof. exact (MK_COMB (@lem1985892) (@lem1985891)). Qed.
Lemma lem1985894 : term223 = term227.
Proof. exact (TRANS (@lem1985889) (@lem1985893)). Qed.
Lemma lem1985895 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1985896 : term228 = term229.
Proof. exact (MK_COMB (@lem1985895) (@lem1985894)). Qed.
Lemma lem1985897 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1985898 (z : real) : (term220 z) = (term230 z).
Proof. exact (MK_COMB (@lem1985896) (@lem1985897 z)). Qed.
Lemma lem1985899 (z : real) : (term219 z) = (term230 z).
Proof. exact (TRANS (@lem1985886 z) (@lem1985898 z)). Qed.
Lemma lem1985900 (z : real) : (term230 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1985901 (z : real) : (term219 z) = z.
Proof. exact (TRANS (@lem1985899 z) (@lem1985900 z)). Qed.
Lemma lem1985904 (y : real) : (term231 y) = (term231 y).
Proof. exact (eq_refl (term231 y)). Qed.
Lemma lem1985905 (y : real) (z : real) : (term218 y z) = (term232 y z).
Proof. exact (MK_COMB (@lem1985904 y) (@lem1985901 z)). Qed.
Lemma lem1985906 (y : real) (z : real) : (term217 y z) = (term232 y z).
Proof. exact (TRANS (@lem1985885 y z) (@lem1985905 y z)). Qed.
Lemma lem1985907 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1985908 (y : real) (z : real) : (term707 y z) = (term708 y z).
Proof. exact (MK_COMB (@lem1985907) (@lem1985906 y z)). Qed.
Lemma lem1985909 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1985910 (y : real) (z : real) : ((term217 y z) = term0) = ((term232 y z) = term0).
Proof. exact (MK_COMB (@lem1985908 y z) (@lem1985909)). Qed.
Lemma lem1985911 (y : real) (z : real) (h1 : term693 y z) : (term232 y z) = term0.
Proof. exact (EQ_MP (@lem1985910 y z) (@lem1985884 y z h1)). Qed.
Lemma lem1985912 (y : real) (z : real) (h1 : term693 y z) : term709 y z.
Proof. exact (conj (@lem1985911 y z h1) (@lem1985877 y z h1)). Qed.
Lemma lem1985914 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1985915 (y : real) (z : real) : term711 y z.
Proof. exact (@lem1985914 (term232 y z) (term201 y z)). Qed.
Lemma lem1985916 (y : real) (z : real) (h1 : term693 y z) : term712 y z.
Proof. exact (@lem1985915 y z (@lem1985912 y z h1)). Qed.
Lemma lem1985917 (y : real) (z : real) : (term713 y z) = (term714 y z).
Proof. exact (@lem1483480 (term193 y) y z (term193 z)). Qed.
Lemma lem1985918 (y : real) : (term715 y) = (term195 y).
Proof. exact (@lem1483440 term189 y). Qed.
Lemma lem1985920 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1985921 : term197 = term0.
Proof. exact (@lem1985920 term166). Qed.
Lemma lem1985922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1985923 : term198 = term199.
Proof. exact (MK_COMB (@lem1985922) (@lem1985921)). Qed.
Lemma lem1985924 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1985925 (y : real) : (term195 y) = (term22 y).
Proof. exact (MK_COMB (@lem1985923) (@lem1985924 y)). Qed.
Lemma lem1985926 (y : real) : (term715 y) = (term22 y).
Proof. exact (TRANS (@lem1985918 y) (@lem1985925 y)). Qed.
Lemma lem1985927 (y : real) : (term22 y) = term0.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1985928 (y : real) : (term715 y) = term0.
Proof. exact (TRANS (@lem1985926 y) (@lem1985927 y)). Qed.
Lemma lem1985929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1985930 (y : real) : (term716 y) = term167.
Proof. exact (MK_COMB (@lem1985929) (@lem1985928 y)). Qed.
Lemma lem1985931 (z : real) : (term194 z) = (term195 z).
Proof. exact (@lem1483442 term189 z). Qed.
Lemma lem1985933 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1985934 : term197 = term0.
Proof. exact (@lem1985933 term166). Qed.
Lemma lem1985935 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1985936 : term198 = term199.
Proof. exact (MK_COMB (@lem1985935) (@lem1985934)). Qed.
Lemma lem1985937 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1985938 (z : real) : (term195 z) = (term22 z).
Proof. exact (MK_COMB (@lem1985936) (@lem1985937 z)). Qed.
Lemma lem1985939 (z : real) : (term194 z) = (term22 z).
Proof. exact (TRANS (@lem1985931 z) (@lem1985938 z)). Qed.
Lemma lem1985940 (z : real) : (term22 z) = term0.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1985941 (z : real) : (term194 z) = term0.
Proof. exact (TRANS (@lem1985939 z) (@lem1985940 z)). Qed.
Lemma lem1985942 (y : real) (z : real) : (term714 y z) = term168.
Proof. exact (MK_COMB (@lem1985930 y) (@lem1985941 z)). Qed.
Lemma lem1985943 (y : real) (z : real) : (term713 y z) = term168.
Proof. exact (TRANS (@lem1985917 y z) (@lem1985942 y z)). Qed.
Lemma lem1985944 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1985945 (y : real) (z : real) : (term713 y z) = term0.
Proof. exact (TRANS (@lem1985943 y z) (@lem1985944)). Qed.
Lemma lem1985946 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1985947 (y : real) (z : real) : (term717 y z) = term175.
Proof. exact (MK_COMB (@lem1985946) (@lem1985945 y z)). Qed.
Lemma lem1985948 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1985949 (y : real) (z : real) : (term712 y z) = term177.
Proof. exact (MK_COMB (@lem1985947 y z) (@lem1985948)). Qed.
Lemma lem1985950 (y : real) (z : real) (h1 : term693 y z) : term177.
Proof. exact (EQ_MP (@lem1985949 y z) (@lem1985916 y z h1)). Qed.
Lemma lem1985952 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1985953 : term177 = term692.
Proof. exact (@lem1985952 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1985954 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1985955 : term177 = False.
Proof. exact (TRANS (@lem1985953) (@lem1985954)). Qed.
Lemma lem1985956 (y : real) (z : real) (h1 : term693 y z) : False.
Proof. exact (EQ_MP (@lem1985955) (@lem1985950 y z h1)). Qed.
Lemma lem1985957 (y : real) (z : real) (h1 : term718 y z) : term718 y z.
Proof. exact (h1). Qed.
Lemma lem1985958 (y : real) (z : real) (h1 : term718 y z) : term237 y z.
Proof. exact (proj2 (@lem1985957 y z h1)). Qed.
Lemma lem1985959 (y : real) (z : real) (h1 : term718 y z) : (term201 y z) = term0.
Proof. exact (proj1 (@lem1985957 y z h1)). Qed.
Lemma lem1985961 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1985962 : term694 = term695.
Proof. exact (@lem1985961 (NUMERAL 0) term166). Qed.
Lemma lem1985963 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1985964 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1985965 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1985964 h1) (fun h1 : term695 = True => @lem1985963)). Qed.
Lemma lem1985966 : term695 = True.
Proof. exact (EQ_MP (@lem1985965) (@lem1985963)). Qed.
Lemma lem1985967 : term694 = True.
Proof. exact (TRANS (@lem1985962) (@lem1985966)). Qed.
Lemma lem1985968 : True = term694.
Proof. exact (SYM (@lem1985967)). Qed.
Lemma lem1985969 : term694.
Proof. exact (EQ_MP (@lem1985968) (@lem0)). Qed.
Lemma lem1985970 (y : real) (z : real) (h1 : term718 y z) : term719 y z.
Proof. exact (conj (@lem1985969) (@lem1985958 y z h1)). Qed.
Lemma lem1985972 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1985973 (y : real) (z : real) : term720 y z.
Proof. exact (@lem1985972 term227 (term232 y z)). Qed.
Lemma lem1985974 (y : real) (z : real) (h1 : term718 y z) : term721 y z.
Proof. exact (@lem1985973 y z (@lem1985970 y z h1)). Qed.
Lemma lem1985975 (y : real) (z : real) : (term722 y z) = (term232 y z).
Proof. exact (@lem1483460 (term232 y z)). Qed.
Lemma lem1985976 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1985977 (y : real) (z : real) : (term723 y z) = (term235 y z).
Proof. exact (MK_COMB (@lem1985976) (@lem1985975 y z)). Qed.
Lemma lem1985978 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1985979 (y : real) (z : real) : (term721 y z) = (term237 y z).
Proof. exact (MK_COMB (@lem1985977 y z) (@lem1985978)). Qed.
Lemma lem1985980 (y : real) (z : real) (h1 : term718 y z) : term237 y z.
Proof. exact (EQ_MP (@lem1985979 y z) (@lem1985974 y z h1)). Qed.
Lemma lem1985982 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1985983 (y : real) (z : real) : term704 y z.
Proof. exact (@lem1985982 (term201 y z)). Qed.
Lemma lem1985984 (y : real) (z : real) (h1 : term718 y z) : term705 y z.
Proof. exact (@lem1985983 y z (@lem1985959 y z h1)). Qed.
Lemma lem1985985 (y : real) (z : real) (h1 : term718 y z) : term724 y z.
Proof. exact (@lem1985984 y z h1 term227). Qed.
Lemma lem1985986 (y : real) (z : real) : (term724 y z) = ((term701 y z) = term0).
Proof. exact (eq_refl (term724 y z)). Qed.
Lemma lem1985987 (y : real) (z : real) (h1 : term718 y z) : (term701 y z) = term0.
Proof. exact (EQ_MP (@lem1985986 y z) (@lem1985985 y z h1)). Qed.
Lemma lem1985988 (y : real) (z : real) : (term701 y z) = (term201 y z).
Proof. exact (@lem1483460 (term201 y z)). Qed.
Lemma lem1985989 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1985990 (y : real) (z : real) : (term725 y z) = (term210 y z).
Proof. exact (MK_COMB (@lem1985989) (@lem1985988 y z)). Qed.
Lemma lem1985991 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1985992 (y : real) (z : real) : ((term701 y z) = term0) = ((term201 y z) = term0).
Proof. exact (MK_COMB (@lem1985990 y z) (@lem1985991)). Qed.
Lemma lem1985993 (y : real) (z : real) (h1 : term718 y z) : (term201 y z) = term0.
Proof. exact (EQ_MP (@lem1985992 y z) (@lem1985987 y z h1)). Qed.
Lemma lem1985994 (y : real) (z : real) (h1 : term718 y z) : term718 y z.
Proof. exact (conj (@lem1985993 y z h1) (@lem1985980 y z h1)). Qed.
Lemma lem1985996 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1985997 (y : real) (z : real) : term726 y z.
Proof. exact (@lem1985996 (term201 y z) (term232 y z)). Qed.
Lemma lem1985998 (y : real) (z : real) (h1 : term718 y z) : term727 y z.
Proof. exact (@lem1985997 y z (@lem1985994 y z h1)). Qed.
Lemma lem1985999 (y : real) (z : real) : (term728 y z) = (term729 y z).
Proof. exact (@lem1483480 y (term193 y) (term193 z) z). Qed.
Lemma lem1986000 (y : real) : (term194 y) = (term195 y).
Proof. exact (@lem1483442 term189 y). Qed.
Lemma lem1986002 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986003 : term197 = term0.
Proof. exact (@lem1986002 term166). Qed.
Lemma lem1986004 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986005 : term198 = term199.
Proof. exact (MK_COMB (@lem1986004) (@lem1986003)). Qed.
Lemma lem1986006 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1986007 (y : real) : (term195 y) = (term22 y).
Proof. exact (MK_COMB (@lem1986005) (@lem1986006 y)). Qed.
Lemma lem1986008 (y : real) : (term194 y) = (term22 y).
Proof. exact (TRANS (@lem1986000 y) (@lem1986007 y)). Qed.
Lemma lem1986009 (y : real) : (term22 y) = term0.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1986010 (y : real) : (term194 y) = term0.
Proof. exact (TRANS (@lem1986008 y) (@lem1986009 y)). Qed.
Lemma lem1986011 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986012 (y : real) : (term200 y) = term167.
Proof. exact (MK_COMB (@lem1986011) (@lem1986010 y)). Qed.
Lemma lem1986013 (z : real) : (term715 z) = (term195 z).
Proof. exact (@lem1483440 term189 z). Qed.
Lemma lem1986015 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986016 : term197 = term0.
Proof. exact (@lem1986015 term166). Qed.
Lemma lem1986017 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986018 : term198 = term199.
Proof. exact (MK_COMB (@lem1986017) (@lem1986016)). Qed.
Lemma lem1986019 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1986020 (z : real) : (term195 z) = (term22 z).
Proof. exact (MK_COMB (@lem1986018) (@lem1986019 z)). Qed.
Lemma lem1986021 (z : real) : (term715 z) = (term22 z).
Proof. exact (TRANS (@lem1986013 z) (@lem1986020 z)). Qed.
Lemma lem1986022 (z : real) : (term22 z) = term0.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1986023 (z : real) : (term715 z) = term0.
Proof. exact (TRANS (@lem1986021 z) (@lem1986022 z)). Qed.
Lemma lem1986024 (y : real) (z : real) : (term729 y z) = term168.
Proof. exact (MK_COMB (@lem1986012 y) (@lem1986023 z)). Qed.
Lemma lem1986025 (y : real) (z : real) : (term728 y z) = term168.
Proof. exact (TRANS (@lem1985999 y z) (@lem1986024 y z)). Qed.
Lemma lem1986026 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986027 (y : real) (z : real) : (term728 y z) = term0.
Proof. exact (TRANS (@lem1986025 y z) (@lem1986026)). Qed.
Lemma lem1986028 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986029 (y : real) (z : real) : (term730 y z) = term175.
Proof. exact (MK_COMB (@lem1986028) (@lem1986027 y z)). Qed.
Lemma lem1986030 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986031 (y : real) (z : real) : (term727 y z) = term177.
Proof. exact (MK_COMB (@lem1986029 y z) (@lem1986030)). Qed.
Lemma lem1986032 (y : real) (z : real) (h1 : term718 y z) : term177.
Proof. exact (EQ_MP (@lem1986031 y z) (@lem1985998 y z h1)). Qed.
Lemma lem1986034 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986035 : term177 = term692.
Proof. exact (@lem1986034 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986036 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986037 : term177 = False.
Proof. exact (TRANS (@lem1986035) (@lem1986036)). Qed.
Lemma lem1986038 (y : real) (z : real) (h1 : term718 y z) : False.
Proof. exact (EQ_MP (@lem1986037) (@lem1986032 y z h1)). Qed.
Lemma lem1986039 (y : real) (z : real) (h1 : term677 y z) : False.
Proof. exact (or_elim (@lem1985853 y z h1) (fun h0 : term693 y z => @lem1985956 y z h0) (fun h0 : term718 y z => @lem1986038 y z h0)). Qed.
Lemma lem1986040 (y : real) (z : real) (h1 : term676 y z) : term676 y z.
Proof. exact (h1). Qed.
Lemma lem1986041 (y : real) (z : real) (h1 : term731 y z) : term731 y z.
Proof. exact (h1). Qed.
Lemma lem1986042 (y : real) (z : real) (h1 : term731 y z) : (term201 y z) = term0.
Proof. exact (proj2 (@lem1986041 y z h1)). Qed.
Lemma lem1986043 (y : real) (z : real) (h1 : term731 y z) : term241 y z.
Proof. exact (proj1 (@lem1986041 y z h1)). Qed.
Lemma lem1986045 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986046 : term694 = term695.
Proof. exact (@lem1986045 (NUMERAL 0) term166). Qed.
Lemma lem1986047 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986048 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1986049 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1986048 h1) (fun h1 : term695 = True => @lem1986047)). Qed.
Lemma lem1986050 : term695 = True.
Proof. exact (EQ_MP (@lem1986049) (@lem1986047)). Qed.
Lemma lem1986051 : term694 = True.
Proof. exact (TRANS (@lem1986046) (@lem1986050)). Qed.
Lemma lem1986052 : True = term694.
Proof. exact (SYM (@lem1986051)). Qed.
Lemma lem1986053 : term694.
Proof. exact (EQ_MP (@lem1986052) (@lem0)). Qed.
Lemma lem1986054 (y : real) (z : real) (h1 : term731 y z) : term697 y z.
Proof. exact (conj (@lem1986053) (@lem1986043 y z h1)). Qed.
Lemma lem1986056 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1986057 (y : real) (z : real) : term699 y z.
Proof. exact (@lem1986056 term227 (term201 y z)). Qed.
Lemma lem1986058 (y : real) (z : real) (h1 : term731 y z) : term700 y z.
Proof. exact (@lem1986057 y z (@lem1986054 y z h1)). Qed.
Lemma lem1986059 (y : real) (z : real) : (term701 y z) = (term201 y z).
Proof. exact (@lem1483460 (term201 y z)). Qed.
Lemma lem1986060 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986061 (y : real) (z : real) : (term702 y z) = (term239 y z).
Proof. exact (MK_COMB (@lem1986060) (@lem1986059 y z)). Qed.
Lemma lem1986062 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986063 (y : real) (z : real) : (term700 y z) = (term241 y z).
Proof. exact (MK_COMB (@lem1986061 y z) (@lem1986062)). Qed.
Lemma lem1986064 (y : real) (z : real) (h1 : term731 y z) : term241 y z.
Proof. exact (EQ_MP (@lem1986063 y z) (@lem1986058 y z h1)). Qed.
Lemma lem1986066 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1986067 (y : real) (z : real) : term704 y z.
Proof. exact (@lem1986066 (term201 y z)). Qed.
Lemma lem1986068 (y : real) (z : real) (h1 : term731 y z) : term705 y z.
Proof. exact (@lem1986067 y z (@lem1986042 y z h1)). Qed.
Lemma lem1986069 (y : real) (z : real) (h1 : term731 y z) : term706 y z.
Proof. exact (@lem1986068 y z h1 term189). Qed.
Lemma lem1986070 (y : real) (z : real) : (term706 y z) = ((term217 y z) = term0).
Proof. exact (eq_refl (term706 y z)). Qed.
Lemma lem1986071 (y : real) (z : real) (h1 : term731 y z) : (term217 y z) = term0.
Proof. exact (EQ_MP (@lem1986070 y z) (@lem1986069 y z h1)). Qed.
Lemma lem1986072 (y : real) (z : real) : (term217 y z) = (term218 y z).
Proof. exact (@lem1483508 y term189 (term193 z)). Qed.
Lemma lem1986073 (z : real) : (term219 z) = (term220 z).
Proof. exact (@lem1483476 term189 term189 z). Qed.
Lemma lem1986075 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1986076 : term223 = term224.
Proof. exact (@lem1986075 term166 term166). Qed.
Lemma lem1986077 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1986078 : term226 = term166.
Proof. exact (EQ_MP (@lem1986077) (@lem940073)). Qed.
Lemma lem1986079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1986080 : term224 = term227.
Proof. exact (MK_COMB (@lem1986079) (@lem1986078)). Qed.
Lemma lem1986081 : term223 = term227.
Proof. exact (TRANS (@lem1986076) (@lem1986080)). Qed.
Lemma lem1986082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986083 : term228 = term229.
Proof. exact (MK_COMB (@lem1986082) (@lem1986081)). Qed.
Lemma lem1986084 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1986085 (z : real) : (term220 z) = (term230 z).
Proof. exact (MK_COMB (@lem1986083) (@lem1986084 z)). Qed.
Lemma lem1986086 (z : real) : (term219 z) = (term230 z).
Proof. exact (TRANS (@lem1986073 z) (@lem1986085 z)). Qed.
Lemma lem1986087 (z : real) : (term230 z) = z.
Proof. exact (@lem1483436 z). Qed.
Lemma lem1986088 (z : real) : (term219 z) = z.
Proof. exact (TRANS (@lem1986086 z) (@lem1986087 z)). Qed.
Lemma lem1986091 (y : real) : (term231 y) = (term231 y).
Proof. exact (eq_refl (term231 y)). Qed.
Lemma lem1986092 (y : real) (z : real) : (term218 y z) = (term232 y z).
Proof. exact (MK_COMB (@lem1986091 y) (@lem1986088 z)). Qed.
Lemma lem1986093 (y : real) (z : real) : (term217 y z) = (term232 y z).
Proof. exact (TRANS (@lem1986072 y z) (@lem1986092 y z)). Qed.
Lemma lem1986094 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986095 (y : real) (z : real) : (term707 y z) = (term708 y z).
Proof. exact (MK_COMB (@lem1986094) (@lem1986093 y z)). Qed.
Lemma lem1986096 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986097 (y : real) (z : real) : ((term217 y z) = term0) = ((term232 y z) = term0).
Proof. exact (MK_COMB (@lem1986095 y z) (@lem1986096)). Qed.
Lemma lem1986098 (y : real) (z : real) (h1 : term731 y z) : (term232 y z) = term0.
Proof. exact (EQ_MP (@lem1986097 y z) (@lem1986071 y z h1)). Qed.
Lemma lem1986099 (y : real) (z : real) (h1 : term731 y z) : term709 y z.
Proof. exact (conj (@lem1986098 y z h1) (@lem1986064 y z h1)). Qed.
Lemma lem1986101 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1986102 (y : real) (z : real) : term711 y z.
Proof. exact (@lem1986101 (term232 y z) (term201 y z)). Qed.
Lemma lem1986103 (y : real) (z : real) (h1 : term731 y z) : term712 y z.
Proof. exact (@lem1986102 y z (@lem1986099 y z h1)). Qed.
Lemma lem1986104 (y : real) (z : real) : (term713 y z) = (term714 y z).
Proof. exact (@lem1483480 (term193 y) y z (term193 z)). Qed.
Lemma lem1986105 (y : real) : (term715 y) = (term195 y).
Proof. exact (@lem1483440 term189 y). Qed.
Lemma lem1986107 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986108 : term197 = term0.
Proof. exact (@lem1986107 term166). Qed.
Lemma lem1986109 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986110 : term198 = term199.
Proof. exact (MK_COMB (@lem1986109) (@lem1986108)). Qed.
Lemma lem1986111 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1986112 (y : real) : (term195 y) = (term22 y).
Proof. exact (MK_COMB (@lem1986110) (@lem1986111 y)). Qed.
Lemma lem1986113 (y : real) : (term715 y) = (term22 y).
Proof. exact (TRANS (@lem1986105 y) (@lem1986112 y)). Qed.
Lemma lem1986114 (y : real) : (term22 y) = term0.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1986115 (y : real) : (term715 y) = term0.
Proof. exact (TRANS (@lem1986113 y) (@lem1986114 y)). Qed.
Lemma lem1986116 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986117 (y : real) : (term716 y) = term167.
Proof. exact (MK_COMB (@lem1986116) (@lem1986115 y)). Qed.
Lemma lem1986118 (z : real) : (term194 z) = (term195 z).
Proof. exact (@lem1483442 term189 z). Qed.
Lemma lem1986120 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986121 : term197 = term0.
Proof. exact (@lem1986120 term166). Qed.
Lemma lem1986122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986123 : term198 = term199.
Proof. exact (MK_COMB (@lem1986122) (@lem1986121)). Qed.
Lemma lem1986124 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1986125 (z : real) : (term195 z) = (term22 z).
Proof. exact (MK_COMB (@lem1986123) (@lem1986124 z)). Qed.
Lemma lem1986126 (z : real) : (term194 z) = (term22 z).
Proof. exact (TRANS (@lem1986118 z) (@lem1986125 z)). Qed.
Lemma lem1986127 (z : real) : (term22 z) = term0.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1986128 (z : real) : (term194 z) = term0.
Proof. exact (TRANS (@lem1986126 z) (@lem1986127 z)). Qed.
Lemma lem1986129 (y : real) (z : real) : (term714 y z) = term168.
Proof. exact (MK_COMB (@lem1986117 y) (@lem1986128 z)). Qed.
Lemma lem1986130 (y : real) (z : real) : (term713 y z) = term168.
Proof. exact (TRANS (@lem1986104 y z) (@lem1986129 y z)). Qed.
Lemma lem1986131 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986132 (y : real) (z : real) : (term713 y z) = term0.
Proof. exact (TRANS (@lem1986130 y z) (@lem1986131)). Qed.
Lemma lem1986133 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986134 (y : real) (z : real) : (term717 y z) = term175.
Proof. exact (MK_COMB (@lem1986133) (@lem1986132 y z)). Qed.
Lemma lem1986135 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986136 (y : real) (z : real) : (term712 y z) = term177.
Proof. exact (MK_COMB (@lem1986134 y z) (@lem1986135)). Qed.
Lemma lem1986137 (y : real) (z : real) (h1 : term731 y z) : term177.
Proof. exact (EQ_MP (@lem1986136 y z) (@lem1986103 y z h1)). Qed.
Lemma lem1986139 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986140 : term177 = term692.
Proof. exact (@lem1986139 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986141 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986142 : term177 = False.
Proof. exact (TRANS (@lem1986140) (@lem1986141)). Qed.
Lemma lem1986143 (y : real) (z : real) (h1 : term731 y z) : False.
Proof. exact (EQ_MP (@lem1986142) (@lem1986137 y z h1)). Qed.
Lemma lem1986144 (y : real) (z : real) (h1 : term732 y z) : term732 y z.
Proof. exact (h1). Qed.
Lemma lem1986145 (y : real) (z : real) (h1 : term732 y z) : (term201 y z) = term0.
Proof. exact (proj2 (@lem1986144 y z h1)). Qed.
Lemma lem1986146 (y : real) (z : real) (h1 : term732 y z) : term237 y z.
Proof. exact (proj1 (@lem1986144 y z h1)). Qed.
Lemma lem1986148 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986149 : term694 = term695.
Proof. exact (@lem1986148 (NUMERAL 0) term166). Qed.
Lemma lem1986150 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986151 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1986152 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1986151 h1) (fun h1 : term695 = True => @lem1986150)). Qed.
Lemma lem1986153 : term695 = True.
Proof. exact (EQ_MP (@lem1986152) (@lem1986150)). Qed.
Lemma lem1986154 : term694 = True.
Proof. exact (TRANS (@lem1986149) (@lem1986153)). Qed.
Lemma lem1986155 : True = term694.
Proof. exact (SYM (@lem1986154)). Qed.
Lemma lem1986156 : term694.
Proof. exact (EQ_MP (@lem1986155) (@lem0)). Qed.
Lemma lem1986157 (y : real) (z : real) (h1 : term732 y z) : term719 y z.
Proof. exact (conj (@lem1986156) (@lem1986146 y z h1)). Qed.
Lemma lem1986159 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1986160 (y : real) (z : real) : term720 y z.
Proof. exact (@lem1986159 term227 (term232 y z)). Qed.
Lemma lem1986161 (y : real) (z : real) (h1 : term732 y z) : term721 y z.
Proof. exact (@lem1986160 y z (@lem1986157 y z h1)). Qed.
Lemma lem1986162 (y : real) (z : real) : (term722 y z) = (term232 y z).
Proof. exact (@lem1483460 (term232 y z)). Qed.
Lemma lem1986163 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986164 (y : real) (z : real) : (term723 y z) = (term235 y z).
Proof. exact (MK_COMB (@lem1986163) (@lem1986162 y z)). Qed.
Lemma lem1986165 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986166 (y : real) (z : real) : (term721 y z) = (term237 y z).
Proof. exact (MK_COMB (@lem1986164 y z) (@lem1986165)). Qed.
Lemma lem1986167 (y : real) (z : real) (h1 : term732 y z) : term237 y z.
Proof. exact (EQ_MP (@lem1986166 y z) (@lem1986161 y z h1)). Qed.
Lemma lem1986169 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1986170 (y : real) (z : real) : term704 y z.
Proof. exact (@lem1986169 (term201 y z)). Qed.
Lemma lem1986171 (y : real) (z : real) (h1 : term732 y z) : term705 y z.
Proof. exact (@lem1986170 y z (@lem1986145 y z h1)). Qed.
Lemma lem1986172 (y : real) (z : real) (h1 : term732 y z) : term724 y z.
Proof. exact (@lem1986171 y z h1 term227). Qed.
Lemma lem1986173 (y : real) (z : real) : (term724 y z) = ((term701 y z) = term0).
Proof. exact (eq_refl (term724 y z)). Qed.
Lemma lem1986174 (y : real) (z : real) (h1 : term732 y z) : (term701 y z) = term0.
Proof. exact (EQ_MP (@lem1986173 y z) (@lem1986172 y z h1)). Qed.
Lemma lem1986175 (y : real) (z : real) : (term701 y z) = (term201 y z).
Proof. exact (@lem1483460 (term201 y z)). Qed.
Lemma lem1986176 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986177 (y : real) (z : real) : (term725 y z) = (term210 y z).
Proof. exact (MK_COMB (@lem1986176) (@lem1986175 y z)). Qed.
Lemma lem1986178 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986179 (y : real) (z : real) : ((term701 y z) = term0) = ((term201 y z) = term0).
Proof. exact (MK_COMB (@lem1986177 y z) (@lem1986178)). Qed.
Lemma lem1986180 (y : real) (z : real) (h1 : term732 y z) : (term201 y z) = term0.
Proof. exact (EQ_MP (@lem1986179 y z) (@lem1986174 y z h1)). Qed.
Lemma lem1986181 (y : real) (z : real) (h1 : term732 y z) : term718 y z.
Proof. exact (conj (@lem1986180 y z h1) (@lem1986167 y z h1)). Qed.
Lemma lem1986183 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1986184 (y : real) (z : real) : term726 y z.
Proof. exact (@lem1986183 (term201 y z) (term232 y z)). Qed.
Lemma lem1986185 (y : real) (z : real) (h1 : term732 y z) : term727 y z.
Proof. exact (@lem1986184 y z (@lem1986181 y z h1)). Qed.
Lemma lem1986186 (y : real) (z : real) : (term728 y z) = (term729 y z).
Proof. exact (@lem1483480 y (term193 y) (term193 z) z). Qed.
Lemma lem1986187 (y : real) : (term194 y) = (term195 y).
Proof. exact (@lem1483442 term189 y). Qed.
Lemma lem1986189 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986190 : term197 = term0.
Proof. exact (@lem1986189 term166). Qed.
Lemma lem1986191 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986192 : term198 = term199.
Proof. exact (MK_COMB (@lem1986191) (@lem1986190)). Qed.
Lemma lem1986193 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1986194 (y : real) : (term195 y) = (term22 y).
Proof. exact (MK_COMB (@lem1986192) (@lem1986193 y)). Qed.
Lemma lem1986195 (y : real) : (term194 y) = (term22 y).
Proof. exact (TRANS (@lem1986187 y) (@lem1986194 y)). Qed.
Lemma lem1986196 (y : real) : (term22 y) = term0.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1986197 (y : real) : (term194 y) = term0.
Proof. exact (TRANS (@lem1986195 y) (@lem1986196 y)). Qed.
Lemma lem1986198 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986199 (y : real) : (term200 y) = term167.
Proof. exact (MK_COMB (@lem1986198) (@lem1986197 y)). Qed.
Lemma lem1986200 (z : real) : (term715 z) = (term195 z).
Proof. exact (@lem1483440 term189 z). Qed.
Lemma lem1986202 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986203 : term197 = term0.
Proof. exact (@lem1986202 term166). Qed.
Lemma lem1986204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986205 : term198 = term199.
Proof. exact (MK_COMB (@lem1986204) (@lem1986203)). Qed.
Lemma lem1986206 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1986207 (z : real) : (term195 z) = (term22 z).
Proof. exact (MK_COMB (@lem1986205) (@lem1986206 z)). Qed.
Lemma lem1986208 (z : real) : (term715 z) = (term22 z).
Proof. exact (TRANS (@lem1986200 z) (@lem1986207 z)). Qed.
Lemma lem1986209 (z : real) : (term22 z) = term0.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1986210 (z : real) : (term715 z) = term0.
Proof. exact (TRANS (@lem1986208 z) (@lem1986209 z)). Qed.
Lemma lem1986211 (y : real) (z : real) : (term729 y z) = term168.
Proof. exact (MK_COMB (@lem1986199 y) (@lem1986210 z)). Qed.
Lemma lem1986212 (y : real) (z : real) : (term728 y z) = term168.
Proof. exact (TRANS (@lem1986186 y z) (@lem1986211 y z)). Qed.
Lemma lem1986213 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986214 (y : real) (z : real) : (term728 y z) = term0.
Proof. exact (TRANS (@lem1986212 y z) (@lem1986213)). Qed.
Lemma lem1986215 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986216 (y : real) (z : real) : (term730 y z) = term175.
Proof. exact (MK_COMB (@lem1986215) (@lem1986214 y z)). Qed.
Lemma lem1986217 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986218 (y : real) (z : real) : (term727 y z) = term177.
Proof. exact (MK_COMB (@lem1986216 y z) (@lem1986217)). Qed.
Lemma lem1986219 (y : real) (z : real) (h1 : term732 y z) : term177.
Proof. exact (EQ_MP (@lem1986218 y z) (@lem1986185 y z h1)). Qed.
Lemma lem1986221 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986222 : term177 = term692.
Proof. exact (@lem1986221 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986223 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986224 : term177 = False.
Proof. exact (TRANS (@lem1986222) (@lem1986223)). Qed.
Lemma lem1986225 (y : real) (z : real) (h1 : term732 y z) : False.
Proof. exact (EQ_MP (@lem1986224) (@lem1986219 y z h1)). Qed.
Lemma lem1986226 (y : real) (z : real) (h1 : term676 y z) : False.
Proof. exact (or_elim (@lem1986040 y z h1) (fun h0 : term731 y z => @lem1986143 y z h0) (fun h0 : term732 y z => @lem1986225 y z h0)). Qed.
Lemma lem1986227 (y : real) (z : real) (h1 : term679 y z) : False.
Proof. exact (or_elim (@lem1985852 y z h1) (fun h0 : term677 y z => @lem1986039 y z h0) (fun h0 : term676 y z => @lem1986226 y z h0)). Qed.
Lemma lem1986228 (y : real) (y' : real) (z : real) (z' : real) (h1 : term675 y y' z z') : term675 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986229 (y : real) (y' : real) (z : real) (z' : real) (h1 : term673 y y' z z') : term673 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986230 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term733 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986231 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term337 y y' z z'.
Proof. exact (proj2 (@lem1986230 y y' z z' h1)). Qed.
Lemma lem1986232 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : (term287 y y' z z') = term0.
Proof. exact (proj1 (@lem1986230 y y' z z' h1)). Qed.
Lemma lem1986234 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986235 : term694 = term695.
Proof. exact (@lem1986234 (NUMERAL 0) term166). Qed.
Lemma lem1986236 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986237 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1986238 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1986237 h1) (fun h1 : term695 = True => @lem1986236)). Qed.
Lemma lem1986239 : term695 = True.
Proof. exact (EQ_MP (@lem1986238) (@lem1986236)). Qed.
Lemma lem1986240 : term694 = True.
Proof. exact (TRANS (@lem1986235) (@lem1986239)). Qed.
Lemma lem1986241 : True = term694.
Proof. exact (SYM (@lem1986240)). Qed.
Lemma lem1986242 : term694.
Proof. exact (EQ_MP (@lem1986241) (@lem0)). Qed.
Lemma lem1986243 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term734 y y' z z'.
Proof. exact (conj (@lem1986242) (@lem1986231 y y' z z' h1)). Qed.
Lemma lem1986245 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1986246 (y : real) (y' : real) (z : real) (z' : real) : term735 y y' z z'.
Proof. exact (@lem1986245 term227 (term287 y y' z z')). Qed.
Lemma lem1986247 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term736 y y' z z'.
Proof. exact (@lem1986246 y y' z z' (@lem1986243 y y' z z' h1)). Qed.
Lemma lem1986248 (y : real) (y' : real) (z : real) (z' : real) : (term737 y y' z z') = (term287 y y' z z').
Proof. exact (@lem1483460 (term287 y y' z z')). Qed.
Lemma lem1986249 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986250 (y : real) (y' : real) (z : real) (z' : real) : (term738 y y' z z') = (term335 y y' z z').
Proof. exact (MK_COMB (@lem1986249) (@lem1986248 y y' z z')). Qed.
Lemma lem1986251 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986252 (y : real) (y' : real) (z : real) (z' : real) : (term736 y y' z z') = (term337 y y' z z').
Proof. exact (MK_COMB (@lem1986250 y y' z z') (@lem1986251)). Qed.
Lemma lem1986253 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term337 y y' z z'.
Proof. exact (EQ_MP (@lem1986252 y y' z z') (@lem1986247 y y' z z' h1)). Qed.
Lemma lem1986255 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1986256 (y : real) (y' : real) (z : real) (z' : real) : term739 y y' z z'.
Proof. exact (@lem1986255 (term287 y y' z z')). Qed.
Lemma lem1986257 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term740 y y' z z'.
Proof. exact (@lem1986256 y y' z z' (@lem1986232 y y' z z' h1)). Qed.
Lemma lem1986258 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term741 y y' z z'.
Proof. exact (@lem1986257 y y' z z' h1 term189). Qed.
Lemma lem1986259 (y : real) (y' : real) (z : real) (z' : real) : (term741 y y' z z') = ((term319 y y' z z') = term0).
Proof. exact (eq_refl (term741 y y' z z')). Qed.
Lemma lem1986260 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : (term319 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986259 y y' z z') (@lem1986258 y y' z z' h1)). Qed.
Lemma lem1986261 (y : real) (y' : real) (z : real) (z' : real) : (term319 y y' z z') = (term320 y y' z z').
Proof. exact (@lem1483508 (real_mul y y') term189 (term285 y y' z z')). Qed.
Lemma lem1986262 (y : real) (y' : real) (z : real) (z' : real) : (term321 y y' z z') = (term322 y y' z z').
Proof. exact (@lem1483508 (term281 y z') term189 (term283 y' z z')). Qed.
Lemma lem1986263 (y' : real) (z : real) (z' : real) : (term323 y' z z') = (term324 y' z z').
Proof. exact (@lem1483508 (term281 z y') term189 (real_mul z z')). Qed.
Lemma lem1986264 (z : real) (z' : real) : (term281 z z') = (term281 z z').
Proof. exact (eq_refl (term281 z z')). Qed.
Lemma lem1986265 (z : real) (y' : real) : (term325 z y') = (term310 z y').
Proof. exact (@lem1483476 term189 term189 (real_mul z y')). Qed.
Lemma lem1986267 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1986268 : term223 = term224.
Proof. exact (@lem1986267 term166 term166). Qed.
Lemma lem1986269 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1986270 : term226 = term166.
Proof. exact (EQ_MP (@lem1986269) (@lem940073)). Qed.
Lemma lem1986271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1986272 : term224 = term227.
Proof. exact (MK_COMB (@lem1986271) (@lem1986270)). Qed.
Lemma lem1986273 : term223 = term227.
Proof. exact (TRANS (@lem1986268) (@lem1986272)). Qed.
Lemma lem1986274 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986275 : term228 = term229.
Proof. exact (MK_COMB (@lem1986274) (@lem1986273)). Qed.
Lemma lem1986276 (z : real) (y' : real) : (real_mul z y') = (real_mul z y').
Proof. exact (eq_refl (real_mul z y')). Qed.
Lemma lem1986277 (z : real) (y' : real) : (term310 z y') = (term311 z y').
Proof. exact (MK_COMB (@lem1986275) (@lem1986276 z y')). Qed.
Lemma lem1986278 (z : real) (y' : real) : (term325 z y') = (term311 z y').
Proof. exact (TRANS (@lem1986265 z y') (@lem1986277 z y')). Qed.
Lemma lem1986279 (z : real) (y' : real) : (term311 z y') = (real_mul z y').
Proof. exact (@lem1483436 (real_mul z y')). Qed.
Lemma lem1986280 (z : real) (y' : real) : (term325 z y') = (real_mul z y').
Proof. exact (TRANS (@lem1986278 z y') (@lem1986279 z y')). Qed.
Lemma lem1986281 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986282 (z : real) (y' : real) : (term326 z y') = (term286 z y').
Proof. exact (MK_COMB (@lem1986281) (@lem1986280 z y')). Qed.
Lemma lem1986283 (y' : real) (z : real) (z' : real) : (term324 y' z z') = (term282 y' z z').
Proof. exact (MK_COMB (@lem1986282 z y') (@lem1986264 z z')). Qed.
Lemma lem1986284 (y' : real) (z : real) (z' : real) : (term323 y' z z') = (term282 y' z z').
Proof. exact (TRANS (@lem1986263 y' z z') (@lem1986283 y' z z')). Qed.
Lemma lem1986285 (y : real) (z' : real) : (term325 y z') = (term310 y z').
Proof. exact (@lem1483476 term189 term189 (real_mul y z')). Qed.
Lemma lem1986287 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1986288 : term223 = term224.
Proof. exact (@lem1986287 term166 term166). Qed.
Lemma lem1986289 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1986290 : term226 = term166.
Proof. exact (EQ_MP (@lem1986289) (@lem940073)). Qed.
Lemma lem1986291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1986292 : term224 = term227.
Proof. exact (MK_COMB (@lem1986291) (@lem1986290)). Qed.
Lemma lem1986293 : term223 = term227.
Proof. exact (TRANS (@lem1986288) (@lem1986292)). Qed.
Lemma lem1986294 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986295 : term228 = term229.
Proof. exact (MK_COMB (@lem1986294) (@lem1986293)). Qed.
Lemma lem1986296 (y : real) (z' : real) : (real_mul y z') = (real_mul y z').
Proof. exact (eq_refl (real_mul y z')). Qed.
Lemma lem1986297 (y : real) (z' : real) : (term310 y z') = (term311 y z').
Proof. exact (MK_COMB (@lem1986295) (@lem1986296 y z')). Qed.
Lemma lem1986298 (y : real) (z' : real) : (term325 y z') = (term311 y z').
Proof. exact (TRANS (@lem1986285 y z') (@lem1986297 y z')). Qed.
Lemma lem1986299 (y : real) (z' : real) : (term311 y z') = (real_mul y z').
Proof. exact (@lem1483436 (real_mul y z')). Qed.
Lemma lem1986300 (y : real) (z' : real) : (term325 y z') = (real_mul y z').
Proof. exact (TRANS (@lem1986298 y z') (@lem1986299 y z')). Qed.
Lemma lem1986301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986302 (y : real) (z' : real) : (term326 y z') = (term286 y z').
Proof. exact (MK_COMB (@lem1986301) (@lem1986300 y z')). Qed.
Lemma lem1986303 (y : real) (y' : real) (z : real) (z' : real) : (term322 y y' z z') = (term327 y y' z z').
Proof. exact (MK_COMB (@lem1986302 y z') (@lem1986284 y' z z')). Qed.
Lemma lem1986304 (y : real) (y' : real) (z : real) (z' : real) : (term321 y y' z z') = (term327 y y' z z').
Proof. exact (TRANS (@lem1986262 y y' z z') (@lem1986303 y y' z z')). Qed.
Lemma lem1986307 (y : real) (y' : real) : (term284 y y') = (term284 y y').
Proof. exact (eq_refl (term284 y y')). Qed.
Lemma lem1986308 (y : real) (y' : real) (z : real) (z' : real) : (term320 y y' z z') = (term328 y y' z z').
Proof. exact (MK_COMB (@lem1986307 y y') (@lem1986304 y y' z z')). Qed.
Lemma lem1986309 (y : real) (y' : real) (z : real) (z' : real) : (term319 y y' z z') = (term328 y y' z z').
Proof. exact (TRANS (@lem1986261 y y' z z') (@lem1986308 y y' z z')). Qed.
Lemma lem1986310 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986311 (y : real) (y' : real) (z : real) (z' : real) : (term742 y y' z z') = (term743 y y' z z').
Proof. exact (MK_COMB (@lem1986310) (@lem1986309 y y' z z')). Qed.
Lemma lem1986312 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986313 (y : real) (y' : real) (z : real) (z' : real) : ((term319 y y' z z') = term0) = ((term328 y y' z z') = term0).
Proof. exact (MK_COMB (@lem1986311 y y' z z') (@lem1986312)). Qed.
Lemma lem1986314 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : (term328 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986313 y y' z z') (@lem1986260 y y' z z' h1)). Qed.
Lemma lem1986315 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term744 y y' z z'.
Proof. exact (conj (@lem1986314 y y' z z' h1) (@lem1986253 y y' z z' h1)). Qed.
Lemma lem1986317 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1986318 (y : real) (y' : real) (z : real) (z' : real) : term745 y y' z z'.
Proof. exact (@lem1986317 (term328 y y' z z') (term287 y y' z z')). Qed.
Lemma lem1986319 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term746 y y' z z'.
Proof. exact (@lem1986318 y y' z z' (@lem1986315 y y' z z' h1)). Qed.
Lemma lem1986320 (y : real) (y' : real) (z : real) (z' : real) : (term747 y y' z z') = (term748 y y' z z').
Proof. exact (@lem1483480 (term281 y y') (real_mul y y') (term327 y y' z z') (term285 y y' z z')). Qed.
Lemma lem1986321 (y : real) (y' : real) : (term749 y y') = (term750 y y').
Proof. exact (@lem1483440 term189 (real_mul y y')). Qed.
Lemma lem1986323 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986324 : term197 = term0.
Proof. exact (@lem1986323 term166). Qed.
Lemma lem1986325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986326 : term198 = term199.
Proof. exact (MK_COMB (@lem1986325) (@lem1986324)). Qed.
Lemma lem1986327 (y : real) (y' : real) : (real_mul y y') = (real_mul y y').
Proof. exact (eq_refl (real_mul y y')). Qed.
Lemma lem1986328 (y : real) (y' : real) : (term750 y y') = (term751 y y').
Proof. exact (MK_COMB (@lem1986326) (@lem1986327 y y')). Qed.
Lemma lem1986329 (y : real) (y' : real) : (term749 y y') = (term751 y y').
Proof. exact (TRANS (@lem1986321 y y') (@lem1986328 y y')). Qed.
Lemma lem1986330 (y : real) (y' : real) : (term751 y y') = term0.
Proof. exact (@lem1483446 (real_mul y y')). Qed.
Lemma lem1986331 (y : real) (y' : real) : (term749 y y') = term0.
Proof. exact (TRANS (@lem1986329 y y') (@lem1986330 y y')). Qed.
Lemma lem1986332 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986333 (y : real) (y' : real) : (term752 y y') = term167.
Proof. exact (MK_COMB (@lem1986332) (@lem1986331 y y')). Qed.
Lemma lem1986334 (y : real) (y' : real) (z : real) (z' : real) : (term753 y y' z z') = (term754 y y' z z').
Proof. exact (@lem1483480 (real_mul y z') (term281 y z') (term282 y' z z') (term283 y' z z')). Qed.
Lemma lem1986335 (y : real) (z' : real) : (term755 y z') = (term750 y z').
Proof. exact (@lem1483442 term189 (real_mul y z')). Qed.
Lemma lem1986337 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986338 : term197 = term0.
Proof. exact (@lem1986337 term166). Qed.
Lemma lem1986339 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986340 : term198 = term199.
Proof. exact (MK_COMB (@lem1986339) (@lem1986338)). Qed.
Lemma lem1986341 (y : real) (z' : real) : (real_mul y z') = (real_mul y z').
Proof. exact (eq_refl (real_mul y z')). Qed.
Lemma lem1986342 (y : real) (z' : real) : (term750 y z') = (term751 y z').
Proof. exact (MK_COMB (@lem1986340) (@lem1986341 y z')). Qed.
Lemma lem1986343 (y : real) (z' : real) : (term755 y z') = (term751 y z').
Proof. exact (TRANS (@lem1986335 y z') (@lem1986342 y z')). Qed.
Lemma lem1986344 (y : real) (z' : real) : (term751 y z') = term0.
Proof. exact (@lem1483446 (real_mul y z')). Qed.
Lemma lem1986345 (y : real) (z' : real) : (term755 y z') = term0.
Proof. exact (TRANS (@lem1986343 y z') (@lem1986344 y z')). Qed.
Lemma lem1986346 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986347 (y : real) (z' : real) : (term756 y z') = term167.
Proof. exact (MK_COMB (@lem1986346) (@lem1986345 y z')). Qed.
Lemma lem1986348 (y' : real) (z : real) (z' : real) : (term757 y' z z') = (term758 y' z z').
Proof. exact (@lem1483480 (real_mul z y') (term281 z y') (term281 z z') (real_mul z z')). Qed.
Lemma lem1986349 (z : real) (y' : real) : (term755 z y') = (term750 z y').
Proof. exact (@lem1483442 term189 (real_mul z y')). Qed.
Lemma lem1986351 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986352 : term197 = term0.
Proof. exact (@lem1986351 term166). Qed.
Lemma lem1986353 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986354 : term198 = term199.
Proof. exact (MK_COMB (@lem1986353) (@lem1986352)). Qed.
Lemma lem1986355 (z : real) (y' : real) : (real_mul z y') = (real_mul z y').
Proof. exact (eq_refl (real_mul z y')). Qed.
Lemma lem1986356 (z : real) (y' : real) : (term750 z y') = (term751 z y').
Proof. exact (MK_COMB (@lem1986354) (@lem1986355 z y')). Qed.
Lemma lem1986357 (z : real) (y' : real) : (term755 z y') = (term751 z y').
Proof. exact (TRANS (@lem1986349 z y') (@lem1986356 z y')). Qed.
Lemma lem1986358 (z : real) (y' : real) : (term751 z y') = term0.
Proof. exact (@lem1483446 (real_mul z y')). Qed.
Lemma lem1986359 (z : real) (y' : real) : (term755 z y') = term0.
Proof. exact (TRANS (@lem1986357 z y') (@lem1986358 z y')). Qed.
Lemma lem1986360 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986361 (z : real) (y' : real) : (term756 z y') = term167.
Proof. exact (MK_COMB (@lem1986360) (@lem1986359 z y')). Qed.
Lemma lem1986362 (z : real) (z' : real) : (term749 z z') = (term750 z z').
Proof. exact (@lem1483440 term189 (real_mul z z')). Qed.
Lemma lem1986364 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986365 : term197 = term0.
Proof. exact (@lem1986364 term166). Qed.
Lemma lem1986366 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986367 : term198 = term199.
Proof. exact (MK_COMB (@lem1986366) (@lem1986365)). Qed.
Lemma lem1986368 (z : real) (z' : real) : (real_mul z z') = (real_mul z z').
Proof. exact (eq_refl (real_mul z z')). Qed.
Lemma lem1986369 (z : real) (z' : real) : (term750 z z') = (term751 z z').
Proof. exact (MK_COMB (@lem1986367) (@lem1986368 z z')). Qed.
Lemma lem1986370 (z : real) (z' : real) : (term749 z z') = (term751 z z').
Proof. exact (TRANS (@lem1986362 z z') (@lem1986369 z z')). Qed.
Lemma lem1986371 (z : real) (z' : real) : (term751 z z') = term0.
Proof. exact (@lem1483446 (real_mul z z')). Qed.
Lemma lem1986372 (z : real) (z' : real) : (term749 z z') = term0.
Proof. exact (TRANS (@lem1986370 z z') (@lem1986371 z z')). Qed.
Lemma lem1986373 (y' : real) (z : real) (z' : real) : (term758 y' z z') = term168.
Proof. exact (MK_COMB (@lem1986361 z y') (@lem1986372 z z')). Qed.
Lemma lem1986374 (y' : real) (z : real) (z' : real) : (term757 y' z z') = term168.
Proof. exact (TRANS (@lem1986348 y' z z') (@lem1986373 y' z z')). Qed.
Lemma lem1986375 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986376 (y' : real) (z : real) (z' : real) : (term757 y' z z') = term0.
Proof. exact (TRANS (@lem1986374 y' z z') (@lem1986375)). Qed.
Lemma lem1986377 (y : real) (y' : real) (z : real) (z' : real) : (term754 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986347 y z') (@lem1986376 y' z z')). Qed.
Lemma lem1986378 (y : real) (y' : real) (z : real) (z' : real) : (term753 y y' z z') = term168.
Proof. exact (TRANS (@lem1986334 y y' z z') (@lem1986377 y y' z z')). Qed.
Lemma lem1986379 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986380 (y : real) (y' : real) (z : real) (z' : real) : (term753 y y' z z') = term0.
Proof. exact (TRANS (@lem1986378 y y' z z') (@lem1986379)). Qed.
Lemma lem1986381 (y : real) (y' : real) (z : real) (z' : real) : (term748 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986333 y y') (@lem1986380 y y' z z')). Qed.
Lemma lem1986382 (y : real) (y' : real) (z : real) (z' : real) : (term747 y y' z z') = term168.
Proof. exact (TRANS (@lem1986320 y y' z z') (@lem1986381 y y' z z')). Qed.
Lemma lem1986383 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986384 (y : real) (y' : real) (z : real) (z' : real) : (term747 y y' z z') = term0.
Proof. exact (TRANS (@lem1986382 y y' z z') (@lem1986383)). Qed.
Lemma lem1986385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986386 (y : real) (y' : real) (z : real) (z' : real) : (term759 y y' z z') = term175.
Proof. exact (MK_COMB (@lem1986385) (@lem1986384 y y' z z')). Qed.
Lemma lem1986387 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986388 (y : real) (y' : real) (z : real) (z' : real) : (term746 y y' z z') = term177.
Proof. exact (MK_COMB (@lem1986386 y y' z z') (@lem1986387)). Qed.
Lemma lem1986389 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : term177.
Proof. exact (EQ_MP (@lem1986388 y y' z z') (@lem1986319 y y' z z' h1)). Qed.
Lemma lem1986391 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986392 : term177 = term692.
Proof. exact (@lem1986391 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986393 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986394 : term177 = False.
Proof. exact (TRANS (@lem1986392) (@lem1986393)). Qed.
Lemma lem1986395 (y : real) (y' : real) (z : real) (z' : real) (h1 : term733 y y' z z') : False.
Proof. exact (EQ_MP (@lem1986394) (@lem1986389 y y' z z' h1)). Qed.
Lemma lem1986396 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term760 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986397 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term333 y y' z z'.
Proof. exact (proj2 (@lem1986396 y y' z z' h1)). Qed.
Lemma lem1986398 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : (term287 y y' z z') = term0.
Proof. exact (proj1 (@lem1986396 y y' z z' h1)). Qed.
Lemma lem1986400 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986401 : term694 = term695.
Proof. exact (@lem1986400 (NUMERAL 0) term166). Qed.
Lemma lem1986402 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986403 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1986404 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1986403 h1) (fun h1 : term695 = True => @lem1986402)). Qed.
Lemma lem1986405 : term695 = True.
Proof. exact (EQ_MP (@lem1986404) (@lem1986402)). Qed.
Lemma lem1986406 : term694 = True.
Proof. exact (TRANS (@lem1986401) (@lem1986405)). Qed.
Lemma lem1986407 : True = term694.
Proof. exact (SYM (@lem1986406)). Qed.
Lemma lem1986408 : term694.
Proof. exact (EQ_MP (@lem1986407) (@lem0)). Qed.
Lemma lem1986409 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term761 y y' z z'.
Proof. exact (conj (@lem1986408) (@lem1986397 y y' z z' h1)). Qed.
Lemma lem1986411 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1986412 (y : real) (y' : real) (z : real) (z' : real) : term762 y y' z z'.
Proof. exact (@lem1986411 term227 (term328 y y' z z')). Qed.
Lemma lem1986413 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term763 y y' z z'.
Proof. exact (@lem1986412 y y' z z' (@lem1986409 y y' z z' h1)). Qed.
Lemma lem1986414 (y : real) (y' : real) (z : real) (z' : real) : (term764 y y' z z') = (term328 y y' z z').
Proof. exact (@lem1483460 (term328 y y' z z')). Qed.
Lemma lem1986415 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986416 (y : real) (y' : real) (z : real) (z' : real) : (term765 y y' z z') = (term331 y y' z z').
Proof. exact (MK_COMB (@lem1986415) (@lem1986414 y y' z z')). Qed.
Lemma lem1986417 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986418 (y : real) (y' : real) (z : real) (z' : real) : (term763 y y' z z') = (term333 y y' z z').
Proof. exact (MK_COMB (@lem1986416 y y' z z') (@lem1986417)). Qed.
Lemma lem1986419 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term333 y y' z z'.
Proof. exact (EQ_MP (@lem1986418 y y' z z') (@lem1986413 y y' z z' h1)). Qed.
Lemma lem1986421 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1986422 (y : real) (y' : real) (z : real) (z' : real) : term739 y y' z z'.
Proof. exact (@lem1986421 (term287 y y' z z')). Qed.
Lemma lem1986423 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term740 y y' z z'.
Proof. exact (@lem1986422 y y' z z' (@lem1986398 y y' z z' h1)). Qed.
Lemma lem1986424 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term766 y y' z z'.
Proof. exact (@lem1986423 y y' z z' h1 term227). Qed.
Lemma lem1986425 (y : real) (y' : real) (z : real) (z' : real) : (term766 y y' z z') = ((term737 y y' z z') = term0).
Proof. exact (eq_refl (term766 y y' z z')). Qed.
Lemma lem1986426 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : (term737 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986425 y y' z z') (@lem1986424 y y' z z' h1)). Qed.
Lemma lem1986427 (y : real) (y' : real) (z : real) (z' : real) : (term737 y y' z z') = (term287 y y' z z').
Proof. exact (@lem1483460 (term287 y y' z z')). Qed.
Lemma lem1986428 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986429 (y : real) (y' : real) (z : real) (z' : real) : (term767 y y' z z') = (term295 y y' z z').
Proof. exact (MK_COMB (@lem1986428) (@lem1986427 y y' z z')). Qed.
Lemma lem1986430 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986431 (y : real) (y' : real) (z : real) (z' : real) : ((term737 y y' z z') = term0) = ((term287 y y' z z') = term0).
Proof. exact (MK_COMB (@lem1986429 y y' z z') (@lem1986430)). Qed.
Lemma lem1986432 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : (term287 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986431 y y' z z') (@lem1986426 y y' z z' h1)). Qed.
Lemma lem1986433 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term760 y y' z z'.
Proof. exact (conj (@lem1986432 y y' z z' h1) (@lem1986419 y y' z z' h1)). Qed.
Lemma lem1986435 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1986436 (y : real) (y' : real) (z : real) (z' : real) : term768 y y' z z'.
Proof. exact (@lem1986435 (term287 y y' z z') (term328 y y' z z')). Qed.
Lemma lem1986437 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term769 y y' z z'.
Proof. exact (@lem1986436 y y' z z' (@lem1986433 y y' z z' h1)). Qed.
Lemma lem1986438 (y : real) (y' : real) (z : real) (z' : real) : (term770 y y' z z') = (term771 y y' z z').
Proof. exact (@lem1483480 (real_mul y y') (term281 y y') (term285 y y' z z') (term327 y y' z z')). Qed.
Lemma lem1986439 (y : real) (y' : real) : (term755 y y') = (term750 y y').
Proof. exact (@lem1483442 term189 (real_mul y y')). Qed.
Lemma lem1986441 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986442 : term197 = term0.
Proof. exact (@lem1986441 term166). Qed.
Lemma lem1986443 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986444 : term198 = term199.
Proof. exact (MK_COMB (@lem1986443) (@lem1986442)). Qed.
Lemma lem1986445 (y : real) (y' : real) : (real_mul y y') = (real_mul y y').
Proof. exact (eq_refl (real_mul y y')). Qed.
Lemma lem1986446 (y : real) (y' : real) : (term750 y y') = (term751 y y').
Proof. exact (MK_COMB (@lem1986444) (@lem1986445 y y')). Qed.
Lemma lem1986447 (y : real) (y' : real) : (term755 y y') = (term751 y y').
Proof. exact (TRANS (@lem1986439 y y') (@lem1986446 y y')). Qed.
Lemma lem1986448 (y : real) (y' : real) : (term751 y y') = term0.
Proof. exact (@lem1483446 (real_mul y y')). Qed.
Lemma lem1986449 (y : real) (y' : real) : (term755 y y') = term0.
Proof. exact (TRANS (@lem1986447 y y') (@lem1986448 y y')). Qed.
Lemma lem1986450 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986451 (y : real) (y' : real) : (term756 y y') = term167.
Proof. exact (MK_COMB (@lem1986450) (@lem1986449 y y')). Qed.
Lemma lem1986452 (y : real) (y' : real) (z : real) (z' : real) : (term772 y y' z z') = (term773 y y' z z').
Proof. exact (@lem1483480 (term281 y z') (real_mul y z') (term283 y' z z') (term282 y' z z')). Qed.
Lemma lem1986453 (y : real) (z' : real) : (term749 y z') = (term750 y z').
Proof. exact (@lem1483440 term189 (real_mul y z')). Qed.
Lemma lem1986455 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986456 : term197 = term0.
Proof. exact (@lem1986455 term166). Qed.
Lemma lem1986457 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986458 : term198 = term199.
Proof. exact (MK_COMB (@lem1986457) (@lem1986456)). Qed.
Lemma lem1986459 (y : real) (z' : real) : (real_mul y z') = (real_mul y z').
Proof. exact (eq_refl (real_mul y z')). Qed.
Lemma lem1986460 (y : real) (z' : real) : (term750 y z') = (term751 y z').
Proof. exact (MK_COMB (@lem1986458) (@lem1986459 y z')). Qed.
Lemma lem1986461 (y : real) (z' : real) : (term749 y z') = (term751 y z').
Proof. exact (TRANS (@lem1986453 y z') (@lem1986460 y z')). Qed.
Lemma lem1986462 (y : real) (z' : real) : (term751 y z') = term0.
Proof. exact (@lem1483446 (real_mul y z')). Qed.
Lemma lem1986463 (y : real) (z' : real) : (term749 y z') = term0.
Proof. exact (TRANS (@lem1986461 y z') (@lem1986462 y z')). Qed.
Lemma lem1986464 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986465 (y : real) (z' : real) : (term752 y z') = term167.
Proof. exact (MK_COMB (@lem1986464) (@lem1986463 y z')). Qed.
Lemma lem1986466 (y' : real) (z : real) (z' : real) : (term774 y' z z') = (term775 y' z z').
Proof. exact (@lem1483480 (term281 z y') (real_mul z y') (real_mul z z') (term281 z z')). Qed.
Lemma lem1986467 (z : real) (y' : real) : (term749 z y') = (term750 z y').
Proof. exact (@lem1483440 term189 (real_mul z y')). Qed.
Lemma lem1986469 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986470 : term197 = term0.
Proof. exact (@lem1986469 term166). Qed.
Lemma lem1986471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986472 : term198 = term199.
Proof. exact (MK_COMB (@lem1986471) (@lem1986470)). Qed.
Lemma lem1986473 (z : real) (y' : real) : (real_mul z y') = (real_mul z y').
Proof. exact (eq_refl (real_mul z y')). Qed.
Lemma lem1986474 (z : real) (y' : real) : (term750 z y') = (term751 z y').
Proof. exact (MK_COMB (@lem1986472) (@lem1986473 z y')). Qed.
Lemma lem1986475 (z : real) (y' : real) : (term749 z y') = (term751 z y').
Proof. exact (TRANS (@lem1986467 z y') (@lem1986474 z y')). Qed.
Lemma lem1986476 (z : real) (y' : real) : (term751 z y') = term0.
Proof. exact (@lem1483446 (real_mul z y')). Qed.
Lemma lem1986477 (z : real) (y' : real) : (term749 z y') = term0.
Proof. exact (TRANS (@lem1986475 z y') (@lem1986476 z y')). Qed.
Lemma lem1986478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986479 (z : real) (y' : real) : (term752 z y') = term167.
Proof. exact (MK_COMB (@lem1986478) (@lem1986477 z y')). Qed.
Lemma lem1986480 (z : real) (z' : real) : (term755 z z') = (term750 z z').
Proof. exact (@lem1483442 term189 (real_mul z z')). Qed.
Lemma lem1986482 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986483 : term197 = term0.
Proof. exact (@lem1986482 term166). Qed.
Lemma lem1986484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986485 : term198 = term199.
Proof. exact (MK_COMB (@lem1986484) (@lem1986483)). Qed.
Lemma lem1986486 (z : real) (z' : real) : (real_mul z z') = (real_mul z z').
Proof. exact (eq_refl (real_mul z z')). Qed.
Lemma lem1986487 (z : real) (z' : real) : (term750 z z') = (term751 z z').
Proof. exact (MK_COMB (@lem1986485) (@lem1986486 z z')). Qed.
Lemma lem1986488 (z : real) (z' : real) : (term755 z z') = (term751 z z').
Proof. exact (TRANS (@lem1986480 z z') (@lem1986487 z z')). Qed.
Lemma lem1986489 (z : real) (z' : real) : (term751 z z') = term0.
Proof. exact (@lem1483446 (real_mul z z')). Qed.
Lemma lem1986490 (z : real) (z' : real) : (term755 z z') = term0.
Proof. exact (TRANS (@lem1986488 z z') (@lem1986489 z z')). Qed.
Lemma lem1986491 (y' : real) (z : real) (z' : real) : (term775 y' z z') = term168.
Proof. exact (MK_COMB (@lem1986479 z y') (@lem1986490 z z')). Qed.
Lemma lem1986492 (y' : real) (z : real) (z' : real) : (term774 y' z z') = term168.
Proof. exact (TRANS (@lem1986466 y' z z') (@lem1986491 y' z z')). Qed.
Lemma lem1986493 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986494 (y' : real) (z : real) (z' : real) : (term774 y' z z') = term0.
Proof. exact (TRANS (@lem1986492 y' z z') (@lem1986493)). Qed.
Lemma lem1986495 (y : real) (y' : real) (z : real) (z' : real) : (term773 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986465 y z') (@lem1986494 y' z z')). Qed.
Lemma lem1986496 (y : real) (y' : real) (z : real) (z' : real) : (term772 y y' z z') = term168.
Proof. exact (TRANS (@lem1986452 y y' z z') (@lem1986495 y y' z z')). Qed.
Lemma lem1986497 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986498 (y : real) (y' : real) (z : real) (z' : real) : (term772 y y' z z') = term0.
Proof. exact (TRANS (@lem1986496 y y' z z') (@lem1986497)). Qed.
Lemma lem1986499 (y : real) (y' : real) (z : real) (z' : real) : (term771 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986451 y y') (@lem1986498 y y' z z')). Qed.
Lemma lem1986500 (y : real) (y' : real) (z : real) (z' : real) : (term770 y y' z z') = term168.
Proof. exact (TRANS (@lem1986438 y y' z z') (@lem1986499 y y' z z')). Qed.
Lemma lem1986501 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986502 (y : real) (y' : real) (z : real) (z' : real) : (term770 y y' z z') = term0.
Proof. exact (TRANS (@lem1986500 y y' z z') (@lem1986501)). Qed.
Lemma lem1986503 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986504 (y : real) (y' : real) (z : real) (z' : real) : (term776 y y' z z') = term175.
Proof. exact (MK_COMB (@lem1986503) (@lem1986502 y y' z z')). Qed.
Lemma lem1986505 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986506 (y : real) (y' : real) (z : real) (z' : real) : (term769 y y' z z') = term177.
Proof. exact (MK_COMB (@lem1986504 y y' z z') (@lem1986505)). Qed.
Lemma lem1986507 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : term177.
Proof. exact (EQ_MP (@lem1986506 y y' z z') (@lem1986437 y y' z z' h1)). Qed.
Lemma lem1986509 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986510 : term177 = term692.
Proof. exact (@lem1986509 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986511 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986512 : term177 = False.
Proof. exact (TRANS (@lem1986510) (@lem1986511)). Qed.
Lemma lem1986513 (y : real) (y' : real) (z : real) (z' : real) (h1 : term760 y y' z z') : False.
Proof. exact (EQ_MP (@lem1986512) (@lem1986507 y y' z z' h1)). Qed.
Lemma lem1986514 (y : real) (y' : real) (z : real) (z' : real) (h1 : term673 y y' z z') : False.
Proof. exact (or_elim (@lem1986229 y y' z z' h1) (fun h0 : term733 y y' z z' => @lem1986395 y y' z z' h0) (fun h0 : term760 y y' z z' => @lem1986513 y y' z z' h0)). Qed.
Lemma lem1986515 (y : real) (y' : real) (z : real) (z' : real) (h1 : term672 y y' z z') : term672 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986516 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term777 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986517 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : (term287 y y' z z') = term0.
Proof. exact (proj2 (@lem1986516 y y' z z' h1)). Qed.
Lemma lem1986518 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term337 y y' z z'.
Proof. exact (proj1 (@lem1986516 y y' z z' h1)). Qed.
Lemma lem1986520 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986521 : term694 = term695.
Proof. exact (@lem1986520 (NUMERAL 0) term166). Qed.
Lemma lem1986522 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986523 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1986524 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1986523 h1) (fun h1 : term695 = True => @lem1986522)). Qed.
Lemma lem1986525 : term695 = True.
Proof. exact (EQ_MP (@lem1986524) (@lem1986522)). Qed.
Lemma lem1986526 : term694 = True.
Proof. exact (TRANS (@lem1986521) (@lem1986525)). Qed.
Lemma lem1986527 : True = term694.
Proof. exact (SYM (@lem1986526)). Qed.
Lemma lem1986528 : term694.
Proof. exact (EQ_MP (@lem1986527) (@lem0)). Qed.
Lemma lem1986529 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term734 y y' z z'.
Proof. exact (conj (@lem1986528) (@lem1986518 y y' z z' h1)). Qed.
Lemma lem1986531 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1986532 (y : real) (y' : real) (z : real) (z' : real) : term735 y y' z z'.
Proof. exact (@lem1986531 term227 (term287 y y' z z')). Qed.
Lemma lem1986533 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term736 y y' z z'.
Proof. exact (@lem1986532 y y' z z' (@lem1986529 y y' z z' h1)). Qed.
Lemma lem1986534 (y : real) (y' : real) (z : real) (z' : real) : (term737 y y' z z') = (term287 y y' z z').
Proof. exact (@lem1483460 (term287 y y' z z')). Qed.
Lemma lem1986535 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986536 (y : real) (y' : real) (z : real) (z' : real) : (term738 y y' z z') = (term335 y y' z z').
Proof. exact (MK_COMB (@lem1986535) (@lem1986534 y y' z z')). Qed.
Lemma lem1986537 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986538 (y : real) (y' : real) (z : real) (z' : real) : (term736 y y' z z') = (term337 y y' z z').
Proof. exact (MK_COMB (@lem1986536 y y' z z') (@lem1986537)). Qed.
Lemma lem1986539 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term337 y y' z z'.
Proof. exact (EQ_MP (@lem1986538 y y' z z') (@lem1986533 y y' z z' h1)). Qed.
Lemma lem1986541 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1986542 (y : real) (y' : real) (z : real) (z' : real) : term739 y y' z z'.
Proof. exact (@lem1986541 (term287 y y' z z')). Qed.
Lemma lem1986543 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term740 y y' z z'.
Proof. exact (@lem1986542 y y' z z' (@lem1986517 y y' z z' h1)). Qed.
Lemma lem1986544 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term741 y y' z z'.
Proof. exact (@lem1986543 y y' z z' h1 term189). Qed.
Lemma lem1986545 (y : real) (y' : real) (z : real) (z' : real) : (term741 y y' z z') = ((term319 y y' z z') = term0).
Proof. exact (eq_refl (term741 y y' z z')). Qed.
Lemma lem1986546 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : (term319 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986545 y y' z z') (@lem1986544 y y' z z' h1)). Qed.
Lemma lem1986547 (y : real) (y' : real) (z : real) (z' : real) : (term319 y y' z z') = (term320 y y' z z').
Proof. exact (@lem1483508 (real_mul y y') term189 (term285 y y' z z')). Qed.
Lemma lem1986548 (y : real) (y' : real) (z : real) (z' : real) : (term321 y y' z z') = (term322 y y' z z').
Proof. exact (@lem1483508 (term281 y z') term189 (term283 y' z z')). Qed.
Lemma lem1986549 (y' : real) (z : real) (z' : real) : (term323 y' z z') = (term324 y' z z').
Proof. exact (@lem1483508 (term281 z y') term189 (real_mul z z')). Qed.
Lemma lem1986550 (z : real) (z' : real) : (term281 z z') = (term281 z z').
Proof. exact (eq_refl (term281 z z')). Qed.
Lemma lem1986551 (z : real) (y' : real) : (term325 z y') = (term310 z y').
Proof. exact (@lem1483476 term189 term189 (real_mul z y')). Qed.
Lemma lem1986553 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1986554 : term223 = term224.
Proof. exact (@lem1986553 term166 term166). Qed.
Lemma lem1986555 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1986556 : term226 = term166.
Proof. exact (EQ_MP (@lem1986555) (@lem940073)). Qed.
Lemma lem1986557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1986558 : term224 = term227.
Proof. exact (MK_COMB (@lem1986557) (@lem1986556)). Qed.
Lemma lem1986559 : term223 = term227.
Proof. exact (TRANS (@lem1986554) (@lem1986558)). Qed.
Lemma lem1986560 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986561 : term228 = term229.
Proof. exact (MK_COMB (@lem1986560) (@lem1986559)). Qed.
Lemma lem1986562 (z : real) (y' : real) : (real_mul z y') = (real_mul z y').
Proof. exact (eq_refl (real_mul z y')). Qed.
Lemma lem1986563 (z : real) (y' : real) : (term310 z y') = (term311 z y').
Proof. exact (MK_COMB (@lem1986561) (@lem1986562 z y')). Qed.
Lemma lem1986564 (z : real) (y' : real) : (term325 z y') = (term311 z y').
Proof. exact (TRANS (@lem1986551 z y') (@lem1986563 z y')). Qed.
Lemma lem1986565 (z : real) (y' : real) : (term311 z y') = (real_mul z y').
Proof. exact (@lem1483436 (real_mul z y')). Qed.
Lemma lem1986566 (z : real) (y' : real) : (term325 z y') = (real_mul z y').
Proof. exact (TRANS (@lem1986564 z y') (@lem1986565 z y')). Qed.
Lemma lem1986567 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986568 (z : real) (y' : real) : (term326 z y') = (term286 z y').
Proof. exact (MK_COMB (@lem1986567) (@lem1986566 z y')). Qed.
Lemma lem1986569 (y' : real) (z : real) (z' : real) : (term324 y' z z') = (term282 y' z z').
Proof. exact (MK_COMB (@lem1986568 z y') (@lem1986550 z z')). Qed.
Lemma lem1986570 (y' : real) (z : real) (z' : real) : (term323 y' z z') = (term282 y' z z').
Proof. exact (TRANS (@lem1986549 y' z z') (@lem1986569 y' z z')). Qed.
Lemma lem1986571 (y : real) (z' : real) : (term325 y z') = (term310 y z').
Proof. exact (@lem1483476 term189 term189 (real_mul y z')). Qed.
Lemma lem1986573 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1986574 : term223 = term224.
Proof. exact (@lem1986573 term166 term166). Qed.
Lemma lem1986575 : (term225 = (BIT1 0)) = (term226 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1986576 : term226 = term166.
Proof. exact (EQ_MP (@lem1986575) (@lem940073)). Qed.
Lemma lem1986577 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1986578 : term224 = term227.
Proof. exact (MK_COMB (@lem1986577) (@lem1986576)). Qed.
Lemma lem1986579 : term223 = term227.
Proof. exact (TRANS (@lem1986574) (@lem1986578)). Qed.
Lemma lem1986580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986581 : term228 = term229.
Proof. exact (MK_COMB (@lem1986580) (@lem1986579)). Qed.
Lemma lem1986582 (y : real) (z' : real) : (real_mul y z') = (real_mul y z').
Proof. exact (eq_refl (real_mul y z')). Qed.
Lemma lem1986583 (y : real) (z' : real) : (term310 y z') = (term311 y z').
Proof. exact (MK_COMB (@lem1986581) (@lem1986582 y z')). Qed.
Lemma lem1986584 (y : real) (z' : real) : (term325 y z') = (term311 y z').
Proof. exact (TRANS (@lem1986571 y z') (@lem1986583 y z')). Qed.
Lemma lem1986585 (y : real) (z' : real) : (term311 y z') = (real_mul y z').
Proof. exact (@lem1483436 (real_mul y z')). Qed.
Lemma lem1986586 (y : real) (z' : real) : (term325 y z') = (real_mul y z').
Proof. exact (TRANS (@lem1986584 y z') (@lem1986585 y z')). Qed.
Lemma lem1986587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986588 (y : real) (z' : real) : (term326 y z') = (term286 y z').
Proof. exact (MK_COMB (@lem1986587) (@lem1986586 y z')). Qed.
Lemma lem1986589 (y : real) (y' : real) (z : real) (z' : real) : (term322 y y' z z') = (term327 y y' z z').
Proof. exact (MK_COMB (@lem1986588 y z') (@lem1986570 y' z z')). Qed.
Lemma lem1986590 (y : real) (y' : real) (z : real) (z' : real) : (term321 y y' z z') = (term327 y y' z z').
Proof. exact (TRANS (@lem1986548 y y' z z') (@lem1986589 y y' z z')). Qed.
Lemma lem1986593 (y : real) (y' : real) : (term284 y y') = (term284 y y').
Proof. exact (eq_refl (term284 y y')). Qed.
Lemma lem1986594 (y : real) (y' : real) (z : real) (z' : real) : (term320 y y' z z') = (term328 y y' z z').
Proof. exact (MK_COMB (@lem1986593 y y') (@lem1986590 y y' z z')). Qed.
Lemma lem1986595 (y : real) (y' : real) (z : real) (z' : real) : (term319 y y' z z') = (term328 y y' z z').
Proof. exact (TRANS (@lem1986547 y y' z z') (@lem1986594 y y' z z')). Qed.
Lemma lem1986596 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986597 (y : real) (y' : real) (z : real) (z' : real) : (term742 y y' z z') = (term743 y y' z z').
Proof. exact (MK_COMB (@lem1986596) (@lem1986595 y y' z z')). Qed.
Lemma lem1986598 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986599 (y : real) (y' : real) (z : real) (z' : real) : ((term319 y y' z z') = term0) = ((term328 y y' z z') = term0).
Proof. exact (MK_COMB (@lem1986597 y y' z z') (@lem1986598)). Qed.
Lemma lem1986600 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : (term328 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986599 y y' z z') (@lem1986546 y y' z z' h1)). Qed.
Lemma lem1986601 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term744 y y' z z'.
Proof. exact (conj (@lem1986600 y y' z z' h1) (@lem1986539 y y' z z' h1)). Qed.
Lemma lem1986603 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1986604 (y : real) (y' : real) (z : real) (z' : real) : term745 y y' z z'.
Proof. exact (@lem1986603 (term328 y y' z z') (term287 y y' z z')). Qed.
Lemma lem1986605 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term746 y y' z z'.
Proof. exact (@lem1986604 y y' z z' (@lem1986601 y y' z z' h1)). Qed.
Lemma lem1986606 (y : real) (y' : real) (z : real) (z' : real) : (term747 y y' z z') = (term748 y y' z z').
Proof. exact (@lem1483480 (term281 y y') (real_mul y y') (term327 y y' z z') (term285 y y' z z')). Qed.
Lemma lem1986607 (y : real) (y' : real) : (term749 y y') = (term750 y y').
Proof. exact (@lem1483440 term189 (real_mul y y')). Qed.
Lemma lem1986609 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986610 : term197 = term0.
Proof. exact (@lem1986609 term166). Qed.
Lemma lem1986611 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986612 : term198 = term199.
Proof. exact (MK_COMB (@lem1986611) (@lem1986610)). Qed.
Lemma lem1986613 (y : real) (y' : real) : (real_mul y y') = (real_mul y y').
Proof. exact (eq_refl (real_mul y y')). Qed.
Lemma lem1986614 (y : real) (y' : real) : (term750 y y') = (term751 y y').
Proof. exact (MK_COMB (@lem1986612) (@lem1986613 y y')). Qed.
Lemma lem1986615 (y : real) (y' : real) : (term749 y y') = (term751 y y').
Proof. exact (TRANS (@lem1986607 y y') (@lem1986614 y y')). Qed.
Lemma lem1986616 (y : real) (y' : real) : (term751 y y') = term0.
Proof. exact (@lem1483446 (real_mul y y')). Qed.
Lemma lem1986617 (y : real) (y' : real) : (term749 y y') = term0.
Proof. exact (TRANS (@lem1986615 y y') (@lem1986616 y y')). Qed.
Lemma lem1986618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986619 (y : real) (y' : real) : (term752 y y') = term167.
Proof. exact (MK_COMB (@lem1986618) (@lem1986617 y y')). Qed.
Lemma lem1986620 (y : real) (y' : real) (z : real) (z' : real) : (term753 y y' z z') = (term754 y y' z z').
Proof. exact (@lem1483480 (real_mul y z') (term281 y z') (term282 y' z z') (term283 y' z z')). Qed.
Lemma lem1986621 (y : real) (z' : real) : (term755 y z') = (term750 y z').
Proof. exact (@lem1483442 term189 (real_mul y z')). Qed.
Lemma lem1986623 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986624 : term197 = term0.
Proof. exact (@lem1986623 term166). Qed.
Lemma lem1986625 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986626 : term198 = term199.
Proof. exact (MK_COMB (@lem1986625) (@lem1986624)). Qed.
Lemma lem1986627 (y : real) (z' : real) : (real_mul y z') = (real_mul y z').
Proof. exact (eq_refl (real_mul y z')). Qed.
Lemma lem1986628 (y : real) (z' : real) : (term750 y z') = (term751 y z').
Proof. exact (MK_COMB (@lem1986626) (@lem1986627 y z')). Qed.
Lemma lem1986629 (y : real) (z' : real) : (term755 y z') = (term751 y z').
Proof. exact (TRANS (@lem1986621 y z') (@lem1986628 y z')). Qed.
Lemma lem1986630 (y : real) (z' : real) : (term751 y z') = term0.
Proof. exact (@lem1483446 (real_mul y z')). Qed.
Lemma lem1986631 (y : real) (z' : real) : (term755 y z') = term0.
Proof. exact (TRANS (@lem1986629 y z') (@lem1986630 y z')). Qed.
Lemma lem1986632 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986633 (y : real) (z' : real) : (term756 y z') = term167.
Proof. exact (MK_COMB (@lem1986632) (@lem1986631 y z')). Qed.
Lemma lem1986634 (y' : real) (z : real) (z' : real) : (term757 y' z z') = (term758 y' z z').
Proof. exact (@lem1483480 (real_mul z y') (term281 z y') (term281 z z') (real_mul z z')). Qed.
Lemma lem1986635 (z : real) (y' : real) : (term755 z y') = (term750 z y').
Proof. exact (@lem1483442 term189 (real_mul z y')). Qed.
Lemma lem1986637 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986638 : term197 = term0.
Proof. exact (@lem1986637 term166). Qed.
Lemma lem1986639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986640 : term198 = term199.
Proof. exact (MK_COMB (@lem1986639) (@lem1986638)). Qed.
Lemma lem1986641 (z : real) (y' : real) : (real_mul z y') = (real_mul z y').
Proof. exact (eq_refl (real_mul z y')). Qed.
Lemma lem1986642 (z : real) (y' : real) : (term750 z y') = (term751 z y').
Proof. exact (MK_COMB (@lem1986640) (@lem1986641 z y')). Qed.
Lemma lem1986643 (z : real) (y' : real) : (term755 z y') = (term751 z y').
Proof. exact (TRANS (@lem1986635 z y') (@lem1986642 z y')). Qed.
Lemma lem1986644 (z : real) (y' : real) : (term751 z y') = term0.
Proof. exact (@lem1483446 (real_mul z y')). Qed.
Lemma lem1986645 (z : real) (y' : real) : (term755 z y') = term0.
Proof. exact (TRANS (@lem1986643 z y') (@lem1986644 z y')). Qed.
Lemma lem1986646 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986647 (z : real) (y' : real) : (term756 z y') = term167.
Proof. exact (MK_COMB (@lem1986646) (@lem1986645 z y')). Qed.
Lemma lem1986648 (z : real) (z' : real) : (term749 z z') = (term750 z z').
Proof. exact (@lem1483440 term189 (real_mul z z')). Qed.
Lemma lem1986650 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986651 : term197 = term0.
Proof. exact (@lem1986650 term166). Qed.
Lemma lem1986652 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986653 : term198 = term199.
Proof. exact (MK_COMB (@lem1986652) (@lem1986651)). Qed.
Lemma lem1986654 (z : real) (z' : real) : (real_mul z z') = (real_mul z z').
Proof. exact (eq_refl (real_mul z z')). Qed.
Lemma lem1986655 (z : real) (z' : real) : (term750 z z') = (term751 z z').
Proof. exact (MK_COMB (@lem1986653) (@lem1986654 z z')). Qed.
Lemma lem1986656 (z : real) (z' : real) : (term749 z z') = (term751 z z').
Proof. exact (TRANS (@lem1986648 z z') (@lem1986655 z z')). Qed.
Lemma lem1986657 (z : real) (z' : real) : (term751 z z') = term0.
Proof. exact (@lem1483446 (real_mul z z')). Qed.
Lemma lem1986658 (z : real) (z' : real) : (term749 z z') = term0.
Proof. exact (TRANS (@lem1986656 z z') (@lem1986657 z z')). Qed.
Lemma lem1986659 (y' : real) (z : real) (z' : real) : (term758 y' z z') = term168.
Proof. exact (MK_COMB (@lem1986647 z y') (@lem1986658 z z')). Qed.
Lemma lem1986660 (y' : real) (z : real) (z' : real) : (term757 y' z z') = term168.
Proof. exact (TRANS (@lem1986634 y' z z') (@lem1986659 y' z z')). Qed.
Lemma lem1986661 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986662 (y' : real) (z : real) (z' : real) : (term757 y' z z') = term0.
Proof. exact (TRANS (@lem1986660 y' z z') (@lem1986661)). Qed.
Lemma lem1986663 (y : real) (y' : real) (z : real) (z' : real) : (term754 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986633 y z') (@lem1986662 y' z z')). Qed.
Lemma lem1986664 (y : real) (y' : real) (z : real) (z' : real) : (term753 y y' z z') = term168.
Proof. exact (TRANS (@lem1986620 y y' z z') (@lem1986663 y y' z z')). Qed.
Lemma lem1986665 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986666 (y : real) (y' : real) (z : real) (z' : real) : (term753 y y' z z') = term0.
Proof. exact (TRANS (@lem1986664 y y' z z') (@lem1986665)). Qed.
Lemma lem1986667 (y : real) (y' : real) (z : real) (z' : real) : (term748 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986619 y y') (@lem1986666 y y' z z')). Qed.
Lemma lem1986668 (y : real) (y' : real) (z : real) (z' : real) : (term747 y y' z z') = term168.
Proof. exact (TRANS (@lem1986606 y y' z z') (@lem1986667 y y' z z')). Qed.
Lemma lem1986669 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986670 (y : real) (y' : real) (z : real) (z' : real) : (term747 y y' z z') = term0.
Proof. exact (TRANS (@lem1986668 y y' z z') (@lem1986669)). Qed.
Lemma lem1986671 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986672 (y : real) (y' : real) (z : real) (z' : real) : (term759 y y' z z') = term175.
Proof. exact (MK_COMB (@lem1986671) (@lem1986670 y y' z z')). Qed.
Lemma lem1986673 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986674 (y : real) (y' : real) (z : real) (z' : real) : (term746 y y' z z') = term177.
Proof. exact (MK_COMB (@lem1986672 y y' z z') (@lem1986673)). Qed.
Lemma lem1986675 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : term177.
Proof. exact (EQ_MP (@lem1986674 y y' z z') (@lem1986605 y y' z z' h1)). Qed.
Lemma lem1986677 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986678 : term177 = term692.
Proof. exact (@lem1986677 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986679 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986680 : term177 = False.
Proof. exact (TRANS (@lem1986678) (@lem1986679)). Qed.
Lemma lem1986681 (y : real) (y' : real) (z : real) (z' : real) (h1 : term777 y y' z z') : False.
Proof. exact (EQ_MP (@lem1986680) (@lem1986675 y y' z z' h1)). Qed.
Lemma lem1986682 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term778 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986683 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : (term287 y y' z z') = term0.
Proof. exact (proj2 (@lem1986682 y y' z z' h1)). Qed.
Lemma lem1986684 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term333 y y' z z'.
Proof. exact (proj1 (@lem1986682 y y' z z' h1)). Qed.
Lemma lem1986686 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986687 : term694 = term695.
Proof. exact (@lem1986686 (NUMERAL 0) term166). Qed.
Lemma lem1986688 : term696 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1986689 (h1 : term696 = (BIT1 0)) : term695 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1986690 : (term696 = (BIT1 0)) = (term695 = True).
Proof. exact (prop_ext (fun h1 : term696 = (BIT1 0) => @lem1986689 h1) (fun h1 : term695 = True => @lem1986688)). Qed.
Lemma lem1986691 : term695 = True.
Proof. exact (EQ_MP (@lem1986690) (@lem1986688)). Qed.
Lemma lem1986692 : term694 = True.
Proof. exact (TRANS (@lem1986687) (@lem1986691)). Qed.
Lemma lem1986693 : True = term694.
Proof. exact (SYM (@lem1986692)). Qed.
Lemma lem1986694 : term694.
Proof. exact (EQ_MP (@lem1986693) (@lem0)). Qed.
Lemma lem1986695 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term761 y y' z z'.
Proof. exact (conj (@lem1986694) (@lem1986684 y y' z z' h1)). Qed.
Lemma lem1986697 (x : real) (y : real) : term698 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1986698 (y : real) (y' : real) (z : real) (z' : real) : term762 y y' z z'.
Proof. exact (@lem1986697 term227 (term328 y y' z z')). Qed.
Lemma lem1986699 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term763 y y' z z'.
Proof. exact (@lem1986698 y y' z z' (@lem1986695 y y' z z' h1)). Qed.
Lemma lem1986700 (y : real) (y' : real) (z : real) (z' : real) : (term764 y y' z z') = (term328 y y' z z').
Proof. exact (@lem1483460 (term328 y y' z z')). Qed.
Lemma lem1986701 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986702 (y : real) (y' : real) (z : real) (z' : real) : (term765 y y' z z') = (term331 y y' z z').
Proof. exact (MK_COMB (@lem1986701) (@lem1986700 y y' z z')). Qed.
Lemma lem1986703 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986704 (y : real) (y' : real) (z : real) (z' : real) : (term763 y y' z z') = (term333 y y' z z').
Proof. exact (MK_COMB (@lem1986702 y y' z z') (@lem1986703)). Qed.
Lemma lem1986705 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term333 y y' z z'.
Proof. exact (EQ_MP (@lem1986704 y y' z z') (@lem1986699 y y' z z' h1)). Qed.
Lemma lem1986707 (y : real) : term703 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1986708 (y : real) (y' : real) (z : real) (z' : real) : term739 y y' z z'.
Proof. exact (@lem1986707 (term287 y y' z z')). Qed.
Lemma lem1986709 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term740 y y' z z'.
Proof. exact (@lem1986708 y y' z z' (@lem1986683 y y' z z' h1)). Qed.
Lemma lem1986710 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term766 y y' z z'.
Proof. exact (@lem1986709 y y' z z' h1 term227). Qed.
Lemma lem1986711 (y : real) (y' : real) (z : real) (z' : real) : (term766 y y' z z') = ((term737 y y' z z') = term0).
Proof. exact (eq_refl (term766 y y' z z')). Qed.
Lemma lem1986712 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : (term737 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986711 y y' z z') (@lem1986710 y y' z z' h1)). Qed.
Lemma lem1986713 (y : real) (y' : real) (z : real) (z' : real) : (term737 y y' z z') = (term287 y y' z z').
Proof. exact (@lem1483460 (term287 y y' z z')). Qed.
Lemma lem1986714 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1986715 (y : real) (y' : real) (z : real) (z' : real) : (term767 y y' z z') = (term295 y y' z z').
Proof. exact (MK_COMB (@lem1986714) (@lem1986713 y y' z z')). Qed.
Lemma lem1986716 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986717 (y : real) (y' : real) (z : real) (z' : real) : ((term737 y y' z z') = term0) = ((term287 y y' z z') = term0).
Proof. exact (MK_COMB (@lem1986715 y y' z z') (@lem1986716)). Qed.
Lemma lem1986718 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : (term287 y y' z z') = term0.
Proof. exact (EQ_MP (@lem1986717 y y' z z') (@lem1986712 y y' z z' h1)). Qed.
Lemma lem1986719 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term760 y y' z z'.
Proof. exact (conj (@lem1986718 y y' z z' h1) (@lem1986705 y y' z z' h1)). Qed.
Lemma lem1986721 (x : real) (y : real) : term710 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1986722 (y : real) (y' : real) (z : real) (z' : real) : term768 y y' z z'.
Proof. exact (@lem1986721 (term287 y y' z z') (term328 y y' z z')). Qed.
Lemma lem1986723 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term769 y y' z z'.
Proof. exact (@lem1986722 y y' z z' (@lem1986719 y y' z z' h1)). Qed.
Lemma lem1986724 (y : real) (y' : real) (z : real) (z' : real) : (term770 y y' z z') = (term771 y y' z z').
Proof. exact (@lem1483480 (real_mul y y') (term281 y y') (term285 y y' z z') (term327 y y' z z')). Qed.
Lemma lem1986725 (y : real) (y' : real) : (term755 y y') = (term750 y y').
Proof. exact (@lem1483442 term189 (real_mul y y')). Qed.
Lemma lem1986727 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986728 : term197 = term0.
Proof. exact (@lem1986727 term166). Qed.
Lemma lem1986729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986730 : term198 = term199.
Proof. exact (MK_COMB (@lem1986729) (@lem1986728)). Qed.
Lemma lem1986731 (y : real) (y' : real) : (real_mul y y') = (real_mul y y').
Proof. exact (eq_refl (real_mul y y')). Qed.
Lemma lem1986732 (y : real) (y' : real) : (term750 y y') = (term751 y y').
Proof. exact (MK_COMB (@lem1986730) (@lem1986731 y y')). Qed.
Lemma lem1986733 (y : real) (y' : real) : (term755 y y') = (term751 y y').
Proof. exact (TRANS (@lem1986725 y y') (@lem1986732 y y')). Qed.
Lemma lem1986734 (y : real) (y' : real) : (term751 y y') = term0.
Proof. exact (@lem1483446 (real_mul y y')). Qed.
Lemma lem1986735 (y : real) (y' : real) : (term755 y y') = term0.
Proof. exact (TRANS (@lem1986733 y y') (@lem1986734 y y')). Qed.
Lemma lem1986736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986737 (y : real) (y' : real) : (term756 y y') = term167.
Proof. exact (MK_COMB (@lem1986736) (@lem1986735 y y')). Qed.
Lemma lem1986738 (y : real) (y' : real) (z : real) (z' : real) : (term772 y y' z z') = (term773 y y' z z').
Proof. exact (@lem1483480 (term281 y z') (real_mul y z') (term283 y' z z') (term282 y' z z')). Qed.
Lemma lem1986739 (y : real) (z' : real) : (term749 y z') = (term750 y z').
Proof. exact (@lem1483440 term189 (real_mul y z')). Qed.
Lemma lem1986741 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986742 : term197 = term0.
Proof. exact (@lem1986741 term166). Qed.
Lemma lem1986743 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986744 : term198 = term199.
Proof. exact (MK_COMB (@lem1986743) (@lem1986742)). Qed.
Lemma lem1986745 (y : real) (z' : real) : (real_mul y z') = (real_mul y z').
Proof. exact (eq_refl (real_mul y z')). Qed.
Lemma lem1986746 (y : real) (z' : real) : (term750 y z') = (term751 y z').
Proof. exact (MK_COMB (@lem1986744) (@lem1986745 y z')). Qed.
Lemma lem1986747 (y : real) (z' : real) : (term749 y z') = (term751 y z').
Proof. exact (TRANS (@lem1986739 y z') (@lem1986746 y z')). Qed.
Lemma lem1986748 (y : real) (z' : real) : (term751 y z') = term0.
Proof. exact (@lem1483446 (real_mul y z')). Qed.
Lemma lem1986749 (y : real) (z' : real) : (term749 y z') = term0.
Proof. exact (TRANS (@lem1986747 y z') (@lem1986748 y z')). Qed.
Lemma lem1986750 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986751 (y : real) (z' : real) : (term752 y z') = term167.
Proof. exact (MK_COMB (@lem1986750) (@lem1986749 y z')). Qed.
Lemma lem1986752 (y' : real) (z : real) (z' : real) : (term774 y' z z') = (term775 y' z z').
Proof. exact (@lem1483480 (term281 z y') (real_mul z y') (real_mul z z') (term281 z z')). Qed.
Lemma lem1986753 (z : real) (y' : real) : (term749 z y') = (term750 z y').
Proof. exact (@lem1483440 term189 (real_mul z y')). Qed.
Lemma lem1986755 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986756 : term197 = term0.
Proof. exact (@lem1986755 term166). Qed.
Lemma lem1986757 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986758 : term198 = term199.
Proof. exact (MK_COMB (@lem1986757) (@lem1986756)). Qed.
Lemma lem1986759 (z : real) (y' : real) : (real_mul z y') = (real_mul z y').
Proof. exact (eq_refl (real_mul z y')). Qed.
Lemma lem1986760 (z : real) (y' : real) : (term750 z y') = (term751 z y').
Proof. exact (MK_COMB (@lem1986758) (@lem1986759 z y')). Qed.
Lemma lem1986761 (z : real) (y' : real) : (term749 z y') = (term751 z y').
Proof. exact (TRANS (@lem1986753 z y') (@lem1986760 z y')). Qed.
Lemma lem1986762 (z : real) (y' : real) : (term751 z y') = term0.
Proof. exact (@lem1483446 (real_mul z y')). Qed.
Lemma lem1986763 (z : real) (y' : real) : (term749 z y') = term0.
Proof. exact (TRANS (@lem1986761 z y') (@lem1986762 z y')). Qed.
Lemma lem1986764 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1986765 (z : real) (y' : real) : (term752 z y') = term167.
Proof. exact (MK_COMB (@lem1986764) (@lem1986763 z y')). Qed.
Lemma lem1986766 (z : real) (z' : real) : (term755 z z') = (term750 z z').
Proof. exact (@lem1483442 term189 (real_mul z z')). Qed.
Lemma lem1986768 (m : nat) : (term196 m) = term0.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1986769 : term197 = term0.
Proof. exact (@lem1986768 term166). Qed.
Lemma lem1986770 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1986771 : term198 = term199.
Proof. exact (MK_COMB (@lem1986770) (@lem1986769)). Qed.
Lemma lem1986772 (z : real) (z' : real) : (real_mul z z') = (real_mul z z').
Proof. exact (eq_refl (real_mul z z')). Qed.
Lemma lem1986773 (z : real) (z' : real) : (term750 z z') = (term751 z z').
Proof. exact (MK_COMB (@lem1986771) (@lem1986772 z z')). Qed.
Lemma lem1986774 (z : real) (z' : real) : (term755 z z') = (term751 z z').
Proof. exact (TRANS (@lem1986766 z z') (@lem1986773 z z')). Qed.
Lemma lem1986775 (z : real) (z' : real) : (term751 z z') = term0.
Proof. exact (@lem1483446 (real_mul z z')). Qed.
Lemma lem1986776 (z : real) (z' : real) : (term755 z z') = term0.
Proof. exact (TRANS (@lem1986774 z z') (@lem1986775 z z')). Qed.
Lemma lem1986777 (y' : real) (z : real) (z' : real) : (term775 y' z z') = term168.
Proof. exact (MK_COMB (@lem1986765 z y') (@lem1986776 z z')). Qed.
Lemma lem1986778 (y' : real) (z : real) (z' : real) : (term774 y' z z') = term168.
Proof. exact (TRANS (@lem1986752 y' z z') (@lem1986777 y' z z')). Qed.
Lemma lem1986779 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986780 (y' : real) (z : real) (z' : real) : (term774 y' z z') = term0.
Proof. exact (TRANS (@lem1986778 y' z z') (@lem1986779)). Qed.
Lemma lem1986781 (y : real) (y' : real) (z : real) (z' : real) : (term773 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986751 y z') (@lem1986780 y' z z')). Qed.
Lemma lem1986782 (y : real) (y' : real) (z : real) (z' : real) : (term772 y y' z z') = term168.
Proof. exact (TRANS (@lem1986738 y y' z z') (@lem1986781 y y' z z')). Qed.
Lemma lem1986783 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986784 (y : real) (y' : real) (z : real) (z' : real) : (term772 y y' z z') = term0.
Proof. exact (TRANS (@lem1986782 y y' z z') (@lem1986783)). Qed.
Lemma lem1986785 (y : real) (y' : real) (z : real) (z' : real) : (term771 y y' z z') = term168.
Proof. exact (MK_COMB (@lem1986737 y y') (@lem1986784 y y' z z')). Qed.
Lemma lem1986786 (y : real) (y' : real) (z : real) (z' : real) : (term770 y y' z z') = term168.
Proof. exact (TRANS (@lem1986724 y y' z z') (@lem1986785 y y' z z')). Qed.
Lemma lem1986787 : term168 = term0.
Proof. exact (@lem1483448 term0). Qed.
Lemma lem1986788 (y : real) (y' : real) (z : real) (z' : real) : (term770 y y' z z') = term0.
Proof. exact (TRANS (@lem1986786 y y' z z') (@lem1986787)). Qed.
Lemma lem1986789 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1986790 (y : real) (y' : real) (z : real) (z' : real) : (term776 y y' z z') = term175.
Proof. exact (MK_COMB (@lem1986789) (@lem1986788 y y' z z')). Qed.
Lemma lem1986791 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1986792 (y : real) (y' : real) (z : real) (z' : real) : (term769 y y' z z') = term177.
Proof. exact (MK_COMB (@lem1986790 y y' z z') (@lem1986791)). Qed.
Lemma lem1986793 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : term177.
Proof. exact (EQ_MP (@lem1986792 y y' z z') (@lem1986723 y y' z z' h1)). Qed.
Lemma lem1986795 (n : nat) (m : nat) : (term691 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1986796 : term177 = term692.
Proof. exact (@lem1986795 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1986797 : term692 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1986798 : term177 = False.
Proof. exact (TRANS (@lem1986796) (@lem1986797)). Qed.
Lemma lem1986799 (y : real) (y' : real) (z : real) (z' : real) (h1 : term778 y y' z z') : False.
Proof. exact (EQ_MP (@lem1986798) (@lem1986793 y y' z z' h1)). Qed.
Lemma lem1986800 (y : real) (y' : real) (z : real) (z' : real) (h1 : term672 y y' z z') : False.
Proof. exact (or_elim (@lem1986515 y y' z z' h1) (fun h0 : term777 y y' z z' => @lem1986681 y y' z z' h0) (fun h0 : term778 y y' z z' => @lem1986799 y y' z z' h0)). Qed.
Lemma lem1986801 (y : real) (y' : real) (z : real) (z' : real) (h1 : term675 y y' z z') : False.
Proof. exact (or_elim (@lem1986228 y y' z z' h1) (fun h0 : term673 y y' z z' => @lem1986514 y y' z z' h0) (fun h0 : term672 y y' z z' => @lem1986800 y y' z z' h0)). Qed.
Lemma lem1986802 (y : real) (y' : real) (z : real) (z' : real) (h1 : term681 y y' z z') : False.
Proof. exact (or_elim (@lem1985851 y y' z z' h1) (fun h0 : term679 y z => @lem1986227 y z h0) (fun h0 : term675 y y' z z' => @lem1986801 y y' z z' h0)). Qed.
Lemma lem1986803 (y : real) (y' : real) (z : real) (z' : real) (h1 : term682 y y' z z') : False.
Proof. exact (or_elim (@lem1985834 y y' z z' h1) (fun h0 : term182 => @lem1985850 h0) (fun h0 : term681 y y' z z' => @lem1986802 y y' z z' h0)). Qed.
Lemma lem1986805 (y : real) (y' : real) (z : real) (z' : real) (h1 : term682 y y' z z') : term682 y y' z z'.
Proof. exact (h1). Qed.
Lemma lem1986806 (y : real) (y' : real) (z : real) (z' : real) (h1 : term682 y y' z z') : (term682 y y' z z') = False.
Proof. exact (prop_ext (fun h2 : term682 y y' z z' => @lem1986803 y y' z z' h1) (fun h2 : False => @lem1986805 y y' z z' h1)). Qed.
Lemma lem1986807 (y : real) (y' : real) (z : real) (z' : real) (h1 : term682 y y' z z') : False.
Proof. exact (EQ_MP (@lem1986806 y y' z z' h1) (@lem1986805 y y' z z' h1)). Qed.
Lemma lem1986808 (y : real) (y' : real) (z : real) (h1 : term684 y y' z) : term684 y y' z.
Proof. exact (h1). Qed.
Lemma lem1986809 (y : real) (y' : real) (z : real) (h1 : term684 y y' z) : False.
Proof. exact (ex_elim (@lem1986808 y y' z h1) (fun z' : real => fun h0 : term683 y y' z z' => @lem1986807 y y' z z' h0)). Qed.
Lemma lem1986810 (y : real) (z : real) (h1 : term686 y z) : term686 y z.
Proof. exact (h1). Qed.
Lemma lem1986811 (y : real) (z : real) (h1 : term686 y z) : False.
Proof. exact (ex_elim (@lem1986810 y z h1) (fun y' : real => fun h0 : term685 y z y' => @lem1986809 y y' z h0)). Qed.
Lemma lem1986812 (y : real) (h1 : term688 y) : term688 y.
Proof. exact (h1). Qed.
Lemma lem1986813 (y : real) (h1 : term688 y) : False.
Proof. exact (ex_elim (@lem1986812 y h1) (fun z : real => fun h0 : term687 y z => @lem1986811 y z h0)). Qed.
Lemma lem1986814 (h1 : term690) : term690.
Proof. exact (h1). Qed.
Lemma lem1986815 (h1 : term690) : False.
Proof. exact (ex_elim (@lem1986814 h1) (fun y : real => fun h0 : term689 y => @lem1986813 y h0)). Qed.
Lemma lem1986816 (h1 : term158) : term158.
Proof. exact (h1). Qed.
Lemma lem1986817 (h1 : term158) : term690.
Proof. exact (EQ_MP (@lem1985776) (@lem1986816 h1)). Qed.
Lemma lem1986818 (h1 : term158) : term690 = False.
Proof. exact (prop_ext (fun h2 : term690 => @lem1986815 h2) (fun h2 : False => @lem1986817 h1)). Qed.
Lemma lem1986819 (h1 : term158) : False.
Proof. exact (EQ_MP (@lem1986818 h1) (@lem1986817 h1)). Qed.
Lemma lem1986820 : term779.
Proof. exact (fun h0 : term158 => @lem1986819 h0). Qed.
Lemma lem1986821 : term780.
Proof. exact (@lem1386578 term85). Qed.
Lemma lem1986822 : term85.
Proof. exact (@lem1986821 (@lem1986820)). Qed.
Lemma lem1986823 : term74.
Proof. exact (EQ_MP (@lem1983279) (@lem1986822)). Qed.
Lemma lem1986826 : term73.
Proof. exact (EQ_MP (@lem1983185) (@lem1986823)). Qed.
