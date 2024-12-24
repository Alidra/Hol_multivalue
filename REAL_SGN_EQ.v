Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_EQ_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365105_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1366971_spec.
Require Import thm1366974_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483535_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996238_spec.
Lemma lem1735074 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1735075 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1735088 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1735075 x) (@lem1735074 x)). Qed.
Lemma lem1735089 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735090 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1735089) (@lem1735088 x)). Qed.
Lemma lem1735091 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735092 (x : real) : ((real_sgn x) = term4) = ((term1 x) = term4).
Proof. exact (MK_COMB (@lem1735090 x) (@lem1735091)). Qed.
Lemma lem1735095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1735096 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1735095) (@lem1735092 x)). Qed.
Lemma lem1735099 (x : real) : (x = term4) = (x = term4).
Proof. exact (eq_refl (x = term4)). Qed.
Lemma lem1735100 (x : real) : (((real_sgn x) = term4) = (x = term4)) = (((term1 x) = term4) = (x = term4)).
Proof. exact (MK_COMB (@lem1735096 x) (@lem1735099 x)). Qed.
Lemma lem1735103 : term7 = term8.
Proof. exact (fun_ext (fun x : real => @lem1735100 x)). Qed.
Lemma lem1735104 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1735105 : term9 = term10.
Proof. exact (MK_COMB (@lem1735104) (@lem1735103)). Qed.
Lemma lem1735110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735111 : term11 = term12.
Proof. exact (MK_COMB (@lem1735110) (@lem1735105)). Qed.
Lemma lem1735123 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1735075 x) (@lem1735074 x)). Qed.
Lemma lem1735124 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735125 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1735124) (@lem1735123 x)). Qed.
Lemma lem1735126 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735127 (x : real) : ((real_sgn x) = term13) = ((term1 x) = term13).
Proof. exact (MK_COMB (@lem1735125 x) (@lem1735126)). Qed.
Lemma lem1735130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1735131 (x : real) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1735130) (@lem1735127 x)). Qed.
Lemma lem1735132 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1735133 (x : real) : (((real_sgn x) = term13) = (term16 x)) = (((term1 x) = term13) = (term16 x)).
Proof. exact (MK_COMB (@lem1735131 x) (@lem1735132 x)). Qed.
Lemma lem1735136 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem1735133 x)). Qed.
Lemma lem1735137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1735138 : term19 = term20.
Proof. exact (MK_COMB (@lem1735137) (@lem1735136)). Qed.
Lemma lem1735143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735144 : term21 = term22.
Proof. exact (MK_COMB (@lem1735143) (@lem1735138)). Qed.
Lemma lem1735154 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1735075 x) (@lem1735074 x)). Qed.
Lemma lem1735155 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735156 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1735155) (@lem1735154 x)). Qed.
Lemma lem1735157 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735158 (x : real) : ((real_sgn x) = term23) = ((term1 x) = term23).
Proof. exact (MK_COMB (@lem1735156 x) (@lem1735157)). Qed.
Lemma lem1735161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1735162 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1735161) (@lem1735158 x)). Qed.
Lemma lem1735163 (x : real) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1735164 (x : real) : (((real_sgn x) = term23) = (term26 x)) = (((term1 x) = term23) = (term26 x)).
Proof. exact (MK_COMB (@lem1735162 x) (@lem1735163 x)). Qed.
Lemma lem1735167 : term27 = term28.
Proof. exact (fun_ext (fun x : real => @lem1735164 x)). Qed.
Lemma lem1735168 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1735169 : term29 = term30.
Proof. exact (MK_COMB (@lem1735168) (@lem1735167)). Qed.
Lemma lem1735174 : term31 = term32.
Proof. exact (MK_COMB (@lem1735144) (@lem1735169)). Qed.
Lemma lem1735177 : term33 = term34.
Proof. exact (MK_COMB (@lem1735111) (@lem1735174)). Qed.
Lemma lem1735180 : term34 = term33.
Proof. exact (SYM (@lem1735177)). Qed.
Lemma lem1735214 (x : real) : (term35 x) = (term36 x).
Proof. exact (@lem17646 ((term1 x) = term4) (x = term4)). Qed.
Lemma lem1735215 (P : real -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1735216 : term39 = term40.
Proof. exact (@lem1735215 term8). Qed.
Lemma lem1735217 (x : real) : (term41 x) = (((term1 x) = term4) = (x = term4)).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1735218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735219 (x : real) : (term42 x) = (term35 x).
Proof. exact (MK_COMB (@lem1735218) (@lem1735217 x)). Qed.
Lemma lem1735220 (x : real) : (term42 x) = (term36 x).
Proof. exact (TRANS (@lem1735219 x) (@lem1735214 x)). Qed.
Lemma lem1735221 : term43 = term44.
Proof. exact (fun_ext (fun x : real => @lem1735220 x)). Qed.
Lemma lem1735222 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1735223 : term40 = term45.
Proof. exact (MK_COMB (@lem1735222) (@lem1735221)). Qed.
Lemma lem1735224 : term39 = term45.
Proof. exact (TRANS (@lem1735216) (@lem1735223)). Qed.
Lemma lem1735239 (x : real) : (term46 x) = (term47 x).
Proof. exact (@lem17646 ((term1 x) = term13) (term16 x)). Qed.
Lemma lem1735240 (P : real -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1735241 : term48 = term49.
Proof. exact (@lem1735240 term18). Qed.
Lemma lem1735242 (x : real) : (term50 x) = (((term1 x) = term13) = (term16 x)).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1735243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735244 (x : real) : (term51 x) = (term46 x).
Proof. exact (MK_COMB (@lem1735243) (@lem1735242 x)). Qed.
Lemma lem1735245 (x : real) : (term51 x) = (term47 x).
Proof. exact (TRANS (@lem1735244 x) (@lem1735239 x)). Qed.
Lemma lem1735246 : term52 = term53.
Proof. exact (fun_ext (fun x : real => @lem1735245 x)). Qed.
Lemma lem1735247 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1735248 : term49 = term54.
Proof. exact (MK_COMB (@lem1735247) (@lem1735246)). Qed.
Lemma lem1735249 : term48 = term54.
Proof. exact (TRANS (@lem1735241) (@lem1735248)). Qed.
Lemma lem1735264 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem17646 ((term1 x) = term23) (term26 x)). Qed.
Lemma lem1735265 (P : real -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1735266 : term57 = term58.
Proof. exact (@lem1735265 term28). Qed.
Lemma lem1735267 (x : real) : (term59 x) = (((term1 x) = term23) = (term26 x)).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1735268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735269 (x : real) : (term60 x) = (term55 x).
Proof. exact (MK_COMB (@lem1735268) (@lem1735267 x)). Qed.
Lemma lem1735270 (x : real) : (term60 x) = (term56 x).
Proof. exact (TRANS (@lem1735269 x) (@lem1735264 x)). Qed.
Lemma lem1735271 : term61 = term62.
Proof. exact (fun_ext (fun x : real => @lem1735270 x)). Qed.
Lemma lem1735272 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1735273 : term58 = term63.
Proof. exact (MK_COMB (@lem1735272) (@lem1735271)). Qed.
Lemma lem1735274 : term57 = term63.
Proof. exact (TRANS (@lem1735266) (@lem1735273)). Qed.
Lemma lem1735275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735276 : term64 = term65.
Proof. exact (MK_COMB (@lem1735275) (@lem1735249)). Qed.
Lemma lem1735277 : term66 = term67.
Proof. exact (MK_COMB (@lem1735276) (@lem1735274)). Qed.
Lemma lem1735278 : term68 = term66.
Proof. exact (@lem17045 term20 term30). Qed.
Lemma lem1735279 : term68 = term67.
Proof. exact (TRANS (@lem1735278) (@lem1735277)). Qed.
Lemma lem1735280 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735281 : term69 = term70.
Proof. exact (MK_COMB (@lem1735280) (@lem1735224)). Qed.
Lemma lem1735282 : term71 = term72.
Proof. exact (MK_COMB (@lem1735281) (@lem1735279)). Qed.
Lemma lem1735283 : term73 = term71.
Proof. exact (@lem17045 term10 term32). Qed.
Lemma lem1735285 : term73 = term72.
Proof. exact (TRANS (@lem1735283) (@lem1735282)). Qed.
Lemma lem1735289 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735290 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735291 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735290) (@lem1735289 x h1)). Qed.
Lemma lem1735292 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735293 (x : real) (h1 : (term74 x) = False) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1735291 x h1) (@lem1735292)). Qed.
Lemma lem1735294 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735295 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1735293 x h1) (@lem1735294 x)). Qed.
Lemma lem1735297 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735298 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735297 real t1 t2). Qed.
Lemma lem1735299 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1735298 term13 (term78 x)). Qed.
Lemma lem1735300 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term78 x).
Proof. exact (TRANS (@lem1735295 x h1) (@lem1735299 x)). Qed.
Lemma lem1735301 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735302 (x : real) (h1 : (term74 x) = False) : (term3 x) = (term80 x).
Proof. exact (MK_COMB (@lem1735301) (@lem1735300 x h1)). Qed.
Lemma lem1735303 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735304 (x : real) (h1 : (term74 x) = False) : ((term1 x) = term4) = ((term78 x) = term4).
Proof. exact (MK_COMB (@lem1735302 x h1) (@lem1735303)). Qed.
Lemma lem1735307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735308 (x : real) (h1 : (term74 x) = False) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1735307) (@lem1735304 x h1)). Qed.
Lemma lem1735311 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1735312 (x : real) (h1 : (term74 x) = False) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1735308 x h1) (@lem1735311 x)). Qed.
Lemma lem1735315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735316 (x : real) (h1 : (term74 x) = False) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1735315) (@lem1735312 x h1)). Qed.
Lemma lem1735318 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735319 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735320 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735319) (@lem1735318 x h1)). Qed.
Lemma lem1735321 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735322 (x : real) (h1 : (term74 x) = False) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1735320 x h1) (@lem1735321)). Qed.
Lemma lem1735323 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735324 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1735322 x h1) (@lem1735323 x)). Qed.
Lemma lem1735326 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735327 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735326 real t1 t2). Qed.
Lemma lem1735328 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1735327 term13 (term78 x)). Qed.
Lemma lem1735329 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term78 x).
Proof. exact (TRANS (@lem1735324 x h1) (@lem1735328 x)). Qed.
Lemma lem1735330 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735331 (x : real) (h1 : (term74 x) = False) : (term3 x) = (term80 x).
Proof. exact (MK_COMB (@lem1735330) (@lem1735329 x h1)). Qed.
Lemma lem1735332 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735333 (x : real) (h1 : (term74 x) = False) : ((term1 x) = term4) = ((term78 x) = term4).
Proof. exact (MK_COMB (@lem1735331 x h1) (@lem1735332)). Qed.
Lemma lem1735336 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735337 (x : real) (h1 : (term74 x) = False) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1735336) (@lem1735333 x h1)). Qed.
Lemma lem1735338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735339 (x : real) (h1 : (term74 x) = False) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem1735338) (@lem1735337 x h1)). Qed.
Lemma lem1735342 (x : real) : (x = term4) = (x = term4).
Proof. exact (eq_refl (x = term4)). Qed.
Lemma lem1735343 (x : real) (h1 : (term74 x) = False) : (term92 x) = (term93 x).
Proof. exact (MK_COMB (@lem1735339 x h1) (@lem1735342 x)). Qed.
Lemma lem1735346 (x : real) (h1 : (term74 x) = False) : (term36 x) = (term94 x).
Proof. exact (MK_COMB (@lem1735316 x h1) (@lem1735343 x h1)). Qed.
Lemma lem1735349 (x : real) : term95 x.
Proof. exact (fun h0 : (term74 x) = False => @lem1735346 x h0). Qed.
Lemma lem1735351 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735352 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735353 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735352) (@lem1735351 x h1)). Qed.
Lemma lem1735354 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735355 (x : real) (h1 : (term74 x) = True) : (term76 x) = term96.
Proof. exact (MK_COMB (@lem1735353 x h1) (@lem1735354)). Qed.
Lemma lem1735356 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735357 (x : real) (h1 : (term74 x) = True) : (term1 x) = (term97 x).
Proof. exact (MK_COMB (@lem1735355 x h1) (@lem1735356 x)). Qed.
Lemma lem1735359 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735360 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735359 real t2 t1). Qed.
Lemma lem1735361 (x : real) : (term97 x) = term13.
Proof. exact (@lem1735360 (term78 x) term13). Qed.
Lemma lem1735362 (x : real) (h1 : (term74 x) = True) : (term1 x) = term13.
Proof. exact (TRANS (@lem1735357 x h1) (@lem1735361 x)). Qed.
Lemma lem1735363 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735364 (x : real) (h1 : (term74 x) = True) : (term3 x) = term98.
Proof. exact (MK_COMB (@lem1735363) (@lem1735362 x h1)). Qed.
Lemma lem1735365 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735366 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term4) = (term13 = term4).
Proof. exact (MK_COMB (@lem1735364 x h1) (@lem1735365)). Qed.
Lemma lem1735369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735370 (x : real) (h1 : (term74 x) = True) : (term81 x) = term99.
Proof. exact (MK_COMB (@lem1735369) (@lem1735366 x h1)). Qed.
Lemma lem1735373 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1735374 (x : real) (h1 : (term74 x) = True) : (term84 x) = (term100 x).
Proof. exact (MK_COMB (@lem1735370 x h1) (@lem1735373 x)). Qed.
Lemma lem1735377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735378 (x : real) (h1 : (term74 x) = True) : (term86 x) = (term101 x).
Proof. exact (MK_COMB (@lem1735377) (@lem1735374 x h1)). Qed.
Lemma lem1735380 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735381 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735382 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735381) (@lem1735380 x h1)). Qed.
Lemma lem1735383 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735384 (x : real) (h1 : (term74 x) = True) : (term76 x) = term96.
Proof. exact (MK_COMB (@lem1735382 x h1) (@lem1735383)). Qed.
Lemma lem1735385 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735386 (x : real) (h1 : (term74 x) = True) : (term1 x) = (term97 x).
Proof. exact (MK_COMB (@lem1735384 x h1) (@lem1735385 x)). Qed.
Lemma lem1735388 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735389 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735388 real t2 t1). Qed.
Lemma lem1735390 (x : real) : (term97 x) = term13.
Proof. exact (@lem1735389 (term78 x) term13). Qed.
Lemma lem1735391 (x : real) (h1 : (term74 x) = True) : (term1 x) = term13.
Proof. exact (TRANS (@lem1735386 x h1) (@lem1735390 x)). Qed.
Lemma lem1735392 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735393 (x : real) (h1 : (term74 x) = True) : (term3 x) = term98.
Proof. exact (MK_COMB (@lem1735392) (@lem1735391 x h1)). Qed.
Lemma lem1735394 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735395 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term4) = (term13 = term4).
Proof. exact (MK_COMB (@lem1735393 x h1) (@lem1735394)). Qed.
Lemma lem1735398 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735399 (x : real) (h1 : (term74 x) = True) : (term88 x) = term102.
Proof. exact (MK_COMB (@lem1735398) (@lem1735395 x h1)). Qed.
Lemma lem1735400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735401 (x : real) (h1 : (term74 x) = True) : (term90 x) = term103.
Proof. exact (MK_COMB (@lem1735400) (@lem1735399 x h1)). Qed.
Lemma lem1735404 (x : real) : (x = term4) = (x = term4).
Proof. exact (eq_refl (x = term4)). Qed.
Lemma lem1735405 (x : real) (h1 : (term74 x) = True) : (term92 x) = (term104 x).
Proof. exact (MK_COMB (@lem1735401 x h1) (@lem1735404 x)). Qed.
Lemma lem1735408 (x : real) (h1 : (term74 x) = True) : (term36 x) = (term105 x).
Proof. exact (MK_COMB (@lem1735378 x h1) (@lem1735405 x h1)). Qed.
Lemma lem1735411 (x : real) : term106 x.
Proof. exact (fun h0 : (term74 x) = True => @lem1735408 x h0). Qed.
Lemma lem1735412 (x : real) : term107 x.
Proof. exact (conj (@lem1735349 x) (@lem1735411 x)). Qed.
Lemma lem1735414 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term108 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1735415 (x : real) : term109 x.
Proof. exact (@lem1735414 (term36 x) (term105 x) (term74 x) (term94 x)). Qed.
Lemma lem1735430 (x : real) : (term36 x) = (term110 x).
Proof. exact (@lem1735415 x (@lem1735412 x)). Qed.
Lemma lem1735450 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735451 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735452 (x : real) (h1 : (term26 x) = False) : (term111 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735451) (@lem1735450 x h1)). Qed.
Lemma lem1735453 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735454 (x : real) (h1 : (term26 x) = False) : (term112 x) = term113.
Proof. exact (MK_COMB (@lem1735452 x h1) (@lem1735453)). Qed.
Lemma lem1735455 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735456 (x : real) (h1 : (term26 x) = False) : (term78 x) = term114.
Proof. exact (MK_COMB (@lem1735454 x h1) (@lem1735455)). Qed.
Lemma lem1735458 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735459 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735458 real t1 t2). Qed.
Lemma lem1735460 : term114 = term4.
Proof. exact (@lem1735459 term23 term4). Qed.
Lemma lem1735461 (x : real) (h1 : (term26 x) = False) : (term78 x) = term4.
Proof. exact (TRANS (@lem1735456 x h1) (@lem1735460)). Qed.
Lemma lem1735462 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735463 (x : real) (h1 : (term26 x) = False) : (term80 x) = term115.
Proof. exact (MK_COMB (@lem1735462) (@lem1735461 x h1)). Qed.
Lemma lem1735464 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735465 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term4) = (term4 = term4).
Proof. exact (MK_COMB (@lem1735463 x h1) (@lem1735464)). Qed.
Lemma lem1735467 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1735468 (x : real) : (x = x) = True.
Proof. exact (@lem1735467 real x). Qed.
Lemma lem1735469 : (term4 = term4) = True.
Proof. exact (@lem1735468 term4). Qed.
Lemma lem1735470 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term4) = True.
Proof. exact (TRANS (@lem1735465 x h1) (@lem1735469)). Qed.
Lemma lem1735471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735472 (x : real) (h1 : (term26 x) = False) : (term82 x) = (and True).
Proof. exact (MK_COMB (@lem1735471) (@lem1735470 x h1)). Qed.
Lemma lem1735475 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1735476 (x : real) (h1 : (term26 x) = False) : (term85 x) = (term116 x).
Proof. exact (MK_COMB (@lem1735472 x h1) (@lem1735475 x)). Qed.
Lemma lem1735478 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1735479 (x : real) : (term116 x) = (term83 x).
Proof. exact (@lem1735478 (term83 x)). Qed.
Lemma lem1735480 (x : real) (h1 : (term26 x) = False) : (term85 x) = (term83 x).
Proof. exact (TRANS (@lem1735476 x h1) (@lem1735479 x)). Qed.
Lemma lem1735481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735482 (x : real) (h1 : (term26 x) = False) : (term87 x) = (term117 x).
Proof. exact (MK_COMB (@lem1735481) (@lem1735480 x h1)). Qed.
Lemma lem1735484 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735485 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735486 (x : real) (h1 : (term26 x) = False) : (term111 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735485) (@lem1735484 x h1)). Qed.
Lemma lem1735487 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735488 (x : real) (h1 : (term26 x) = False) : (term112 x) = term113.
Proof. exact (MK_COMB (@lem1735486 x h1) (@lem1735487)). Qed.
Lemma lem1735489 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735490 (x : real) (h1 : (term26 x) = False) : (term78 x) = term114.
Proof. exact (MK_COMB (@lem1735488 x h1) (@lem1735489)). Qed.
Lemma lem1735492 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735493 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735492 real t1 t2). Qed.
Lemma lem1735494 : term114 = term4.
Proof. exact (@lem1735493 term23 term4). Qed.
Lemma lem1735495 (x : real) (h1 : (term26 x) = False) : (term78 x) = term4.
Proof. exact (TRANS (@lem1735490 x h1) (@lem1735494)). Qed.
Lemma lem1735496 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735497 (x : real) (h1 : (term26 x) = False) : (term80 x) = term115.
Proof. exact (MK_COMB (@lem1735496) (@lem1735495 x h1)). Qed.
Lemma lem1735498 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735499 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term4) = (term4 = term4).
Proof. exact (MK_COMB (@lem1735497 x h1) (@lem1735498)). Qed.
Lemma lem1735501 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1735502 (x : real) : (x = x) = True.
Proof. exact (@lem1735501 real x). Qed.
Lemma lem1735503 : (term4 = term4) = True.
Proof. exact (@lem1735502 term4). Qed.
Lemma lem1735504 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term4) = True.
Proof. exact (TRANS (@lem1735499 x h1) (@lem1735503)). Qed.
Lemma lem1735505 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735506 (x : real) (h1 : (term26 x) = False) : (term89 x) = (~ True).
Proof. exact (MK_COMB (@lem1735505) (@lem1735504 x h1)). Qed.
Lemma lem1735508 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1735509 (x : real) (h1 : (term26 x) = False) : (term89 x) = False.
Proof. exact (TRANS (@lem1735506 x h1) (@lem1735508)). Qed.
Lemma lem1735510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735511 (x : real) (h1 : (term26 x) = False) : (term91 x) = (and False).
Proof. exact (MK_COMB (@lem1735510) (@lem1735509 x h1)). Qed.
Lemma lem1735514 (x : real) : (x = term4) = (x = term4).
Proof. exact (eq_refl (x = term4)). Qed.
Lemma lem1735515 (x : real) (h1 : (term26 x) = False) : (term93 x) = (term118 x).
Proof. exact (MK_COMB (@lem1735511 x h1) (@lem1735514 x)). Qed.
Lemma lem1735517 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1735518 (x : real) : (term118 x) = False.
Proof. exact (@lem1735517 (x = term4)). Qed.
Lemma lem1735519 (x : real) (h1 : (term26 x) = False) : (term93 x) = False.
Proof. exact (TRANS (@lem1735515 x h1) (@lem1735518 x)). Qed.
Lemma lem1735520 (x : real) (h1 : (term26 x) = False) : (term94 x) = (term119 x).
Proof. exact (MK_COMB (@lem1735482 x h1) (@lem1735519 x h1)). Qed.
Lemma lem1735522 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1735523 (x : real) : (term119 x) = (term83 x).
Proof. exact (@lem1735522 (term83 x)). Qed.
Lemma lem1735524 (x : real) (h1 : (term26 x) = False) : (term94 x) = (term83 x).
Proof. exact (TRANS (@lem1735520 x h1) (@lem1735523 x)). Qed.
Lemma lem1735525 (x : real) : (term120 x) = (term120 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1735526 (x : real) (h1 : (term26 x) = False) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1735525 x) (@lem1735524 x h1)). Qed.
Lemma lem1735529 (x : real) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1735530 (x : real) (h1 : (term26 x) = False) : (term110 x) = (term124 x).
Proof. exact (MK_COMB (@lem1735529 x) (@lem1735526 x h1)). Qed.
Lemma lem1735533 (x : real) : term125 x.
Proof. exact (fun h0 : (term26 x) = False => @lem1735530 x h0). Qed.
Lemma lem1735551 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735552 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735553 (x : real) (h1 : (term26 x) = True) : (term111 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735552) (@lem1735551 x h1)). Qed.
Lemma lem1735554 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735555 (x : real) (h1 : (term26 x) = True) : (term112 x) = term126.
Proof. exact (MK_COMB (@lem1735553 x h1) (@lem1735554)). Qed.
Lemma lem1735556 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735557 (x : real) (h1 : (term26 x) = True) : (term78 x) = term127.
Proof. exact (MK_COMB (@lem1735555 x h1) (@lem1735556)). Qed.
Lemma lem1735559 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735560 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735559 real t2 t1). Qed.
Lemma lem1735561 : term127 = term23.
Proof. exact (@lem1735560 term4 term23). Qed.
Lemma lem1735562 (x : real) (h1 : (term26 x) = True) : (term78 x) = term23.
Proof. exact (TRANS (@lem1735557 x h1) (@lem1735561)). Qed.
Lemma lem1735563 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735564 (x : real) (h1 : (term26 x) = True) : (term80 x) = term128.
Proof. exact (MK_COMB (@lem1735563) (@lem1735562 x h1)). Qed.
Lemma lem1735565 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735566 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term4) = (term23 = term4).
Proof. exact (MK_COMB (@lem1735564 x h1) (@lem1735565)). Qed.
Lemma lem1735569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735570 (x : real) (h1 : (term26 x) = True) : (term82 x) = term129.
Proof. exact (MK_COMB (@lem1735569) (@lem1735566 x h1)). Qed.
Lemma lem1735573 (x : real) : (term83 x) = (term83 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1735574 (x : real) (h1 : (term26 x) = True) : (term85 x) = (term130 x).
Proof. exact (MK_COMB (@lem1735570 x h1) (@lem1735573 x)). Qed.
Lemma lem1735577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735578 (x : real) (h1 : (term26 x) = True) : (term87 x) = (term131 x).
Proof. exact (MK_COMB (@lem1735577) (@lem1735574 x h1)). Qed.
Lemma lem1735580 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735581 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735582 (x : real) (h1 : (term26 x) = True) : (term111 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735581) (@lem1735580 x h1)). Qed.
Lemma lem1735583 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735584 (x : real) (h1 : (term26 x) = True) : (term112 x) = term126.
Proof. exact (MK_COMB (@lem1735582 x h1) (@lem1735583)). Qed.
Lemma lem1735585 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735586 (x : real) (h1 : (term26 x) = True) : (term78 x) = term127.
Proof. exact (MK_COMB (@lem1735584 x h1) (@lem1735585)). Qed.
Lemma lem1735588 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735589 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735588 real t2 t1). Qed.
Lemma lem1735590 : term127 = term23.
Proof. exact (@lem1735589 term4 term23). Qed.
Lemma lem1735591 (x : real) (h1 : (term26 x) = True) : (term78 x) = term23.
Proof. exact (TRANS (@lem1735586 x h1) (@lem1735590)). Qed.
Lemma lem1735592 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735593 (x : real) (h1 : (term26 x) = True) : (term80 x) = term128.
Proof. exact (MK_COMB (@lem1735592) (@lem1735591 x h1)). Qed.
Lemma lem1735594 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735595 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term4) = (term23 = term4).
Proof. exact (MK_COMB (@lem1735593 x h1) (@lem1735594)). Qed.
Lemma lem1735598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735599 (x : real) (h1 : (term26 x) = True) : (term89 x) = term132.
Proof. exact (MK_COMB (@lem1735598) (@lem1735595 x h1)). Qed.
Lemma lem1735600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735601 (x : real) (h1 : (term26 x) = True) : (term91 x) = term133.
Proof. exact (MK_COMB (@lem1735600) (@lem1735599 x h1)). Qed.
Lemma lem1735604 (x : real) : (x = term4) = (x = term4).
Proof. exact (eq_refl (x = term4)). Qed.
Lemma lem1735605 (x : real) (h1 : (term26 x) = True) : (term93 x) = (term134 x).
Proof. exact (MK_COMB (@lem1735601 x h1) (@lem1735604 x)). Qed.
Lemma lem1735608 (x : real) (h1 : (term26 x) = True) : (term94 x) = (term135 x).
Proof. exact (MK_COMB (@lem1735578 x h1) (@lem1735605 x h1)). Qed.
Lemma lem1735611 (x : real) : (term120 x) = (term120 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1735612 (x : real) (h1 : (term26 x) = True) : (term121 x) = (term136 x).
Proof. exact (MK_COMB (@lem1735611 x) (@lem1735608 x h1)). Qed.
Lemma lem1735615 (x : real) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1735616 (x : real) (h1 : (term26 x) = True) : (term110 x) = (term137 x).
Proof. exact (MK_COMB (@lem1735615 x) (@lem1735612 x h1)). Qed.
Lemma lem1735619 (x : real) : term138 x.
Proof. exact (fun h0 : (term26 x) = True => @lem1735616 x h0). Qed.
Lemma lem1735620 (x : real) : term139 x.
Proof. exact (conj (@lem1735533 x) (@lem1735619 x)). Qed.
Lemma lem1735622 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term108 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1735623 (x : real) : term140 x.
Proof. exact (@lem1735622 (term110 x) (term137 x) (term26 x) (term124 x)). Qed.
Lemma lem1735734 (x : real) : (term110 x) = (term141 x).
Proof. exact (@lem1735623 x (@lem1735620 x)). Qed.
Lemma lem1735735 (x : real) : (term142 x) = (term142 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1735736 (x : real) : ((term36 x) = (term110 x)) = ((term36 x) = (term141 x)).
Proof. exact (MK_COMB (@lem1735735 x) (@lem1735734 x)). Qed.
Lemma lem1735737 (x : real) : (term36 x) = (term141 x).
Proof. exact (EQ_MP (@lem1735736 x) (@lem1735430 x)). Qed.
Lemma lem1735738 : term44 = term143.
Proof. exact (fun_ext (fun x : real => @lem1735737 x)). Qed.
Lemma lem1735739 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1735740 : term45 = term144.
Proof. exact (MK_COMB (@lem1735739) (@lem1735738)). Qed.
Lemma lem1735744 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735745 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735746 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735745) (@lem1735744 x h1)). Qed.
Lemma lem1735747 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735748 (x : real) (h1 : (term74 x) = False) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1735746 x h1) (@lem1735747)). Qed.
Lemma lem1735749 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735750 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1735748 x h1) (@lem1735749 x)). Qed.
Lemma lem1735752 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735753 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735752 real t1 t2). Qed.
Lemma lem1735754 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1735753 term13 (term78 x)). Qed.
Lemma lem1735755 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term78 x).
Proof. exact (TRANS (@lem1735750 x h1) (@lem1735754 x)). Qed.
Lemma lem1735756 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735757 (x : real) (h1 : (term74 x) = False) : (term3 x) = (term80 x).
Proof. exact (MK_COMB (@lem1735756) (@lem1735755 x h1)). Qed.
Lemma lem1735758 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735759 (x : real) (h1 : (term74 x) = False) : ((term1 x) = term13) = ((term78 x) = term13).
Proof. exact (MK_COMB (@lem1735757 x h1) (@lem1735758)). Qed.
Lemma lem1735762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735763 (x : real) (h1 : (term74 x) = False) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1735762) (@lem1735759 x h1)). Qed.
Lemma lem1735764 (x : real) : (term147 x) = (term147 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1735765 (x : real) (h1 : (term74 x) = False) : (term148 x) = (term149 x).
Proof. exact (MK_COMB (@lem1735763 x h1) (@lem1735764 x)). Qed.
Lemma lem1735768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735769 (x : real) (h1 : (term74 x) = False) : (term150 x) = (term151 x).
Proof. exact (MK_COMB (@lem1735768) (@lem1735765 x h1)). Qed.
Lemma lem1735771 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735772 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735773 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735772) (@lem1735771 x h1)). Qed.
Lemma lem1735774 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735775 (x : real) (h1 : (term74 x) = False) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1735773 x h1) (@lem1735774)). Qed.
Lemma lem1735776 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735777 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1735775 x h1) (@lem1735776 x)). Qed.
Lemma lem1735779 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735780 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735779 real t1 t2). Qed.
Lemma lem1735781 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1735780 term13 (term78 x)). Qed.
Lemma lem1735782 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term78 x).
Proof. exact (TRANS (@lem1735777 x h1) (@lem1735781 x)). Qed.
Lemma lem1735783 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735784 (x : real) (h1 : (term74 x) = False) : (term3 x) = (term80 x).
Proof. exact (MK_COMB (@lem1735783) (@lem1735782 x h1)). Qed.
Lemma lem1735785 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735786 (x : real) (h1 : (term74 x) = False) : ((term1 x) = term13) = ((term78 x) = term13).
Proof. exact (MK_COMB (@lem1735784 x h1) (@lem1735785)). Qed.
Lemma lem1735789 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735790 (x : real) (h1 : (term74 x) = False) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1735789) (@lem1735786 x h1)). Qed.
Lemma lem1735791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735792 (x : real) (h1 : (term74 x) = False) : (term154 x) = (term155 x).
Proof. exact (MK_COMB (@lem1735791) (@lem1735790 x h1)). Qed.
Lemma lem1735793 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1735794 (x : real) (h1 : (term74 x) = False) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1735792 x h1) (@lem1735793 x)). Qed.
Lemma lem1735797 (x : real) (h1 : (term74 x) = False) : (term47 x) = (term158 x).
Proof. exact (MK_COMB (@lem1735769 x h1) (@lem1735794 x h1)). Qed.
Lemma lem1735800 (x : real) : term159 x.
Proof. exact (fun h0 : (term74 x) = False => @lem1735797 x h0). Qed.
Lemma lem1735802 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735803 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735804 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735803) (@lem1735802 x h1)). Qed.
Lemma lem1735805 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735806 (x : real) (h1 : (term74 x) = True) : (term76 x) = term96.
Proof. exact (MK_COMB (@lem1735804 x h1) (@lem1735805)). Qed.
Lemma lem1735807 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735808 (x : real) (h1 : (term74 x) = True) : (term1 x) = (term97 x).
Proof. exact (MK_COMB (@lem1735806 x h1) (@lem1735807 x)). Qed.
Lemma lem1735810 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735811 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735810 real t2 t1). Qed.
Lemma lem1735812 (x : real) : (term97 x) = term13.
Proof. exact (@lem1735811 (term78 x) term13). Qed.
Lemma lem1735813 (x : real) (h1 : (term74 x) = True) : (term1 x) = term13.
Proof. exact (TRANS (@lem1735808 x h1) (@lem1735812 x)). Qed.
Lemma lem1735814 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735815 (x : real) (h1 : (term74 x) = True) : (term3 x) = term98.
Proof. exact (MK_COMB (@lem1735814) (@lem1735813 x h1)). Qed.
Lemma lem1735816 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735817 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term13) = (term13 = term13).
Proof. exact (MK_COMB (@lem1735815 x h1) (@lem1735816)). Qed.
Lemma lem1735819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1735820 (x : real) : (x = x) = True.
Proof. exact (@lem1735819 real x). Qed.
Lemma lem1735821 : (term13 = term13) = True.
Proof. exact (@lem1735820 term13). Qed.
Lemma lem1735822 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term13) = True.
Proof. exact (TRANS (@lem1735817 x h1) (@lem1735821)). Qed.
Lemma lem1735823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735824 (x : real) (h1 : (term74 x) = True) : (term145 x) = (and True).
Proof. exact (MK_COMB (@lem1735823) (@lem1735822 x h1)). Qed.
Lemma lem1735825 (x : real) : (term147 x) = (term147 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1735826 (x : real) (h1 : (term74 x) = True) : (term148 x) = (term160 x).
Proof. exact (MK_COMB (@lem1735824 x h1) (@lem1735825 x)). Qed.
Lemma lem1735828 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1735829 (x : real) : (term160 x) = (term147 x).
Proof. exact (@lem1735828 (term147 x)). Qed.
Lemma lem1735830 (x : real) (h1 : (term74 x) = True) : (term148 x) = (term147 x).
Proof. exact (TRANS (@lem1735826 x h1) (@lem1735829 x)). Qed.
Lemma lem1735831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735832 (x : real) (h1 : (term74 x) = True) : (term150 x) = (term161 x).
Proof. exact (MK_COMB (@lem1735831) (@lem1735830 x h1)). Qed.
Lemma lem1735834 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735835 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735836 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735835) (@lem1735834 x h1)). Qed.
Lemma lem1735837 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735838 (x : real) (h1 : (term74 x) = True) : (term76 x) = term96.
Proof. exact (MK_COMB (@lem1735836 x h1) (@lem1735837)). Qed.
Lemma lem1735839 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1735840 (x : real) (h1 : (term74 x) = True) : (term1 x) = (term97 x).
Proof. exact (MK_COMB (@lem1735838 x h1) (@lem1735839 x)). Qed.
Lemma lem1735842 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735843 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735842 real t2 t1). Qed.
Lemma lem1735844 (x : real) : (term97 x) = term13.
Proof. exact (@lem1735843 (term78 x) term13). Qed.
Lemma lem1735845 (x : real) (h1 : (term74 x) = True) : (term1 x) = term13.
Proof. exact (TRANS (@lem1735840 x h1) (@lem1735844 x)). Qed.
Lemma lem1735846 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735847 (x : real) (h1 : (term74 x) = True) : (term3 x) = term98.
Proof. exact (MK_COMB (@lem1735846) (@lem1735845 x h1)). Qed.
Lemma lem1735848 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735849 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term13) = (term13 = term13).
Proof. exact (MK_COMB (@lem1735847 x h1) (@lem1735848)). Qed.
Lemma lem1735851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1735852 (x : real) : (x = x) = True.
Proof. exact (@lem1735851 real x). Qed.
Lemma lem1735853 : (term13 = term13) = True.
Proof. exact (@lem1735852 term13). Qed.
Lemma lem1735854 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term13) = True.
Proof. exact (TRANS (@lem1735849 x h1) (@lem1735853)). Qed.
Lemma lem1735855 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735856 (x : real) (h1 : (term74 x) = True) : (term152 x) = (~ True).
Proof. exact (MK_COMB (@lem1735855) (@lem1735854 x h1)). Qed.
Lemma lem1735858 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1735859 (x : real) (h1 : (term74 x) = True) : (term152 x) = False.
Proof. exact (TRANS (@lem1735856 x h1) (@lem1735858)). Qed.
Lemma lem1735860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735861 (x : real) (h1 : (term74 x) = True) : (term154 x) = (and False).
Proof. exact (MK_COMB (@lem1735860) (@lem1735859 x h1)). Qed.
Lemma lem1735862 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1735863 (x : real) (h1 : (term74 x) = True) : (term156 x) = (term162 x).
Proof. exact (MK_COMB (@lem1735861 x h1) (@lem1735862 x)). Qed.
Lemma lem1735865 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1735866 (x : real) : (term162 x) = False.
Proof. exact (@lem1735865 (term16 x)). Qed.
Lemma lem1735867 (x : real) (h1 : (term74 x) = True) : (term156 x) = False.
Proof. exact (TRANS (@lem1735863 x h1) (@lem1735866 x)). Qed.
Lemma lem1735868 (x : real) (h1 : (term74 x) = True) : (term47 x) = (term163 x).
Proof. exact (MK_COMB (@lem1735832 x h1) (@lem1735867 x h1)). Qed.
Lemma lem1735870 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1735871 (x : real) : (term163 x) = (term147 x).
Proof. exact (@lem1735870 (term147 x)). Qed.
Lemma lem1735872 (x : real) (h1 : (term74 x) = True) : (term47 x) = (term147 x).
Proof. exact (TRANS (@lem1735868 x h1) (@lem1735871 x)). Qed.
Lemma lem1735873 (x : real) : term164 x.
Proof. exact (fun h0 : (term74 x) = True => @lem1735872 x h0). Qed.
Lemma lem1735874 (x : real) : term165 x.
Proof. exact (conj (@lem1735800 x) (@lem1735873 x)). Qed.
Lemma lem1735876 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term108 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1735877 (x : real) : term166 x.
Proof. exact (@lem1735876 (term47 x) (term147 x) (term74 x) (term158 x)). Qed.
Lemma lem1735892 (x : real) : (term47 x) = (term167 x).
Proof. exact (@lem1735877 x (@lem1735874 x)). Qed.
Lemma lem1735898 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735899 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735900 (x : real) (h1 : (term26 x) = False) : (term111 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735899) (@lem1735898 x h1)). Qed.
Lemma lem1735901 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735902 (x : real) (h1 : (term26 x) = False) : (term112 x) = term113.
Proof. exact (MK_COMB (@lem1735900 x h1) (@lem1735901)). Qed.
Lemma lem1735903 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735904 (x : real) (h1 : (term26 x) = False) : (term78 x) = term114.
Proof. exact (MK_COMB (@lem1735902 x h1) (@lem1735903)). Qed.
Lemma lem1735906 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735907 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735906 real t1 t2). Qed.
Lemma lem1735908 : term114 = term4.
Proof. exact (@lem1735907 term23 term4). Qed.
Lemma lem1735909 (x : real) (h1 : (term26 x) = False) : (term78 x) = term4.
Proof. exact (TRANS (@lem1735904 x h1) (@lem1735908)). Qed.
Lemma lem1735910 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735911 (x : real) (h1 : (term26 x) = False) : (term80 x) = term115.
Proof. exact (MK_COMB (@lem1735910) (@lem1735909 x h1)). Qed.
Lemma lem1735912 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735913 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term13) = (term4 = term13).
Proof. exact (MK_COMB (@lem1735911 x h1) (@lem1735912)). Qed.
Lemma lem1735916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735917 (x : real) (h1 : (term26 x) = False) : (term146 x) = term168.
Proof. exact (MK_COMB (@lem1735916) (@lem1735913 x h1)). Qed.
Lemma lem1735918 (x : real) : (term147 x) = (term147 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1735919 (x : real) (h1 : (term26 x) = False) : (term149 x) = (term169 x).
Proof. exact (MK_COMB (@lem1735917 x h1) (@lem1735918 x)). Qed.
Lemma lem1735922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735923 (x : real) (h1 : (term26 x) = False) : (term151 x) = (term170 x).
Proof. exact (MK_COMB (@lem1735922) (@lem1735919 x h1)). Qed.
Lemma lem1735925 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1735926 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735927 (x : real) (h1 : (term26 x) = False) : (term111 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1735926) (@lem1735925 x h1)). Qed.
Lemma lem1735928 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735929 (x : real) (h1 : (term26 x) = False) : (term112 x) = term113.
Proof. exact (MK_COMB (@lem1735927 x h1) (@lem1735928)). Qed.
Lemma lem1735930 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735931 (x : real) (h1 : (term26 x) = False) : (term78 x) = term114.
Proof. exact (MK_COMB (@lem1735929 x h1) (@lem1735930)). Qed.
Lemma lem1735933 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1735934 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1735933 real t1 t2). Qed.
Lemma lem1735935 : term114 = term4.
Proof. exact (@lem1735934 term23 term4). Qed.
Lemma lem1735936 (x : real) (h1 : (term26 x) = False) : (term78 x) = term4.
Proof. exact (TRANS (@lem1735931 x h1) (@lem1735935)). Qed.
Lemma lem1735937 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735938 (x : real) (h1 : (term26 x) = False) : (term80 x) = term115.
Proof. exact (MK_COMB (@lem1735937) (@lem1735936 x h1)). Qed.
Lemma lem1735939 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735940 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term13) = (term4 = term13).
Proof. exact (MK_COMB (@lem1735938 x h1) (@lem1735939)). Qed.
Lemma lem1735943 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1735944 (x : real) (h1 : (term26 x) = False) : (term153 x) = term171.
Proof. exact (MK_COMB (@lem1735943) (@lem1735940 x h1)). Qed.
Lemma lem1735945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735946 (x : real) (h1 : (term26 x) = False) : (term155 x) = term172.
Proof. exact (MK_COMB (@lem1735945) (@lem1735944 x h1)). Qed.
Lemma lem1735947 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1735948 (x : real) (h1 : (term26 x) = False) : (term157 x) = (term173 x).
Proof. exact (MK_COMB (@lem1735946 x h1) (@lem1735947 x)). Qed.
Lemma lem1735951 (x : real) (h1 : (term26 x) = False) : (term158 x) = (term174 x).
Proof. exact (MK_COMB (@lem1735923 x h1) (@lem1735948 x h1)). Qed.
Lemma lem1735954 (x : real) : (term120 x) = (term120 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1735955 (x : real) (h1 : (term26 x) = False) : (term175 x) = (term176 x).
Proof. exact (MK_COMB (@lem1735954 x) (@lem1735951 x h1)). Qed.
Lemma lem1735958 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1735959 (x : real) (h1 : (term26 x) = False) : (term167 x) = (term178 x).
Proof. exact (MK_COMB (@lem1735958 x) (@lem1735955 x h1)). Qed.
Lemma lem1735962 (x : real) : term179 x.
Proof. exact (fun h0 : (term26 x) = False => @lem1735959 x h0). Qed.
Lemma lem1735966 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735967 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735968 (x : real) (h1 : (term26 x) = True) : (term111 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735967) (@lem1735966 x h1)). Qed.
Lemma lem1735969 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735970 (x : real) (h1 : (term26 x) = True) : (term112 x) = term126.
Proof. exact (MK_COMB (@lem1735968 x h1) (@lem1735969)). Qed.
Lemma lem1735971 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735972 (x : real) (h1 : (term26 x) = True) : (term78 x) = term127.
Proof. exact (MK_COMB (@lem1735970 x h1) (@lem1735971)). Qed.
Lemma lem1735974 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1735975 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1735974 real t2 t1). Qed.
Lemma lem1735976 : term127 = term23.
Proof. exact (@lem1735975 term4 term23). Qed.
Lemma lem1735977 (x : real) (h1 : (term26 x) = True) : (term78 x) = term23.
Proof. exact (TRANS (@lem1735972 x h1) (@lem1735976)). Qed.
Lemma lem1735978 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1735979 (x : real) (h1 : (term26 x) = True) : (term80 x) = term128.
Proof. exact (MK_COMB (@lem1735978) (@lem1735977 x h1)). Qed.
Lemma lem1735980 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1735981 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term13) = (term23 = term13).
Proof. exact (MK_COMB (@lem1735979 x h1) (@lem1735980)). Qed.
Lemma lem1735984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1735985 (x : real) (h1 : (term26 x) = True) : (term146 x) = term180.
Proof. exact (MK_COMB (@lem1735984) (@lem1735981 x h1)). Qed.
Lemma lem1735986 (x : real) : (term147 x) = (term147 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1735987 (x : real) (h1 : (term26 x) = True) : (term149 x) = (term181 x).
Proof. exact (MK_COMB (@lem1735985 x h1) (@lem1735986 x)). Qed.
Lemma lem1735990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1735991 (x : real) (h1 : (term26 x) = True) : (term151 x) = (term182 x).
Proof. exact (MK_COMB (@lem1735990) (@lem1735987 x h1)). Qed.
Lemma lem1735993 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1735994 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1735995 (x : real) (h1 : (term26 x) = True) : (term111 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1735994) (@lem1735993 x h1)). Qed.
Lemma lem1735996 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1735997 (x : real) (h1 : (term26 x) = True) : (term112 x) = term126.
Proof. exact (MK_COMB (@lem1735995 x h1) (@lem1735996)). Qed.
Lemma lem1735998 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1735999 (x : real) (h1 : (term26 x) = True) : (term78 x) = term127.
Proof. exact (MK_COMB (@lem1735997 x h1) (@lem1735998)). Qed.
Lemma lem1736001 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1736002 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1736001 real t2 t1). Qed.
Lemma lem1736003 : term127 = term23.
Proof. exact (@lem1736002 term4 term23). Qed.
Lemma lem1736004 (x : real) (h1 : (term26 x) = True) : (term78 x) = term23.
Proof. exact (TRANS (@lem1735999 x h1) (@lem1736003)). Qed.
Lemma lem1736005 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736006 (x : real) (h1 : (term26 x) = True) : (term80 x) = term128.
Proof. exact (MK_COMB (@lem1736005) (@lem1736004 x h1)). Qed.
Lemma lem1736007 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1736008 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term13) = (term23 = term13).
Proof. exact (MK_COMB (@lem1736006 x h1) (@lem1736007)). Qed.
Lemma lem1736011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736012 (x : real) (h1 : (term26 x) = True) : (term153 x) = term183.
Proof. exact (MK_COMB (@lem1736011) (@lem1736008 x h1)). Qed.
Lemma lem1736013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736014 (x : real) (h1 : (term26 x) = True) : (term155 x) = term184.
Proof. exact (MK_COMB (@lem1736013) (@lem1736012 x h1)). Qed.
Lemma lem1736015 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1736016 (x : real) (h1 : (term26 x) = True) : (term157 x) = (term185 x).
Proof. exact (MK_COMB (@lem1736014 x h1) (@lem1736015 x)). Qed.
Lemma lem1736019 (x : real) (h1 : (term26 x) = True) : (term158 x) = (term186 x).
Proof. exact (MK_COMB (@lem1735991 x h1) (@lem1736016 x h1)). Qed.
Lemma lem1736022 (x : real) : (term120 x) = (term120 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1736023 (x : real) (h1 : (term26 x) = True) : (term175 x) = (term187 x).
Proof. exact (MK_COMB (@lem1736022 x) (@lem1736019 x h1)). Qed.
Lemma lem1736026 (x : real) : (term177 x) = (term177 x).
Proof. exact (eq_refl (term177 x)). Qed.
Lemma lem1736027 (x : real) (h1 : (term26 x) = True) : (term167 x) = (term188 x).
Proof. exact (MK_COMB (@lem1736026 x) (@lem1736023 x h1)). Qed.
Lemma lem1736030 (x : real) : term189 x.
Proof. exact (fun h0 : (term26 x) = True => @lem1736027 x h0). Qed.
Lemma lem1736031 (x : real) : term190 x.
Proof. exact (conj (@lem1735962 x) (@lem1736030 x)). Qed.
Lemma lem1736033 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term108 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1736034 (x : real) : term191 x.
Proof. exact (@lem1736033 (term167 x) (term188 x) (term26 x) (term178 x)). Qed.
Lemma lem1736131 (x : real) : (term167 x) = (term192 x).
Proof. exact (@lem1736034 x (@lem1736031 x)). Qed.
Lemma lem1736132 (x : real) : (term193 x) = (term193 x).
Proof. exact (eq_refl (term193 x)). Qed.
Lemma lem1736133 (x : real) : ((term47 x) = (term167 x)) = ((term47 x) = (term192 x)).
Proof. exact (MK_COMB (@lem1736132 x) (@lem1736131 x)). Qed.
Lemma lem1736134 (x : real) : (term47 x) = (term192 x).
Proof. exact (EQ_MP (@lem1736133 x) (@lem1735892 x)). Qed.
Lemma lem1736135 : term53 = term194.
Proof. exact (fun_ext (fun x : real => @lem1736134 x)). Qed.
Lemma lem1736136 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1736137 : term54 = term195.
Proof. exact (MK_COMB (@lem1736136) (@lem1736135)). Qed.
Lemma lem1736141 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736142 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736143 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1736142) (@lem1736141 x h1)). Qed.
Lemma lem1736144 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1736145 (x : real) (h1 : (term74 x) = False) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1736143 x h1) (@lem1736144)). Qed.
Lemma lem1736146 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1736147 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1736145 x h1) (@lem1736146 x)). Qed.
Lemma lem1736149 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1736150 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1736149 real t1 t2). Qed.
Lemma lem1736151 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1736150 term13 (term78 x)). Qed.
Lemma lem1736152 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term78 x).
Proof. exact (TRANS (@lem1736147 x h1) (@lem1736151 x)). Qed.
Lemma lem1736153 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736154 (x : real) (h1 : (term74 x) = False) : (term3 x) = (term80 x).
Proof. exact (MK_COMB (@lem1736153) (@lem1736152 x h1)). Qed.
Lemma lem1736155 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736156 (x : real) (h1 : (term74 x) = False) : ((term1 x) = term23) = ((term78 x) = term23).
Proof. exact (MK_COMB (@lem1736154 x h1) (@lem1736155)). Qed.
Lemma lem1736159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736160 (x : real) (h1 : (term74 x) = False) : (term196 x) = (term197 x).
Proof. exact (MK_COMB (@lem1736159) (@lem1736156 x h1)). Qed.
Lemma lem1736161 (x : real) : (term198 x) = (term198 x).
Proof. exact (eq_refl (term198 x)). Qed.
Lemma lem1736162 (x : real) (h1 : (term74 x) = False) : (term199 x) = (term200 x).
Proof. exact (MK_COMB (@lem1736160 x h1) (@lem1736161 x)). Qed.
Lemma lem1736165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736166 (x : real) (h1 : (term74 x) = False) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1736165) (@lem1736162 x h1)). Qed.
Lemma lem1736168 (x : real) (h1 : (term74 x) = False) : (term74 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736169 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736170 (x : real) (h1 : (term74 x) = False) : (term75 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1736169) (@lem1736168 x h1)). Qed.
Lemma lem1736171 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1736172 (x : real) (h1 : (term74 x) = False) : (term76 x) = term77.
Proof. exact (MK_COMB (@lem1736170 x h1) (@lem1736171)). Qed.
Lemma lem1736173 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1736174 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term79 x).
Proof. exact (MK_COMB (@lem1736172 x h1) (@lem1736173 x)). Qed.
Lemma lem1736176 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1736177 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1736176 real t1 t2). Qed.
Lemma lem1736178 (x : real) : (term79 x) = (term78 x).
Proof. exact (@lem1736177 term13 (term78 x)). Qed.
Lemma lem1736179 (x : real) (h1 : (term74 x) = False) : (term1 x) = (term78 x).
Proof. exact (TRANS (@lem1736174 x h1) (@lem1736178 x)). Qed.
Lemma lem1736180 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736181 (x : real) (h1 : (term74 x) = False) : (term3 x) = (term80 x).
Proof. exact (MK_COMB (@lem1736180) (@lem1736179 x h1)). Qed.
Lemma lem1736182 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736183 (x : real) (h1 : (term74 x) = False) : ((term1 x) = term23) = ((term78 x) = term23).
Proof. exact (MK_COMB (@lem1736181 x h1) (@lem1736182)). Qed.
Lemma lem1736186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736187 (x : real) (h1 : (term74 x) = False) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1736186) (@lem1736183 x h1)). Qed.
Lemma lem1736188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736189 (x : real) (h1 : (term74 x) = False) : (term205 x) = (term206 x).
Proof. exact (MK_COMB (@lem1736188) (@lem1736187 x h1)). Qed.
Lemma lem1736190 (x : real) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1736191 (x : real) (h1 : (term74 x) = False) : (term207 x) = (term208 x).
Proof. exact (MK_COMB (@lem1736189 x h1) (@lem1736190 x)). Qed.
Lemma lem1736194 (x : real) (h1 : (term74 x) = False) : (term56 x) = (term209 x).
Proof. exact (MK_COMB (@lem1736166 x h1) (@lem1736191 x h1)). Qed.
Lemma lem1736197 (x : real) : term210 x.
Proof. exact (fun h0 : (term74 x) = False => @lem1736194 x h0). Qed.
Lemma lem1736199 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736200 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736201 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1736200) (@lem1736199 x h1)). Qed.
Lemma lem1736202 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1736203 (x : real) (h1 : (term74 x) = True) : (term76 x) = term96.
Proof. exact (MK_COMB (@lem1736201 x h1) (@lem1736202)). Qed.
Lemma lem1736204 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1736205 (x : real) (h1 : (term74 x) = True) : (term1 x) = (term97 x).
Proof. exact (MK_COMB (@lem1736203 x h1) (@lem1736204 x)). Qed.
Lemma lem1736207 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1736208 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1736207 real t2 t1). Qed.
Lemma lem1736209 (x : real) : (term97 x) = term13.
Proof. exact (@lem1736208 (term78 x) term13). Qed.
Lemma lem1736210 (x : real) (h1 : (term74 x) = True) : (term1 x) = term13.
Proof. exact (TRANS (@lem1736205 x h1) (@lem1736209 x)). Qed.
Lemma lem1736211 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736212 (x : real) (h1 : (term74 x) = True) : (term3 x) = term98.
Proof. exact (MK_COMB (@lem1736211) (@lem1736210 x h1)). Qed.
Lemma lem1736213 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736214 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term23) = (term13 = term23).
Proof. exact (MK_COMB (@lem1736212 x h1) (@lem1736213)). Qed.
Lemma lem1736217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736218 (x : real) (h1 : (term74 x) = True) : (term196 x) = term211.
Proof. exact (MK_COMB (@lem1736217) (@lem1736214 x h1)). Qed.
Lemma lem1736219 (x : real) : (term198 x) = (term198 x).
Proof. exact (eq_refl (term198 x)). Qed.
Lemma lem1736220 (x : real) (h1 : (term74 x) = True) : (term199 x) = (term212 x).
Proof. exact (MK_COMB (@lem1736218 x h1) (@lem1736219 x)). Qed.
Lemma lem1736223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736224 (x : real) (h1 : (term74 x) = True) : (term201 x) = (term213 x).
Proof. exact (MK_COMB (@lem1736223) (@lem1736220 x h1)). Qed.
Lemma lem1736226 (x : real) (h1 : (term74 x) = True) : (term74 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736227 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736228 (x : real) (h1 : (term74 x) = True) : (term75 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1736227) (@lem1736226 x h1)). Qed.
Lemma lem1736229 : term13 = term13.
Proof. exact (eq_refl term13). Qed.
Lemma lem1736230 (x : real) (h1 : (term74 x) = True) : (term76 x) = term96.
Proof. exact (MK_COMB (@lem1736228 x h1) (@lem1736229)). Qed.
Lemma lem1736231 (x : real) : (term78 x) = (term78 x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1736232 (x : real) (h1 : (term74 x) = True) : (term1 x) = (term97 x).
Proof. exact (MK_COMB (@lem1736230 x h1) (@lem1736231 x)). Qed.
Lemma lem1736234 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1736235 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1736234 real t2 t1). Qed.
Lemma lem1736236 (x : real) : (term97 x) = term13.
Proof. exact (@lem1736235 (term78 x) term13). Qed.
Lemma lem1736237 (x : real) (h1 : (term74 x) = True) : (term1 x) = term13.
Proof. exact (TRANS (@lem1736232 x h1) (@lem1736236 x)). Qed.
Lemma lem1736238 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736239 (x : real) (h1 : (term74 x) = True) : (term3 x) = term98.
Proof. exact (MK_COMB (@lem1736238) (@lem1736237 x h1)). Qed.
Lemma lem1736240 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736241 (x : real) (h1 : (term74 x) = True) : ((term1 x) = term23) = (term13 = term23).
Proof. exact (MK_COMB (@lem1736239 x h1) (@lem1736240)). Qed.
Lemma lem1736244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736245 (x : real) (h1 : (term74 x) = True) : (term203 x) = term214.
Proof. exact (MK_COMB (@lem1736244) (@lem1736241 x h1)). Qed.
Lemma lem1736246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736247 (x : real) (h1 : (term74 x) = True) : (term205 x) = term215.
Proof. exact (MK_COMB (@lem1736246) (@lem1736245 x h1)). Qed.
Lemma lem1736248 (x : real) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1736249 (x : real) (h1 : (term74 x) = True) : (term207 x) = (term216 x).
Proof. exact (MK_COMB (@lem1736247 x h1) (@lem1736248 x)). Qed.
Lemma lem1736252 (x : real) (h1 : (term74 x) = True) : (term56 x) = (term217 x).
Proof. exact (MK_COMB (@lem1736224 x h1) (@lem1736249 x h1)). Qed.
Lemma lem1736255 (x : real) : term218 x.
Proof. exact (fun h0 : (term74 x) = True => @lem1736252 x h0). Qed.
Lemma lem1736256 (x : real) : term219 x.
Proof. exact (conj (@lem1736197 x) (@lem1736255 x)). Qed.
Lemma lem1736258 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term108 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1736259 (x : real) : term220 x.
Proof. exact (@lem1736258 (term56 x) (term217 x) (term74 x) (term209 x)). Qed.
Lemma lem1736274 (x : real) : (term56 x) = (term221 x).
Proof. exact (@lem1736259 x (@lem1736256 x)). Qed.
Lemma lem1736280 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736282 (x : real) (h1 : (term26 x) = False) : (term198 x) = (~ False).
Proof. exact (MK_COMB (@lem1736281) (@lem1736280 x h1)). Qed.
Lemma lem1736284 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1736285 (x : real) (h1 : (term26 x) = False) : (term198 x) = True.
Proof. exact (TRANS (@lem1736282 x h1) (@lem1736284)). Qed.
Lemma lem1736286 : term211 = term211.
Proof. exact (eq_refl term211). Qed.
Lemma lem1736287 (x : real) (h1 : (term26 x) = False) : (term212 x) = term222.
Proof. exact (MK_COMB (@lem1736286) (@lem1736285 x h1)). Qed.
Lemma lem1736289 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1736290 : term222 = (term13 = term23).
Proof. exact (@lem1736289 (term13 = term23)). Qed.
Lemma lem1736293 (x : real) (h1 : (term26 x) = False) : (term212 x) = (term13 = term23).
Proof. exact (TRANS (@lem1736287 x h1) (@lem1736290)). Qed.
Lemma lem1736294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736295 (x : real) (h1 : (term26 x) = False) : (term213 x) = term223.
Proof. exact (MK_COMB (@lem1736294) (@lem1736293 x h1)). Qed.
Lemma lem1736299 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736300 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem1736301 (x : real) (h1 : (term26 x) = False) : (term216 x) = term224.
Proof. exact (MK_COMB (@lem1736300) (@lem1736299 x h1)). Qed.
Lemma lem1736303 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1736304 : term224 = False.
Proof. exact (@lem1736303 term214). Qed.
Lemma lem1736305 (x : real) (h1 : (term26 x) = False) : (term216 x) = False.
Proof. exact (TRANS (@lem1736301 x h1) (@lem1736304)). Qed.
Lemma lem1736306 (x : real) (h1 : (term26 x) = False) : (term217 x) = term225.
Proof. exact (MK_COMB (@lem1736295 x h1) (@lem1736305 x h1)). Qed.
Lemma lem1736308 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1736309 : term225 = (term13 = term23).
Proof. exact (@lem1736308 (term13 = term23)). Qed.
Lemma lem1736312 (x : real) (h1 : (term26 x) = False) : (term217 x) = (term13 = term23).
Proof. exact (TRANS (@lem1736306 x h1) (@lem1736309)). Qed.
Lemma lem1736313 (x : real) : (term226 x) = (term226 x).
Proof. exact (eq_refl (term226 x)). Qed.
Lemma lem1736314 (x : real) (h1 : (term26 x) = False) : (term227 x) = (term228 x).
Proof. exact (MK_COMB (@lem1736313 x) (@lem1736312 x h1)). Qed.
Lemma lem1736317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736318 (x : real) (h1 : (term26 x) = False) : (term229 x) = (term230 x).
Proof. exact (MK_COMB (@lem1736317) (@lem1736314 x h1)). Qed.
Lemma lem1736320 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736321 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736322 (x : real) (h1 : (term26 x) = False) : (term111 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1736321) (@lem1736320 x h1)). Qed.
Lemma lem1736323 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736324 (x : real) (h1 : (term26 x) = False) : (term112 x) = term113.
Proof. exact (MK_COMB (@lem1736322 x h1) (@lem1736323)). Qed.
Lemma lem1736325 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736326 (x : real) (h1 : (term26 x) = False) : (term78 x) = term114.
Proof. exact (MK_COMB (@lem1736324 x h1) (@lem1736325)). Qed.
Lemma lem1736328 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1736329 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1736328 real t1 t2). Qed.
Lemma lem1736330 : term114 = term4.
Proof. exact (@lem1736329 term23 term4). Qed.
Lemma lem1736331 (x : real) (h1 : (term26 x) = False) : (term78 x) = term4.
Proof. exact (TRANS (@lem1736326 x h1) (@lem1736330)). Qed.
Lemma lem1736332 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736333 (x : real) (h1 : (term26 x) = False) : (term80 x) = term115.
Proof. exact (MK_COMB (@lem1736332) (@lem1736331 x h1)). Qed.
Lemma lem1736334 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736335 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term23) = (term4 = term23).
Proof. exact (MK_COMB (@lem1736333 x h1) (@lem1736334)). Qed.
Lemma lem1736338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736339 (x : real) (h1 : (term26 x) = False) : (term197 x) = term231.
Proof. exact (MK_COMB (@lem1736338) (@lem1736335 x h1)). Qed.
Lemma lem1736341 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736343 (x : real) (h1 : (term26 x) = False) : (term198 x) = (~ False).
Proof. exact (MK_COMB (@lem1736342) (@lem1736341 x h1)). Qed.
Lemma lem1736345 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1736346 (x : real) (h1 : (term26 x) = False) : (term198 x) = True.
Proof. exact (TRANS (@lem1736343 x h1) (@lem1736345)). Qed.
Lemma lem1736347 (x : real) (h1 : (term26 x) = False) : (term200 x) = term232.
Proof. exact (MK_COMB (@lem1736339 x h1) (@lem1736346 x h1)). Qed.
Lemma lem1736349 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1736350 : term232 = (term4 = term23).
Proof. exact (@lem1736349 (term4 = term23)). Qed.
Lemma lem1736353 (x : real) (h1 : (term26 x) = False) : (term200 x) = (term4 = term23).
Proof. exact (TRANS (@lem1736347 x h1) (@lem1736350)). Qed.
Lemma lem1736354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736355 (x : real) (h1 : (term26 x) = False) : (term202 x) = term233.
Proof. exact (MK_COMB (@lem1736354) (@lem1736353 x h1)). Qed.
Lemma lem1736357 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736358 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736359 (x : real) (h1 : (term26 x) = False) : (term111 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1736358) (@lem1736357 x h1)). Qed.
Lemma lem1736360 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736361 (x : real) (h1 : (term26 x) = False) : (term112 x) = term113.
Proof. exact (MK_COMB (@lem1736359 x h1) (@lem1736360)). Qed.
Lemma lem1736362 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736363 (x : real) (h1 : (term26 x) = False) : (term78 x) = term114.
Proof. exact (MK_COMB (@lem1736361 x h1) (@lem1736362)). Qed.
Lemma lem1736365 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1736366 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1736365 real t1 t2). Qed.
Lemma lem1736367 : term114 = term4.
Proof. exact (@lem1736366 term23 term4). Qed.
Lemma lem1736368 (x : real) (h1 : (term26 x) = False) : (term78 x) = term4.
Proof. exact (TRANS (@lem1736363 x h1) (@lem1736367)). Qed.
Lemma lem1736369 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736370 (x : real) (h1 : (term26 x) = False) : (term80 x) = term115.
Proof. exact (MK_COMB (@lem1736369) (@lem1736368 x h1)). Qed.
Lemma lem1736371 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736372 (x : real) (h1 : (term26 x) = False) : ((term78 x) = term23) = (term4 = term23).
Proof. exact (MK_COMB (@lem1736370 x h1) (@lem1736371)). Qed.
Lemma lem1736375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736376 (x : real) (h1 : (term26 x) = False) : (term204 x) = term234.
Proof. exact (MK_COMB (@lem1736375) (@lem1736372 x h1)). Qed.
Lemma lem1736377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736378 (x : real) (h1 : (term26 x) = False) : (term206 x) = term235.
Proof. exact (MK_COMB (@lem1736377) (@lem1736376 x h1)). Qed.
Lemma lem1736380 (x : real) (h1 : (term26 x) = False) : (term26 x) = False.
Proof. exact (h1). Qed.
Lemma lem1736381 (x : real) (h1 : (term26 x) = False) : (term208 x) = term236.
Proof. exact (MK_COMB (@lem1736378 x h1) (@lem1736380 x h1)). Qed.
Lemma lem1736383 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1736384 : term236 = False.
Proof. exact (@lem1736383 term234). Qed.
Lemma lem1736385 (x : real) (h1 : (term26 x) = False) : (term208 x) = False.
Proof. exact (TRANS (@lem1736381 x h1) (@lem1736384)). Qed.
Lemma lem1736386 (x : real) (h1 : (term26 x) = False) : (term209 x) = term237.
Proof. exact (MK_COMB (@lem1736355 x h1) (@lem1736385 x h1)). Qed.
Lemma lem1736388 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1736389 : term237 = (term4 = term23).
Proof. exact (@lem1736388 (term4 = term23)). Qed.
Lemma lem1736392 (x : real) (h1 : (term26 x) = False) : (term209 x) = (term4 = term23).
Proof. exact (TRANS (@lem1736386 x h1) (@lem1736389)). Qed.
Lemma lem1736393 (x : real) : (term120 x) = (term120 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1736394 (x : real) (h1 : (term26 x) = False) : (term238 x) = (term239 x).
Proof. exact (MK_COMB (@lem1736393 x) (@lem1736392 x h1)). Qed.
Lemma lem1736397 (x : real) (h1 : (term26 x) = False) : (term221 x) = (term240 x).
Proof. exact (MK_COMB (@lem1736318 x h1) (@lem1736394 x h1)). Qed.
Lemma lem1736400 (x : real) : term241 x.
Proof. exact (fun h0 : (term26 x) = False => @lem1736397 x h0). Qed.
Lemma lem1736404 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736406 (x : real) (h1 : (term26 x) = True) : (term198 x) = (~ True).
Proof. exact (MK_COMB (@lem1736405) (@lem1736404 x h1)). Qed.
Lemma lem1736408 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1736409 (x : real) (h1 : (term26 x) = True) : (term198 x) = False.
Proof. exact (TRANS (@lem1736406 x h1) (@lem1736408)). Qed.
Lemma lem1736410 : term211 = term211.
Proof. exact (eq_refl term211). Qed.
Lemma lem1736411 (x : real) (h1 : (term26 x) = True) : (term212 x) = term242.
Proof. exact (MK_COMB (@lem1736410) (@lem1736409 x h1)). Qed.
Lemma lem1736413 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1736414 : term242 = False.
Proof. exact (@lem1736413 (term13 = term23)). Qed.
Lemma lem1736415 (x : real) (h1 : (term26 x) = True) : (term212 x) = False.
Proof. exact (TRANS (@lem1736411 x h1) (@lem1736414)). Qed.
Lemma lem1736416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736417 (x : real) (h1 : (term26 x) = True) : (term213 x) = (or False).
Proof. exact (MK_COMB (@lem1736416) (@lem1736415 x h1)). Qed.
Lemma lem1736421 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736422 : term215 = term215.
Proof. exact (eq_refl term215). Qed.
Lemma lem1736423 (x : real) (h1 : (term26 x) = True) : (term216 x) = term243.
Proof. exact (MK_COMB (@lem1736422) (@lem1736421 x h1)). Qed.
Lemma lem1736425 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1736426 : term243 = term214.
Proof. exact (@lem1736425 term214). Qed.
Lemma lem1736427 (x : real) (h1 : (term26 x) = True) : (term216 x) = term214.
Proof. exact (TRANS (@lem1736423 x h1) (@lem1736426)). Qed.
Lemma lem1736428 (x : real) (h1 : (term26 x) = True) : (term217 x) = term244.
Proof. exact (MK_COMB (@lem1736417 x h1) (@lem1736427 x h1)). Qed.
Lemma lem1736430 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1736431 : term244 = term214.
Proof. exact (@lem1736430 term214). Qed.
Lemma lem1736432 (x : real) (h1 : (term26 x) = True) : (term217 x) = term214.
Proof. exact (TRANS (@lem1736428 x h1) (@lem1736431)). Qed.
Lemma lem1736433 (x : real) : (term226 x) = (term226 x).
Proof. exact (eq_refl (term226 x)). Qed.
Lemma lem1736434 (x : real) (h1 : (term26 x) = True) : (term227 x) = (term245 x).
Proof. exact (MK_COMB (@lem1736433 x) (@lem1736432 x h1)). Qed.
Lemma lem1736437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736438 (x : real) (h1 : (term26 x) = True) : (term229 x) = (term246 x).
Proof. exact (MK_COMB (@lem1736437) (@lem1736434 x h1)). Qed.
Lemma lem1736440 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736441 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736442 (x : real) (h1 : (term26 x) = True) : (term111 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1736441) (@lem1736440 x h1)). Qed.
Lemma lem1736443 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736444 (x : real) (h1 : (term26 x) = True) : (term112 x) = term126.
Proof. exact (MK_COMB (@lem1736442 x h1) (@lem1736443)). Qed.
Lemma lem1736445 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736446 (x : real) (h1 : (term26 x) = True) : (term78 x) = term127.
Proof. exact (MK_COMB (@lem1736444 x h1) (@lem1736445)). Qed.
Lemma lem1736448 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1736449 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1736448 real t2 t1). Qed.
Lemma lem1736450 : term127 = term23.
Proof. exact (@lem1736449 term4 term23). Qed.
Lemma lem1736451 (x : real) (h1 : (term26 x) = True) : (term78 x) = term23.
Proof. exact (TRANS (@lem1736446 x h1) (@lem1736450)). Qed.
Lemma lem1736452 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736453 (x : real) (h1 : (term26 x) = True) : (term80 x) = term128.
Proof. exact (MK_COMB (@lem1736452) (@lem1736451 x h1)). Qed.
Lemma lem1736454 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736455 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term23) = (term23 = term23).
Proof. exact (MK_COMB (@lem1736453 x h1) (@lem1736454)). Qed.
Lemma lem1736457 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1736458 (x : real) : (x = x) = True.
Proof. exact (@lem1736457 real x). Qed.
Lemma lem1736459 : (term23 = term23) = True.
Proof. exact (@lem1736458 term23). Qed.
Lemma lem1736460 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term23) = True.
Proof. exact (TRANS (@lem1736455 x h1) (@lem1736459)). Qed.
Lemma lem1736461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736462 (x : real) (h1 : (term26 x) = True) : (term197 x) = (and True).
Proof. exact (MK_COMB (@lem1736461) (@lem1736460 x h1)). Qed.
Lemma lem1736464 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736466 (x : real) (h1 : (term26 x) = True) : (term198 x) = (~ True).
Proof. exact (MK_COMB (@lem1736465) (@lem1736464 x h1)). Qed.
Lemma lem1736468 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1736469 (x : real) (h1 : (term26 x) = True) : (term198 x) = False.
Proof. exact (TRANS (@lem1736466 x h1) (@lem1736468)). Qed.
Lemma lem1736470 (x : real) (h1 : (term26 x) = True) : (term200 x) = (True /\ False).
Proof. exact (MK_COMB (@lem1736462 x h1) (@lem1736469 x h1)). Qed.
Lemma lem1736472 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1736473 : (True /\ False) = False.
Proof. exact (@lem1736472 False). Qed.
Lemma lem1736474 (x : real) (h1 : (term26 x) = True) : (term200 x) = False.
Proof. exact (TRANS (@lem1736470 x h1) (@lem1736473)). Qed.
Lemma lem1736475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736476 (x : real) (h1 : (term26 x) = True) : (term202 x) = (or False).
Proof. exact (MK_COMB (@lem1736475) (@lem1736474 x h1)). Qed.
Lemma lem1736478 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736479 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1736480 (x : real) (h1 : (term26 x) = True) : (term111 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1736479) (@lem1736478 x h1)). Qed.
Lemma lem1736481 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736482 (x : real) (h1 : (term26 x) = True) : (term112 x) = term126.
Proof. exact (MK_COMB (@lem1736480 x h1) (@lem1736481)). Qed.
Lemma lem1736483 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736484 (x : real) (h1 : (term26 x) = True) : (term78 x) = term127.
Proof. exact (MK_COMB (@lem1736482 x h1) (@lem1736483)). Qed.
Lemma lem1736486 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1736487 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1736486 real t2 t1). Qed.
Lemma lem1736488 : term127 = term23.
Proof. exact (@lem1736487 term4 term23). Qed.
Lemma lem1736489 (x : real) (h1 : (term26 x) = True) : (term78 x) = term23.
Proof. exact (TRANS (@lem1736484 x h1) (@lem1736488)). Qed.
Lemma lem1736490 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736491 (x : real) (h1 : (term26 x) = True) : (term80 x) = term128.
Proof. exact (MK_COMB (@lem1736490) (@lem1736489 x h1)). Qed.
Lemma lem1736492 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem1736493 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term23) = (term23 = term23).
Proof. exact (MK_COMB (@lem1736491 x h1) (@lem1736492)). Qed.
Lemma lem1736495 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1736496 (x : real) : (x = x) = True.
Proof. exact (@lem1736495 real x). Qed.
Lemma lem1736497 : (term23 = term23) = True.
Proof. exact (@lem1736496 term23). Qed.
Lemma lem1736498 (x : real) (h1 : (term26 x) = True) : ((term78 x) = term23) = True.
Proof. exact (TRANS (@lem1736493 x h1) (@lem1736497)). Qed.
Lemma lem1736499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1736500 (x : real) (h1 : (term26 x) = True) : (term204 x) = (~ True).
Proof. exact (MK_COMB (@lem1736499) (@lem1736498 x h1)). Qed.
Lemma lem1736502 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1736503 (x : real) (h1 : (term26 x) = True) : (term204 x) = False.
Proof. exact (TRANS (@lem1736500 x h1) (@lem1736502)). Qed.
Lemma lem1736504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736505 (x : real) (h1 : (term26 x) = True) : (term206 x) = (and False).
Proof. exact (MK_COMB (@lem1736504) (@lem1736503 x h1)). Qed.
Lemma lem1736507 (x : real) (h1 : (term26 x) = True) : (term26 x) = True.
Proof. exact (h1). Qed.
Lemma lem1736508 (x : real) (h1 : (term26 x) = True) : (term208 x) = (False /\ True).
Proof. exact (MK_COMB (@lem1736505 x h1) (@lem1736507 x h1)). Qed.
Lemma lem1736510 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1736511 : (False /\ True) = False.
Proof. exact (@lem1736510 True). Qed.
Lemma lem1736512 (x : real) (h1 : (term26 x) = True) : (term208 x) = False.
Proof. exact (TRANS (@lem1736508 x h1) (@lem1736511)). Qed.
Lemma lem1736513 (x : real) (h1 : (term26 x) = True) : (term209 x) = (False \/ False).
Proof. exact (MK_COMB (@lem1736476 x h1) (@lem1736512 x h1)). Qed.
Lemma lem1736515 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1736516 : (False \/ False) = False.
Proof. exact (@lem1736515 False). Qed.
Lemma lem1736517 (x : real) (h1 : (term26 x) = True) : (term209 x) = False.
Proof. exact (TRANS (@lem1736513 x h1) (@lem1736516)). Qed.
Lemma lem1736518 (x : real) : (term120 x) = (term120 x).
Proof. exact (eq_refl (term120 x)). Qed.
Lemma lem1736519 (x : real) (h1 : (term26 x) = True) : (term238 x) = (term247 x).
Proof. exact (MK_COMB (@lem1736518 x) (@lem1736517 x h1)). Qed.
Lemma lem1736521 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1736522 (x : real) : (term247 x) = False.
Proof. exact (@lem1736521 (term248 x)). Qed.
Lemma lem1736523 (x : real) (h1 : (term26 x) = True) : (term238 x) = False.
Proof. exact (TRANS (@lem1736519 x h1) (@lem1736522 x)). Qed.
Lemma lem1736524 (x : real) (h1 : (term26 x) = True) : (term221 x) = (term249 x).
Proof. exact (MK_COMB (@lem1736438 x h1) (@lem1736523 x h1)). Qed.
Lemma lem1736526 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1736527 (x : real) : (term249 x) = (term245 x).
Proof. exact (@lem1736526 (term245 x)). Qed.
Lemma lem1736530 (x : real) (h1 : (term26 x) = True) : (term221 x) = (term245 x).
Proof. exact (TRANS (@lem1736524 x h1) (@lem1736527 x)). Qed.
Lemma lem1736531 (x : real) : term250 x.
Proof. exact (fun h0 : (term26 x) = True => @lem1736530 x h0). Qed.
Lemma lem1736532 (x : real) : term251 x.
Proof. exact (conj (@lem1736400 x) (@lem1736531 x)). Qed.
Lemma lem1736534 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term108 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1736535 (x : real) : term252 x.
Proof. exact (@lem1736534 (term221 x) (term245 x) (term26 x) (term240 x)). Qed.
Lemma lem1736588 (x : real) : (term221 x) = (term253 x).
Proof. exact (@lem1736535 x (@lem1736532 x)). Qed.
Lemma lem1736589 (x : real) : (term254 x) = (term254 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem1736590 (x : real) : ((term56 x) = (term221 x)) = ((term56 x) = (term253 x)).
Proof. exact (MK_COMB (@lem1736589 x) (@lem1736588 x)). Qed.
Lemma lem1736591 (x : real) : (term56 x) = (term253 x).
Proof. exact (EQ_MP (@lem1736590 x) (@lem1736274 x)). Qed.
Lemma lem1736592 : term62 = term255.
Proof. exact (fun_ext (fun x : real => @lem1736591 x)). Qed.
Lemma lem1736593 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1736594 : term63 = term256.
Proof. exact (MK_COMB (@lem1736593) (@lem1736592)). Qed.
Lemma lem1736595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736596 : term65 = term257.
Proof. exact (MK_COMB (@lem1736595) (@lem1736137)). Qed.
Lemma lem1736597 : term67 = term258.
Proof. exact (MK_COMB (@lem1736596) (@lem1736594)). Qed.
Lemma lem1736598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736599 : term70 = term259.
Proof. exact (MK_COMB (@lem1736598) (@lem1735740)). Qed.
Lemma lem1736600 : term72 = term260.
Proof. exact (MK_COMB (@lem1736599) (@lem1736597)). Qed.
Lemma lem1736601 : term73 = term260.
Proof. exact (TRANS (@lem1735285) (@lem1736600)). Qed.
Lemma lem1736602 (x : real) : (term26 x) = (term261 x).
Proof. exact (@lem1483521 term4 x). Qed.
Lemma lem1736608 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1736613 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1736615 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1736608 x) (@lem1736613 x)). Qed.
Lemma lem1736616 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736617 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1736616) (@lem1736615 x)). Qed.
Lemma lem1736618 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736619 (x : real) : (term261 x) = (term267 x).
Proof. exact (MK_COMB (@lem1736617 x) (@lem1736618)). Qed.
Lemma lem1736620 (x : real) : (term26 x) = (term267 x).
Proof. exact (TRANS (@lem1736602 x) (@lem1736619 x)). Qed.
Lemma lem1736621 (x : real) : (term74 x) = (term268 x).
Proof. exact (@lem1483521 x term4). Qed.
Lemma lem1736627 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736629 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736630 : term272 = term4.
Proof. exact (@lem1736629 term273). Qed.
Lemma lem1736631 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736632 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736631 x) (@lem1736630)). Qed.
Lemma lem1736633 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736634 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736632 x) (@lem1736633 x)). Qed.
Lemma lem1736636 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736627 x) (@lem1736634 x)). Qed.
Lemma lem1736637 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736638 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1736637) (@lem1736636 x)). Qed.
Lemma lem1736639 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736640 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1736638 x) (@lem1736639)). Qed.
Lemma lem1736641 (x : real) : (term74 x) = (term16 x).
Proof. exact (TRANS (@lem1736621 x) (@lem1736640 x)). Qed.
Lemma lem1736642 : (term13 = term4) = (term276 = term4).
Proof. exact (@lem1483529 term13 term4). Qed.
Lemma lem1736648 : term276 = term277.
Proof. exact (@lem1483519 term13 term4). Qed.
Lemma lem1736650 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736651 : term272 = term4.
Proof. exact (@lem1736650 term273). Qed.
Lemma lem1736652 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1736653 : term277 = term279.
Proof. exact (MK_COMB (@lem1736652) (@lem1736651)). Qed.
Lemma lem1736654 : term279 = term13.
Proof. exact (@lem1483450 term13). Qed.
Lemma lem1736655 : term277 = term13.
Proof. exact (TRANS (@lem1736653) (@lem1736654)). Qed.
Lemma lem1736657 : term276 = term13.
Proof. exact (TRANS (@lem1736648) (@lem1736655)). Qed.
Lemma lem1736658 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736659 : term280 = term98.
Proof. exact (MK_COMB (@lem1736658) (@lem1736657)). Qed.
Lemma lem1736660 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736661 : (term276 = term4) = (term13 = term4).
Proof. exact (MK_COMB (@lem1736659) (@lem1736660)). Qed.
Lemma lem1736662 : (term13 = term4) = (term13 = term4).
Proof. exact (TRANS (@lem1736642) (@lem1736661)). Qed.
Lemma lem1736663 (x : real) : (term83 x) = (term281 x).
Proof. exact (@lem1483554 x term4). Qed.
Lemma lem1736669 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736671 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736672 : term272 = term4.
Proof. exact (@lem1736671 term273). Qed.
Lemma lem1736673 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736674 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736673 x) (@lem1736672)). Qed.
Lemma lem1736675 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736676 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736674 x) (@lem1736675 x)). Qed.
Lemma lem1736678 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736669 x) (@lem1736676 x)). Qed.
Lemma lem1736679 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1736680 (x : real) : (term282 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1736679) (@lem1736678 x)). Qed.
Lemma lem1736683 (x : real) : (real_neg x) = (term264 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1736684 (x : real) : (term283 x) = (term283 x).
Proof. exact (eq_refl (term283 x)). Qed.
Lemma lem1736685 (x : real) : ((term282 x) = (real_neg x)) = ((term282 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1736684 x) (@lem1736683 x)). Qed.
Lemma lem1736686 (x : real) : (term282 x) = (term264 x).
Proof. exact (EQ_MP (@lem1736685 x) (@lem1736680 x)). Qed.
Lemma lem1736687 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736688 (x : real) : (term284 x) = (term266 x).
Proof. exact (MK_COMB (@lem1736687) (@lem1736686 x)). Qed.
Lemma lem1736689 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736690 (x : real) : (term285 x) = (term267 x).
Proof. exact (MK_COMB (@lem1736688 x) (@lem1736689)). Qed.
Lemma lem1736691 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736692 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1736691) (@lem1736678 x)). Qed.
Lemma lem1736693 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736694 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1736692 x) (@lem1736693)). Qed.
Lemma lem1736695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736696 (x : real) : (term286 x) = (term287 x).
Proof. exact (MK_COMB (@lem1736695) (@lem1736694 x)). Qed.
Lemma lem1736697 (x : real) : (term281 x) = (term288 x).
Proof. exact (MK_COMB (@lem1736696 x) (@lem1736690 x)). Qed.
Lemma lem1736698 (x : real) : (term83 x) = (term288 x).
Proof. exact (TRANS (@lem1736663 x) (@lem1736697 x)). Qed.
Lemma lem1736699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736700 : term99 = term99.
Proof. exact (MK_COMB (@lem1736699) (@lem1736662)). Qed.
Lemma lem1736701 (x : real) : (term100 x) = (term289 x).
Proof. exact (MK_COMB (@lem1736700) (@lem1736698 x)). Qed.
Lemma lem1736702 : term102 = term290.
Proof. exact (@lem1483554 term13 term4). Qed.
Lemma lem1736708 : term276 = term277.
Proof. exact (@lem1483519 term13 term4). Qed.
Lemma lem1736710 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736711 : term272 = term4.
Proof. exact (@lem1736710 term273). Qed.
Lemma lem1736712 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1736713 : term277 = term279.
Proof. exact (MK_COMB (@lem1736712) (@lem1736711)). Qed.
Lemma lem1736714 : term279 = term13.
Proof. exact (@lem1483450 term13). Qed.
Lemma lem1736715 : term277 = term13.
Proof. exact (TRANS (@lem1736713) (@lem1736714)). Qed.
Lemma lem1736717 : term276 = term13.
Proof. exact (TRANS (@lem1736708) (@lem1736715)). Qed.
Lemma lem1736718 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1736719 : term291 = term23.
Proof. exact (MK_COMB (@lem1736718) (@lem1736717)). Qed.
Lemma lem1736720 : term23 = term292.
Proof. exact (@lem1483512 term13). Qed.
Lemma lem1736722 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1736723 : term292 = term295.
Proof. exact (@lem1736722 term273 term273). Qed.
Lemma lem1736724 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1736725 : term297 = term273.
Proof. exact (EQ_MP (@lem1736724) (@lem940073)). Qed.
Lemma lem1736726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1736727 : term298 = term13.
Proof. exact (MK_COMB (@lem1736726) (@lem1736725)). Qed.
Lemma lem1736728 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1736729 : term295 = term23.
Proof. exact (MK_COMB (@lem1736728) (@lem1736727)). Qed.
Lemma lem1736730 : term292 = term23.
Proof. exact (TRANS (@lem1736723) (@lem1736729)). Qed.
Lemma lem1736731 : term23 = term23.
Proof. exact (TRANS (@lem1736720) (@lem1736730)). Qed.
Lemma lem1736732 : term299 = term299.
Proof. exact (eq_refl term299). Qed.
Lemma lem1736733 : (term291 = term23) = (term291 = term23).
Proof. exact (MK_COMB (@lem1736732) (@lem1736731)). Qed.
Lemma lem1736734 : term291 = term23.
Proof. exact (EQ_MP (@lem1736733) (@lem1736719)). Qed.
Lemma lem1736735 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736736 : term300 = term301.
Proof. exact (MK_COMB (@lem1736735) (@lem1736734)). Qed.
Lemma lem1736737 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736738 : term302 = term303.
Proof. exact (MK_COMB (@lem1736736) (@lem1736737)). Qed.
Lemma lem1736739 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736740 : term304 = term305.
Proof. exact (MK_COMB (@lem1736739) (@lem1736717)). Qed.
Lemma lem1736741 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736742 : term306 = term307.
Proof. exact (MK_COMB (@lem1736740) (@lem1736741)). Qed.
Lemma lem1736743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736744 : term308 = term309.
Proof. exact (MK_COMB (@lem1736743) (@lem1736742)). Qed.
Lemma lem1736745 : term290 = term310.
Proof. exact (MK_COMB (@lem1736744) (@lem1736738)). Qed.
Lemma lem1736746 : term102 = term310.
Proof. exact (TRANS (@lem1736702) (@lem1736745)). Qed.
Lemma lem1736747 (x : real) : (x = term4) = ((term269 x) = term4).
Proof. exact (@lem1483529 x term4). Qed.
Lemma lem1736753 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736755 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736756 : term272 = term4.
Proof. exact (@lem1736755 term273). Qed.
Lemma lem1736757 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736758 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736757 x) (@lem1736756)). Qed.
Lemma lem1736759 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736760 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736758 x) (@lem1736759 x)). Qed.
Lemma lem1736762 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736753 x) (@lem1736760 x)). Qed.
Lemma lem1736763 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736764 (x : real) : (term311 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1736763) (@lem1736762 x)). Qed.
Lemma lem1736765 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736766 (x : real) : ((term269 x) = term4) = (x = term4).
Proof. exact (MK_COMB (@lem1736764 x) (@lem1736765)). Qed.
Lemma lem1736767 (x : real) : (x = term4) = (x = term4).
Proof. exact (TRANS (@lem1736747 x) (@lem1736766 x)). Qed.
Lemma lem1736768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736769 : term103 = term312.
Proof. exact (MK_COMB (@lem1736768) (@lem1736746)). Qed.
Lemma lem1736770 (x : real) : (term104 x) = (term313 x).
Proof. exact (MK_COMB (@lem1736769) (@lem1736767 x)). Qed.
Lemma lem1736771 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736772 (x : real) : (term101 x) = (term314 x).
Proof. exact (MK_COMB (@lem1736771) (@lem1736701 x)). Qed.
Lemma lem1736773 (x : real) : (term105 x) = (term315 x).
Proof. exact (MK_COMB (@lem1736772 x) (@lem1736770 x)). Qed.
Lemma lem1736774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736775 (x : real) : (term226 x) = (term316 x).
Proof. exact (MK_COMB (@lem1736774) (@lem1736641 x)). Qed.
Lemma lem1736776 (x : real) : (term317 x) = (term318 x).
Proof. exact (MK_COMB (@lem1736775 x) (@lem1736773 x)). Qed.
Lemma lem1736777 (x : real) : (term248 x) = (term319 x).
Proof. exact (@lem1483531 term4 x). Qed.
Lemma lem1736783 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1736788 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1736790 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1736783 x) (@lem1736788 x)). Qed.
Lemma lem1736791 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1736792 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1736791) (@lem1736790 x)). Qed.
Lemma lem1736793 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736794 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1736792 x) (@lem1736793)). Qed.
Lemma lem1736795 (x : real) : (term248 x) = (term322 x).
Proof. exact (TRANS (@lem1736777 x) (@lem1736794 x)). Qed.
Lemma lem1736796 : (term23 = term4) = (term323 = term4).
Proof. exact (@lem1483529 term23 term4). Qed.
Lemma lem1736802 : term323 = term324.
Proof. exact (@lem1483519 term23 term4). Qed.
Lemma lem1736804 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736805 : term272 = term4.
Proof. exact (@lem1736804 term273). Qed.
Lemma lem1736806 : term325 = term325.
Proof. exact (eq_refl term325). Qed.
Lemma lem1736807 : term324 = term326.
Proof. exact (MK_COMB (@lem1736806) (@lem1736805)). Qed.
Lemma lem1736808 : term326 = term23.
Proof. exact (@lem1483450 term23). Qed.
Lemma lem1736809 : term324 = term23.
Proof. exact (TRANS (@lem1736807) (@lem1736808)). Qed.
Lemma lem1736811 : term323 = term23.
Proof. exact (TRANS (@lem1736802) (@lem1736809)). Qed.
Lemma lem1736812 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736813 : term327 = term128.
Proof. exact (MK_COMB (@lem1736812) (@lem1736811)). Qed.
Lemma lem1736814 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736815 : (term323 = term4) = (term23 = term4).
Proof. exact (MK_COMB (@lem1736813) (@lem1736814)). Qed.
Lemma lem1736816 : (term23 = term4) = (term23 = term4).
Proof. exact (TRANS (@lem1736796) (@lem1736815)). Qed.
Lemma lem1736817 (x : real) : (term83 x) = (term281 x).
Proof. exact (@lem1483554 x term4). Qed.
Lemma lem1736823 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736825 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736826 : term272 = term4.
Proof. exact (@lem1736825 term273). Qed.
Lemma lem1736827 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736828 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736827 x) (@lem1736826)). Qed.
Lemma lem1736829 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736830 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736828 x) (@lem1736829 x)). Qed.
Lemma lem1736832 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736823 x) (@lem1736830 x)). Qed.
Lemma lem1736833 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1736834 (x : real) : (term282 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1736833) (@lem1736832 x)). Qed.
Lemma lem1736837 (x : real) : (real_neg x) = (term264 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1736838 (x : real) : (term283 x) = (term283 x).
Proof. exact (eq_refl (term283 x)). Qed.
Lemma lem1736839 (x : real) : ((term282 x) = (real_neg x)) = ((term282 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1736838 x) (@lem1736837 x)). Qed.
Lemma lem1736840 (x : real) : (term282 x) = (term264 x).
Proof. exact (EQ_MP (@lem1736839 x) (@lem1736834 x)). Qed.
Lemma lem1736841 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736842 (x : real) : (term284 x) = (term266 x).
Proof. exact (MK_COMB (@lem1736841) (@lem1736840 x)). Qed.
Lemma lem1736843 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736844 (x : real) : (term285 x) = (term267 x).
Proof. exact (MK_COMB (@lem1736842 x) (@lem1736843)). Qed.
Lemma lem1736845 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736846 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1736845) (@lem1736832 x)). Qed.
Lemma lem1736847 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736848 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1736846 x) (@lem1736847)). Qed.
Lemma lem1736849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736850 (x : real) : (term286 x) = (term287 x).
Proof. exact (MK_COMB (@lem1736849) (@lem1736848 x)). Qed.
Lemma lem1736851 (x : real) : (term281 x) = (term288 x).
Proof. exact (MK_COMB (@lem1736850 x) (@lem1736844 x)). Qed.
Lemma lem1736852 (x : real) : (term83 x) = (term288 x).
Proof. exact (TRANS (@lem1736817 x) (@lem1736851 x)). Qed.
Lemma lem1736853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736854 : term129 = term129.
Proof. exact (MK_COMB (@lem1736853) (@lem1736816)). Qed.
Lemma lem1736855 (x : real) : (term130 x) = (term328 x).
Proof. exact (MK_COMB (@lem1736854) (@lem1736852 x)). Qed.
Lemma lem1736856 : term132 = term329.
Proof. exact (@lem1483554 term23 term4). Qed.
Lemma lem1736862 : term323 = term324.
Proof. exact (@lem1483519 term23 term4). Qed.
Lemma lem1736864 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736865 : term272 = term4.
Proof. exact (@lem1736864 term273). Qed.
Lemma lem1736866 : term325 = term325.
Proof. exact (eq_refl term325). Qed.
Lemma lem1736867 : term324 = term326.
Proof. exact (MK_COMB (@lem1736866) (@lem1736865)). Qed.
Lemma lem1736868 : term326 = term23.
Proof. exact (@lem1483450 term23). Qed.
Lemma lem1736869 : term324 = term23.
Proof. exact (TRANS (@lem1736867) (@lem1736868)). Qed.
Lemma lem1736871 : term323 = term23.
Proof. exact (TRANS (@lem1736862) (@lem1736869)). Qed.
Lemma lem1736872 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1736873 : term330 = term331.
Proof. exact (MK_COMB (@lem1736872) (@lem1736871)). Qed.
Lemma lem1736874 : term331 = term332.
Proof. exact (@lem1483512 term23). Qed.
Lemma lem1736876 (m : nat) (n : nat) : (term333 m n) = (term334 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1736877 : term332 = term298.
Proof. exact (@lem1736876 term273 term273). Qed.
Lemma lem1736878 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1736879 : term297 = term273.
Proof. exact (EQ_MP (@lem1736878) (@lem940073)). Qed.
Lemma lem1736880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1736881 : term298 = term13.
Proof. exact (MK_COMB (@lem1736880) (@lem1736879)). Qed.
Lemma lem1736882 : term332 = term13.
Proof. exact (TRANS (@lem1736877) (@lem1736881)). Qed.
Lemma lem1736883 : term331 = term13.
Proof. exact (TRANS (@lem1736874) (@lem1736882)). Qed.
Lemma lem1736884 : term335 = term335.
Proof. exact (eq_refl term335). Qed.
Lemma lem1736885 : (term330 = term331) = (term330 = term13).
Proof. exact (MK_COMB (@lem1736884) (@lem1736883)). Qed.
Lemma lem1736886 : term330 = term13.
Proof. exact (EQ_MP (@lem1736885) (@lem1736873)). Qed.
Lemma lem1736887 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736888 : term336 = term305.
Proof. exact (MK_COMB (@lem1736887) (@lem1736886)). Qed.
Lemma lem1736889 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736890 : term337 = term307.
Proof. exact (MK_COMB (@lem1736888) (@lem1736889)). Qed.
Lemma lem1736891 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736892 : term338 = term301.
Proof. exact (MK_COMB (@lem1736891) (@lem1736871)). Qed.
Lemma lem1736893 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736894 : term339 = term303.
Proof. exact (MK_COMB (@lem1736892) (@lem1736893)). Qed.
Lemma lem1736895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736896 : term340 = term341.
Proof. exact (MK_COMB (@lem1736895) (@lem1736894)). Qed.
Lemma lem1736897 : term329 = term342.
Proof. exact (MK_COMB (@lem1736896) (@lem1736890)). Qed.
Lemma lem1736898 : term132 = term342.
Proof. exact (TRANS (@lem1736856) (@lem1736897)). Qed.
Lemma lem1736899 (x : real) : (x = term4) = ((term269 x) = term4).
Proof. exact (@lem1483529 x term4). Qed.
Lemma lem1736905 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736907 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736908 : term272 = term4.
Proof. exact (@lem1736907 term273). Qed.
Lemma lem1736909 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736910 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736909 x) (@lem1736908)). Qed.
Lemma lem1736911 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736912 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736910 x) (@lem1736911 x)). Qed.
Lemma lem1736914 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736905 x) (@lem1736912 x)). Qed.
Lemma lem1736915 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736916 (x : real) : (term311 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1736915) (@lem1736914 x)). Qed.
Lemma lem1736917 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736918 (x : real) : ((term269 x) = term4) = (x = term4).
Proof. exact (MK_COMB (@lem1736916 x) (@lem1736917)). Qed.
Lemma lem1736919 (x : real) : (x = term4) = (x = term4).
Proof. exact (TRANS (@lem1736899 x) (@lem1736918 x)). Qed.
Lemma lem1736920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736921 : term133 = term343.
Proof. exact (MK_COMB (@lem1736920) (@lem1736898)). Qed.
Lemma lem1736922 (x : real) : (term134 x) = (term344 x).
Proof. exact (MK_COMB (@lem1736921) (@lem1736919 x)). Qed.
Lemma lem1736923 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736924 (x : real) : (term131 x) = (term345 x).
Proof. exact (MK_COMB (@lem1736923) (@lem1736855 x)). Qed.
Lemma lem1736925 (x : real) : (term135 x) = (term346 x).
Proof. exact (MK_COMB (@lem1736924 x) (@lem1736922 x)). Qed.
Lemma lem1736926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736927 (x : real) : (term120 x) = (term347 x).
Proof. exact (MK_COMB (@lem1736926) (@lem1736795 x)). Qed.
Lemma lem1736928 (x : real) : (term136 x) = (term348 x).
Proof. exact (MK_COMB (@lem1736927 x) (@lem1736925 x)). Qed.
Lemma lem1736929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1736930 (x : real) : (term123 x) = (term349 x).
Proof. exact (MK_COMB (@lem1736929) (@lem1736776 x)). Qed.
Lemma lem1736931 (x : real) : (term137 x) = (term350 x).
Proof. exact (MK_COMB (@lem1736930 x) (@lem1736928 x)). Qed.
Lemma lem1736932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1736933 (x : real) : (term351 x) = (term352 x).
Proof. exact (MK_COMB (@lem1736932) (@lem1736620 x)). Qed.
Lemma lem1736934 (x : real) : (term353 x) = (term354 x).
Proof. exact (MK_COMB (@lem1736933 x) (@lem1736931 x)). Qed.
Lemma lem1736935 (x : real) : (term198 x) = (term355 x).
Proof. exact (@lem1483531 x term4). Qed.
Lemma lem1736941 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736943 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736944 : term272 = term4.
Proof. exact (@lem1736943 term273). Qed.
Lemma lem1736945 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736946 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736945 x) (@lem1736944)). Qed.
Lemma lem1736947 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736948 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736946 x) (@lem1736947 x)). Qed.
Lemma lem1736950 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736941 x) (@lem1736948 x)). Qed.
Lemma lem1736951 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1736952 (x : real) : (term356 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1736951) (@lem1736950 x)). Qed.
Lemma lem1736953 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736954 (x : real) : (term355 x) = (term357 x).
Proof. exact (MK_COMB (@lem1736952 x) (@lem1736953)). Qed.
Lemma lem1736955 (x : real) : (term198 x) = (term357 x).
Proof. exact (TRANS (@lem1736935 x) (@lem1736954 x)). Qed.
Lemma lem1736956 (x : real) : (term74 x) = (term268 x).
Proof. exact (@lem1483521 x term4). Qed.
Lemma lem1736962 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1736964 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736965 : term272 = term4.
Proof. exact (@lem1736964 term273). Qed.
Lemma lem1736966 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1736967 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1736966 x) (@lem1736965)). Qed.
Lemma lem1736968 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1736969 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1736967 x) (@lem1736968 x)). Qed.
Lemma lem1736971 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1736962 x) (@lem1736969 x)). Qed.
Lemma lem1736972 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1736973 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1736972) (@lem1736971 x)). Qed.
Lemma lem1736974 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736975 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1736973 x) (@lem1736974)). Qed.
Lemma lem1736976 (x : real) : (term74 x) = (term16 x).
Proof. exact (TRANS (@lem1736956 x) (@lem1736975 x)). Qed.
Lemma lem1736977 : (term13 = term4) = (term276 = term4).
Proof. exact (@lem1483529 term13 term4). Qed.
Lemma lem1736983 : term276 = term277.
Proof. exact (@lem1483519 term13 term4). Qed.
Lemma lem1736985 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1736986 : term272 = term4.
Proof. exact (@lem1736985 term273). Qed.
Lemma lem1736987 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1736988 : term277 = term279.
Proof. exact (MK_COMB (@lem1736987) (@lem1736986)). Qed.
Lemma lem1736989 : term279 = term13.
Proof. exact (@lem1483450 term13). Qed.
Lemma lem1736990 : term277 = term13.
Proof. exact (TRANS (@lem1736988) (@lem1736989)). Qed.
Lemma lem1736992 : term276 = term13.
Proof. exact (TRANS (@lem1736983) (@lem1736990)). Qed.
Lemma lem1736993 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1736994 : term280 = term98.
Proof. exact (MK_COMB (@lem1736993) (@lem1736992)). Qed.
Lemma lem1736995 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1736996 : (term276 = term4) = (term13 = term4).
Proof. exact (MK_COMB (@lem1736994) (@lem1736995)). Qed.
Lemma lem1736997 : (term13 = term4) = (term13 = term4).
Proof. exact (TRANS (@lem1736977) (@lem1736996)). Qed.
Lemma lem1736998 (x : real) : (term83 x) = (term281 x).
Proof. exact (@lem1483554 x term4). Qed.
Lemma lem1737004 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737006 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737007 : term272 = term4.
Proof. exact (@lem1737006 term273). Qed.
Lemma lem1737008 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737009 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737008 x) (@lem1737007)). Qed.
Lemma lem1737010 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737011 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737009 x) (@lem1737010 x)). Qed.
Lemma lem1737013 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737004 x) (@lem1737011 x)). Qed.
Lemma lem1737014 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737015 (x : real) : (term282 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1737014) (@lem1737013 x)). Qed.
Lemma lem1737018 (x : real) : (real_neg x) = (term264 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1737019 (x : real) : (term283 x) = (term283 x).
Proof. exact (eq_refl (term283 x)). Qed.
Lemma lem1737020 (x : real) : ((term282 x) = (real_neg x)) = ((term282 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1737019 x) (@lem1737018 x)). Qed.
Lemma lem1737021 (x : real) : (term282 x) = (term264 x).
Proof. exact (EQ_MP (@lem1737020 x) (@lem1737015 x)). Qed.
Lemma lem1737022 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737023 (x : real) : (term284 x) = (term266 x).
Proof. exact (MK_COMB (@lem1737022) (@lem1737021 x)). Qed.
Lemma lem1737024 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737025 (x : real) : (term285 x) = (term267 x).
Proof. exact (MK_COMB (@lem1737023 x) (@lem1737024)). Qed.
Lemma lem1737026 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737027 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737026) (@lem1737013 x)). Qed.
Lemma lem1737028 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737029 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737027 x) (@lem1737028)). Qed.
Lemma lem1737030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737031 (x : real) : (term286 x) = (term287 x).
Proof. exact (MK_COMB (@lem1737030) (@lem1737029 x)). Qed.
Lemma lem1737032 (x : real) : (term281 x) = (term288 x).
Proof. exact (MK_COMB (@lem1737031 x) (@lem1737025 x)). Qed.
Lemma lem1737033 (x : real) : (term83 x) = (term288 x).
Proof. exact (TRANS (@lem1736998 x) (@lem1737032 x)). Qed.
Lemma lem1737034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737035 : term99 = term99.
Proof. exact (MK_COMB (@lem1737034) (@lem1736997)). Qed.
Lemma lem1737036 (x : real) : (term100 x) = (term289 x).
Proof. exact (MK_COMB (@lem1737035) (@lem1737033 x)). Qed.
Lemma lem1737037 : term102 = term290.
Proof. exact (@lem1483554 term13 term4). Qed.
Lemma lem1737043 : term276 = term277.
Proof. exact (@lem1483519 term13 term4). Qed.
Lemma lem1737045 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737046 : term272 = term4.
Proof. exact (@lem1737045 term273). Qed.
Lemma lem1737047 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1737048 : term277 = term279.
Proof. exact (MK_COMB (@lem1737047) (@lem1737046)). Qed.
Lemma lem1737049 : term279 = term13.
Proof. exact (@lem1483450 term13). Qed.
Lemma lem1737050 : term277 = term13.
Proof. exact (TRANS (@lem1737048) (@lem1737049)). Qed.
Lemma lem1737052 : term276 = term13.
Proof. exact (TRANS (@lem1737043) (@lem1737050)). Qed.
Lemma lem1737053 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737054 : term291 = term23.
Proof. exact (MK_COMB (@lem1737053) (@lem1737052)). Qed.
Lemma lem1737055 : term23 = term292.
Proof. exact (@lem1483512 term13). Qed.
Lemma lem1737057 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1737058 : term292 = term295.
Proof. exact (@lem1737057 term273 term273). Qed.
Lemma lem1737059 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737060 : term297 = term273.
Proof. exact (EQ_MP (@lem1737059) (@lem940073)). Qed.
Lemma lem1737061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737062 : term298 = term13.
Proof. exact (MK_COMB (@lem1737061) (@lem1737060)). Qed.
Lemma lem1737063 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737064 : term295 = term23.
Proof. exact (MK_COMB (@lem1737063) (@lem1737062)). Qed.
Lemma lem1737065 : term292 = term23.
Proof. exact (TRANS (@lem1737058) (@lem1737064)). Qed.
Lemma lem1737066 : term23 = term23.
Proof. exact (TRANS (@lem1737055) (@lem1737065)). Qed.
Lemma lem1737067 : term299 = term299.
Proof. exact (eq_refl term299). Qed.
Lemma lem1737068 : (term291 = term23) = (term291 = term23).
Proof. exact (MK_COMB (@lem1737067) (@lem1737066)). Qed.
Lemma lem1737069 : term291 = term23.
Proof. exact (EQ_MP (@lem1737068) (@lem1737054)). Qed.
Lemma lem1737070 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737071 : term300 = term301.
Proof. exact (MK_COMB (@lem1737070) (@lem1737069)). Qed.
Lemma lem1737072 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737073 : term302 = term303.
Proof. exact (MK_COMB (@lem1737071) (@lem1737072)). Qed.
Lemma lem1737074 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737075 : term304 = term305.
Proof. exact (MK_COMB (@lem1737074) (@lem1737052)). Qed.
Lemma lem1737076 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737077 : term306 = term307.
Proof. exact (MK_COMB (@lem1737075) (@lem1737076)). Qed.
Lemma lem1737078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737079 : term308 = term309.
Proof. exact (MK_COMB (@lem1737078) (@lem1737077)). Qed.
Lemma lem1737080 : term290 = term310.
Proof. exact (MK_COMB (@lem1737079) (@lem1737073)). Qed.
Lemma lem1737081 : term102 = term310.
Proof. exact (TRANS (@lem1737037) (@lem1737080)). Qed.
Lemma lem1737082 (x : real) : (x = term4) = ((term269 x) = term4).
Proof. exact (@lem1483529 x term4). Qed.
Lemma lem1737088 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737090 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737091 : term272 = term4.
Proof. exact (@lem1737090 term273). Qed.
Lemma lem1737092 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737093 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737092 x) (@lem1737091)). Qed.
Lemma lem1737094 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737095 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737093 x) (@lem1737094 x)). Qed.
Lemma lem1737097 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737088 x) (@lem1737095 x)). Qed.
Lemma lem1737098 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1737099 (x : real) : (term311 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1737098) (@lem1737097 x)). Qed.
Lemma lem1737100 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737101 (x : real) : ((term269 x) = term4) = (x = term4).
Proof. exact (MK_COMB (@lem1737099 x) (@lem1737100)). Qed.
Lemma lem1737102 (x : real) : (x = term4) = (x = term4).
Proof. exact (TRANS (@lem1737082 x) (@lem1737101 x)). Qed.
Lemma lem1737103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737104 : term103 = term312.
Proof. exact (MK_COMB (@lem1737103) (@lem1737081)). Qed.
Lemma lem1737105 (x : real) : (term104 x) = (term313 x).
Proof. exact (MK_COMB (@lem1737104) (@lem1737102 x)). Qed.
Lemma lem1737106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737107 (x : real) : (term101 x) = (term314 x).
Proof. exact (MK_COMB (@lem1737106) (@lem1737036 x)). Qed.
Lemma lem1737108 (x : real) : (term105 x) = (term315 x).
Proof. exact (MK_COMB (@lem1737107 x) (@lem1737105 x)). Qed.
Lemma lem1737109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737110 (x : real) : (term226 x) = (term316 x).
Proof. exact (MK_COMB (@lem1737109) (@lem1736976 x)). Qed.
Lemma lem1737111 (x : real) : (term317 x) = (term318 x).
Proof. exact (MK_COMB (@lem1737110 x) (@lem1737108 x)). Qed.
Lemma lem1737112 (x : real) : (term248 x) = (term319 x).
Proof. exact (@lem1483531 term4 x). Qed.
Lemma lem1737118 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737123 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737125 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737118 x) (@lem1737123 x)). Qed.
Lemma lem1737126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737127 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737126) (@lem1737125 x)). Qed.
Lemma lem1737128 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737129 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737127 x) (@lem1737128)). Qed.
Lemma lem1737130 (x : real) : (term248 x) = (term322 x).
Proof. exact (TRANS (@lem1737112 x) (@lem1737129 x)). Qed.
Lemma lem1737131 (x : real) : (term83 x) = (term281 x).
Proof. exact (@lem1483554 x term4). Qed.
Lemma lem1737137 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737139 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737140 : term272 = term4.
Proof. exact (@lem1737139 term273). Qed.
Lemma lem1737141 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737142 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737141 x) (@lem1737140)). Qed.
Lemma lem1737143 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737144 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737142 x) (@lem1737143 x)). Qed.
Lemma lem1737146 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737137 x) (@lem1737144 x)). Qed.
Lemma lem1737147 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737148 (x : real) : (term282 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1737147) (@lem1737146 x)). Qed.
Lemma lem1737151 (x : real) : (real_neg x) = (term264 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1737152 (x : real) : (term283 x) = (term283 x).
Proof. exact (eq_refl (term283 x)). Qed.
Lemma lem1737153 (x : real) : ((term282 x) = (real_neg x)) = ((term282 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1737152 x) (@lem1737151 x)). Qed.
Lemma lem1737154 (x : real) : (term282 x) = (term264 x).
Proof. exact (EQ_MP (@lem1737153 x) (@lem1737148 x)). Qed.
Lemma lem1737155 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737156 (x : real) : (term284 x) = (term266 x).
Proof. exact (MK_COMB (@lem1737155) (@lem1737154 x)). Qed.
Lemma lem1737157 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737158 (x : real) : (term285 x) = (term267 x).
Proof. exact (MK_COMB (@lem1737156 x) (@lem1737157)). Qed.
Lemma lem1737159 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737160 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737159) (@lem1737146 x)). Qed.
Lemma lem1737161 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737162 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737160 x) (@lem1737161)). Qed.
Lemma lem1737163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737164 (x : real) : (term286 x) = (term287 x).
Proof. exact (MK_COMB (@lem1737163) (@lem1737162 x)). Qed.
Lemma lem1737165 (x : real) : (term281 x) = (term288 x).
Proof. exact (MK_COMB (@lem1737164 x) (@lem1737158 x)). Qed.
Lemma lem1737166 (x : real) : (term83 x) = (term288 x).
Proof. exact (TRANS (@lem1737131 x) (@lem1737165 x)). Qed.
Lemma lem1737167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737168 (x : real) : (term120 x) = (term347 x).
Proof. exact (MK_COMB (@lem1737167) (@lem1737130 x)). Qed.
Lemma lem1737169 (x : real) : (term122 x) = (term358 x).
Proof. exact (MK_COMB (@lem1737168 x) (@lem1737166 x)). Qed.
Lemma lem1737170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737171 (x : real) : (term123 x) = (term349 x).
Proof. exact (MK_COMB (@lem1737170) (@lem1737111 x)). Qed.
Lemma lem1737172 (x : real) : (term124 x) = (term359 x).
Proof. exact (MK_COMB (@lem1737171 x) (@lem1737169 x)). Qed.
Lemma lem1737173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737174 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1737173) (@lem1736955 x)). Qed.
Lemma lem1737175 (x : real) : (term362 x) = (term363 x).
Proof. exact (MK_COMB (@lem1737174 x) (@lem1737172 x)). Qed.
Lemma lem1737176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737177 (x : real) : (term364 x) = (term365 x).
Proof. exact (MK_COMB (@lem1737176) (@lem1736934 x)). Qed.
Lemma lem1737178 (x : real) : (term141 x) = (term366 x).
Proof. exact (MK_COMB (@lem1737177 x) (@lem1737175 x)). Qed.
Lemma lem1737179 : term143 = term367.
Proof. exact (fun_ext (fun x : real => @lem1737178 x)). Qed.
Lemma lem1737180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1737181 : term144 = term368.
Proof. exact (MK_COMB (@lem1737180) (@lem1737179)). Qed.
Lemma lem1737182 (x : real) : (term26 x) = (term261 x).
Proof. exact (@lem1483521 term4 x). Qed.
Lemma lem1737188 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737193 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737195 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737188 x) (@lem1737193 x)). Qed.
Lemma lem1737196 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737197 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1737196) (@lem1737195 x)). Qed.
Lemma lem1737198 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737199 (x : real) : (term261 x) = (term267 x).
Proof. exact (MK_COMB (@lem1737197 x) (@lem1737198)). Qed.
Lemma lem1737200 (x : real) : (term26 x) = (term267 x).
Proof. exact (TRANS (@lem1737182 x) (@lem1737199 x)). Qed.
Lemma lem1737201 (x : real) : (term74 x) = (term268 x).
Proof. exact (@lem1483521 x term4). Qed.
Lemma lem1737207 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737209 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737210 : term272 = term4.
Proof. exact (@lem1737209 term273). Qed.
Lemma lem1737211 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737212 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737211 x) (@lem1737210)). Qed.
Lemma lem1737213 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737214 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737212 x) (@lem1737213 x)). Qed.
Lemma lem1737216 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737207 x) (@lem1737214 x)). Qed.
Lemma lem1737217 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737218 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737217) (@lem1737216 x)). Qed.
Lemma lem1737219 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737220 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737218 x) (@lem1737219)). Qed.
Lemma lem1737221 (x : real) : (term74 x) = (term16 x).
Proof. exact (TRANS (@lem1737201 x) (@lem1737220 x)). Qed.
Lemma lem1737222 (x : real) : (term147 x) = (term319 x).
Proof. exact (@lem1483535 term4 x). Qed.
Lemma lem1737228 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737233 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737235 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737228 x) (@lem1737233 x)). Qed.
Lemma lem1737236 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737237 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737236) (@lem1737235 x)). Qed.
Lemma lem1737238 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737239 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737237 x) (@lem1737238)). Qed.
Lemma lem1737240 (x : real) : (term147 x) = (term322 x).
Proof. exact (TRANS (@lem1737222 x) (@lem1737239 x)). Qed.
Lemma lem1737241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737242 (x : real) : (term226 x) = (term316 x).
Proof. exact (MK_COMB (@lem1737241) (@lem1737221 x)). Qed.
Lemma lem1737243 (x : real) : (term369 x) = (term370 x).
Proof. exact (MK_COMB (@lem1737242 x) (@lem1737240 x)). Qed.
Lemma lem1737244 (x : real) : (term248 x) = (term319 x).
Proof. exact (@lem1483531 term4 x). Qed.
Lemma lem1737250 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737255 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737257 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737250 x) (@lem1737255 x)). Qed.
Lemma lem1737258 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737259 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737258) (@lem1737257 x)). Qed.
Lemma lem1737260 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737261 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737259 x) (@lem1737260)). Qed.
Lemma lem1737262 (x : real) : (term248 x) = (term322 x).
Proof. exact (TRANS (@lem1737244 x) (@lem1737261 x)). Qed.
Lemma lem1737263 : (term23 = term13) = (term371 = term4).
Proof. exact (@lem1483529 term23 term13). Qed.
Lemma lem1737269 : term371 = term372.
Proof. exact (@lem1483519 term23 term13). Qed.
Lemma lem1737271 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1737272 : term292 = term295.
Proof. exact (@lem1737271 term273 term273). Qed.
Lemma lem1737273 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737274 : term297 = term273.
Proof. exact (EQ_MP (@lem1737273) (@lem940073)). Qed.
Lemma lem1737275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737276 : term298 = term13.
Proof. exact (MK_COMB (@lem1737275) (@lem1737274)). Qed.
Lemma lem1737277 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737278 : term295 = term23.
Proof. exact (MK_COMB (@lem1737277) (@lem1737276)). Qed.
Lemma lem1737279 : term292 = term23.
Proof. exact (TRANS (@lem1737272) (@lem1737278)). Qed.
Lemma lem1737280 : term325 = term325.
Proof. exact (eq_refl term325). Qed.
Lemma lem1737281 : term372 = term373.
Proof. exact (MK_COMB (@lem1737280) (@lem1737279)). Qed.
Lemma lem1737282 : term373 = term374.
Proof. exact (@lem1367763 term273 term273). Qed.
Lemma lem1737283 : term375 = term376.
Proof. exact (@lem706885). Qed.
Lemma lem1737284 : (term375 = term376) = (term377 = term378).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term376). Qed.
Lemma lem1737285 : term377 = term378.
Proof. exact (EQ_MP (@lem1737284) (@lem1737283)). Qed.
Lemma lem1737286 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737287 : term379 = term380.
Proof. exact (MK_COMB (@lem1737286) (@lem1737285)). Qed.
Lemma lem1737288 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737289 : term374 = term381.
Proof. exact (MK_COMB (@lem1737288) (@lem1737287)). Qed.
Lemma lem1737290 : term373 = term381.
Proof. exact (TRANS (@lem1737282) (@lem1737289)). Qed.
Lemma lem1737291 : term372 = term381.
Proof. exact (TRANS (@lem1737281) (@lem1737290)). Qed.
Lemma lem1737293 : term371 = term381.
Proof. exact (TRANS (@lem1737269) (@lem1737291)). Qed.
Lemma lem1737294 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1737295 : term382 = term383.
Proof. exact (MK_COMB (@lem1737294) (@lem1737293)). Qed.
Lemma lem1737296 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737297 : (term371 = term4) = (term381 = term4).
Proof. exact (MK_COMB (@lem1737295) (@lem1737296)). Qed.
Lemma lem1737298 : (term23 = term13) = (term381 = term4).
Proof. exact (TRANS (@lem1737263) (@lem1737297)). Qed.
Lemma lem1737299 (x : real) : (term147 x) = (term319 x).
Proof. exact (@lem1483535 term4 x). Qed.
Lemma lem1737305 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737310 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737312 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737305 x) (@lem1737310 x)). Qed.
Lemma lem1737313 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737314 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737313) (@lem1737312 x)). Qed.
Lemma lem1737315 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737316 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737314 x) (@lem1737315)). Qed.
Lemma lem1737317 (x : real) : (term147 x) = (term322 x).
Proof. exact (TRANS (@lem1737299 x) (@lem1737316 x)). Qed.
Lemma lem1737318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737319 : term180 = term384.
Proof. exact (MK_COMB (@lem1737318) (@lem1737298)). Qed.
Lemma lem1737320 (x : real) : (term181 x) = (term385 x).
Proof. exact (MK_COMB (@lem1737319) (@lem1737317 x)). Qed.
Lemma lem1737321 : term183 = term386.
Proof. exact (@lem1483554 term23 term13). Qed.
Lemma lem1737327 : term371 = term372.
Proof. exact (@lem1483519 term23 term13). Qed.
Lemma lem1737329 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1737330 : term292 = term295.
Proof. exact (@lem1737329 term273 term273). Qed.
Lemma lem1737331 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737332 : term297 = term273.
Proof. exact (EQ_MP (@lem1737331) (@lem940073)). Qed.
Lemma lem1737333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737334 : term298 = term13.
Proof. exact (MK_COMB (@lem1737333) (@lem1737332)). Qed.
Lemma lem1737335 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737336 : term295 = term23.
Proof. exact (MK_COMB (@lem1737335) (@lem1737334)). Qed.
Lemma lem1737337 : term292 = term23.
Proof. exact (TRANS (@lem1737330) (@lem1737336)). Qed.
Lemma lem1737338 : term325 = term325.
Proof. exact (eq_refl term325). Qed.
Lemma lem1737339 : term372 = term373.
Proof. exact (MK_COMB (@lem1737338) (@lem1737337)). Qed.
Lemma lem1737340 : term373 = term374.
Proof. exact (@lem1367763 term273 term273). Qed.
Lemma lem1737341 : term375 = term376.
Proof. exact (@lem706885). Qed.
Lemma lem1737342 : (term375 = term376) = (term377 = term378).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term376). Qed.
Lemma lem1737343 : term377 = term378.
Proof. exact (EQ_MP (@lem1737342) (@lem1737341)). Qed.
Lemma lem1737344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737345 : term379 = term380.
Proof. exact (MK_COMB (@lem1737344) (@lem1737343)). Qed.
Lemma lem1737346 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737347 : term374 = term381.
Proof. exact (MK_COMB (@lem1737346) (@lem1737345)). Qed.
Lemma lem1737348 : term373 = term381.
Proof. exact (TRANS (@lem1737340) (@lem1737347)). Qed.
Lemma lem1737349 : term372 = term381.
Proof. exact (TRANS (@lem1737339) (@lem1737348)). Qed.
Lemma lem1737351 : term371 = term381.
Proof. exact (TRANS (@lem1737327) (@lem1737349)). Qed.
Lemma lem1737352 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737353 : term387 = term388.
Proof. exact (MK_COMB (@lem1737352) (@lem1737351)). Qed.
Lemma lem1737354 : term388 = term389.
Proof. exact (@lem1483512 term381). Qed.
Lemma lem1737356 (m : nat) (n : nat) : (term333 m n) = (term334 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1737357 : term389 = term390.
Proof. exact (@lem1737356 term273 term378). Qed.
Lemma lem1737358 : term391 = term376.
Proof. exact (@lem996238 term376). Qed.
Lemma lem1737359 : (term391 = term376) = (term392 = term378).
Proof. exact (@lem1007663 (BIT1 0) term376 term376). Qed.
Lemma lem1737360 : term392 = term378.
Proof. exact (EQ_MP (@lem1737359) (@lem1737358)). Qed.
Lemma lem1737361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737362 : term390 = term380.
Proof. exact (MK_COMB (@lem1737361) (@lem1737360)). Qed.
Lemma lem1737363 : term389 = term380.
Proof. exact (TRANS (@lem1737357) (@lem1737362)). Qed.
Lemma lem1737364 : term388 = term380.
Proof. exact (TRANS (@lem1737354) (@lem1737363)). Qed.
Lemma lem1737365 : term393 = term393.
Proof. exact (eq_refl term393). Qed.
Lemma lem1737366 : (term387 = term388) = (term387 = term380).
Proof. exact (MK_COMB (@lem1737365) (@lem1737364)). Qed.
Lemma lem1737367 : term387 = term380.
Proof. exact (EQ_MP (@lem1737366) (@lem1737353)). Qed.
Lemma lem1737368 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737369 : term394 = term395.
Proof. exact (MK_COMB (@lem1737368) (@lem1737367)). Qed.
Lemma lem1737370 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737371 : term396 = term397.
Proof. exact (MK_COMB (@lem1737369) (@lem1737370)). Qed.
Lemma lem1737372 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737373 : term398 = term399.
Proof. exact (MK_COMB (@lem1737372) (@lem1737351)). Qed.
Lemma lem1737374 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737375 : term400 = term401.
Proof. exact (MK_COMB (@lem1737373) (@lem1737374)). Qed.
Lemma lem1737376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737377 : term402 = term403.
Proof. exact (MK_COMB (@lem1737376) (@lem1737375)). Qed.
Lemma lem1737378 : term386 = term404.
Proof. exact (MK_COMB (@lem1737377) (@lem1737371)). Qed.
Lemma lem1737379 : term183 = term404.
Proof. exact (TRANS (@lem1737321) (@lem1737378)). Qed.
Lemma lem1737380 (x : real) : (term16 x) = (term268 x).
Proof. exact (@lem1483525 x term4). Qed.
Lemma lem1737386 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737388 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737389 : term272 = term4.
Proof. exact (@lem1737388 term273). Qed.
Lemma lem1737390 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737391 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737390 x) (@lem1737389)). Qed.
Lemma lem1737392 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737393 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737391 x) (@lem1737392 x)). Qed.
Lemma lem1737395 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737386 x) (@lem1737393 x)). Qed.
Lemma lem1737396 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737397 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737396) (@lem1737395 x)). Qed.
Lemma lem1737398 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737399 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737397 x) (@lem1737398)). Qed.
Lemma lem1737400 (x : real) : (term16 x) = (term16 x).
Proof. exact (TRANS (@lem1737380 x) (@lem1737399 x)). Qed.
Lemma lem1737401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737402 : term184 = term405.
Proof. exact (MK_COMB (@lem1737401) (@lem1737379)). Qed.
Lemma lem1737403 (x : real) : (term185 x) = (term406 x).
Proof. exact (MK_COMB (@lem1737402) (@lem1737400 x)). Qed.
Lemma lem1737404 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737405 (x : real) : (term182 x) = (term407 x).
Proof. exact (MK_COMB (@lem1737404) (@lem1737320 x)). Qed.
Lemma lem1737406 (x : real) : (term186 x) = (term408 x).
Proof. exact (MK_COMB (@lem1737405 x) (@lem1737403 x)). Qed.
Lemma lem1737407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737408 (x : real) : (term120 x) = (term347 x).
Proof. exact (MK_COMB (@lem1737407) (@lem1737262 x)). Qed.
Lemma lem1737409 (x : real) : (term187 x) = (term409 x).
Proof. exact (MK_COMB (@lem1737408 x) (@lem1737406 x)). Qed.
Lemma lem1737410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737411 (x : real) : (term177 x) = (term410 x).
Proof. exact (MK_COMB (@lem1737410) (@lem1737243 x)). Qed.
Lemma lem1737412 (x : real) : (term188 x) = (term411 x).
Proof. exact (MK_COMB (@lem1737411 x) (@lem1737409 x)). Qed.
Lemma lem1737413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737414 (x : real) : (term351 x) = (term352 x).
Proof. exact (MK_COMB (@lem1737413) (@lem1737200 x)). Qed.
Lemma lem1737415 (x : real) : (term412 x) = (term413 x).
Proof. exact (MK_COMB (@lem1737414 x) (@lem1737412 x)). Qed.
Lemma lem1737416 (x : real) : (term198 x) = (term355 x).
Proof. exact (@lem1483531 x term4). Qed.
Lemma lem1737422 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737424 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737425 : term272 = term4.
Proof. exact (@lem1737424 term273). Qed.
Lemma lem1737426 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737427 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737426 x) (@lem1737425)). Qed.
Lemma lem1737428 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737429 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737427 x) (@lem1737428 x)). Qed.
Lemma lem1737431 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737422 x) (@lem1737429 x)). Qed.
Lemma lem1737432 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737433 (x : real) : (term356 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1737432) (@lem1737431 x)). Qed.
Lemma lem1737434 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737435 (x : real) : (term355 x) = (term357 x).
Proof. exact (MK_COMB (@lem1737433 x) (@lem1737434)). Qed.
Lemma lem1737436 (x : real) : (term198 x) = (term357 x).
Proof. exact (TRANS (@lem1737416 x) (@lem1737435 x)). Qed.
Lemma lem1737437 (x : real) : (term74 x) = (term268 x).
Proof. exact (@lem1483521 x term4). Qed.
Lemma lem1737443 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737445 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737446 : term272 = term4.
Proof. exact (@lem1737445 term273). Qed.
Lemma lem1737447 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737448 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737447 x) (@lem1737446)). Qed.
Lemma lem1737449 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737450 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737448 x) (@lem1737449 x)). Qed.
Lemma lem1737452 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737443 x) (@lem1737450 x)). Qed.
Lemma lem1737453 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737454 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737453) (@lem1737452 x)). Qed.
Lemma lem1737455 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737456 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737454 x) (@lem1737455)). Qed.
Lemma lem1737457 (x : real) : (term74 x) = (term16 x).
Proof. exact (TRANS (@lem1737437 x) (@lem1737456 x)). Qed.
Lemma lem1737458 (x : real) : (term147 x) = (term319 x).
Proof. exact (@lem1483535 term4 x). Qed.
Lemma lem1737464 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737469 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737471 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737464 x) (@lem1737469 x)). Qed.
Lemma lem1737472 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737473 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737472) (@lem1737471 x)). Qed.
Lemma lem1737474 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737475 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737473 x) (@lem1737474)). Qed.
Lemma lem1737476 (x : real) : (term147 x) = (term322 x).
Proof. exact (TRANS (@lem1737458 x) (@lem1737475 x)). Qed.
Lemma lem1737477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737478 (x : real) : (term226 x) = (term316 x).
Proof. exact (MK_COMB (@lem1737477) (@lem1737457 x)). Qed.
Lemma lem1737479 (x : real) : (term369 x) = (term370 x).
Proof. exact (MK_COMB (@lem1737478 x) (@lem1737476 x)). Qed.
Lemma lem1737480 (x : real) : (term248 x) = (term319 x).
Proof. exact (@lem1483531 term4 x). Qed.
Lemma lem1737486 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737491 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737493 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737486 x) (@lem1737491 x)). Qed.
Lemma lem1737494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737495 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737494) (@lem1737493 x)). Qed.
Lemma lem1737496 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737497 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737495 x) (@lem1737496)). Qed.
Lemma lem1737498 (x : real) : (term248 x) = (term322 x).
Proof. exact (TRANS (@lem1737480 x) (@lem1737497 x)). Qed.
Lemma lem1737499 : (term4 = term13) = (term414 = term4).
Proof. exact (@lem1483529 term4 term13). Qed.
Lemma lem1737505 : term414 = term415.
Proof. exact (@lem1483519 term4 term13). Qed.
Lemma lem1737507 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1737508 : term292 = term295.
Proof. exact (@lem1737507 term273 term273). Qed.
Lemma lem1737509 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737510 : term297 = term273.
Proof. exact (EQ_MP (@lem1737509) (@lem940073)). Qed.
Lemma lem1737511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737512 : term298 = term13.
Proof. exact (MK_COMB (@lem1737511) (@lem1737510)). Qed.
Lemma lem1737513 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737514 : term295 = term23.
Proof. exact (MK_COMB (@lem1737513) (@lem1737512)). Qed.
Lemma lem1737515 : term292 = term23.
Proof. exact (TRANS (@lem1737508) (@lem1737514)). Qed.
Lemma lem1737516 : term416 = term416.
Proof. exact (eq_refl term416). Qed.
Lemma lem1737517 : term415 = term417.
Proof. exact (MK_COMB (@lem1737516) (@lem1737515)). Qed.
Lemma lem1737518 : term417 = term23.
Proof. exact (@lem1483448 term23). Qed.
Lemma lem1737519 : term415 = term23.
Proof. exact (TRANS (@lem1737517) (@lem1737518)). Qed.
Lemma lem1737521 : term414 = term23.
Proof. exact (TRANS (@lem1737505) (@lem1737519)). Qed.
Lemma lem1737522 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1737523 : term418 = term128.
Proof. exact (MK_COMB (@lem1737522) (@lem1737521)). Qed.
Lemma lem1737524 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737525 : (term414 = term4) = (term23 = term4).
Proof. exact (MK_COMB (@lem1737523) (@lem1737524)). Qed.
Lemma lem1737526 : (term4 = term13) = (term23 = term4).
Proof. exact (TRANS (@lem1737499) (@lem1737525)). Qed.
Lemma lem1737527 (x : real) : (term147 x) = (term319 x).
Proof. exact (@lem1483535 term4 x). Qed.
Lemma lem1737533 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737538 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737540 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737533 x) (@lem1737538 x)). Qed.
Lemma lem1737541 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737542 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737541) (@lem1737540 x)). Qed.
Lemma lem1737543 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737544 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737542 x) (@lem1737543)). Qed.
Lemma lem1737545 (x : real) : (term147 x) = (term322 x).
Proof. exact (TRANS (@lem1737527 x) (@lem1737544 x)). Qed.
Lemma lem1737546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737547 : term168 = term129.
Proof. exact (MK_COMB (@lem1737546) (@lem1737526)). Qed.
Lemma lem1737548 (x : real) : (term169 x) = (term419 x).
Proof. exact (MK_COMB (@lem1737547) (@lem1737545 x)). Qed.
Lemma lem1737549 : term171 = term420.
Proof. exact (@lem1483554 term4 term13). Qed.
Lemma lem1737555 : term414 = term415.
Proof. exact (@lem1483519 term4 term13). Qed.
Lemma lem1737557 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1737558 : term292 = term295.
Proof. exact (@lem1737557 term273 term273). Qed.
Lemma lem1737559 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737560 : term297 = term273.
Proof. exact (EQ_MP (@lem1737559) (@lem940073)). Qed.
Lemma lem1737561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737562 : term298 = term13.
Proof. exact (MK_COMB (@lem1737561) (@lem1737560)). Qed.
Lemma lem1737563 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737564 : term295 = term23.
Proof. exact (MK_COMB (@lem1737563) (@lem1737562)). Qed.
Lemma lem1737565 : term292 = term23.
Proof. exact (TRANS (@lem1737558) (@lem1737564)). Qed.
Lemma lem1737566 : term416 = term416.
Proof. exact (eq_refl term416). Qed.
Lemma lem1737567 : term415 = term417.
Proof. exact (MK_COMB (@lem1737566) (@lem1737565)). Qed.
Lemma lem1737568 : term417 = term23.
Proof. exact (@lem1483448 term23). Qed.
Lemma lem1737569 : term415 = term23.
Proof. exact (TRANS (@lem1737567) (@lem1737568)). Qed.
Lemma lem1737571 : term414 = term23.
Proof. exact (TRANS (@lem1737555) (@lem1737569)). Qed.
Lemma lem1737572 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737573 : term421 = term331.
Proof. exact (MK_COMB (@lem1737572) (@lem1737571)). Qed.
Lemma lem1737574 : term331 = term332.
Proof. exact (@lem1483512 term23). Qed.
Lemma lem1737576 (m : nat) (n : nat) : (term333 m n) = (term334 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1737577 : term332 = term298.
Proof. exact (@lem1737576 term273 term273). Qed.
Lemma lem1737578 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737579 : term297 = term273.
Proof. exact (EQ_MP (@lem1737578) (@lem940073)). Qed.
Lemma lem1737580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737581 : term298 = term13.
Proof. exact (MK_COMB (@lem1737580) (@lem1737579)). Qed.
Lemma lem1737582 : term332 = term13.
Proof. exact (TRANS (@lem1737577) (@lem1737581)). Qed.
Lemma lem1737583 : term331 = term13.
Proof. exact (TRANS (@lem1737574) (@lem1737582)). Qed.
Lemma lem1737584 : term422 = term422.
Proof. exact (eq_refl term422). Qed.
Lemma lem1737585 : (term421 = term331) = (term421 = term13).
Proof. exact (MK_COMB (@lem1737584) (@lem1737583)). Qed.
Lemma lem1737586 : term421 = term13.
Proof. exact (EQ_MP (@lem1737585) (@lem1737573)). Qed.
Lemma lem1737587 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737588 : term423 = term305.
Proof. exact (MK_COMB (@lem1737587) (@lem1737586)). Qed.
Lemma lem1737589 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737590 : term424 = term307.
Proof. exact (MK_COMB (@lem1737588) (@lem1737589)). Qed.
Lemma lem1737591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737592 : term425 = term301.
Proof. exact (MK_COMB (@lem1737591) (@lem1737571)). Qed.
Lemma lem1737593 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737594 : term426 = term303.
Proof. exact (MK_COMB (@lem1737592) (@lem1737593)). Qed.
Lemma lem1737595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737596 : term427 = term341.
Proof. exact (MK_COMB (@lem1737595) (@lem1737594)). Qed.
Lemma lem1737597 : term420 = term342.
Proof. exact (MK_COMB (@lem1737596) (@lem1737590)). Qed.
Lemma lem1737598 : term171 = term342.
Proof. exact (TRANS (@lem1737549) (@lem1737597)). Qed.
Lemma lem1737599 (x : real) : (term16 x) = (term268 x).
Proof. exact (@lem1483525 x term4). Qed.
Lemma lem1737605 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737607 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737608 : term272 = term4.
Proof. exact (@lem1737607 term273). Qed.
Lemma lem1737609 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737610 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737609 x) (@lem1737608)). Qed.
Lemma lem1737611 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737612 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737610 x) (@lem1737611 x)). Qed.
Lemma lem1737614 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737605 x) (@lem1737612 x)). Qed.
Lemma lem1737615 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737616 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737615) (@lem1737614 x)). Qed.
Lemma lem1737617 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737618 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737616 x) (@lem1737617)). Qed.
Lemma lem1737619 (x : real) : (term16 x) = (term16 x).
Proof. exact (TRANS (@lem1737599 x) (@lem1737618 x)). Qed.
Lemma lem1737620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737621 : term172 = term343.
Proof. exact (MK_COMB (@lem1737620) (@lem1737598)). Qed.
Lemma lem1737622 (x : real) : (term173 x) = (term428 x).
Proof. exact (MK_COMB (@lem1737621) (@lem1737619 x)). Qed.
Lemma lem1737623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737624 (x : real) : (term170 x) = (term429 x).
Proof. exact (MK_COMB (@lem1737623) (@lem1737548 x)). Qed.
Lemma lem1737625 (x : real) : (term174 x) = (term430 x).
Proof. exact (MK_COMB (@lem1737624 x) (@lem1737622 x)). Qed.
Lemma lem1737626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737627 (x : real) : (term120 x) = (term347 x).
Proof. exact (MK_COMB (@lem1737626) (@lem1737498 x)). Qed.
Lemma lem1737628 (x : real) : (term176 x) = (term431 x).
Proof. exact (MK_COMB (@lem1737627 x) (@lem1737625 x)). Qed.
Lemma lem1737629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737630 (x : real) : (term177 x) = (term410 x).
Proof. exact (MK_COMB (@lem1737629) (@lem1737479 x)). Qed.
Lemma lem1737631 (x : real) : (term178 x) = (term432 x).
Proof. exact (MK_COMB (@lem1737630 x) (@lem1737628 x)). Qed.
Lemma lem1737632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737633 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1737632) (@lem1737436 x)). Qed.
Lemma lem1737634 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1737633 x) (@lem1737631 x)). Qed.
Lemma lem1737635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737636 (x : real) : (term435 x) = (term436 x).
Proof. exact (MK_COMB (@lem1737635) (@lem1737415 x)). Qed.
Lemma lem1737637 (x : real) : (term192 x) = (term437 x).
Proof. exact (MK_COMB (@lem1737636 x) (@lem1737634 x)). Qed.
Lemma lem1737638 : term194 = term438.
Proof. exact (fun_ext (fun x : real => @lem1737637 x)). Qed.
Lemma lem1737639 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1737640 : term195 = term439.
Proof. exact (MK_COMB (@lem1737639) (@lem1737638)). Qed.
Lemma lem1737641 (x : real) : (term26 x) = (term261 x).
Proof. exact (@lem1483521 term4 x). Qed.
Lemma lem1737647 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737652 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737654 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737647 x) (@lem1737652 x)). Qed.
Lemma lem1737655 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737656 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1737655) (@lem1737654 x)). Qed.
Lemma lem1737657 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737658 (x : real) : (term261 x) = (term267 x).
Proof. exact (MK_COMB (@lem1737656 x) (@lem1737657)). Qed.
Lemma lem1737659 (x : real) : (term26 x) = (term267 x).
Proof. exact (TRANS (@lem1737641 x) (@lem1737658 x)). Qed.
Lemma lem1737660 (x : real) : (term74 x) = (term268 x).
Proof. exact (@lem1483521 x term4). Qed.
Lemma lem1737666 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737668 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737669 : term272 = term4.
Proof. exact (@lem1737668 term273). Qed.
Lemma lem1737670 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737671 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737670 x) (@lem1737669)). Qed.
Lemma lem1737672 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737673 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737671 x) (@lem1737672 x)). Qed.
Lemma lem1737675 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737666 x) (@lem1737673 x)). Qed.
Lemma lem1737676 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737677 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737676) (@lem1737675 x)). Qed.
Lemma lem1737678 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737679 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737677 x) (@lem1737678)). Qed.
Lemma lem1737680 (x : real) : (term74 x) = (term16 x).
Proof. exact (TRANS (@lem1737660 x) (@lem1737679 x)). Qed.
Lemma lem1737681 : term214 = term440.
Proof. exact (@lem1483554 term13 term23). Qed.
Lemma lem1737687 : term441 = term442.
Proof. exact (@lem1483519 term13 term23). Qed.
Lemma lem1737689 (m : nat) (n : nat) : (term333 m n) = (term334 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1737690 : term332 = term298.
Proof. exact (@lem1737689 term273 term273). Qed.
Lemma lem1737691 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737692 : term297 = term273.
Proof. exact (EQ_MP (@lem1737691) (@lem940073)). Qed.
Lemma lem1737693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737694 : term298 = term13.
Proof. exact (MK_COMB (@lem1737693) (@lem1737692)). Qed.
Lemma lem1737695 : term332 = term13.
Proof. exact (TRANS (@lem1737690) (@lem1737694)). Qed.
Lemma lem1737696 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1737697 : term442 = term443.
Proof. exact (MK_COMB (@lem1737696) (@lem1737695)). Qed.
Lemma lem1737698 : term443 = term379.
Proof. exact (@lem1367770 term273 term273). Qed.
Lemma lem1737699 : term375 = term376.
Proof. exact (@lem706885). Qed.
Lemma lem1737700 : (term375 = term376) = (term377 = term378).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term376). Qed.
Lemma lem1737701 : term377 = term378.
Proof. exact (EQ_MP (@lem1737700) (@lem1737699)). Qed.
Lemma lem1737702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737703 : term379 = term380.
Proof. exact (MK_COMB (@lem1737702) (@lem1737701)). Qed.
Lemma lem1737704 : term443 = term380.
Proof. exact (TRANS (@lem1737698) (@lem1737703)). Qed.
Lemma lem1737705 : term442 = term380.
Proof. exact (TRANS (@lem1737697) (@lem1737704)). Qed.
Lemma lem1737707 : term441 = term380.
Proof. exact (TRANS (@lem1737687) (@lem1737705)). Qed.
Lemma lem1737708 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737709 : term444 = term381.
Proof. exact (MK_COMB (@lem1737708) (@lem1737707)). Qed.
Lemma lem1737710 : term381 = term445.
Proof. exact (@lem1483512 term380). Qed.
Lemma lem1737712 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1737713 : term445 = term446.
Proof. exact (@lem1737712 term273 term378). Qed.
Lemma lem1737714 : term391 = term376.
Proof. exact (@lem996238 term376). Qed.
Lemma lem1737715 : (term391 = term376) = (term392 = term378).
Proof. exact (@lem1007663 (BIT1 0) term376 term376). Qed.
Lemma lem1737716 : term392 = term378.
Proof. exact (EQ_MP (@lem1737715) (@lem1737714)). Qed.
Lemma lem1737717 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737718 : term390 = term380.
Proof. exact (MK_COMB (@lem1737717) (@lem1737716)). Qed.
Lemma lem1737719 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1737720 : term446 = term381.
Proof. exact (MK_COMB (@lem1737719) (@lem1737718)). Qed.
Lemma lem1737721 : term445 = term381.
Proof. exact (TRANS (@lem1737713) (@lem1737720)). Qed.
Lemma lem1737722 : term381 = term381.
Proof. exact (TRANS (@lem1737710) (@lem1737721)). Qed.
Lemma lem1737723 : term447 = term447.
Proof. exact (eq_refl term447). Qed.
Lemma lem1737724 : (term444 = term381) = (term444 = term381).
Proof. exact (MK_COMB (@lem1737723) (@lem1737722)). Qed.
Lemma lem1737725 : term444 = term381.
Proof. exact (EQ_MP (@lem1737724) (@lem1737709)). Qed.
Lemma lem1737726 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737727 : term448 = term399.
Proof. exact (MK_COMB (@lem1737726) (@lem1737725)). Qed.
Lemma lem1737728 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737729 : term449 = term401.
Proof. exact (MK_COMB (@lem1737727) (@lem1737728)). Qed.
Lemma lem1737730 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737731 : term450 = term395.
Proof. exact (MK_COMB (@lem1737730) (@lem1737707)). Qed.
Lemma lem1737732 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737733 : term451 = term397.
Proof. exact (MK_COMB (@lem1737731) (@lem1737732)). Qed.
Lemma lem1737734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737735 : term452 = term453.
Proof. exact (MK_COMB (@lem1737734) (@lem1737733)). Qed.
Lemma lem1737736 : term440 = term454.
Proof. exact (MK_COMB (@lem1737735) (@lem1737729)). Qed.
Lemma lem1737737 : term214 = term454.
Proof. exact (TRANS (@lem1737681) (@lem1737736)). Qed.
Lemma lem1737738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737739 (x : real) : (term226 x) = (term316 x).
Proof. exact (MK_COMB (@lem1737738) (@lem1737680 x)). Qed.
Lemma lem1737740 (x : real) : (term245 x) = (term455 x).
Proof. exact (MK_COMB (@lem1737739 x) (@lem1737737)). Qed.
Lemma lem1737741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737742 (x : real) : (term351 x) = (term352 x).
Proof. exact (MK_COMB (@lem1737741) (@lem1737659 x)). Qed.
Lemma lem1737743 (x : real) : (term456 x) = (term457 x).
Proof. exact (MK_COMB (@lem1737742 x) (@lem1737740 x)). Qed.
Lemma lem1737744 (x : real) : (term198 x) = (term355 x).
Proof. exact (@lem1483531 x term4). Qed.
Lemma lem1737750 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737752 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737753 : term272 = term4.
Proof. exact (@lem1737752 term273). Qed.
Lemma lem1737754 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737755 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737754 x) (@lem1737753)). Qed.
Lemma lem1737756 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737757 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737755 x) (@lem1737756 x)). Qed.
Lemma lem1737759 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737750 x) (@lem1737757 x)). Qed.
Lemma lem1737760 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737761 (x : real) : (term356 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1737760) (@lem1737759 x)). Qed.
Lemma lem1737762 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737763 (x : real) : (term355 x) = (term357 x).
Proof. exact (MK_COMB (@lem1737761 x) (@lem1737762)). Qed.
Lemma lem1737764 (x : real) : (term198 x) = (term357 x).
Proof. exact (TRANS (@lem1737744 x) (@lem1737763 x)). Qed.
Lemma lem1737765 (x : real) : (term74 x) = (term268 x).
Proof. exact (@lem1483521 x term4). Qed.
Lemma lem1737771 (x : real) : (term269 x) = (term270 x).
Proof. exact (@lem1483519 x term4). Qed.
Lemma lem1737773 (x : nat) : (term271 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1737774 : term272 = term4.
Proof. exact (@lem1737773 term273). Qed.
Lemma lem1737775 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1737776 (x : real) : (term270 x) = (term274 x).
Proof. exact (MK_COMB (@lem1737775 x) (@lem1737774)). Qed.
Lemma lem1737777 (x : real) : (term274 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1737778 (x : real) : (term270 x) = x.
Proof. exact (TRANS (@lem1737776 x) (@lem1737777 x)). Qed.
Lemma lem1737780 (x : real) : (term269 x) = x.
Proof. exact (TRANS (@lem1737771 x) (@lem1737778 x)). Qed.
Lemma lem1737781 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1737782 (x : real) : (term275 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1737781) (@lem1737780 x)). Qed.
Lemma lem1737783 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737784 (x : real) : (term268 x) = (term16 x).
Proof. exact (MK_COMB (@lem1737782 x) (@lem1737783)). Qed.
Lemma lem1737785 (x : real) : (term74 x) = (term16 x).
Proof. exact (TRANS (@lem1737765 x) (@lem1737784 x)). Qed.
Lemma lem1737786 : (term13 = term23) = (term441 = term4).
Proof. exact (@lem1483529 term13 term23). Qed.
Lemma lem1737792 : term441 = term442.
Proof. exact (@lem1483519 term13 term23). Qed.
Lemma lem1737794 (m : nat) (n : nat) : (term333 m n) = (term334 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1737795 : term332 = term298.
Proof. exact (@lem1737794 term273 term273). Qed.
Lemma lem1737796 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737797 : term297 = term273.
Proof. exact (EQ_MP (@lem1737796) (@lem940073)). Qed.
Lemma lem1737798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737799 : term298 = term13.
Proof. exact (MK_COMB (@lem1737798) (@lem1737797)). Qed.
Lemma lem1737800 : term332 = term13.
Proof. exact (TRANS (@lem1737795) (@lem1737799)). Qed.
Lemma lem1737801 : term278 = term278.
Proof. exact (eq_refl term278). Qed.
Lemma lem1737802 : term442 = term443.
Proof. exact (MK_COMB (@lem1737801) (@lem1737800)). Qed.
Lemma lem1737803 : term443 = term379.
Proof. exact (@lem1367770 term273 term273). Qed.
Lemma lem1737804 : term375 = term376.
Proof. exact (@lem706885). Qed.
Lemma lem1737805 : (term375 = term376) = (term377 = term378).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term376). Qed.
Lemma lem1737806 : term377 = term378.
Proof. exact (EQ_MP (@lem1737805) (@lem1737804)). Qed.
Lemma lem1737807 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737808 : term379 = term380.
Proof. exact (MK_COMB (@lem1737807) (@lem1737806)). Qed.
Lemma lem1737809 : term443 = term380.
Proof. exact (TRANS (@lem1737803) (@lem1737808)). Qed.
Lemma lem1737810 : term442 = term380.
Proof. exact (TRANS (@lem1737802) (@lem1737809)). Qed.
Lemma lem1737812 : term441 = term380.
Proof. exact (TRANS (@lem1737792) (@lem1737810)). Qed.
Lemma lem1737813 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1737814 : term458 = term459.
Proof. exact (MK_COMB (@lem1737813) (@lem1737812)). Qed.
Lemma lem1737815 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737816 : (term441 = term4) = (term380 = term4).
Proof. exact (MK_COMB (@lem1737814) (@lem1737815)). Qed.
Lemma lem1737817 : (term13 = term23) = (term380 = term4).
Proof. exact (TRANS (@lem1737786) (@lem1737816)). Qed.
Lemma lem1737818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737819 (x : real) : (term226 x) = (term316 x).
Proof. exact (MK_COMB (@lem1737818) (@lem1737785 x)). Qed.
Lemma lem1737820 (x : real) : (term228 x) = (term460 x).
Proof. exact (MK_COMB (@lem1737819 x) (@lem1737817)). Qed.
Lemma lem1737821 (x : real) : (term248 x) = (term319 x).
Proof. exact (@lem1483531 term4 x). Qed.
Lemma lem1737827 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 term4 x). Qed.
Lemma lem1737832 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1483448 (term264 x)). Qed.
Lemma lem1737834 (x : real) : (term262 x) = (term264 x).
Proof. exact (TRANS (@lem1737827 x) (@lem1737832 x)). Qed.
Lemma lem1737835 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1737836 (x : real) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1737835) (@lem1737834 x)). Qed.
Lemma lem1737837 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737838 (x : real) : (term319 x) = (term322 x).
Proof. exact (MK_COMB (@lem1737836 x) (@lem1737837)). Qed.
Lemma lem1737839 (x : real) : (term248 x) = (term322 x).
Proof. exact (TRANS (@lem1737821 x) (@lem1737838 x)). Qed.
Lemma lem1737840 : (term4 = term23) = (term461 = term4).
Proof. exact (@lem1483529 term4 term23). Qed.
Lemma lem1737846 : term461 = term462.
Proof. exact (@lem1483519 term4 term23). Qed.
Lemma lem1737848 (m : nat) (n : nat) : (term333 m n) = (term334 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1737849 : term332 = term298.
Proof. exact (@lem1737848 term273 term273). Qed.
Lemma lem1737850 : (term296 = (BIT1 0)) = (term297 = term273).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1737851 : term297 = term273.
Proof. exact (EQ_MP (@lem1737850) (@lem940073)). Qed.
Lemma lem1737852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1737853 : term298 = term13.
Proof. exact (MK_COMB (@lem1737852) (@lem1737851)). Qed.
Lemma lem1737854 : term332 = term13.
Proof. exact (TRANS (@lem1737849) (@lem1737853)). Qed.
Lemma lem1737855 : term416 = term416.
Proof. exact (eq_refl term416). Qed.
Lemma lem1737856 : term462 = term463.
Proof. exact (MK_COMB (@lem1737855) (@lem1737854)). Qed.
Lemma lem1737857 : term463 = term13.
Proof. exact (@lem1483448 term13). Qed.
Lemma lem1737858 : term462 = term13.
Proof. exact (TRANS (@lem1737856) (@lem1737857)). Qed.
Lemma lem1737860 : term461 = term13.
Proof. exact (TRANS (@lem1737846) (@lem1737858)). Qed.
Lemma lem1737861 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1737862 : term464 = term98.
Proof. exact (MK_COMB (@lem1737861) (@lem1737860)). Qed.
Lemma lem1737863 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1737864 : (term461 = term4) = (term13 = term4).
Proof. exact (MK_COMB (@lem1737862) (@lem1737863)). Qed.
Lemma lem1737865 : (term4 = term23) = (term13 = term4).
Proof. exact (TRANS (@lem1737840) (@lem1737864)). Qed.
Lemma lem1737866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737867 (x : real) : (term120 x) = (term347 x).
Proof. exact (MK_COMB (@lem1737866) (@lem1737839 x)). Qed.
Lemma lem1737868 (x : real) : (term239 x) = (term465 x).
Proof. exact (MK_COMB (@lem1737867 x) (@lem1737865)). Qed.
Lemma lem1737869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737870 (x : real) : (term230 x) = (term466 x).
Proof. exact (MK_COMB (@lem1737869) (@lem1737820 x)). Qed.
Lemma lem1737871 (x : real) : (term240 x) = (term467 x).
Proof. exact (MK_COMB (@lem1737870 x) (@lem1737868 x)). Qed.
Lemma lem1737872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1737873 (x : real) : (term360 x) = (term361 x).
Proof. exact (MK_COMB (@lem1737872) (@lem1737764 x)). Qed.
Lemma lem1737874 (x : real) : (term468 x) = (term469 x).
Proof. exact (MK_COMB (@lem1737873 x) (@lem1737871 x)). Qed.
Lemma lem1737875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737876 (x : real) : (term470 x) = (term471 x).
Proof. exact (MK_COMB (@lem1737875) (@lem1737743 x)). Qed.
Lemma lem1737877 (x : real) : (term253 x) = (term472 x).
Proof. exact (MK_COMB (@lem1737876 x) (@lem1737874 x)). Qed.
Lemma lem1737878 : term255 = term473.
Proof. exact (fun_ext (fun x : real => @lem1737877 x)). Qed.
Lemma lem1737879 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1737880 : term256 = term474.
Proof. exact (MK_COMB (@lem1737879) (@lem1737878)). Qed.
Lemma lem1737881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737882 : term257 = term475.
Proof. exact (MK_COMB (@lem1737881) (@lem1737640)). Qed.
Lemma lem1737883 : term258 = term476.
Proof. exact (MK_COMB (@lem1737882) (@lem1737880)). Qed.
Lemma lem1737884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737885 : term259 = term477.
Proof. exact (MK_COMB (@lem1737884) (@lem1737181)). Qed.
Lemma lem1737886 : term260 = term478.
Proof. exact (MK_COMB (@lem1737885) (@lem1737883)). Qed.
Lemma lem1737887 : term73 = term478.
Proof. exact (TRANS (@lem1736601) (@lem1737886)). Qed.
Lemma lem1737889 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term479 A P Q) = (term480 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1737890 (P : real -> Prop) (Q : real -> Prop) : (term481 P Q) = (term482 P Q).
Proof. exact (@lem1737889 real P Q). Qed.
Lemma lem1737891 : term483 = term484.
Proof. exact (@lem1737890 term485 term486). Qed.
Lemma lem1737892 (x : real) : (term487 x) = (term354 x).
Proof. exact (eq_refl (term487 x)). Qed.
Lemma lem1737893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737894 (x : real) : (term488 x) = (term365 x).
Proof. exact (MK_COMB (@lem1737893) (@lem1737892 x)). Qed.
Lemma lem1737895 (x : real) : (term489 x) = (term363 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem1737896 (x : real) : (term490 x) = (term366 x).
Proof. exact (MK_COMB (@lem1737894 x) (@lem1737895 x)). Qed.
Lemma lem1737897 : term491 = term367.
Proof. exact (fun_ext (fun x : real => @lem1737896 x)). Qed.
Lemma lem1737898 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1737899 : term483 = term368.
Proof. exact (MK_COMB (@lem1737898) (@lem1737897)). Qed.
Lemma lem1737900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1737901 : term492 = term493.
Proof. exact (MK_COMB (@lem1737900) (@lem1737899)). Qed.
Lemma lem1737902 (x : real) : (term487 x) = (term354 x).
Proof. exact (eq_refl (term487 x)). Qed.
Lemma lem1737903 : term494 = term485.
Proof. exact (fun_ext (fun x : real => @lem1737902 x)). Qed.
Lemma lem1737904 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1737905 : term495 = term496.
Proof. exact (MK_COMB (@lem1737904) (@lem1737903)). Qed.
Lemma lem1737906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1737907 : term497 = term498.
Proof. exact (MK_COMB (@lem1737906) (@lem1737905)). Qed.
Lemma lem1737908 (x : real) : (term489 x) = (term363 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem1737909 : term499 = term486.
Proof. exact (fun_ext (fun x : real => @lem1737908 x)). Qed.
Lemma lem1737910 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1737911 : term500 = term501.
Proof. exact (MK_COMB (@lem1737910) (@lem1737909)). Qed.
Lemma lem1737912 : term484 = term502.
Proof. exact (MK_COMB (@lem1737907) (@lem1737911)). Qed.
Lemma lem1737913 : (term483 = term484) = (term368 = term502).
Proof. exact (MK_COMB (@lem1737901) (@lem1737912)). Qed.
Lemma lem1737914 : term368 = term502.
Proof. exact (EQ_MP (@lem1737913) (@lem1737891)). Qed.
Lemma lem1738011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738012 : term477 = term503.
Proof. exact (MK_COMB (@lem1738011) (@lem1737914)). Qed.
Lemma lem1738014 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term479 A P Q) = (term480 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1738015 (P : real -> Prop) (Q : real -> Prop) : (term481 P Q) = (term482 P Q).
Proof. exact (@lem1738014 real P Q). Qed.
Lemma lem1738016 : term504 = term505.
Proof. exact (@lem1738015 term506 term507). Qed.
Lemma lem1738017 (x : real) : (term508 x) = (term413 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1738018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738019 (x : real) : (term509 x) = (term436 x).
Proof. exact (MK_COMB (@lem1738018) (@lem1738017 x)). Qed.
Lemma lem1738020 (x : real) : (term510 x) = (term434 x).
Proof. exact (eq_refl (term510 x)). Qed.
Lemma lem1738021 (x : real) : (term511 x) = (term437 x).
Proof. exact (MK_COMB (@lem1738019 x) (@lem1738020 x)). Qed.
Lemma lem1738022 : term512 = term438.
Proof. exact (fun_ext (fun x : real => @lem1738021 x)). Qed.
Lemma lem1738023 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738024 : term504 = term439.
Proof. exact (MK_COMB (@lem1738023) (@lem1738022)). Qed.
Lemma lem1738025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738026 : term513 = term514.
Proof. exact (MK_COMB (@lem1738025) (@lem1738024)). Qed.
Lemma lem1738027 (x : real) : (term508 x) = (term413 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1738028 : term515 = term506.
Proof. exact (fun_ext (fun x : real => @lem1738027 x)). Qed.
Lemma lem1738029 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738030 : term516 = term517.
Proof. exact (MK_COMB (@lem1738029) (@lem1738028)). Qed.
Lemma lem1738031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738032 : term518 = term519.
Proof. exact (MK_COMB (@lem1738031) (@lem1738030)). Qed.
Lemma lem1738033 (x : real) : (term510 x) = (term434 x).
Proof. exact (eq_refl (term510 x)). Qed.
Lemma lem1738034 : term520 = term507.
Proof. exact (fun_ext (fun x : real => @lem1738033 x)). Qed.
Lemma lem1738035 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738036 : term521 = term522.
Proof. exact (MK_COMB (@lem1738035) (@lem1738034)). Qed.
Lemma lem1738037 : term505 = term523.
Proof. exact (MK_COMB (@lem1738032) (@lem1738036)). Qed.
Lemma lem1738038 : (term504 = term505) = (term439 = term523).
Proof. exact (MK_COMB (@lem1738026) (@lem1738037)). Qed.
Lemma lem1738039 : term439 = term523.
Proof. exact (EQ_MP (@lem1738038) (@lem1738016)). Qed.
Lemma lem1738136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738137 : term475 = term524.
Proof. exact (MK_COMB (@lem1738136) (@lem1738039)). Qed.
Lemma lem1738139 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term479 A P Q) = (term480 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1738140 (P : real -> Prop) (Q : real -> Prop) : (term481 P Q) = (term482 P Q).
Proof. exact (@lem1738139 real P Q). Qed.
Lemma lem1738141 : term525 = term526.
Proof. exact (@lem1738140 term527 term528). Qed.
Lemma lem1738142 (x : real) : (term529 x) = (term457 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1738143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738144 (x : real) : (term530 x) = (term471 x).
Proof. exact (MK_COMB (@lem1738143) (@lem1738142 x)). Qed.
Lemma lem1738145 (x : real) : (term531 x) = (term469 x).
Proof. exact (eq_refl (term531 x)). Qed.
Lemma lem1738146 (x : real) : (term532 x) = (term472 x).
Proof. exact (MK_COMB (@lem1738144 x) (@lem1738145 x)). Qed.
Lemma lem1738147 : term533 = term473.
Proof. exact (fun_ext (fun x : real => @lem1738146 x)). Qed.
Lemma lem1738148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738149 : term525 = term474.
Proof. exact (MK_COMB (@lem1738148) (@lem1738147)). Qed.
Lemma lem1738150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738151 : term534 = term535.
Proof. exact (MK_COMB (@lem1738150) (@lem1738149)). Qed.
Lemma lem1738152 (x : real) : (term529 x) = (term457 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1738153 : term536 = term527.
Proof. exact (fun_ext (fun x : real => @lem1738152 x)). Qed.
Lemma lem1738154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738155 : term537 = term538.
Proof. exact (MK_COMB (@lem1738154) (@lem1738153)). Qed.
Lemma lem1738156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738157 : term539 = term540.
Proof. exact (MK_COMB (@lem1738156) (@lem1738155)). Qed.
Lemma lem1738158 (x : real) : (term531 x) = (term469 x).
Proof. exact (eq_refl (term531 x)). Qed.
Lemma lem1738159 : term541 = term528.
Proof. exact (fun_ext (fun x : real => @lem1738158 x)). Qed.
Lemma lem1738160 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738161 : term542 = term543.
Proof. exact (MK_COMB (@lem1738160) (@lem1738159)). Qed.
Lemma lem1738162 : term526 = term544.
Proof. exact (MK_COMB (@lem1738157) (@lem1738161)). Qed.
Lemma lem1738163 : (term525 = term526) = (term474 = term544).
Proof. exact (MK_COMB (@lem1738151) (@lem1738162)). Qed.
Lemma lem1738164 : term474 = term544.
Proof. exact (EQ_MP (@lem1738163) (@lem1738141)). Qed.
Lemma lem1738261 : term476 = term545.
Proof. exact (MK_COMB (@lem1738137) (@lem1738164)). Qed.
Lemma lem1738262 : term478 = term546.
Proof. exact (MK_COMB (@lem1738012) (@lem1738261)). Qed.
Lemma lem1738264 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term480 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1738265 (P : real -> Prop) (Q : real -> Prop) : (term482 P Q) = (term481 P Q).
Proof. exact (@lem1738264 real P Q). Qed.
Lemma lem1738266 : term484 = term483.
Proof. exact (@lem1738265 term485 term486). Qed.
Lemma lem1738267 (x : real) : (term487 x) = (term354 x).
Proof. exact (eq_refl (term487 x)). Qed.
Lemma lem1738268 : term494 = term485.
Proof. exact (fun_ext (fun x : real => @lem1738267 x)). Qed.
Lemma lem1738269 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738270 : term495 = term496.
Proof. exact (MK_COMB (@lem1738269) (@lem1738268)). Qed.
Lemma lem1738271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738272 : term497 = term498.
Proof. exact (MK_COMB (@lem1738271) (@lem1738270)). Qed.
Lemma lem1738273 (x : real) : (term489 x) = (term363 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem1738274 : term499 = term486.
Proof. exact (fun_ext (fun x : real => @lem1738273 x)). Qed.
Lemma lem1738275 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738276 : term500 = term501.
Proof. exact (MK_COMB (@lem1738275) (@lem1738274)). Qed.
Lemma lem1738277 : term484 = term502.
Proof. exact (MK_COMB (@lem1738272) (@lem1738276)). Qed.
Lemma lem1738278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738279 : term547 = term548.
Proof. exact (MK_COMB (@lem1738278) (@lem1738277)). Qed.
Lemma lem1738280 (x : real) : (term487 x) = (term354 x).
Proof. exact (eq_refl (term487 x)). Qed.
Lemma lem1738281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738282 (x : real) : (term488 x) = (term365 x).
Proof. exact (MK_COMB (@lem1738281) (@lem1738280 x)). Qed.
Lemma lem1738283 (x : real) : (term489 x) = (term363 x).
Proof. exact (eq_refl (term489 x)). Qed.
Lemma lem1738284 (x : real) : (term490 x) = (term366 x).
Proof. exact (MK_COMB (@lem1738282 x) (@lem1738283 x)). Qed.
Lemma lem1738285 : term491 = term367.
Proof. exact (fun_ext (fun x : real => @lem1738284 x)). Qed.
Lemma lem1738286 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738287 : term483 = term368.
Proof. exact (MK_COMB (@lem1738286) (@lem1738285)). Qed.
Lemma lem1738288 : (term484 = term483) = (term502 = term368).
Proof. exact (MK_COMB (@lem1738279) (@lem1738287)). Qed.
Lemma lem1738289 : term502 = term368.
Proof. exact (EQ_MP (@lem1738288) (@lem1738266)). Qed.
Lemma lem1738290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738291 : term503 = term477.
Proof. exact (MK_COMB (@lem1738290) (@lem1738289)). Qed.
Lemma lem1738293 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term480 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1738294 (P : real -> Prop) (Q : real -> Prop) : (term482 P Q) = (term481 P Q).
Proof. exact (@lem1738293 real P Q). Qed.
Lemma lem1738295 : term505 = term504.
Proof. exact (@lem1738294 term506 term507). Qed.
Lemma lem1738296 (x : real) : (term508 x) = (term413 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1738297 : term515 = term506.
Proof. exact (fun_ext (fun x : real => @lem1738296 x)). Qed.
Lemma lem1738298 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738299 : term516 = term517.
Proof. exact (MK_COMB (@lem1738298) (@lem1738297)). Qed.
Lemma lem1738300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738301 : term518 = term519.
Proof. exact (MK_COMB (@lem1738300) (@lem1738299)). Qed.
Lemma lem1738302 (x : real) : (term510 x) = (term434 x).
Proof. exact (eq_refl (term510 x)). Qed.
Lemma lem1738303 : term520 = term507.
Proof. exact (fun_ext (fun x : real => @lem1738302 x)). Qed.
Lemma lem1738304 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738305 : term521 = term522.
Proof. exact (MK_COMB (@lem1738304) (@lem1738303)). Qed.
Lemma lem1738306 : term505 = term523.
Proof. exact (MK_COMB (@lem1738301) (@lem1738305)). Qed.
Lemma lem1738307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738308 : term549 = term550.
Proof. exact (MK_COMB (@lem1738307) (@lem1738306)). Qed.
Lemma lem1738309 (x : real) : (term508 x) = (term413 x).
Proof. exact (eq_refl (term508 x)). Qed.
Lemma lem1738310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738311 (x : real) : (term509 x) = (term436 x).
Proof. exact (MK_COMB (@lem1738310) (@lem1738309 x)). Qed.
Lemma lem1738312 (x : real) : (term510 x) = (term434 x).
Proof. exact (eq_refl (term510 x)). Qed.
Lemma lem1738313 (x : real) : (term511 x) = (term437 x).
Proof. exact (MK_COMB (@lem1738311 x) (@lem1738312 x)). Qed.
Lemma lem1738314 : term512 = term438.
Proof. exact (fun_ext (fun x : real => @lem1738313 x)). Qed.
Lemma lem1738315 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738316 : term504 = term439.
Proof. exact (MK_COMB (@lem1738315) (@lem1738314)). Qed.
Lemma lem1738317 : (term505 = term504) = (term523 = term439).
Proof. exact (MK_COMB (@lem1738308) (@lem1738316)). Qed.
Lemma lem1738318 : term523 = term439.
Proof. exact (EQ_MP (@lem1738317) (@lem1738295)). Qed.
Lemma lem1738319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738320 : term524 = term475.
Proof. exact (MK_COMB (@lem1738319) (@lem1738318)). Qed.
Lemma lem1738322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term480 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1738323 (P : real -> Prop) (Q : real -> Prop) : (term482 P Q) = (term481 P Q).
Proof. exact (@lem1738322 real P Q). Qed.
Lemma lem1738324 : term526 = term525.
Proof. exact (@lem1738323 term527 term528). Qed.
Lemma lem1738325 (x : real) : (term529 x) = (term457 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1738326 : term536 = term527.
Proof. exact (fun_ext (fun x : real => @lem1738325 x)). Qed.
Lemma lem1738327 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738328 : term537 = term538.
Proof. exact (MK_COMB (@lem1738327) (@lem1738326)). Qed.
Lemma lem1738329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738330 : term539 = term540.
Proof. exact (MK_COMB (@lem1738329) (@lem1738328)). Qed.
Lemma lem1738331 (x : real) : (term531 x) = (term469 x).
Proof. exact (eq_refl (term531 x)). Qed.
Lemma lem1738332 : term541 = term528.
Proof. exact (fun_ext (fun x : real => @lem1738331 x)). Qed.
Lemma lem1738333 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738334 : term542 = term543.
Proof. exact (MK_COMB (@lem1738333) (@lem1738332)). Qed.
Lemma lem1738335 : term526 = term544.
Proof. exact (MK_COMB (@lem1738330) (@lem1738334)). Qed.
Lemma lem1738336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738337 : term551 = term552.
Proof. exact (MK_COMB (@lem1738336) (@lem1738335)). Qed.
Lemma lem1738338 (x : real) : (term529 x) = (term457 x).
Proof. exact (eq_refl (term529 x)). Qed.
Lemma lem1738339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738340 (x : real) : (term530 x) = (term471 x).
Proof. exact (MK_COMB (@lem1738339) (@lem1738338 x)). Qed.
Lemma lem1738341 (x : real) : (term531 x) = (term469 x).
Proof. exact (eq_refl (term531 x)). Qed.
Lemma lem1738342 (x : real) : (term532 x) = (term472 x).
Proof. exact (MK_COMB (@lem1738340 x) (@lem1738341 x)). Qed.
Lemma lem1738343 : term533 = term473.
Proof. exact (fun_ext (fun x : real => @lem1738342 x)). Qed.
Lemma lem1738344 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738345 : term525 = term474.
Proof. exact (MK_COMB (@lem1738344) (@lem1738343)). Qed.
Lemma lem1738346 : (term526 = term525) = (term544 = term474).
Proof. exact (MK_COMB (@lem1738337) (@lem1738345)). Qed.
Lemma lem1738347 : term544 = term474.
Proof. exact (EQ_MP (@lem1738346) (@lem1738324)). Qed.
Lemma lem1738348 : term545 = term476.
Proof. exact (MK_COMB (@lem1738320) (@lem1738347)). Qed.
Lemma lem1738350 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term480 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1738351 (P : real -> Prop) (Q : real -> Prop) : (term482 P Q) = (term481 P Q).
Proof. exact (@lem1738350 real P Q). Qed.
Lemma lem1738352 : term553 = term554.
Proof. exact (@lem1738351 term438 term473). Qed.
Lemma lem1738353 (x : real) : (term555 x) = (term437 x).
Proof. exact (eq_refl (term555 x)). Qed.
Lemma lem1738354 : term556 = term438.
Proof. exact (fun_ext (fun x : real => @lem1738353 x)). Qed.
Lemma lem1738355 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738356 : term557 = term439.
Proof. exact (MK_COMB (@lem1738355) (@lem1738354)). Qed.
Lemma lem1738357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738358 : term558 = term475.
Proof. exact (MK_COMB (@lem1738357) (@lem1738356)). Qed.
Lemma lem1738359 (x : real) : (term559 x) = (term472 x).
Proof. exact (eq_refl (term559 x)). Qed.
Lemma lem1738360 : term560 = term473.
Proof. exact (fun_ext (fun x : real => @lem1738359 x)). Qed.
Lemma lem1738361 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738362 : term561 = term474.
Proof. exact (MK_COMB (@lem1738361) (@lem1738360)). Qed.
Lemma lem1738363 : term553 = term476.
Proof. exact (MK_COMB (@lem1738358) (@lem1738362)). Qed.
Lemma lem1738364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738365 : term562 = term563.
Proof. exact (MK_COMB (@lem1738364) (@lem1738363)). Qed.
Lemma lem1738366 (x : real) : (term555 x) = (term437 x).
Proof. exact (eq_refl (term555 x)). Qed.
Lemma lem1738367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738368 (x : real) : (term564 x) = (term565 x).
Proof. exact (MK_COMB (@lem1738367) (@lem1738366 x)). Qed.
Lemma lem1738369 (x : real) : (term559 x) = (term472 x).
Proof. exact (eq_refl (term559 x)). Qed.
Lemma lem1738370 (x : real) : (term566 x) = (term567 x).
Proof. exact (MK_COMB (@lem1738368 x) (@lem1738369 x)). Qed.
Lemma lem1738371 : term568 = term569.
Proof. exact (fun_ext (fun x : real => @lem1738370 x)). Qed.
Lemma lem1738372 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738373 : term554 = term570.
Proof. exact (MK_COMB (@lem1738372) (@lem1738371)). Qed.
Lemma lem1738374 : (term553 = term554) = (term476 = term570).
Proof. exact (MK_COMB (@lem1738365) (@lem1738373)). Qed.
Lemma lem1738375 : term476 = term570.
Proof. exact (EQ_MP (@lem1738374) (@lem1738352)). Qed.
Lemma lem1738376 : term545 = term570.
Proof. exact (TRANS (@lem1738348) (@lem1738375)). Qed.
Lemma lem1738377 : term546 = term571.
Proof. exact (MK_COMB (@lem1738291) (@lem1738376)). Qed.
Lemma lem1738379 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term480 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1738380 (P : real -> Prop) (Q : real -> Prop) : (term482 P Q) = (term481 P Q).
Proof. exact (@lem1738379 real P Q). Qed.
Lemma lem1738381 : term572 = term573.
Proof. exact (@lem1738380 term367 term569). Qed.
Lemma lem1738382 (x : real) : (term574 x) = (term366 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1738383 : term575 = term367.
Proof. exact (fun_ext (fun x : real => @lem1738382 x)). Qed.
Lemma lem1738384 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738385 : term576 = term368.
Proof. exact (MK_COMB (@lem1738384) (@lem1738383)). Qed.
Lemma lem1738386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738387 : term577 = term477.
Proof. exact (MK_COMB (@lem1738386) (@lem1738385)). Qed.
Lemma lem1738388 (x : real) : (term578 x) = (term567 x).
Proof. exact (eq_refl (term578 x)). Qed.
Lemma lem1738389 : term579 = term569.
Proof. exact (fun_ext (fun x : real => @lem1738388 x)). Qed.
Lemma lem1738390 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738391 : term580 = term570.
Proof. exact (MK_COMB (@lem1738390) (@lem1738389)). Qed.
Lemma lem1738392 : term572 = term571.
Proof. exact (MK_COMB (@lem1738387) (@lem1738391)). Qed.
Lemma lem1738393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1738394 : term581 = term582.
Proof. exact (MK_COMB (@lem1738393) (@lem1738392)). Qed.
Lemma lem1738395 (x : real) : (term574 x) = (term366 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem1738396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738397 (x : real) : (term583 x) = (term584 x).
Proof. exact (MK_COMB (@lem1738396) (@lem1738395 x)). Qed.
Lemma lem1738398 (x : real) : (term578 x) = (term567 x).
Proof. exact (eq_refl (term578 x)). Qed.
Lemma lem1738399 (x : real) : (term585 x) = (term586 x).
Proof. exact (MK_COMB (@lem1738397 x) (@lem1738398 x)). Qed.
Lemma lem1738400 : term587 = term588.
Proof. exact (fun_ext (fun x : real => @lem1738399 x)). Qed.
Lemma lem1738401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738402 : term573 = term589.
Proof. exact (MK_COMB (@lem1738401) (@lem1738400)). Qed.
Lemma lem1738403 : (term572 = term573) = (term571 = term589).
Proof. exact (MK_COMB (@lem1738394) (@lem1738402)). Qed.
Lemma lem1738404 : term571 = term589.
Proof. exact (EQ_MP (@lem1738403) (@lem1738381)). Qed.
Lemma lem1738405 : term546 = term589.
Proof. exact (TRANS (@lem1738377) (@lem1738404)). Qed.
Lemma lem1738406 : term478 = term589.
Proof. exact (TRANS (@lem1738262) (@lem1738405)). Qed.
Lemma lem1738409 : term73 = term589.
Proof. exact (TRANS (@lem1737887) (@lem1738406)). Qed.
Lemma lem1738438 (x : real) : (term469 x) = (term590 x).
Proof. exact (@lem19158 (term460 x) (term357 x) (term465 x)). Qed.
Lemma lem1738455 (x : real) : (term455 x) = (term591 x).
Proof. exact (@lem19158 term397 (term16 x) term401). Qed.
Lemma lem1738458 (x : real) : (term352 x) = (term352 x).
Proof. exact (eq_refl (term352 x)). Qed.
Lemma lem1738459 (x : real) : (term457 x) = (term592 x).
Proof. exact (MK_COMB (@lem1738458 x) (@lem1738455 x)). Qed.
Lemma lem1738466 (x : real) : (term592 x) = (term593 x).
Proof. exact (@lem19158 (term594 x) (term267 x) (term595 x)). Qed.
Lemma lem1738467 (x : real) : (term457 x) = (term593 x).
Proof. exact (TRANS (@lem1738459 x) (@lem1738466 x)). Qed.
Lemma lem1738468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738469 (x : real) : (term471 x) = (term596 x).
Proof. exact (MK_COMB (@lem1738468) (@lem1738467 x)). Qed.
Lemma lem1738470 (x : real) : (term472 x) = (term597 x).
Proof. exact (MK_COMB (@lem1738469 x) (@lem1738438 x)). Qed.
Lemma lem1738487 (x : real) : (term428 x) = (term598 x).
Proof. exact (@lem19367 term303 term307 (term16 x)). Qed.
Lemma lem1738496 (x : real) : (term429 x) = (term429 x).
Proof. exact (eq_refl (term429 x)). Qed.
Lemma lem1738497 (x : real) : (term430 x) = (term599 x).
Proof. exact (MK_COMB (@lem1738496 x) (@lem1738487 x)). Qed.
Lemma lem1738500 (x : real) : (term347 x) = (term347 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem1738501 (x : real) : (term431 x) = (term600 x).
Proof. exact (MK_COMB (@lem1738500 x) (@lem1738497 x)). Qed.
Lemma lem1738502 (x : real) : (term600 x) = (term601 x).
Proof. exact (@lem19158 (term419 x) (term322 x) (term598 x)). Qed.
Lemma lem1738509 (x : real) : (term602 x) = (term603 x).
Proof. exact (@lem19158 (term604 x) (term322 x) (term605 x)). Qed.
Lemma lem1738512 (x : real) : (term606 x) = (term606 x).
Proof. exact (eq_refl (term606 x)). Qed.
Lemma lem1738513 (x : real) : (term601 x) = (term607 x).
Proof. exact (MK_COMB (@lem1738512 x) (@lem1738509 x)). Qed.
Lemma lem1738514 (x : real) : (term600 x) = (term607 x).
Proof. exact (TRANS (@lem1738502 x) (@lem1738513 x)). Qed.
Lemma lem1738515 (x : real) : (term431 x) = (term607 x).
Proof. exact (TRANS (@lem1738501 x) (@lem1738514 x)). Qed.
Lemma lem1738524 (x : real) : (term410 x) = (term410 x).
Proof. exact (eq_refl (term410 x)). Qed.
Lemma lem1738525 (x : real) : (term432 x) = (term608 x).
Proof. exact (MK_COMB (@lem1738524 x) (@lem1738515 x)). Qed.
Lemma lem1738528 (x : real) : (term361 x) = (term361 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem1738529 (x : real) : (term434 x) = (term609 x).
Proof. exact (MK_COMB (@lem1738528 x) (@lem1738525 x)). Qed.
Lemma lem1738530 (x : real) : (term609 x) = (term610 x).
Proof. exact (@lem19158 (term370 x) (term357 x) (term607 x)). Qed.
Lemma lem1738531 (x : real) : (term611 x) = (term612 x).
Proof. exact (@lem19158 (term613 x) (term357 x) (term603 x)). Qed.
Lemma lem1738538 (x : real) : (term614 x) = (term615 x).
Proof. exact (@lem19158 (term616 x) (term357 x) (term617 x)). Qed.
Lemma lem1738541 (x : real) : (term618 x) = (term618 x).
Proof. exact (eq_refl (term618 x)). Qed.
Lemma lem1738542 (x : real) : (term612 x) = (term619 x).
Proof. exact (MK_COMB (@lem1738541 x) (@lem1738538 x)). Qed.
Lemma lem1738543 (x : real) : (term611 x) = (term619 x).
Proof. exact (TRANS (@lem1738531 x) (@lem1738542 x)). Qed.
Lemma lem1738546 (x : real) : (term620 x) = (term620 x).
Proof. exact (eq_refl (term620 x)). Qed.
Lemma lem1738547 (x : real) : (term610 x) = (term621 x).
Proof. exact (MK_COMB (@lem1738546 x) (@lem1738543 x)). Qed.
Lemma lem1738548 (x : real) : (term609 x) = (term621 x).
Proof. exact (TRANS (@lem1738530 x) (@lem1738547 x)). Qed.
Lemma lem1738549 (x : real) : (term434 x) = (term621 x).
Proof. exact (TRANS (@lem1738529 x) (@lem1738548 x)). Qed.
Lemma lem1738566 (x : real) : (term406 x) = (term622 x).
Proof. exact (@lem19367 term401 term397 (term16 x)). Qed.
Lemma lem1738575 (x : real) : (term407 x) = (term407 x).
Proof. exact (eq_refl (term407 x)). Qed.
Lemma lem1738576 (x : real) : (term408 x) = (term623 x).
Proof. exact (MK_COMB (@lem1738575 x) (@lem1738566 x)). Qed.
Lemma lem1738579 (x : real) : (term347 x) = (term347 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem1738580 (x : real) : (term409 x) = (term624 x).
Proof. exact (MK_COMB (@lem1738579 x) (@lem1738576 x)). Qed.
Lemma lem1738581 (x : real) : (term624 x) = (term625 x).
Proof. exact (@lem19158 (term385 x) (term322 x) (term622 x)). Qed.
Lemma lem1738588 (x : real) : (term626 x) = (term627 x).
Proof. exact (@lem19158 (term628 x) (term322 x) (term629 x)). Qed.
Lemma lem1738591 (x : real) : (term630 x) = (term630 x).
Proof. exact (eq_refl (term630 x)). Qed.
Lemma lem1738592 (x : real) : (term625 x) = (term631 x).
Proof. exact (MK_COMB (@lem1738591 x) (@lem1738588 x)). Qed.
Lemma lem1738593 (x : real) : (term624 x) = (term631 x).
Proof. exact (TRANS (@lem1738581 x) (@lem1738592 x)). Qed.
Lemma lem1738594 (x : real) : (term409 x) = (term631 x).
Proof. exact (TRANS (@lem1738580 x) (@lem1738593 x)). Qed.
Lemma lem1738603 (x : real) : (term410 x) = (term410 x).
Proof. exact (eq_refl (term410 x)). Qed.
Lemma lem1738604 (x : real) : (term411 x) = (term632 x).
Proof. exact (MK_COMB (@lem1738603 x) (@lem1738594 x)). Qed.
Lemma lem1738607 (x : real) : (term352 x) = (term352 x).
Proof. exact (eq_refl (term352 x)). Qed.
Lemma lem1738608 (x : real) : (term413 x) = (term633 x).
Proof. exact (MK_COMB (@lem1738607 x) (@lem1738604 x)). Qed.
Lemma lem1738609 (x : real) : (term633 x) = (term634 x).
Proof. exact (@lem19158 (term370 x) (term267 x) (term631 x)). Qed.
Lemma lem1738610 (x : real) : (term635 x) = (term636 x).
Proof. exact (@lem19158 (term637 x) (term267 x) (term627 x)). Qed.
Lemma lem1738617 (x : real) : (term638 x) = (term639 x).
Proof. exact (@lem19158 (term640 x) (term267 x) (term641 x)). Qed.
Lemma lem1738620 (x : real) : (term642 x) = (term642 x).
Proof. exact (eq_refl (term642 x)). Qed.
Lemma lem1738621 (x : real) : (term636 x) = (term643 x).
Proof. exact (MK_COMB (@lem1738620 x) (@lem1738617 x)). Qed.
Lemma lem1738622 (x : real) : (term635 x) = (term643 x).
Proof. exact (TRANS (@lem1738610 x) (@lem1738621 x)). Qed.
Lemma lem1738625 (x : real) : (term644 x) = (term644 x).
Proof. exact (eq_refl (term644 x)). Qed.
Lemma lem1738626 (x : real) : (term634 x) = (term645 x).
Proof. exact (MK_COMB (@lem1738625 x) (@lem1738622 x)). Qed.
Lemma lem1738627 (x : real) : (term633 x) = (term645 x).
Proof. exact (TRANS (@lem1738609 x) (@lem1738626 x)). Qed.
Lemma lem1738628 (x : real) : (term413 x) = (term645 x).
Proof. exact (TRANS (@lem1738608 x) (@lem1738627 x)). Qed.
Lemma lem1738629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738630 (x : real) : (term436 x) = (term646 x).
Proof. exact (MK_COMB (@lem1738629) (@lem1738628 x)). Qed.
Lemma lem1738631 (x : real) : (term437 x) = (term647 x).
Proof. exact (MK_COMB (@lem1738630 x) (@lem1738549 x)). Qed.
Lemma lem1738632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738633 (x : real) : (term565 x) = (term648 x).
Proof. exact (MK_COMB (@lem1738632) (@lem1738631 x)). Qed.
Lemma lem1738634 (x : real) : (term567 x) = (term649 x).
Proof. exact (MK_COMB (@lem1738633 x) (@lem1738470 x)). Qed.
Lemma lem1738651 (x : real) : (term358 x) = (term650 x).
Proof. exact (@lem19158 (term16 x) (term322 x) (term267 x)). Qed.
Lemma lem1738668 (x : real) : (term313 x) = (term651 x).
Proof. exact (@lem19367 term307 term303 (x = term4)). Qed.
Lemma lem1738685 (x : real) : (term289 x) = (term652 x).
Proof. exact (@lem19158 (term16 x) (term13 = term4) (term267 x)). Qed.
Lemma lem1738686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738687 (x : real) : (term314 x) = (term653 x).
Proof. exact (MK_COMB (@lem1738686) (@lem1738685 x)). Qed.
Lemma lem1738688 (x : real) : (term315 x) = (term654 x).
Proof. exact (MK_COMB (@lem1738687 x) (@lem1738668 x)). Qed.
Lemma lem1738691 (x : real) : (term316 x) = (term316 x).
Proof. exact (eq_refl (term316 x)). Qed.
Lemma lem1738692 (x : real) : (term318 x) = (term655 x).
Proof. exact (MK_COMB (@lem1738691 x) (@lem1738688 x)). Qed.
Lemma lem1738693 (x : real) : (term655 x) = (term656 x).
Proof. exact (@lem19158 (term652 x) (term16 x) (term651 x)). Qed.
Lemma lem1738700 (x : real) : (term657 x) = (term658 x).
Proof. exact (@lem19158 (term659 x) (term16 x) (term660 x)). Qed.
Lemma lem1738707 (x : real) : (term661 x) = (term662 x).
Proof. exact (@lem19158 (term663 x) (term16 x) (term664 x)). Qed.
Lemma lem1738708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738709 (x : real) : (term665 x) = (term666 x).
Proof. exact (MK_COMB (@lem1738708) (@lem1738707 x)). Qed.
Lemma lem1738710 (x : real) : (term656 x) = (term667 x).
Proof. exact (MK_COMB (@lem1738709 x) (@lem1738700 x)). Qed.
Lemma lem1738711 (x : real) : (term655 x) = (term667 x).
Proof. exact (TRANS (@lem1738693 x) (@lem1738710 x)). Qed.
Lemma lem1738712 (x : real) : (term318 x) = (term667 x).
Proof. exact (TRANS (@lem1738692 x) (@lem1738711 x)). Qed.
Lemma lem1738713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738714 (x : real) : (term349 x) = (term668 x).
Proof. exact (MK_COMB (@lem1738713) (@lem1738712 x)). Qed.
Lemma lem1738715 (x : real) : (term359 x) = (term669 x).
Proof. exact (MK_COMB (@lem1738714 x) (@lem1738651 x)). Qed.
Lemma lem1738718 (x : real) : (term361 x) = (term361 x).
Proof. exact (eq_refl (term361 x)). Qed.
Lemma lem1738719 (x : real) : (term363 x) = (term670 x).
Proof. exact (MK_COMB (@lem1738718 x) (@lem1738715 x)). Qed.
Lemma lem1738720 (x : real) : (term670 x) = (term671 x).
Proof. exact (@lem19158 (term667 x) (term357 x) (term650 x)). Qed.
Lemma lem1738727 (x : real) : (term672 x) = (term673 x).
Proof. exact (@lem19158 (term674 x) (term357 x) (term675 x)). Qed.
Lemma lem1738728 (x : real) : (term676 x) = (term677 x).
Proof. exact (@lem19158 (term662 x) (term357 x) (term658 x)). Qed.
Lemma lem1738735 (x : real) : (term678 x) = (term679 x).
Proof. exact (@lem19158 (term680 x) (term357 x) (term681 x)). Qed.
Lemma lem1738742 (x : real) : (term682 x) = (term683 x).
Proof. exact (@lem19158 (term684 x) (term357 x) (term685 x)). Qed.
Lemma lem1738743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738744 (x : real) : (term686 x) = (term687 x).
Proof. exact (MK_COMB (@lem1738743) (@lem1738742 x)). Qed.
Lemma lem1738745 (x : real) : (term677 x) = (term688 x).
Proof. exact (MK_COMB (@lem1738744 x) (@lem1738735 x)). Qed.
Lemma lem1738746 (x : real) : (term676 x) = (term688 x).
Proof. exact (TRANS (@lem1738728 x) (@lem1738745 x)). Qed.
Lemma lem1738747 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738748 (x : real) : (term689 x) = (term690 x).
Proof. exact (MK_COMB (@lem1738747) (@lem1738746 x)). Qed.
Lemma lem1738749 (x : real) : (term671 x) = (term691 x).
Proof. exact (MK_COMB (@lem1738748 x) (@lem1738727 x)). Qed.
Lemma lem1738750 (x : real) : (term670 x) = (term691 x).
Proof. exact (TRANS (@lem1738720 x) (@lem1738749 x)). Qed.
Lemma lem1738751 (x : real) : (term363 x) = (term691 x).
Proof. exact (TRANS (@lem1738719 x) (@lem1738750 x)). Qed.
Lemma lem1738768 (x : real) : (term344 x) = (term692 x).
Proof. exact (@lem19367 term303 term307 (x = term4)). Qed.
Lemma lem1738785 (x : real) : (term328 x) = (term693 x).
Proof. exact (@lem19158 (term16 x) (term23 = term4) (term267 x)). Qed.
Lemma lem1738786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738787 (x : real) : (term345 x) = (term694 x).
Proof. exact (MK_COMB (@lem1738786) (@lem1738785 x)). Qed.
Lemma lem1738788 (x : real) : (term346 x) = (term695 x).
Proof. exact (MK_COMB (@lem1738787 x) (@lem1738768 x)). Qed.
Lemma lem1738791 (x : real) : (term347 x) = (term347 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem1738792 (x : real) : (term348 x) = (term696 x).
Proof. exact (MK_COMB (@lem1738791 x) (@lem1738788 x)). Qed.
Lemma lem1738793 (x : real) : (term696 x) = (term697 x).
Proof. exact (@lem19158 (term693 x) (term322 x) (term692 x)). Qed.
Lemma lem1738800 (x : real) : (term698 x) = (term699 x).
Proof. exact (@lem19158 (term660 x) (term322 x) (term659 x)). Qed.
Lemma lem1738807 (x : real) : (term700 x) = (term701 x).
Proof. exact (@lem19158 (term702 x) (term322 x) (term703 x)). Qed.
Lemma lem1738808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738809 (x : real) : (term704 x) = (term705 x).
Proof. exact (MK_COMB (@lem1738808) (@lem1738807 x)). Qed.
Lemma lem1738810 (x : real) : (term697 x) = (term706 x).
Proof. exact (MK_COMB (@lem1738809 x) (@lem1738800 x)). Qed.
Lemma lem1738811 (x : real) : (term696 x) = (term706 x).
Proof. exact (TRANS (@lem1738793 x) (@lem1738810 x)). Qed.
Lemma lem1738812 (x : real) : (term348 x) = (term706 x).
Proof. exact (TRANS (@lem1738792 x) (@lem1738811 x)). Qed.
Lemma lem1738829 (x : real) : (term313 x) = (term651 x).
Proof. exact (@lem19367 term307 term303 (x = term4)). Qed.
Lemma lem1738846 (x : real) : (term289 x) = (term652 x).
Proof. exact (@lem19158 (term16 x) (term13 = term4) (term267 x)). Qed.
Lemma lem1738847 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738848 (x : real) : (term314 x) = (term653 x).
Proof. exact (MK_COMB (@lem1738847) (@lem1738846 x)). Qed.
Lemma lem1738849 (x : real) : (term315 x) = (term654 x).
Proof. exact (MK_COMB (@lem1738848 x) (@lem1738829 x)). Qed.
Lemma lem1738852 (x : real) : (term316 x) = (term316 x).
Proof. exact (eq_refl (term316 x)). Qed.
Lemma lem1738853 (x : real) : (term318 x) = (term655 x).
Proof. exact (MK_COMB (@lem1738852 x) (@lem1738849 x)). Qed.
Lemma lem1738854 (x : real) : (term655 x) = (term656 x).
Proof. exact (@lem19158 (term652 x) (term16 x) (term651 x)). Qed.
Lemma lem1738861 (x : real) : (term657 x) = (term658 x).
Proof. exact (@lem19158 (term659 x) (term16 x) (term660 x)). Qed.
Lemma lem1738868 (x : real) : (term661 x) = (term662 x).
Proof. exact (@lem19158 (term663 x) (term16 x) (term664 x)). Qed.
Lemma lem1738869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738870 (x : real) : (term665 x) = (term666 x).
Proof. exact (MK_COMB (@lem1738869) (@lem1738868 x)). Qed.
Lemma lem1738871 (x : real) : (term656 x) = (term667 x).
Proof. exact (MK_COMB (@lem1738870 x) (@lem1738861 x)). Qed.
Lemma lem1738872 (x : real) : (term655 x) = (term667 x).
Proof. exact (TRANS (@lem1738854 x) (@lem1738871 x)). Qed.
Lemma lem1738873 (x : real) : (term318 x) = (term667 x).
Proof. exact (TRANS (@lem1738853 x) (@lem1738872 x)). Qed.
Lemma lem1738874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738875 (x : real) : (term349 x) = (term668 x).
Proof. exact (MK_COMB (@lem1738874) (@lem1738873 x)). Qed.
Lemma lem1738876 (x : real) : (term350 x) = (term707 x).
Proof. exact (MK_COMB (@lem1738875 x) (@lem1738812 x)). Qed.
Lemma lem1738879 (x : real) : (term352 x) = (term352 x).
Proof. exact (eq_refl (term352 x)). Qed.
Lemma lem1738880 (x : real) : (term354 x) = (term708 x).
Proof. exact (MK_COMB (@lem1738879 x) (@lem1738876 x)). Qed.
Lemma lem1738881 (x : real) : (term708 x) = (term709 x).
Proof. exact (@lem19158 (term667 x) (term267 x) (term706 x)). Qed.
Lemma lem1738882 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem19158 (term701 x) (term267 x) (term699 x)). Qed.
Lemma lem1738889 (x : real) : (term712 x) = (term713 x).
Proof. exact (@lem19158 (term714 x) (term267 x) (term715 x)). Qed.
Lemma lem1738896 (x : real) : (term716 x) = (term717 x).
Proof. exact (@lem19158 (term718 x) (term267 x) (term719 x)). Qed.
Lemma lem1738897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738898 (x : real) : (term720 x) = (term721 x).
Proof. exact (MK_COMB (@lem1738897) (@lem1738896 x)). Qed.
Lemma lem1738899 (x : real) : (term711 x) = (term722 x).
Proof. exact (MK_COMB (@lem1738898 x) (@lem1738889 x)). Qed.
Lemma lem1738900 (x : real) : (term710 x) = (term722 x).
Proof. exact (TRANS (@lem1738882 x) (@lem1738899 x)). Qed.
Lemma lem1738901 (x : real) : (term723 x) = (term724 x).
Proof. exact (@lem19158 (term662 x) (term267 x) (term658 x)). Qed.
Lemma lem1738908 (x : real) : (term725 x) = (term726 x).
Proof. exact (@lem19158 (term680 x) (term267 x) (term681 x)). Qed.
Lemma lem1738915 (x : real) : (term727 x) = (term728 x).
Proof. exact (@lem19158 (term684 x) (term267 x) (term685 x)). Qed.
Lemma lem1738916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738917 (x : real) : (term729 x) = (term730 x).
Proof. exact (MK_COMB (@lem1738916) (@lem1738915 x)). Qed.
Lemma lem1738918 (x : real) : (term724 x) = (term731 x).
Proof. exact (MK_COMB (@lem1738917 x) (@lem1738908 x)). Qed.
Lemma lem1738919 (x : real) : (term723 x) = (term731 x).
Proof. exact (TRANS (@lem1738901 x) (@lem1738918 x)). Qed.
Lemma lem1738920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738921 (x : real) : (term732 x) = (term733 x).
Proof. exact (MK_COMB (@lem1738920) (@lem1738919 x)). Qed.
Lemma lem1738922 (x : real) : (term709 x) = (term734 x).
Proof. exact (MK_COMB (@lem1738921 x) (@lem1738900 x)). Qed.
Lemma lem1738923 (x : real) : (term708 x) = (term734 x).
Proof. exact (TRANS (@lem1738881 x) (@lem1738922 x)). Qed.
Lemma lem1738924 (x : real) : (term354 x) = (term734 x).
Proof. exact (TRANS (@lem1738880 x) (@lem1738923 x)). Qed.
Lemma lem1738925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738926 (x : real) : (term365 x) = (term735 x).
Proof. exact (MK_COMB (@lem1738925) (@lem1738924 x)). Qed.
Lemma lem1738927 (x : real) : (term366 x) = (term736 x).
Proof. exact (MK_COMB (@lem1738926 x) (@lem1738751 x)). Qed.
Lemma lem1738928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1738929 (x : real) : (term584 x) = (term737 x).
Proof. exact (MK_COMB (@lem1738928) (@lem1738927 x)). Qed.
Lemma lem1738930 (x : real) : (term586 x) = (term738 x).
Proof. exact (MK_COMB (@lem1738929 x) (@lem1738634 x)). Qed.
Lemma lem1738931 : term588 = term739.
Proof. exact (fun_ext (fun x : real => @lem1738930 x)). Qed.
Lemma lem1738932 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1738933 : term589 = term740.
Proof. exact (MK_COMB (@lem1738932) (@lem1738931)). Qed.
Lemma lem1738934 : term73 = term740.
Proof. exact (TRANS (@lem1738409) (@lem1738933)). Qed.
Lemma lem1739088 (x : real) (h1 : term738 x) : term738 x.
Proof. exact (h1). Qed.
Lemma lem1739089 (x : real) (h1 : term736 x) : term736 x.
Proof. exact (h1). Qed.
Lemma lem1739090 (x : real) (h1 : term734 x) : term734 x.
Proof. exact (h1). Qed.
Lemma lem1739091 (x : real) (h1 : term731 x) : term731 x.
Proof. exact (h1). Qed.
Lemma lem1739092 (x : real) (h1 : term728 x) : term728 x.
Proof. exact (h1). Qed.
Lemma lem1739093 (x : real) (h1 : term741 x) : term741 x.
Proof. exact (h1). Qed.
Lemma lem1739094 (x : real) (h1 : term741 x) : term684 x.
Proof. exact (proj2 (@lem1739093 x h1)). Qed.
Lemma lem1739096 (x : real) (h1 : term741 x) : term663 x.
Proof. exact (proj2 (@lem1739094 x h1)). Qed.
Lemma lem1739099 (x : real) (h1 : term741 x) : term13 = term4.
Proof. exact (proj1 (@lem1739096 x h1)). Qed.
Lemma lem1739101 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1739102 : (term13 = term4) = (term273 = (NUMERAL 0)).
Proof. exact (@lem1739101 term273 (NUMERAL 0)). Qed.
Lemma lem1739103 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739104 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739105 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739104 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739103)). Qed.
Lemma lem1739106 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739105) (@lem1739103)). Qed.
Lemma lem1739107 : (term13 = term4) = False.
Proof. exact (TRANS (@lem1739102) (@lem1739106)). Qed.
Lemma lem1739108 (x : real) (h1 : term741 x) : False.
Proof. exact (EQ_MP (@lem1739107) (@lem1739099 x h1)). Qed.
Lemma lem1739109 (x : real) (h1 : term743 x) : term743 x.
Proof. exact (h1). Qed.
Lemma lem1739110 (x : real) (h1 : term743 x) : term685 x.
Proof. exact (proj2 (@lem1739109 x h1)). Qed.
Lemma lem1739112 (x : real) (h1 : term743 x) : term664 x.
Proof. exact (proj2 (@lem1739110 x h1)). Qed.
Lemma lem1739115 (x : real) (h1 : term743 x) : term13 = term4.
Proof. exact (proj1 (@lem1739112 x h1)). Qed.
Lemma lem1739117 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1739118 : (term13 = term4) = (term273 = (NUMERAL 0)).
Proof. exact (@lem1739117 term273 (NUMERAL 0)). Qed.
Lemma lem1739119 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739120 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739121 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739120 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739119)). Qed.
Lemma lem1739122 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739121) (@lem1739119)). Qed.
Lemma lem1739123 : (term13 = term4) = False.
Proof. exact (TRANS (@lem1739118) (@lem1739122)). Qed.
Lemma lem1739124 (x : real) (h1 : term743 x) : False.
Proof. exact (EQ_MP (@lem1739123) (@lem1739115 x h1)). Qed.
Lemma lem1739125 (x : real) (h1 : term728 x) : False.
Proof. exact (or_elim (@lem1739092 x h1) (fun h0 : term741 x => @lem1739108 x h0) (fun h0 : term743 x => @lem1739124 x h0)). Qed.
Lemma lem1739126 (x : real) (h1 : term726 x) : term726 x.
Proof. exact (h1). Qed.
Lemma lem1739127 (x : real) (h1 : term744 x) : term744 x.
Proof. exact (h1). Qed.
Lemma lem1739128 (x : real) (h1 : term744 x) : term680 x.
Proof. exact (proj2 (@lem1739127 x h1)). Qed.
Lemma lem1739130 (x : real) (h1 : term744 x) : term659 x.
Proof. exact (proj2 (@lem1739128 x h1)). Qed.
Lemma lem1739131 (x : real) (h1 : term744 x) : term16 x.
Proof. exact (proj1 (@lem1739128 x h1)). Qed.
Lemma lem1739132 (x : real) (h1 : term744 x) : x = term4.
Proof. exact (proj2 (@lem1739130 x h1)). Qed.
Lemma lem1739135 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739136 : term307 = term746.
Proof. exact (@lem1739135 (NUMERAL 0) term273). Qed.
Lemma lem1739137 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739138 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739139 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739138 h1) (fun h1 : term746 = True => @lem1739137)). Qed.
Lemma lem1739140 : term746 = True.
Proof. exact (EQ_MP (@lem1739139) (@lem1739137)). Qed.
Lemma lem1739141 : term307 = True.
Proof. exact (TRANS (@lem1739136) (@lem1739140)). Qed.
Lemma lem1739142 : True = term307.
Proof. exact (SYM (@lem1739141)). Qed.
Lemma lem1739143 : term307.
Proof. exact (EQ_MP (@lem1739142) (@lem0)). Qed.
Lemma lem1739144 (x : real) (h1 : term744 x) : term605 x.
Proof. exact (conj (@lem1739143) (@lem1739131 x h1)). Qed.
Lemma lem1739146 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739147 (x : real) : term748 x.
Proof. exact (@lem1739146 term13 x). Qed.
Lemma lem1739148 (x : real) (h1 : term744 x) : term749 x.
Proof. exact (@lem1739147 x (@lem1739144 x h1)). Qed.
Lemma lem1739149 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739150 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739151 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739150) (@lem1739149 x)). Qed.
Lemma lem1739152 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739153 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739151 x) (@lem1739152)). Qed.
Lemma lem1739154 (x : real) (h1 : term744 x) : term16 x.
Proof. exact (EQ_MP (@lem1739153 x) (@lem1739148 x h1)). Qed.
Lemma lem1739156 (y : real) : term752 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1739157 (x : real) : term752 x.
Proof. exact (@lem1739156 x). Qed.
Lemma lem1739158 (x : real) (h1 : term744 x) : term753 x.
Proof. exact (@lem1739157 x (@lem1739132 x h1)). Qed.
Lemma lem1739159 (x : real) (h1 : term744 x) : term754 x.
Proof. exact (@lem1739158 x h1 term23). Qed.
Lemma lem1739160 (x : real) : (term754 x) = ((term264 x) = term4).
Proof. exact (eq_refl (term754 x)). Qed.
Lemma lem1739167 (x : real) (h1 : term744 x) : (term264 x) = term4.
Proof. exact (EQ_MP (@lem1739160 x) (@lem1739159 x h1)). Qed.
Lemma lem1739168 (x : real) (h1 : term744 x) : term755 x.
Proof. exact (conj (@lem1739167 x h1) (@lem1739154 x h1)). Qed.
Lemma lem1739170 (x : real) (y : real) : term756 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1739171 (x : real) : term757 x.
Proof. exact (@lem1739170 (term264 x) x). Qed.
Lemma lem1739172 (x : real) (h1 : term744 x) : term758 x.
Proof. exact (@lem1739171 x (@lem1739168 x h1)). Qed.
Lemma lem1739173 (x : real) : (term759 x) = (term760 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1739175 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739176 : term762 = term4.
Proof. exact (@lem1739175 term273). Qed.
Lemma lem1739177 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739178 : term763 = term764.
Proof. exact (MK_COMB (@lem1739177) (@lem1739176)). Qed.
Lemma lem1739179 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739180 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739178) (@lem1739179 x)). Qed.
Lemma lem1739181 (x : real) : (term759 x) = (term765 x).
Proof. exact (TRANS (@lem1739173 x) (@lem1739180 x)). Qed.
Lemma lem1739182 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739183 (x : real) : (term759 x) = term4.
Proof. exact (TRANS (@lem1739181 x) (@lem1739182 x)). Qed.
Lemma lem1739184 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739185 (x : real) : (term766 x) = term767.
Proof. exact (MK_COMB (@lem1739184) (@lem1739183 x)). Qed.
Lemma lem1739186 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739187 (x : real) : (term758 x) = term768.
Proof. exact (MK_COMB (@lem1739185 x) (@lem1739186)). Qed.
Lemma lem1739188 (x : real) (h1 : term744 x) : term768.
Proof. exact (EQ_MP (@lem1739187 x) (@lem1739172 x h1)). Qed.
Lemma lem1739190 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739191 : term768 = term769.
Proof. exact (@lem1739190 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739192 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739193 : term768 = False.
Proof. exact (TRANS (@lem1739191) (@lem1739192)). Qed.
Lemma lem1739194 (x : real) (h1 : term744 x) : False.
Proof. exact (EQ_MP (@lem1739193) (@lem1739188 x h1)). Qed.
Lemma lem1739195 (x : real) (h1 : term770 x) : term770 x.
Proof. exact (h1). Qed.
Lemma lem1739196 (x : real) (h1 : term770 x) : term681 x.
Proof. exact (proj2 (@lem1739195 x h1)). Qed.
Lemma lem1739198 (x : real) (h1 : term770 x) : term660 x.
Proof. exact (proj2 (@lem1739196 x h1)). Qed.
Lemma lem1739201 (x : real) (h1 : term770 x) : term303.
Proof. exact (proj1 (@lem1739198 x h1)). Qed.
Lemma lem1739203 (m : nat) (n : nat) : (term771 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1739204 : term303 = False.
Proof. exact (@lem1739203 term273 (NUMERAL 0)). Qed.
Lemma lem1739205 (x : real) (h1 : term770 x) : False.
Proof. exact (EQ_MP (@lem1739204) (@lem1739201 x h1)). Qed.
Lemma lem1739206 (x : real) (h1 : term726 x) : False.
Proof. exact (or_elim (@lem1739126 x h1) (fun h0 : term744 x => @lem1739194 x h0) (fun h0 : term770 x => @lem1739205 x h0)). Qed.
Lemma lem1739207 (x : real) (h1 : term731 x) : False.
Proof. exact (or_elim (@lem1739091 x h1) (fun h0 : term728 x => @lem1739125 x h0) (fun h0 : term726 x => @lem1739206 x h0)). Qed.
Lemma lem1739208 (x : real) (h1 : term722 x) : term722 x.
Proof. exact (h1). Qed.
Lemma lem1739209 (x : real) (h1 : term717 x) : term717 x.
Proof. exact (h1). Qed.
Lemma lem1739210 (x : real) (h1 : term772 x) : term772 x.
Proof. exact (h1). Qed.
Lemma lem1739211 (x : real) (h1 : term772 x) : term718 x.
Proof. exact (proj2 (@lem1739210 x h1)). Qed.
Lemma lem1739213 (x : real) (h1 : term772 x) : term702 x.
Proof. exact (proj2 (@lem1739211 x h1)). Qed.
Lemma lem1739216 (x : real) (h1 : term772 x) : term23 = term4.
Proof. exact (proj1 (@lem1739213 x h1)). Qed.
Lemma lem1739218 (m : nat) (n : nat) : ((term773 m) = (real_of_num n)) = (term774 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem1739219 : (term23 = term4) = term775.
Proof. exact (@lem1739218 term273 (NUMERAL 0)). Qed.
Lemma lem1739220 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1739221 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739222 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739223 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739222 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739221)). Qed.
Lemma lem1739224 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739223) (@lem1739221)). Qed.
Lemma lem1739225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1739226 : term776 = (and False).
Proof. exact (MK_COMB (@lem1739225) (@lem1739224)). Qed.
Lemma lem1739227 : term775 = (False /\ True).
Proof. exact (MK_COMB (@lem1739226) (@lem1739220)). Qed.
Lemma lem1739229 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1739230 : term775 = False.
Proof. exact (TRANS (@lem1739227) (@lem1739229)). Qed.
Lemma lem1739231 : (term23 = term4) = False.
Proof. exact (TRANS (@lem1739219) (@lem1739230)). Qed.
Lemma lem1739232 (x : real) (h1 : term772 x) : False.
Proof. exact (EQ_MP (@lem1739231) (@lem1739216 x h1)). Qed.
Lemma lem1739233 (x : real) (h1 : term777 x) : term777 x.
Proof. exact (h1). Qed.
Lemma lem1739234 (x : real) (h1 : term777 x) : term719 x.
Proof. exact (proj2 (@lem1739233 x h1)). Qed.
Lemma lem1739236 (x : real) (h1 : term777 x) : term703 x.
Proof. exact (proj2 (@lem1739234 x h1)). Qed.
Lemma lem1739239 (x : real) (h1 : term777 x) : term23 = term4.
Proof. exact (proj1 (@lem1739236 x h1)). Qed.
Lemma lem1739241 (m : nat) (n : nat) : ((term773 m) = (real_of_num n)) = (term774 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem1739242 : (term23 = term4) = term775.
Proof. exact (@lem1739241 term273 (NUMERAL 0)). Qed.
Lemma lem1739243 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1739244 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739245 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739246 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739245 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739244)). Qed.
Lemma lem1739247 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739246) (@lem1739244)). Qed.
Lemma lem1739248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1739249 : term776 = (and False).
Proof. exact (MK_COMB (@lem1739248) (@lem1739247)). Qed.
Lemma lem1739250 : term775 = (False /\ True).
Proof. exact (MK_COMB (@lem1739249) (@lem1739243)). Qed.
Lemma lem1739252 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1739253 : term775 = False.
Proof. exact (TRANS (@lem1739250) (@lem1739252)). Qed.
Lemma lem1739254 : (term23 = term4) = False.
Proof. exact (TRANS (@lem1739242) (@lem1739253)). Qed.
Lemma lem1739255 (x : real) (h1 : term777 x) : False.
Proof. exact (EQ_MP (@lem1739254) (@lem1739239 x h1)). Qed.
Lemma lem1739256 (x : real) (h1 : term717 x) : False.
Proof. exact (or_elim (@lem1739209 x h1) (fun h0 : term772 x => @lem1739232 x h0) (fun h0 : term777 x => @lem1739255 x h0)). Qed.
Lemma lem1739257 (x : real) (h1 : term713 x) : term713 x.
Proof. exact (h1). Qed.
Lemma lem1739258 (x : real) (h1 : term778 x) : term778 x.
Proof. exact (h1). Qed.
Lemma lem1739259 (x : real) (h1 : term778 x) : term714 x.
Proof. exact (proj2 (@lem1739258 x h1)). Qed.
Lemma lem1739261 (x : real) (h1 : term778 x) : term660 x.
Proof. exact (proj2 (@lem1739259 x h1)). Qed.
Lemma lem1739264 (x : real) (h1 : term778 x) : term303.
Proof. exact (proj1 (@lem1739261 x h1)). Qed.
Lemma lem1739266 (m : nat) (n : nat) : (term771 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1739267 : term303 = False.
Proof. exact (@lem1739266 term273 (NUMERAL 0)). Qed.
Lemma lem1739268 (x : real) (h1 : term778 x) : False.
Proof. exact (EQ_MP (@lem1739267) (@lem1739264 x h1)). Qed.
Lemma lem1739269 (x : real) (h1 : term779 x) : term779 x.
Proof. exact (h1). Qed.
Lemma lem1739270 (x : real) (h1 : term779 x) : term715 x.
Proof. exact (proj2 (@lem1739269 x h1)). Qed.
Lemma lem1739271 (x : real) (h1 : term779 x) : term267 x.
Proof. exact (proj1 (@lem1739269 x h1)). Qed.
Lemma lem1739272 (x : real) (h1 : term779 x) : term659 x.
Proof. exact (proj2 (@lem1739270 x h1)). Qed.
Lemma lem1739274 (x : real) (h1 : term779 x) : x = term4.
Proof. exact (proj2 (@lem1739272 x h1)). Qed.
Lemma lem1739277 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739278 : term307 = term746.
Proof. exact (@lem1739277 (NUMERAL 0) term273). Qed.
Lemma lem1739279 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739280 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739281 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739280 h1) (fun h1 : term746 = True => @lem1739279)). Qed.
Lemma lem1739282 : term746 = True.
Proof. exact (EQ_MP (@lem1739281) (@lem1739279)). Qed.
Lemma lem1739283 : term307 = True.
Proof. exact (TRANS (@lem1739278) (@lem1739282)). Qed.
Lemma lem1739284 : True = term307.
Proof. exact (SYM (@lem1739283)). Qed.
Lemma lem1739285 : term307.
Proof. exact (EQ_MP (@lem1739284) (@lem0)). Qed.
Lemma lem1739286 (x : real) (h1 : term779 x) : term780 x.
Proof. exact (conj (@lem1739285) (@lem1739271 x h1)). Qed.
Lemma lem1739288 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739289 (x : real) : term781 x.
Proof. exact (@lem1739288 term13 (term264 x)). Qed.
Lemma lem1739290 (x : real) (h1 : term779 x) : term782 x.
Proof. exact (@lem1739289 x (@lem1739286 x h1)). Qed.
Lemma lem1739291 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739292 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739293 (x : real) : (term784 x) = (term266 x).
Proof. exact (MK_COMB (@lem1739292) (@lem1739291 x)). Qed.
Lemma lem1739294 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739295 (x : real) : (term782 x) = (term267 x).
Proof. exact (MK_COMB (@lem1739293 x) (@lem1739294)). Qed.
Lemma lem1739296 (x : real) (h1 : term779 x) : term267 x.
Proof. exact (EQ_MP (@lem1739295 x) (@lem1739290 x h1)). Qed.
Lemma lem1739298 (y : real) : term752 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1739299 (x : real) : term752 x.
Proof. exact (@lem1739298 x). Qed.
Lemma lem1739300 (x : real) (h1 : term779 x) : term753 x.
Proof. exact (@lem1739299 x (@lem1739274 x h1)). Qed.
Lemma lem1739301 (x : real) (h1 : term779 x) : term785 x.
Proof. exact (@lem1739300 x h1 term13). Qed.
Lemma lem1739302 (x : real) : (term785 x) = ((term750 x) = term4).
Proof. exact (eq_refl (term785 x)). Qed.
Lemma lem1739303 (x : real) (h1 : term779 x) : (term750 x) = term4.
Proof. exact (EQ_MP (@lem1739302 x) (@lem1739301 x h1)). Qed.
Lemma lem1739304 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739305 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1739306 (x : real) : (term786 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1739305) (@lem1739304 x)). Qed.
Lemma lem1739307 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739308 (x : real) : ((term750 x) = term4) = (x = term4).
Proof. exact (MK_COMB (@lem1739306 x) (@lem1739307)). Qed.
Lemma lem1739309 (x : real) (h1 : term779 x) : x = term4.
Proof. exact (EQ_MP (@lem1739308 x) (@lem1739303 x h1)). Qed.
Lemma lem1739310 (x : real) (h1 : term779 x) : term787 x.
Proof. exact (conj (@lem1739309 x h1) (@lem1739296 x h1)). Qed.
Lemma lem1739312 (x : real) (y : real) : term756 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1739313 (x : real) : term788 x.
Proof. exact (@lem1739312 x (term264 x)). Qed.
Lemma lem1739314 (x : real) (h1 : term779 x) : term789 x.
Proof. exact (@lem1739313 x (@lem1739310 x h1)). Qed.
Lemma lem1739315 (x : real) : (term790 x) = (term760 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1739317 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739318 : term762 = term4.
Proof. exact (@lem1739317 term273). Qed.
Lemma lem1739319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739320 : term763 = term764.
Proof. exact (MK_COMB (@lem1739319) (@lem1739318)). Qed.
Lemma lem1739321 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739322 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739320) (@lem1739321 x)). Qed.
Lemma lem1739323 (x : real) : (term790 x) = (term765 x).
Proof. exact (TRANS (@lem1739315 x) (@lem1739322 x)). Qed.
Lemma lem1739324 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739325 (x : real) : (term790 x) = term4.
Proof. exact (TRANS (@lem1739323 x) (@lem1739324 x)). Qed.
Lemma lem1739326 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739327 (x : real) : (term791 x) = term767.
Proof. exact (MK_COMB (@lem1739326) (@lem1739325 x)). Qed.
Lemma lem1739328 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739329 (x : real) : (term789 x) = term768.
Proof. exact (MK_COMB (@lem1739327 x) (@lem1739328)). Qed.
Lemma lem1739330 (x : real) (h1 : term779 x) : term768.
Proof. exact (EQ_MP (@lem1739329 x) (@lem1739314 x h1)). Qed.
Lemma lem1739332 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739333 : term768 = term769.
Proof. exact (@lem1739332 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739334 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739335 : term768 = False.
Proof. exact (TRANS (@lem1739333) (@lem1739334)). Qed.
Lemma lem1739336 (x : real) (h1 : term779 x) : False.
Proof. exact (EQ_MP (@lem1739335) (@lem1739330 x h1)). Qed.
Lemma lem1739337 (x : real) (h1 : term713 x) : False.
Proof. exact (or_elim (@lem1739257 x h1) (fun h0 : term778 x => @lem1739268 x h0) (fun h0 : term779 x => @lem1739336 x h0)). Qed.
Lemma lem1739338 (x : real) (h1 : term722 x) : False.
Proof. exact (or_elim (@lem1739208 x h1) (fun h0 : term717 x => @lem1739256 x h0) (fun h0 : term713 x => @lem1739337 x h0)). Qed.
Lemma lem1739339 (x : real) (h1 : term734 x) : False.
Proof. exact (or_elim (@lem1739090 x h1) (fun h0 : term731 x => @lem1739207 x h0) (fun h0 : term722 x => @lem1739338 x h0)). Qed.
Lemma lem1739340 (x : real) (h1 : term691 x) : term691 x.
Proof. exact (h1). Qed.
Lemma lem1739341 (x : real) (h1 : term688 x) : term688 x.
Proof. exact (h1). Qed.
Lemma lem1739342 (x : real) (h1 : term683 x) : term683 x.
Proof. exact (h1). Qed.
Lemma lem1739343 (x : real) (h1 : term792 x) : term792 x.
Proof. exact (h1). Qed.
Lemma lem1739344 (x : real) (h1 : term792 x) : term684 x.
Proof. exact (proj2 (@lem1739343 x h1)). Qed.
Lemma lem1739346 (x : real) (h1 : term792 x) : term663 x.
Proof. exact (proj2 (@lem1739344 x h1)). Qed.
Lemma lem1739349 (x : real) (h1 : term792 x) : term13 = term4.
Proof. exact (proj1 (@lem1739346 x h1)). Qed.
Lemma lem1739351 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1739352 : (term13 = term4) = (term273 = (NUMERAL 0)).
Proof. exact (@lem1739351 term273 (NUMERAL 0)). Qed.
Lemma lem1739353 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739354 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739355 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739354 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739353)). Qed.
Lemma lem1739356 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739355) (@lem1739353)). Qed.
Lemma lem1739357 : (term13 = term4) = False.
Proof. exact (TRANS (@lem1739352) (@lem1739356)). Qed.
Lemma lem1739358 (x : real) (h1 : term792 x) : False.
Proof. exact (EQ_MP (@lem1739357) (@lem1739349 x h1)). Qed.
Lemma lem1739359 (x : real) (h1 : term793 x) : term793 x.
Proof. exact (h1). Qed.
Lemma lem1739360 (x : real) (h1 : term793 x) : term685 x.
Proof. exact (proj2 (@lem1739359 x h1)). Qed.
Lemma lem1739362 (x : real) (h1 : term793 x) : term664 x.
Proof. exact (proj2 (@lem1739360 x h1)). Qed.
Lemma lem1739365 (x : real) (h1 : term793 x) : term13 = term4.
Proof. exact (proj1 (@lem1739362 x h1)). Qed.
Lemma lem1739367 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1739368 : (term13 = term4) = (term273 = (NUMERAL 0)).
Proof. exact (@lem1739367 term273 (NUMERAL 0)). Qed.
Lemma lem1739369 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739370 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739371 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739370 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739369)). Qed.
Lemma lem1739372 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739371) (@lem1739369)). Qed.
Lemma lem1739373 : (term13 = term4) = False.
Proof. exact (TRANS (@lem1739368) (@lem1739372)). Qed.
Lemma lem1739374 (x : real) (h1 : term793 x) : False.
Proof. exact (EQ_MP (@lem1739373) (@lem1739365 x h1)). Qed.
Lemma lem1739375 (x : real) (h1 : term683 x) : False.
Proof. exact (or_elim (@lem1739342 x h1) (fun h0 : term792 x => @lem1739358 x h0) (fun h0 : term793 x => @lem1739374 x h0)). Qed.
Lemma lem1739376 (x : real) (h1 : term679 x) : term679 x.
Proof. exact (h1). Qed.
Lemma lem1739377 (x : real) (h1 : term794 x) : term794 x.
Proof. exact (h1). Qed.
Lemma lem1739378 (x : real) (h1 : term794 x) : term680 x.
Proof. exact (proj2 (@lem1739377 x h1)). Qed.
Lemma lem1739380 (x : real) (h1 : term794 x) : term659 x.
Proof. exact (proj2 (@lem1739378 x h1)). Qed.
Lemma lem1739381 (x : real) (h1 : term794 x) : term16 x.
Proof. exact (proj1 (@lem1739378 x h1)). Qed.
Lemma lem1739382 (x : real) (h1 : term794 x) : x = term4.
Proof. exact (proj2 (@lem1739380 x h1)). Qed.
Lemma lem1739385 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739386 : term307 = term746.
Proof. exact (@lem1739385 (NUMERAL 0) term273). Qed.
Lemma lem1739387 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739388 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739389 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739388 h1) (fun h1 : term746 = True => @lem1739387)). Qed.
Lemma lem1739390 : term746 = True.
Proof. exact (EQ_MP (@lem1739389) (@lem1739387)). Qed.
Lemma lem1739391 : term307 = True.
Proof. exact (TRANS (@lem1739386) (@lem1739390)). Qed.
Lemma lem1739392 : True = term307.
Proof. exact (SYM (@lem1739391)). Qed.
Lemma lem1739393 : term307.
Proof. exact (EQ_MP (@lem1739392) (@lem0)). Qed.
Lemma lem1739394 (x : real) (h1 : term794 x) : term605 x.
Proof. exact (conj (@lem1739393) (@lem1739381 x h1)). Qed.
Lemma lem1739396 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739397 (x : real) : term748 x.
Proof. exact (@lem1739396 term13 x). Qed.
Lemma lem1739398 (x : real) (h1 : term794 x) : term749 x.
Proof. exact (@lem1739397 x (@lem1739394 x h1)). Qed.
Lemma lem1739399 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739400 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739401 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739400) (@lem1739399 x)). Qed.
Lemma lem1739402 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739403 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739401 x) (@lem1739402)). Qed.
Lemma lem1739404 (x : real) (h1 : term794 x) : term16 x.
Proof. exact (EQ_MP (@lem1739403 x) (@lem1739398 x h1)). Qed.
Lemma lem1739406 (y : real) : term752 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1739407 (x : real) : term752 x.
Proof. exact (@lem1739406 x). Qed.
Lemma lem1739408 (x : real) (h1 : term794 x) : term753 x.
Proof. exact (@lem1739407 x (@lem1739382 x h1)). Qed.
Lemma lem1739409 (x : real) (h1 : term794 x) : term754 x.
Proof. exact (@lem1739408 x h1 term23). Qed.
Lemma lem1739410 (x : real) : (term754 x) = ((term264 x) = term4).
Proof. exact (eq_refl (term754 x)). Qed.
Lemma lem1739417 (x : real) (h1 : term794 x) : (term264 x) = term4.
Proof. exact (EQ_MP (@lem1739410 x) (@lem1739409 x h1)). Qed.
Lemma lem1739418 (x : real) (h1 : term794 x) : term755 x.
Proof. exact (conj (@lem1739417 x h1) (@lem1739404 x h1)). Qed.
Lemma lem1739420 (x : real) (y : real) : term756 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1739421 (x : real) : term757 x.
Proof. exact (@lem1739420 (term264 x) x). Qed.
Lemma lem1739422 (x : real) (h1 : term794 x) : term758 x.
Proof. exact (@lem1739421 x (@lem1739418 x h1)). Qed.
Lemma lem1739423 (x : real) : (term759 x) = (term760 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1739425 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739426 : term762 = term4.
Proof. exact (@lem1739425 term273). Qed.
Lemma lem1739427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739428 : term763 = term764.
Proof. exact (MK_COMB (@lem1739427) (@lem1739426)). Qed.
Lemma lem1739429 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739430 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739428) (@lem1739429 x)). Qed.
Lemma lem1739431 (x : real) : (term759 x) = (term765 x).
Proof. exact (TRANS (@lem1739423 x) (@lem1739430 x)). Qed.
Lemma lem1739432 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739433 (x : real) : (term759 x) = term4.
Proof. exact (TRANS (@lem1739431 x) (@lem1739432 x)). Qed.
Lemma lem1739434 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739435 (x : real) : (term766 x) = term767.
Proof. exact (MK_COMB (@lem1739434) (@lem1739433 x)). Qed.
Lemma lem1739436 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739437 (x : real) : (term758 x) = term768.
Proof. exact (MK_COMB (@lem1739435 x) (@lem1739436)). Qed.
Lemma lem1739438 (x : real) (h1 : term794 x) : term768.
Proof. exact (EQ_MP (@lem1739437 x) (@lem1739422 x h1)). Qed.
Lemma lem1739440 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739441 : term768 = term769.
Proof. exact (@lem1739440 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739442 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739443 : term768 = False.
Proof. exact (TRANS (@lem1739441) (@lem1739442)). Qed.
Lemma lem1739444 (x : real) (h1 : term794 x) : False.
Proof. exact (EQ_MP (@lem1739443) (@lem1739438 x h1)). Qed.
Lemma lem1739445 (x : real) (h1 : term795 x) : term795 x.
Proof. exact (h1). Qed.
Lemma lem1739446 (x : real) (h1 : term795 x) : term681 x.
Proof. exact (proj2 (@lem1739445 x h1)). Qed.
Lemma lem1739448 (x : real) (h1 : term795 x) : term660 x.
Proof. exact (proj2 (@lem1739446 x h1)). Qed.
Lemma lem1739451 (x : real) (h1 : term795 x) : term303.
Proof. exact (proj1 (@lem1739448 x h1)). Qed.
Lemma lem1739453 (m : nat) (n : nat) : (term771 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1739454 : term303 = False.
Proof. exact (@lem1739453 term273 (NUMERAL 0)). Qed.
Lemma lem1739455 (x : real) (h1 : term795 x) : False.
Proof. exact (EQ_MP (@lem1739454) (@lem1739451 x h1)). Qed.
Lemma lem1739456 (x : real) (h1 : term679 x) : False.
Proof. exact (or_elim (@lem1739376 x h1) (fun h0 : term794 x => @lem1739444 x h0) (fun h0 : term795 x => @lem1739455 x h0)). Qed.
Lemma lem1739457 (x : real) (h1 : term688 x) : False.
Proof. exact (or_elim (@lem1739341 x h1) (fun h0 : term683 x => @lem1739375 x h0) (fun h0 : term679 x => @lem1739456 x h0)). Qed.
Lemma lem1739458 (x : real) (h1 : term673 x) : term673 x.
Proof. exact (h1). Qed.
Lemma lem1739459 (x : real) (h1 : term796 x) : term796 x.
Proof. exact (h1). Qed.
Lemma lem1739460 (x : real) (h1 : term796 x) : term674 x.
Proof. exact (proj2 (@lem1739459 x h1)). Qed.
Lemma lem1739462 (x : real) (h1 : term796 x) : term16 x.
Proof. exact (proj2 (@lem1739460 x h1)). Qed.
Lemma lem1739463 (x : real) (h1 : term796 x) : term322 x.
Proof. exact (proj1 (@lem1739460 x h1)). Qed.
Lemma lem1739465 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739466 : term307 = term746.
Proof. exact (@lem1739465 (NUMERAL 0) term273). Qed.
Lemma lem1739467 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739468 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739469 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739468 h1) (fun h1 : term746 = True => @lem1739467)). Qed.
Lemma lem1739470 : term746 = True.
Proof. exact (EQ_MP (@lem1739469) (@lem1739467)). Qed.
Lemma lem1739471 : term307 = True.
Proof. exact (TRANS (@lem1739466) (@lem1739470)). Qed.
Lemma lem1739472 : True = term307.
Proof. exact (SYM (@lem1739471)). Qed.
Lemma lem1739473 : term307.
Proof. exact (EQ_MP (@lem1739472) (@lem0)). Qed.
Lemma lem1739474 (x : real) (h1 : term796 x) : term797 x.
Proof. exact (conj (@lem1739473) (@lem1739463 x h1)). Qed.
Lemma lem1739476 (x : real) (y : real) : term798 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1739477 (x : real) : term799 x.
Proof. exact (@lem1739476 term13 (term264 x)). Qed.
Lemma lem1739478 (x : real) (h1 : term796 x) : term800 x.
Proof. exact (@lem1739477 x (@lem1739474 x h1)). Qed.
Lemma lem1739479 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739480 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1739481 (x : real) : (term801 x) = (term321 x).
Proof. exact (MK_COMB (@lem1739480) (@lem1739479 x)). Qed.
Lemma lem1739482 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739483 (x : real) : (term800 x) = (term322 x).
Proof. exact (MK_COMB (@lem1739481 x) (@lem1739482)). Qed.
Lemma lem1739484 (x : real) (h1 : term796 x) : term322 x.
Proof. exact (EQ_MP (@lem1739483 x) (@lem1739478 x h1)). Qed.
Lemma lem1739486 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739487 : term307 = term746.
Proof. exact (@lem1739486 (NUMERAL 0) term273). Qed.
Lemma lem1739488 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739489 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739490 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739489 h1) (fun h1 : term746 = True => @lem1739488)). Qed.
Lemma lem1739491 : term746 = True.
Proof. exact (EQ_MP (@lem1739490) (@lem1739488)). Qed.
Lemma lem1739492 : term307 = True.
Proof. exact (TRANS (@lem1739487) (@lem1739491)). Qed.
Lemma lem1739493 : True = term307.
Proof. exact (SYM (@lem1739492)). Qed.
Lemma lem1739494 : term307.
Proof. exact (EQ_MP (@lem1739493) (@lem0)). Qed.
Lemma lem1739495 (x : real) (h1 : term796 x) : term605 x.
Proof. exact (conj (@lem1739494) (@lem1739462 x h1)). Qed.
Lemma lem1739497 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739498 (x : real) : term748 x.
Proof. exact (@lem1739497 term13 x). Qed.
Lemma lem1739499 (x : real) (h1 : term796 x) : term749 x.
Proof. exact (@lem1739498 x (@lem1739495 x h1)). Qed.
Lemma lem1739500 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739501 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739502 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739501) (@lem1739500 x)). Qed.
Lemma lem1739503 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739504 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739502 x) (@lem1739503)). Qed.
Lemma lem1739505 (x : real) (h1 : term796 x) : term16 x.
Proof. exact (EQ_MP (@lem1739504 x) (@lem1739499 x h1)). Qed.
Lemma lem1739506 (x : real) (h1 : term796 x) : term370 x.
Proof. exact (conj (@lem1739505 x h1) (@lem1739484 x h1)). Qed.
Lemma lem1739508 (x : real) (y : real) : term802 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1739509 (x : real) : term803 x.
Proof. exact (@lem1739508 x (term264 x)). Qed.
Lemma lem1739510 (x : real) (h1 : term796 x) : term789 x.
Proof. exact (@lem1739509 x (@lem1739506 x h1)). Qed.
Lemma lem1739511 (x : real) : (term790 x) = (term760 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1739513 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739514 : term762 = term4.
Proof. exact (@lem1739513 term273). Qed.
Lemma lem1739515 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739516 : term763 = term764.
Proof. exact (MK_COMB (@lem1739515) (@lem1739514)). Qed.
Lemma lem1739517 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739518 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739516) (@lem1739517 x)). Qed.
Lemma lem1739519 (x : real) : (term790 x) = (term765 x).
Proof. exact (TRANS (@lem1739511 x) (@lem1739518 x)). Qed.
Lemma lem1739520 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739521 (x : real) : (term790 x) = term4.
Proof. exact (TRANS (@lem1739519 x) (@lem1739520 x)). Qed.
Lemma lem1739522 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739523 (x : real) : (term791 x) = term767.
Proof. exact (MK_COMB (@lem1739522) (@lem1739521 x)). Qed.
Lemma lem1739524 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739525 (x : real) : (term789 x) = term768.
Proof. exact (MK_COMB (@lem1739523 x) (@lem1739524)). Qed.
Lemma lem1739526 (x : real) (h1 : term796 x) : term768.
Proof. exact (EQ_MP (@lem1739525 x) (@lem1739510 x h1)). Qed.
Lemma lem1739528 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739529 : term768 = term769.
Proof. exact (@lem1739528 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739530 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739531 : term768 = False.
Proof. exact (TRANS (@lem1739529) (@lem1739530)). Qed.
Lemma lem1739532 (x : real) (h1 : term796 x) : False.
Proof. exact (EQ_MP (@lem1739531) (@lem1739526 x h1)). Qed.
Lemma lem1739533 (x : real) (h1 : term804 x) : term804 x.
Proof. exact (h1). Qed.
Lemma lem1739534 (x : real) (h1 : term804 x) : term675 x.
Proof. exact (proj2 (@lem1739533 x h1)). Qed.
Lemma lem1739535 (x : real) (h1 : term804 x) : term357 x.
Proof. exact (proj1 (@lem1739533 x h1)). Qed.
Lemma lem1739536 (x : real) (h1 : term804 x) : term267 x.
Proof. exact (proj2 (@lem1739534 x h1)). Qed.
Lemma lem1739539 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739540 : term307 = term746.
Proof. exact (@lem1739539 (NUMERAL 0) term273). Qed.
Lemma lem1739541 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739542 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739543 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739542 h1) (fun h1 : term746 = True => @lem1739541)). Qed.
Lemma lem1739544 : term746 = True.
Proof. exact (EQ_MP (@lem1739543) (@lem1739541)). Qed.
Lemma lem1739545 : term307 = True.
Proof. exact (TRANS (@lem1739540) (@lem1739544)). Qed.
Lemma lem1739546 : True = term307.
Proof. exact (SYM (@lem1739545)). Qed.
Lemma lem1739547 : term307.
Proof. exact (EQ_MP (@lem1739546) (@lem0)). Qed.
Lemma lem1739548 (x : real) (h1 : term804 x) : term805 x.
Proof. exact (conj (@lem1739547) (@lem1739535 x h1)). Qed.
Lemma lem1739550 (x : real) (y : real) : term798 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1739551 (x : real) : term806 x.
Proof. exact (@lem1739550 term13 x). Qed.
Lemma lem1739552 (x : real) (h1 : term804 x) : term807 x.
Proof. exact (@lem1739551 x (@lem1739548 x h1)). Qed.
Lemma lem1739553 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739554 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1739555 (x : real) : (term808 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1739554) (@lem1739553 x)). Qed.
Lemma lem1739556 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739557 (x : real) : (term807 x) = (term357 x).
Proof. exact (MK_COMB (@lem1739555 x) (@lem1739556)). Qed.
Lemma lem1739558 (x : real) (h1 : term804 x) : term357 x.
Proof. exact (EQ_MP (@lem1739557 x) (@lem1739552 x h1)). Qed.
Lemma lem1739560 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739561 : term307 = term746.
Proof. exact (@lem1739560 (NUMERAL 0) term273). Qed.
Lemma lem1739562 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739563 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739564 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739563 h1) (fun h1 : term746 = True => @lem1739562)). Qed.
Lemma lem1739565 : term746 = True.
Proof. exact (EQ_MP (@lem1739564) (@lem1739562)). Qed.
Lemma lem1739566 : term307 = True.
Proof. exact (TRANS (@lem1739561) (@lem1739565)). Qed.
Lemma lem1739567 : True = term307.
Proof. exact (SYM (@lem1739566)). Qed.
Lemma lem1739568 : term307.
Proof. exact (EQ_MP (@lem1739567) (@lem0)). Qed.
Lemma lem1739569 (x : real) (h1 : term804 x) : term780 x.
Proof. exact (conj (@lem1739568) (@lem1739536 x h1)). Qed.
Lemma lem1739571 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739572 (x : real) : term781 x.
Proof. exact (@lem1739571 term13 (term264 x)). Qed.
Lemma lem1739573 (x : real) (h1 : term804 x) : term782 x.
Proof. exact (@lem1739572 x (@lem1739569 x h1)). Qed.
Lemma lem1739574 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739575 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739576 (x : real) : (term784 x) = (term266 x).
Proof. exact (MK_COMB (@lem1739575) (@lem1739574 x)). Qed.
Lemma lem1739577 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739578 (x : real) : (term782 x) = (term267 x).
Proof. exact (MK_COMB (@lem1739576 x) (@lem1739577)). Qed.
Lemma lem1739579 (x : real) (h1 : term804 x) : term267 x.
Proof. exact (EQ_MP (@lem1739578 x) (@lem1739573 x h1)). Qed.
Lemma lem1739580 (x : real) (h1 : term804 x) : term809 x.
Proof. exact (conj (@lem1739579 x h1) (@lem1739558 x h1)). Qed.
Lemma lem1739582 (x : real) (y : real) : term802 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1739583 (x : real) : term810 x.
Proof. exact (@lem1739582 (term264 x) x). Qed.
Lemma lem1739584 (x : real) (h1 : term804 x) : term758 x.
Proof. exact (@lem1739583 x (@lem1739580 x h1)). Qed.
Lemma lem1739585 (x : real) : (term759 x) = (term760 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1739587 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739588 : term762 = term4.
Proof. exact (@lem1739587 term273). Qed.
Lemma lem1739589 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739590 : term763 = term764.
Proof. exact (MK_COMB (@lem1739589) (@lem1739588)). Qed.
Lemma lem1739591 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739592 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739590) (@lem1739591 x)). Qed.
Lemma lem1739593 (x : real) : (term759 x) = (term765 x).
Proof. exact (TRANS (@lem1739585 x) (@lem1739592 x)). Qed.
Lemma lem1739594 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739595 (x : real) : (term759 x) = term4.
Proof. exact (TRANS (@lem1739593 x) (@lem1739594 x)). Qed.
Lemma lem1739596 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739597 (x : real) : (term766 x) = term767.
Proof. exact (MK_COMB (@lem1739596) (@lem1739595 x)). Qed.
Lemma lem1739598 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739599 (x : real) : (term758 x) = term768.
Proof. exact (MK_COMB (@lem1739597 x) (@lem1739598)). Qed.
Lemma lem1739600 (x : real) (h1 : term804 x) : term768.
Proof. exact (EQ_MP (@lem1739599 x) (@lem1739584 x h1)). Qed.
Lemma lem1739602 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739603 : term768 = term769.
Proof. exact (@lem1739602 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739604 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739605 : term768 = False.
Proof. exact (TRANS (@lem1739603) (@lem1739604)). Qed.
Lemma lem1739606 (x : real) (h1 : term804 x) : False.
Proof. exact (EQ_MP (@lem1739605) (@lem1739600 x h1)). Qed.
Lemma lem1739607 (x : real) (h1 : term673 x) : False.
Proof. exact (or_elim (@lem1739458 x h1) (fun h0 : term796 x => @lem1739532 x h0) (fun h0 : term804 x => @lem1739606 x h0)). Qed.
Lemma lem1739608 (x : real) (h1 : term691 x) : False.
Proof. exact (or_elim (@lem1739340 x h1) (fun h0 : term688 x => @lem1739457 x h0) (fun h0 : term673 x => @lem1739607 x h0)). Qed.
Lemma lem1739609 (x : real) (h1 : term736 x) : False.
Proof. exact (or_elim (@lem1739089 x h1) (fun h0 : term734 x => @lem1739339 x h0) (fun h0 : term691 x => @lem1739608 x h0)). Qed.
Lemma lem1739610 (x : real) (h1 : term649 x) : term649 x.
Proof. exact (h1). Qed.
Lemma lem1739611 (x : real) (h1 : term647 x) : term647 x.
Proof. exact (h1). Qed.
Lemma lem1739612 (x : real) (h1 : term645 x) : term645 x.
Proof. exact (h1). Qed.
Lemma lem1739613 (x : real) (h1 : term811 x) : term811 x.
Proof. exact (h1). Qed.
Lemma lem1739614 (x : real) (h1 : term811 x) : term370 x.
Proof. exact (proj2 (@lem1739613 x h1)). Qed.
Lemma lem1739615 (x : real) (h1 : term811 x) : term267 x.
Proof. exact (proj1 (@lem1739613 x h1)). Qed.
Lemma lem1739617 (x : real) (h1 : term811 x) : term16 x.
Proof. exact (proj1 (@lem1739614 x h1)). Qed.
Lemma lem1739619 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739620 : term307 = term746.
Proof. exact (@lem1739619 (NUMERAL 0) term273). Qed.
Lemma lem1739621 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739622 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739623 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739622 h1) (fun h1 : term746 = True => @lem1739621)). Qed.
Lemma lem1739624 : term746 = True.
Proof. exact (EQ_MP (@lem1739623) (@lem1739621)). Qed.
Lemma lem1739625 : term307 = True.
Proof. exact (TRANS (@lem1739620) (@lem1739624)). Qed.
Lemma lem1739626 : True = term307.
Proof. exact (SYM (@lem1739625)). Qed.
Lemma lem1739627 : term307.
Proof. exact (EQ_MP (@lem1739626) (@lem0)). Qed.
Lemma lem1739628 (x : real) (h1 : term811 x) : term605 x.
Proof. exact (conj (@lem1739627) (@lem1739617 x h1)). Qed.
Lemma lem1739630 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739631 (x : real) : term748 x.
Proof. exact (@lem1739630 term13 x). Qed.
Lemma lem1739632 (x : real) (h1 : term811 x) : term749 x.
Proof. exact (@lem1739631 x (@lem1739628 x h1)). Qed.
Lemma lem1739633 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739634 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739635 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739634) (@lem1739633 x)). Qed.
Lemma lem1739636 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739637 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739635 x) (@lem1739636)). Qed.
Lemma lem1739638 (x : real) (h1 : term811 x) : term16 x.
Proof. exact (EQ_MP (@lem1739637 x) (@lem1739632 x h1)). Qed.
Lemma lem1739640 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739641 : term307 = term746.
Proof. exact (@lem1739640 (NUMERAL 0) term273). Qed.
Lemma lem1739642 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739643 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739644 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739643 h1) (fun h1 : term746 = True => @lem1739642)). Qed.
Lemma lem1739645 : term746 = True.
Proof. exact (EQ_MP (@lem1739644) (@lem1739642)). Qed.
Lemma lem1739646 : term307 = True.
Proof. exact (TRANS (@lem1739641) (@lem1739645)). Qed.
Lemma lem1739647 : True = term307.
Proof. exact (SYM (@lem1739646)). Qed.
Lemma lem1739648 : term307.
Proof. exact (EQ_MP (@lem1739647) (@lem0)). Qed.
Lemma lem1739649 (x : real) (h1 : term811 x) : term780 x.
Proof. exact (conj (@lem1739648) (@lem1739615 x h1)). Qed.
Lemma lem1739651 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739652 (x : real) : term781 x.
Proof. exact (@lem1739651 term13 (term264 x)). Qed.
Lemma lem1739653 (x : real) (h1 : term811 x) : term782 x.
Proof. exact (@lem1739652 x (@lem1739649 x h1)). Qed.
Lemma lem1739654 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739655 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739656 (x : real) : (term784 x) = (term266 x).
Proof. exact (MK_COMB (@lem1739655) (@lem1739654 x)). Qed.
Lemma lem1739657 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739658 (x : real) : (term782 x) = (term267 x).
Proof. exact (MK_COMB (@lem1739656 x) (@lem1739657)). Qed.
Lemma lem1739659 (x : real) (h1 : term811 x) : term267 x.
Proof. exact (EQ_MP (@lem1739658 x) (@lem1739653 x h1)). Qed.
Lemma lem1739660 (x : real) (h1 : term811 x) : term812 x.
Proof. exact (conj (@lem1739659 x h1) (@lem1739638 x h1)). Qed.
Lemma lem1739662 (x : real) (y : real) : term813 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1739663 (x : real) : term814 x.
Proof. exact (@lem1739662 (term264 x) x). Qed.
Lemma lem1739664 (x : real) (h1 : term811 x) : term758 x.
Proof. exact (@lem1739663 x (@lem1739660 x h1)). Qed.
Lemma lem1739665 (x : real) : (term759 x) = (term760 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1739667 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739668 : term762 = term4.
Proof. exact (@lem1739667 term273). Qed.
Lemma lem1739669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739670 : term763 = term764.
Proof. exact (MK_COMB (@lem1739669) (@lem1739668)). Qed.
Lemma lem1739671 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739672 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739670) (@lem1739671 x)). Qed.
Lemma lem1739673 (x : real) : (term759 x) = (term765 x).
Proof. exact (TRANS (@lem1739665 x) (@lem1739672 x)). Qed.
Lemma lem1739674 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739675 (x : real) : (term759 x) = term4.
Proof. exact (TRANS (@lem1739673 x) (@lem1739674 x)). Qed.
Lemma lem1739676 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739677 (x : real) : (term766 x) = term767.
Proof. exact (MK_COMB (@lem1739676) (@lem1739675 x)). Qed.
Lemma lem1739678 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739679 (x : real) : (term758 x) = term768.
Proof. exact (MK_COMB (@lem1739677 x) (@lem1739678)). Qed.
Lemma lem1739680 (x : real) (h1 : term811 x) : term768.
Proof. exact (EQ_MP (@lem1739679 x) (@lem1739664 x h1)). Qed.
Lemma lem1739682 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739683 : term768 = term769.
Proof. exact (@lem1739682 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739684 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739685 : term768 = False.
Proof. exact (TRANS (@lem1739683) (@lem1739684)). Qed.
Lemma lem1739686 (x : real) (h1 : term811 x) : False.
Proof. exact (EQ_MP (@lem1739685) (@lem1739680 x h1)). Qed.
Lemma lem1739687 (x : real) (h1 : term643 x) : term643 x.
Proof. exact (h1). Qed.
Lemma lem1739688 (x : real) (h1 : term815 x) : term815 x.
Proof. exact (h1). Qed.
Lemma lem1739689 (x : real) (h1 : term815 x) : term637 x.
Proof. exact (proj2 (@lem1739688 x h1)). Qed.
Lemma lem1739691 (x : real) (h1 : term815 x) : term385 x.
Proof. exact (proj2 (@lem1739689 x h1)). Qed.
Lemma lem1739694 (x : real) (h1 : term815 x) : term381 = term4.
Proof. exact (proj1 (@lem1739691 x h1)). Qed.
Lemma lem1739696 (m : nat) (n : nat) : ((term773 m) = (real_of_num n)) = (term774 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem1739697 : (term381 = term4) = term816.
Proof. exact (@lem1739696 term378 (NUMERAL 0)). Qed.
Lemma lem1739698 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1739699 : term817 = term376.
Proof. exact (@lem912803). Qed.
Lemma lem1739700 (h1 : term817 = term376) : (term378 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term376 h1). Qed.
Lemma lem1739701 : (term817 = term376) = ((term378 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term817 = term376 => @lem1739700 h1) (fun h1 : (term378 = (NUMERAL 0)) = False => @lem1739699)). Qed.
Lemma lem1739702 : (term378 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739701) (@lem1739699)). Qed.
Lemma lem1739703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1739704 : term818 = (and False).
Proof. exact (MK_COMB (@lem1739703) (@lem1739702)). Qed.
Lemma lem1739705 : term816 = (False /\ True).
Proof. exact (MK_COMB (@lem1739704) (@lem1739698)). Qed.
Lemma lem1739707 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1739708 : term816 = False.
Proof. exact (TRANS (@lem1739705) (@lem1739707)). Qed.
Lemma lem1739709 : (term381 = term4) = False.
Proof. exact (TRANS (@lem1739697) (@lem1739708)). Qed.
Lemma lem1739710 (x : real) (h1 : term815 x) : False.
Proof. exact (EQ_MP (@lem1739709) (@lem1739694 x h1)). Qed.
Lemma lem1739711 (x : real) (h1 : term639 x) : term639 x.
Proof. exact (h1). Qed.
Lemma lem1739712 (x : real) (h1 : term819 x) : term819 x.
Proof. exact (h1). Qed.
Lemma lem1739713 (x : real) (h1 : term819 x) : term640 x.
Proof. exact (proj2 (@lem1739712 x h1)). Qed.
Lemma lem1739715 (x : real) (h1 : term819 x) : term628 x.
Proof. exact (proj2 (@lem1739713 x h1)). Qed.
Lemma lem1739718 (x : real) (h1 : term819 x) : term401.
Proof. exact (proj1 (@lem1739715 x h1)). Qed.
Lemma lem1739720 (m : nat) (n : nat) : (term771 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1739721 : term401 = False.
Proof. exact (@lem1739720 term378 (NUMERAL 0)). Qed.
Lemma lem1739722 (x : real) (h1 : term819 x) : False.
Proof. exact (EQ_MP (@lem1739721) (@lem1739718 x h1)). Qed.
Lemma lem1739723 (x : real) (h1 : term820 x) : term820 x.
Proof. exact (h1). Qed.
Lemma lem1739724 (x : real) (h1 : term820 x) : term641 x.
Proof. exact (proj2 (@lem1739723 x h1)). Qed.
Lemma lem1739725 (x : real) (h1 : term820 x) : term267 x.
Proof. exact (proj1 (@lem1739723 x h1)). Qed.
Lemma lem1739726 (x : real) (h1 : term820 x) : term629 x.
Proof. exact (proj2 (@lem1739724 x h1)). Qed.
Lemma lem1739728 (x : real) (h1 : term820 x) : term16 x.
Proof. exact (proj2 (@lem1739726 x h1)). Qed.
Lemma lem1739731 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739732 : term307 = term746.
Proof. exact (@lem1739731 (NUMERAL 0) term273). Qed.
Lemma lem1739733 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739734 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739735 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739734 h1) (fun h1 : term746 = True => @lem1739733)). Qed.
Lemma lem1739736 : term746 = True.
Proof. exact (EQ_MP (@lem1739735) (@lem1739733)). Qed.
Lemma lem1739737 : term307 = True.
Proof. exact (TRANS (@lem1739732) (@lem1739736)). Qed.
Lemma lem1739738 : True = term307.
Proof. exact (SYM (@lem1739737)). Qed.
Lemma lem1739739 : term307.
Proof. exact (EQ_MP (@lem1739738) (@lem0)). Qed.
Lemma lem1739740 (x : real) (h1 : term820 x) : term605 x.
Proof. exact (conj (@lem1739739) (@lem1739728 x h1)). Qed.
Lemma lem1739742 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739743 (x : real) : term748 x.
Proof. exact (@lem1739742 term13 x). Qed.
Lemma lem1739744 (x : real) (h1 : term820 x) : term749 x.
Proof. exact (@lem1739743 x (@lem1739740 x h1)). Qed.
Lemma lem1739745 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739746 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739747 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739746) (@lem1739745 x)). Qed.
Lemma lem1739748 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739749 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739747 x) (@lem1739748)). Qed.
Lemma lem1739750 (x : real) (h1 : term820 x) : term16 x.
Proof. exact (EQ_MP (@lem1739749 x) (@lem1739744 x h1)). Qed.
Lemma lem1739752 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739753 : term307 = term746.
Proof. exact (@lem1739752 (NUMERAL 0) term273). Qed.
Lemma lem1739754 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739755 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739756 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739755 h1) (fun h1 : term746 = True => @lem1739754)). Qed.
Lemma lem1739757 : term746 = True.
Proof. exact (EQ_MP (@lem1739756) (@lem1739754)). Qed.
Lemma lem1739758 : term307 = True.
Proof. exact (TRANS (@lem1739753) (@lem1739757)). Qed.
Lemma lem1739759 : True = term307.
Proof. exact (SYM (@lem1739758)). Qed.
Lemma lem1739760 : term307.
Proof. exact (EQ_MP (@lem1739759) (@lem0)). Qed.
Lemma lem1739761 (x : real) (h1 : term820 x) : term780 x.
Proof. exact (conj (@lem1739760) (@lem1739725 x h1)). Qed.
Lemma lem1739763 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739764 (x : real) : term781 x.
Proof. exact (@lem1739763 term13 (term264 x)). Qed.
Lemma lem1739765 (x : real) (h1 : term820 x) : term782 x.
Proof. exact (@lem1739764 x (@lem1739761 x h1)). Qed.
Lemma lem1739766 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739767 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739768 (x : real) : (term784 x) = (term266 x).
Proof. exact (MK_COMB (@lem1739767) (@lem1739766 x)). Qed.
Lemma lem1739769 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739770 (x : real) : (term782 x) = (term267 x).
Proof. exact (MK_COMB (@lem1739768 x) (@lem1739769)). Qed.
Lemma lem1739771 (x : real) (h1 : term820 x) : term267 x.
Proof. exact (EQ_MP (@lem1739770 x) (@lem1739765 x h1)). Qed.
Lemma lem1739772 (x : real) (h1 : term820 x) : term812 x.
Proof. exact (conj (@lem1739771 x h1) (@lem1739750 x h1)). Qed.
Lemma lem1739774 (x : real) (y : real) : term813 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1739775 (x : real) : term814 x.
Proof. exact (@lem1739774 (term264 x) x). Qed.
Lemma lem1739776 (x : real) (h1 : term820 x) : term758 x.
Proof. exact (@lem1739775 x (@lem1739772 x h1)). Qed.
Lemma lem1739777 (x : real) : (term759 x) = (term760 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1739779 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739780 : term762 = term4.
Proof. exact (@lem1739779 term273). Qed.
Lemma lem1739781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739782 : term763 = term764.
Proof. exact (MK_COMB (@lem1739781) (@lem1739780)). Qed.
Lemma lem1739783 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739784 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739782) (@lem1739783 x)). Qed.
Lemma lem1739785 (x : real) : (term759 x) = (term765 x).
Proof. exact (TRANS (@lem1739777 x) (@lem1739784 x)). Qed.
Lemma lem1739786 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739787 (x : real) : (term759 x) = term4.
Proof. exact (TRANS (@lem1739785 x) (@lem1739786 x)). Qed.
Lemma lem1739788 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739789 (x : real) : (term766 x) = term767.
Proof. exact (MK_COMB (@lem1739788) (@lem1739787 x)). Qed.
Lemma lem1739790 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739791 (x : real) : (term758 x) = term768.
Proof. exact (MK_COMB (@lem1739789 x) (@lem1739790)). Qed.
Lemma lem1739792 (x : real) (h1 : term820 x) : term768.
Proof. exact (EQ_MP (@lem1739791 x) (@lem1739776 x h1)). Qed.
Lemma lem1739794 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739795 : term768 = term769.
Proof. exact (@lem1739794 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739796 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739797 : term768 = False.
Proof. exact (TRANS (@lem1739795) (@lem1739796)). Qed.
Lemma lem1739798 (x : real) (h1 : term820 x) : False.
Proof. exact (EQ_MP (@lem1739797) (@lem1739792 x h1)). Qed.
Lemma lem1739799 (x : real) (h1 : term639 x) : False.
Proof. exact (or_elim (@lem1739711 x h1) (fun h0 : term819 x => @lem1739722 x h0) (fun h0 : term820 x => @lem1739798 x h0)). Qed.
Lemma lem1739800 (x : real) (h1 : term643 x) : False.
Proof. exact (or_elim (@lem1739687 x h1) (fun h0 : term815 x => @lem1739710 x h0) (fun h0 : term639 x => @lem1739799 x h0)). Qed.
Lemma lem1739801 (x : real) (h1 : term645 x) : False.
Proof. exact (or_elim (@lem1739612 x h1) (fun h0 : term811 x => @lem1739686 x h0) (fun h0 : term643 x => @lem1739800 x h0)). Qed.
Lemma lem1739802 (x : real) (h1 : term621 x) : term621 x.
Proof. exact (h1). Qed.
Lemma lem1739803 (x : real) (h1 : term821 x) : term821 x.
Proof. exact (h1). Qed.
Lemma lem1739804 (x : real) (h1 : term821 x) : term370 x.
Proof. exact (proj2 (@lem1739803 x h1)). Qed.
Lemma lem1739806 (x : real) (h1 : term821 x) : term322 x.
Proof. exact (proj2 (@lem1739804 x h1)). Qed.
Lemma lem1739807 (x : real) (h1 : term821 x) : term16 x.
Proof. exact (proj1 (@lem1739804 x h1)). Qed.
Lemma lem1739809 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739810 : term307 = term746.
Proof. exact (@lem1739809 (NUMERAL 0) term273). Qed.
Lemma lem1739811 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739812 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739813 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739812 h1) (fun h1 : term746 = True => @lem1739811)). Qed.
Lemma lem1739814 : term746 = True.
Proof. exact (EQ_MP (@lem1739813) (@lem1739811)). Qed.
Lemma lem1739815 : term307 = True.
Proof. exact (TRANS (@lem1739810) (@lem1739814)). Qed.
Lemma lem1739816 : True = term307.
Proof. exact (SYM (@lem1739815)). Qed.
Lemma lem1739817 : term307.
Proof. exact (EQ_MP (@lem1739816) (@lem0)). Qed.
Lemma lem1739818 (x : real) (h1 : term821 x) : term797 x.
Proof. exact (conj (@lem1739817) (@lem1739806 x h1)). Qed.
Lemma lem1739820 (x : real) (y : real) : term798 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1739821 (x : real) : term799 x.
Proof. exact (@lem1739820 term13 (term264 x)). Qed.
Lemma lem1739822 (x : real) (h1 : term821 x) : term800 x.
Proof. exact (@lem1739821 x (@lem1739818 x h1)). Qed.
Lemma lem1739823 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739824 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1739825 (x : real) : (term801 x) = (term321 x).
Proof. exact (MK_COMB (@lem1739824) (@lem1739823 x)). Qed.
Lemma lem1739826 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739827 (x : real) : (term800 x) = (term322 x).
Proof. exact (MK_COMB (@lem1739825 x) (@lem1739826)). Qed.
Lemma lem1739828 (x : real) (h1 : term821 x) : term322 x.
Proof. exact (EQ_MP (@lem1739827 x) (@lem1739822 x h1)). Qed.
Lemma lem1739830 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739831 : term307 = term746.
Proof. exact (@lem1739830 (NUMERAL 0) term273). Qed.
Lemma lem1739832 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739833 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739834 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739833 h1) (fun h1 : term746 = True => @lem1739832)). Qed.
Lemma lem1739835 : term746 = True.
Proof. exact (EQ_MP (@lem1739834) (@lem1739832)). Qed.
Lemma lem1739836 : term307 = True.
Proof. exact (TRANS (@lem1739831) (@lem1739835)). Qed.
Lemma lem1739837 : True = term307.
Proof. exact (SYM (@lem1739836)). Qed.
Lemma lem1739838 : term307.
Proof. exact (EQ_MP (@lem1739837) (@lem0)). Qed.
Lemma lem1739839 (x : real) (h1 : term821 x) : term605 x.
Proof. exact (conj (@lem1739838) (@lem1739807 x h1)). Qed.
Lemma lem1739841 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739842 (x : real) : term748 x.
Proof. exact (@lem1739841 term13 x). Qed.
Lemma lem1739843 (x : real) (h1 : term821 x) : term749 x.
Proof. exact (@lem1739842 x (@lem1739839 x h1)). Qed.
Lemma lem1739844 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739845 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739846 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739845) (@lem1739844 x)). Qed.
Lemma lem1739847 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739848 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739846 x) (@lem1739847)). Qed.
Lemma lem1739849 (x : real) (h1 : term821 x) : term16 x.
Proof. exact (EQ_MP (@lem1739848 x) (@lem1739843 x h1)). Qed.
Lemma lem1739850 (x : real) (h1 : term821 x) : term370 x.
Proof. exact (conj (@lem1739849 x h1) (@lem1739828 x h1)). Qed.
Lemma lem1739852 (x : real) (y : real) : term802 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1739853 (x : real) : term803 x.
Proof. exact (@lem1739852 x (term264 x)). Qed.
Lemma lem1739854 (x : real) (h1 : term821 x) : term789 x.
Proof. exact (@lem1739853 x (@lem1739850 x h1)). Qed.
Lemma lem1739855 (x : real) : (term790 x) = (term760 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1739857 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739858 : term762 = term4.
Proof. exact (@lem1739857 term273). Qed.
Lemma lem1739859 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739860 : term763 = term764.
Proof. exact (MK_COMB (@lem1739859) (@lem1739858)). Qed.
Lemma lem1739861 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739862 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739860) (@lem1739861 x)). Qed.
Lemma lem1739863 (x : real) : (term790 x) = (term765 x).
Proof. exact (TRANS (@lem1739855 x) (@lem1739862 x)). Qed.
Lemma lem1739864 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739865 (x : real) : (term790 x) = term4.
Proof. exact (TRANS (@lem1739863 x) (@lem1739864 x)). Qed.
Lemma lem1739866 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739867 (x : real) : (term791 x) = term767.
Proof. exact (MK_COMB (@lem1739866) (@lem1739865 x)). Qed.
Lemma lem1739868 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739869 (x : real) : (term789 x) = term768.
Proof. exact (MK_COMB (@lem1739867 x) (@lem1739868)). Qed.
Lemma lem1739870 (x : real) (h1 : term821 x) : term768.
Proof. exact (EQ_MP (@lem1739869 x) (@lem1739854 x h1)). Qed.
Lemma lem1739872 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739873 : term768 = term769.
Proof. exact (@lem1739872 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739874 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739875 : term768 = False.
Proof. exact (TRANS (@lem1739873) (@lem1739874)). Qed.
Lemma lem1739876 (x : real) (h1 : term821 x) : False.
Proof. exact (EQ_MP (@lem1739875) (@lem1739870 x h1)). Qed.
Lemma lem1739877 (x : real) (h1 : term619 x) : term619 x.
Proof. exact (h1). Qed.
Lemma lem1739878 (x : real) (h1 : term822 x) : term822 x.
Proof. exact (h1). Qed.
Lemma lem1739879 (x : real) (h1 : term822 x) : term613 x.
Proof. exact (proj2 (@lem1739878 x h1)). Qed.
Lemma lem1739881 (x : real) (h1 : term822 x) : term419 x.
Proof. exact (proj2 (@lem1739879 x h1)). Qed.
Lemma lem1739884 (x : real) (h1 : term822 x) : term23 = term4.
Proof. exact (proj1 (@lem1739881 x h1)). Qed.
Lemma lem1739886 (m : nat) (n : nat) : ((term773 m) = (real_of_num n)) = (term774 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem1739887 : (term23 = term4) = term775.
Proof. exact (@lem1739886 term273 (NUMERAL 0)). Qed.
Lemma lem1739888 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1739889 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739890 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1739891 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739890 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1739889)). Qed.
Lemma lem1739892 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1739891) (@lem1739889)). Qed.
Lemma lem1739893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1739894 : term776 = (and False).
Proof. exact (MK_COMB (@lem1739893) (@lem1739892)). Qed.
Lemma lem1739895 : term775 = (False /\ True).
Proof. exact (MK_COMB (@lem1739894) (@lem1739888)). Qed.
Lemma lem1739897 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1739898 : term775 = False.
Proof. exact (TRANS (@lem1739895) (@lem1739897)). Qed.
Lemma lem1739899 : (term23 = term4) = False.
Proof. exact (TRANS (@lem1739887) (@lem1739898)). Qed.
Lemma lem1739900 (x : real) (h1 : term822 x) : False.
Proof. exact (EQ_MP (@lem1739899) (@lem1739884 x h1)). Qed.
Lemma lem1739901 (x : real) (h1 : term615 x) : term615 x.
Proof. exact (h1). Qed.
Lemma lem1739902 (x : real) (h1 : term823 x) : term823 x.
Proof. exact (h1). Qed.
Lemma lem1739903 (x : real) (h1 : term823 x) : term616 x.
Proof. exact (proj2 (@lem1739902 x h1)). Qed.
Lemma lem1739905 (x : real) (h1 : term823 x) : term604 x.
Proof. exact (proj2 (@lem1739903 x h1)). Qed.
Lemma lem1739908 (x : real) (h1 : term823 x) : term303.
Proof. exact (proj1 (@lem1739905 x h1)). Qed.
Lemma lem1739910 (m : nat) (n : nat) : (term771 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1739911 : term303 = False.
Proof. exact (@lem1739910 term273 (NUMERAL 0)). Qed.
Lemma lem1739912 (x : real) (h1 : term823 x) : False.
Proof. exact (EQ_MP (@lem1739911) (@lem1739908 x h1)). Qed.
Lemma lem1739913 (x : real) (h1 : term824 x) : term824 x.
Proof. exact (h1). Qed.
Lemma lem1739914 (x : real) (h1 : term824 x) : term617 x.
Proof. exact (proj2 (@lem1739913 x h1)). Qed.
Lemma lem1739916 (x : real) (h1 : term824 x) : term605 x.
Proof. exact (proj2 (@lem1739914 x h1)). Qed.
Lemma lem1739917 (x : real) (h1 : term824 x) : term322 x.
Proof. exact (proj1 (@lem1739914 x h1)). Qed.
Lemma lem1739918 (x : real) (h1 : term824 x) : term16 x.
Proof. exact (proj2 (@lem1739916 x h1)). Qed.
Lemma lem1739921 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739922 : term307 = term746.
Proof. exact (@lem1739921 (NUMERAL 0) term273). Qed.
Lemma lem1739923 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739924 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739925 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739924 h1) (fun h1 : term746 = True => @lem1739923)). Qed.
Lemma lem1739926 : term746 = True.
Proof. exact (EQ_MP (@lem1739925) (@lem1739923)). Qed.
Lemma lem1739927 : term307 = True.
Proof. exact (TRANS (@lem1739922) (@lem1739926)). Qed.
Lemma lem1739928 : True = term307.
Proof. exact (SYM (@lem1739927)). Qed.
Lemma lem1739929 : term307.
Proof. exact (EQ_MP (@lem1739928) (@lem0)). Qed.
Lemma lem1739930 (x : real) (h1 : term824 x) : term797 x.
Proof. exact (conj (@lem1739929) (@lem1739917 x h1)). Qed.
Lemma lem1739932 (x : real) (y : real) : term798 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1739933 (x : real) : term799 x.
Proof. exact (@lem1739932 term13 (term264 x)). Qed.
Lemma lem1739934 (x : real) (h1 : term824 x) : term800 x.
Proof. exact (@lem1739933 x (@lem1739930 x h1)). Qed.
Lemma lem1739935 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1739936 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1739937 (x : real) : (term801 x) = (term321 x).
Proof. exact (MK_COMB (@lem1739936) (@lem1739935 x)). Qed.
Lemma lem1739938 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739939 (x : real) : (term800 x) = (term322 x).
Proof. exact (MK_COMB (@lem1739937 x) (@lem1739938)). Qed.
Lemma lem1739940 (x : real) (h1 : term824 x) : term322 x.
Proof. exact (EQ_MP (@lem1739939 x) (@lem1739934 x h1)). Qed.
Lemma lem1739942 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739943 : term307 = term746.
Proof. exact (@lem1739942 (NUMERAL 0) term273). Qed.
Lemma lem1739944 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1739945 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1739946 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1739945 h1) (fun h1 : term746 = True => @lem1739944)). Qed.
Lemma lem1739947 : term746 = True.
Proof. exact (EQ_MP (@lem1739946) (@lem1739944)). Qed.
Lemma lem1739948 : term307 = True.
Proof. exact (TRANS (@lem1739943) (@lem1739947)). Qed.
Lemma lem1739949 : True = term307.
Proof. exact (SYM (@lem1739948)). Qed.
Lemma lem1739950 : term307.
Proof. exact (EQ_MP (@lem1739949) (@lem0)). Qed.
Lemma lem1739951 (x : real) (h1 : term824 x) : term605 x.
Proof. exact (conj (@lem1739950) (@lem1739918 x h1)). Qed.
Lemma lem1739953 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1739954 (x : real) : term748 x.
Proof. exact (@lem1739953 term13 x). Qed.
Lemma lem1739955 (x : real) (h1 : term824 x) : term749 x.
Proof. exact (@lem1739954 x (@lem1739951 x h1)). Qed.
Lemma lem1739956 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1739957 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739958 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1739957) (@lem1739956 x)). Qed.
Lemma lem1739959 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739960 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1739958 x) (@lem1739959)). Qed.
Lemma lem1739961 (x : real) (h1 : term824 x) : term16 x.
Proof. exact (EQ_MP (@lem1739960 x) (@lem1739955 x h1)). Qed.
Lemma lem1739962 (x : real) (h1 : term824 x) : term370 x.
Proof. exact (conj (@lem1739961 x h1) (@lem1739940 x h1)). Qed.
Lemma lem1739964 (x : real) (y : real) : term802 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1739965 (x : real) : term803 x.
Proof. exact (@lem1739964 x (term264 x)). Qed.
Lemma lem1739966 (x : real) (h1 : term824 x) : term789 x.
Proof. exact (@lem1739965 x (@lem1739962 x h1)). Qed.
Lemma lem1739967 (x : real) : (term790 x) = (term760 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1739969 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1739970 : term762 = term4.
Proof. exact (@lem1739969 term273). Qed.
Lemma lem1739971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1739972 : term763 = term764.
Proof. exact (MK_COMB (@lem1739971) (@lem1739970)). Qed.
Lemma lem1739973 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1739974 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1739972) (@lem1739973 x)). Qed.
Lemma lem1739975 (x : real) : (term790 x) = (term765 x).
Proof. exact (TRANS (@lem1739967 x) (@lem1739974 x)). Qed.
Lemma lem1739976 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1739977 (x : real) : (term790 x) = term4.
Proof. exact (TRANS (@lem1739975 x) (@lem1739976 x)). Qed.
Lemma lem1739978 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1739979 (x : real) : (term791 x) = term767.
Proof. exact (MK_COMB (@lem1739978) (@lem1739977 x)). Qed.
Lemma lem1739980 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1739981 (x : real) : (term789 x) = term768.
Proof. exact (MK_COMB (@lem1739979 x) (@lem1739980)). Qed.
Lemma lem1739982 (x : real) (h1 : term824 x) : term768.
Proof. exact (EQ_MP (@lem1739981 x) (@lem1739966 x h1)). Qed.
Lemma lem1739984 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1739985 : term768 = term769.
Proof. exact (@lem1739984 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1739986 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1739987 : term768 = False.
Proof. exact (TRANS (@lem1739985) (@lem1739986)). Qed.
Lemma lem1739988 (x : real) (h1 : term824 x) : False.
Proof. exact (EQ_MP (@lem1739987) (@lem1739982 x h1)). Qed.
Lemma lem1739989 (x : real) (h1 : term615 x) : False.
Proof. exact (or_elim (@lem1739901 x h1) (fun h0 : term823 x => @lem1739912 x h0) (fun h0 : term824 x => @lem1739988 x h0)). Qed.
Lemma lem1739990 (x : real) (h1 : term619 x) : False.
Proof. exact (or_elim (@lem1739877 x h1) (fun h0 : term822 x => @lem1739900 x h0) (fun h0 : term615 x => @lem1739989 x h0)). Qed.
Lemma lem1739991 (x : real) (h1 : term621 x) : False.
Proof. exact (or_elim (@lem1739802 x h1) (fun h0 : term821 x => @lem1739876 x h0) (fun h0 : term619 x => @lem1739990 x h0)). Qed.
Lemma lem1739992 (x : real) (h1 : term647 x) : False.
Proof. exact (or_elim (@lem1739611 x h1) (fun h0 : term645 x => @lem1739801 x h0) (fun h0 : term621 x => @lem1739991 x h0)). Qed.
Lemma lem1739993 (x : real) (h1 : term597 x) : term597 x.
Proof. exact (h1). Qed.
Lemma lem1739994 (x : real) (h1 : term593 x) : term593 x.
Proof. exact (h1). Qed.
Lemma lem1739995 (x : real) (h1 : term825 x) : term825 x.
Proof. exact (h1). Qed.
Lemma lem1739996 (x : real) (h1 : term825 x) : term594 x.
Proof. exact (proj2 (@lem1739995 x h1)). Qed.
Lemma lem1739997 (x : real) (h1 : term825 x) : term267 x.
Proof. exact (proj1 (@lem1739995 x h1)). Qed.
Lemma lem1739999 (x : real) (h1 : term825 x) : term16 x.
Proof. exact (proj1 (@lem1739996 x h1)). Qed.
Lemma lem1740001 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1740002 : term307 = term746.
Proof. exact (@lem1740001 (NUMERAL 0) term273). Qed.
Lemma lem1740003 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1740004 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1740005 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1740004 h1) (fun h1 : term746 = True => @lem1740003)). Qed.
Lemma lem1740006 : term746 = True.
Proof. exact (EQ_MP (@lem1740005) (@lem1740003)). Qed.
Lemma lem1740007 : term307 = True.
Proof. exact (TRANS (@lem1740002) (@lem1740006)). Qed.
Lemma lem1740008 : True = term307.
Proof. exact (SYM (@lem1740007)). Qed.
Lemma lem1740009 : term307.
Proof. exact (EQ_MP (@lem1740008) (@lem0)). Qed.
Lemma lem1740010 (x : real) (h1 : term825 x) : term605 x.
Proof. exact (conj (@lem1740009) (@lem1739999 x h1)). Qed.
Lemma lem1740012 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1740013 (x : real) : term748 x.
Proof. exact (@lem1740012 term13 x). Qed.
Lemma lem1740014 (x : real) (h1 : term825 x) : term749 x.
Proof. exact (@lem1740013 x (@lem1740010 x h1)). Qed.
Lemma lem1740015 (x : real) : (term750 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1740016 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1740017 (x : real) : (term751 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1740016) (@lem1740015 x)). Qed.
Lemma lem1740018 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740019 (x : real) : (term749 x) = (term16 x).
Proof. exact (MK_COMB (@lem1740017 x) (@lem1740018)). Qed.
Lemma lem1740020 (x : real) (h1 : term825 x) : term16 x.
Proof. exact (EQ_MP (@lem1740019 x) (@lem1740014 x h1)). Qed.
Lemma lem1740022 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1740023 : term307 = term746.
Proof. exact (@lem1740022 (NUMERAL 0) term273). Qed.
Lemma lem1740024 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1740025 (h1 : term742 = (BIT1 0)) : term746 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1740026 : (term742 = (BIT1 0)) = (term746 = True).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1740025 h1) (fun h1 : term746 = True => @lem1740024)). Qed.
Lemma lem1740027 : term746 = True.
Proof. exact (EQ_MP (@lem1740026) (@lem1740024)). Qed.
Lemma lem1740028 : term307 = True.
Proof. exact (TRANS (@lem1740023) (@lem1740027)). Qed.
Lemma lem1740029 : True = term307.
Proof. exact (SYM (@lem1740028)). Qed.
Lemma lem1740030 : term307.
Proof. exact (EQ_MP (@lem1740029) (@lem0)). Qed.
Lemma lem1740031 (x : real) (h1 : term825 x) : term780 x.
Proof. exact (conj (@lem1740030) (@lem1739997 x h1)). Qed.
Lemma lem1740033 (x : real) (y : real) : term747 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1740034 (x : real) : term781 x.
Proof. exact (@lem1740033 term13 (term264 x)). Qed.
Lemma lem1740035 (x : real) (h1 : term825 x) : term782 x.
Proof. exact (@lem1740034 x (@lem1740031 x h1)). Qed.
Lemma lem1740036 (x : real) : (term783 x) = (term264 x).
Proof. exact (@lem1483460 (term264 x)). Qed.
Lemma lem1740037 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1740038 (x : real) : (term784 x) = (term266 x).
Proof. exact (MK_COMB (@lem1740037) (@lem1740036 x)). Qed.
Lemma lem1740039 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740040 (x : real) : (term782 x) = (term267 x).
Proof. exact (MK_COMB (@lem1740038 x) (@lem1740039)). Qed.
Lemma lem1740041 (x : real) (h1 : term825 x) : term267 x.
Proof. exact (EQ_MP (@lem1740040 x) (@lem1740035 x h1)). Qed.
Lemma lem1740042 (x : real) (h1 : term825 x) : term812 x.
Proof. exact (conj (@lem1740041 x h1) (@lem1740020 x h1)). Qed.
Lemma lem1740044 (x : real) (y : real) : term813 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1740045 (x : real) : term814 x.
Proof. exact (@lem1740044 (term264 x) x). Qed.
Lemma lem1740046 (x : real) (h1 : term825 x) : term758 x.
Proof. exact (@lem1740045 x (@lem1740042 x h1)). Qed.
Lemma lem1740047 (x : real) : (term759 x) = (term760 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1740049 (m : nat) : (term761 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1740050 : term762 = term4.
Proof. exact (@lem1740049 term273). Qed.
Lemma lem1740051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1740052 : term763 = term764.
Proof. exact (MK_COMB (@lem1740051) (@lem1740050)). Qed.
Lemma lem1740053 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1740054 (x : real) : (term760 x) = (term765 x).
Proof. exact (MK_COMB (@lem1740052) (@lem1740053 x)). Qed.
Lemma lem1740055 (x : real) : (term759 x) = (term765 x).
Proof. exact (TRANS (@lem1740047 x) (@lem1740054 x)). Qed.
Lemma lem1740056 (x : real) : (term765 x) = term4.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1740057 (x : real) : (term759 x) = term4.
Proof. exact (TRANS (@lem1740055 x) (@lem1740056 x)). Qed.
Lemma lem1740058 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1740059 (x : real) : (term766 x) = term767.
Proof. exact (MK_COMB (@lem1740058) (@lem1740057 x)). Qed.
Lemma lem1740060 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1740061 (x : real) : (term758 x) = term768.
Proof. exact (MK_COMB (@lem1740059 x) (@lem1740060)). Qed.
Lemma lem1740062 (x : real) (h1 : term825 x) : term768.
Proof. exact (EQ_MP (@lem1740061 x) (@lem1740046 x h1)). Qed.
Lemma lem1740064 (n : nat) (m : nat) : (term745 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1740065 : term768 = term769.
Proof. exact (@lem1740064 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1740066 : term769 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1740067 : term768 = False.
Proof. exact (TRANS (@lem1740065) (@lem1740066)). Qed.
Lemma lem1740068 (x : real) (h1 : term825 x) : False.
Proof. exact (EQ_MP (@lem1740067) (@lem1740062 x h1)). Qed.
Lemma lem1740069 (x : real) (h1 : term826 x) : term826 x.
Proof. exact (h1). Qed.
Lemma lem1740070 (x : real) (h1 : term826 x) : term595 x.
Proof. exact (proj2 (@lem1740069 x h1)). Qed.
Lemma lem1740072 (x : real) (h1 : term826 x) : term401.
Proof. exact (proj2 (@lem1740070 x h1)). Qed.
Lemma lem1740075 (m : nat) (n : nat) : (term771 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1740076 : term401 = False.
Proof. exact (@lem1740075 term378 (NUMERAL 0)). Qed.
Lemma lem1740077 (x : real) (h1 : term826 x) : False.
Proof. exact (EQ_MP (@lem1740076) (@lem1740072 x h1)). Qed.
Lemma lem1740078 (x : real) (h1 : term593 x) : False.
Proof. exact (or_elim (@lem1739994 x h1) (fun h0 : term825 x => @lem1740068 x h0) (fun h0 : term826 x => @lem1740077 x h0)). Qed.
Lemma lem1740079 (x : real) (h1 : term590 x) : term590 x.
Proof. exact (h1). Qed.
Lemma lem1740080 (x : real) (h1 : term827 x) : term827 x.
Proof. exact (h1). Qed.
Lemma lem1740081 (x : real) (h1 : term827 x) : term460 x.
Proof. exact (proj2 (@lem1740080 x h1)). Qed.
Lemma lem1740083 (x : real) (h1 : term827 x) : term380 = term4.
Proof. exact (proj2 (@lem1740081 x h1)). Qed.
Lemma lem1740086 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1740087 : (term380 = term4) = (term378 = (NUMERAL 0)).
Proof. exact (@lem1740086 term378 (NUMERAL 0)). Qed.
Lemma lem1740088 : term817 = term376.
Proof. exact (@lem912803). Qed.
Lemma lem1740089 (h1 : term817 = term376) : (term378 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term376 h1). Qed.
Lemma lem1740090 : (term817 = term376) = ((term378 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term817 = term376 => @lem1740089 h1) (fun h1 : (term378 = (NUMERAL 0)) = False => @lem1740088)). Qed.
Lemma lem1740091 : (term378 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1740090) (@lem1740088)). Qed.
Lemma lem1740092 : (term380 = term4) = False.
Proof. exact (TRANS (@lem1740087) (@lem1740091)). Qed.
Lemma lem1740093 (x : real) (h1 : term827 x) : False.
Proof. exact (EQ_MP (@lem1740092) (@lem1740083 x h1)). Qed.
Lemma lem1740094 (x : real) (h1 : term828 x) : term828 x.
Proof. exact (h1). Qed.
Lemma lem1740095 (x : real) (h1 : term828 x) : term465 x.
Proof. exact (proj2 (@lem1740094 x h1)). Qed.
Lemma lem1740097 (x : real) (h1 : term828 x) : term13 = term4.
Proof. exact (proj2 (@lem1740095 x h1)). Qed.
Lemma lem1740100 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1740101 : (term13 = term4) = (term273 = (NUMERAL 0)).
Proof. exact (@lem1740100 term273 (NUMERAL 0)). Qed.
Lemma lem1740102 : term742 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1740103 (h1 : term742 = (BIT1 0)) : (term273 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1740104 : (term742 = (BIT1 0)) = ((term273 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term742 = (BIT1 0) => @lem1740103 h1) (fun h1 : (term273 = (NUMERAL 0)) = False => @lem1740102)). Qed.
Lemma lem1740105 : (term273 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1740104) (@lem1740102)). Qed.
Lemma lem1740106 : (term13 = term4) = False.
Proof. exact (TRANS (@lem1740101) (@lem1740105)). Qed.
Lemma lem1740107 (x : real) (h1 : term828 x) : False.
Proof. exact (EQ_MP (@lem1740106) (@lem1740097 x h1)). Qed.
Lemma lem1740108 (x : real) (h1 : term590 x) : False.
Proof. exact (or_elim (@lem1740079 x h1) (fun h0 : term827 x => @lem1740093 x h0) (fun h0 : term828 x => @lem1740107 x h0)). Qed.
Lemma lem1740109 (x : real) (h1 : term597 x) : False.
Proof. exact (or_elim (@lem1739993 x h1) (fun h0 : term593 x => @lem1740078 x h0) (fun h0 : term590 x => @lem1740108 x h0)). Qed.
Lemma lem1740110 (x : real) (h1 : term649 x) : False.
Proof. exact (or_elim (@lem1739610 x h1) (fun h0 : term647 x => @lem1739992 x h0) (fun h0 : term597 x => @lem1740109 x h0)). Qed.
Lemma lem1740111 (x : real) (h1 : term738 x) : False.
Proof. exact (or_elim (@lem1739088 x h1) (fun h0 : term736 x => @lem1739609 x h0) (fun h0 : term649 x => @lem1740110 x h0)). Qed.
Lemma lem1740113 (x : real) (h1 : term738 x) : term738 x.
Proof. exact (h1). Qed.
Lemma lem1740114 (x : real) (h1 : term738 x) : (term738 x) = False.
Proof. exact (prop_ext (fun h2 : term738 x => @lem1740111 x h1) (fun h2 : False => @lem1740113 x h1)). Qed.
Lemma lem1740115 (x : real) (h1 : term738 x) : False.
Proof. exact (EQ_MP (@lem1740114 x h1) (@lem1740113 x h1)). Qed.
Lemma lem1740116 (h1 : term740) : term740.
Proof. exact (h1). Qed.
Lemma lem1740117 (h1 : term740) : False.
Proof. exact (ex_elim (@lem1740116 h1) (fun x : real => fun h0 : term739 x => @lem1740115 x h0)). Qed.
Lemma lem1740118 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1740119 (h1 : term73) : term740.
Proof. exact (EQ_MP (@lem1738934) (@lem1740118 h1)). Qed.
Lemma lem1740120 (h1 : term73) : term740 = False.
Proof. exact (prop_ext (fun h2 : term740 => @lem1740117 h2) (fun h2 : False => @lem1740119 h1)). Qed.
Lemma lem1740121 (h1 : term73) : False.
Proof. exact (EQ_MP (@lem1740120 h1) (@lem1740119 h1)). Qed.
Lemma lem1740122 : term829.
Proof. exact (fun h0 : term73 => @lem1740121 h0). Qed.
Lemma lem1740123 : term830.
Proof. exact (@lem1386578 term34). Qed.
Lemma lem1740124 : term34.
Proof. exact (@lem1740123 (@lem1740122)). Qed.
Lemma lem1740125 : term33.
Proof. exact (EQ_MP (@lem1735180) (@lem1740124)). Qed.
