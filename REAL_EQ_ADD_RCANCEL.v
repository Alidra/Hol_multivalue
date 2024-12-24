Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_ADD_RCANCEL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
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
Require Import thm69_spec.
Lemma lem1353168 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1353169 : term1 = term2.
Proof. exact (@lem1353168 term1). Qed.
Lemma lem1353170 : term2 = term1.
Proof. exact (SYM (@lem1353169)). Qed.
Lemma lem1353171 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1353174 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1353175 : term5.
Proof. exact (fun h0 : term4 => @lem1353174 h0). Qed.
Lemma lem1353176 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1353177 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1353178 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1353176 h2 (@lem1353177 h1)). Qed.
Lemma lem1353179 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1353178 h1 h0). Qed.
Lemma lem1353180 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1353181 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1353179 h1 (@lem1353180 h2)). Qed.
Lemma lem1353182 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1353181 h0 h1). Qed.
Lemma lem1353183 : term7.
Proof. exact (fun h0 : term5 => @lem1353182 h0). Qed.
Lemma lem1353186 : term5.
Proof. exact (@lem1353183 (@lem1353175)). Qed.
Lemma lem1353216 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1353217 : term8 = term9.
Proof. exact (@lem1353216 term10). Qed.
Lemma lem1353226 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1353227 : term12 = term13.
Proof. exact (MK_COMB (@lem1353226) (@lem1353217)). Qed.
Lemma lem1353230 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1353237 : term4 = term15.
Proof. exact (MK_COMB (@lem1353230) (@lem1353227)). Qed.
Lemma lem1353238 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1353239 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1353238 y x)). Qed.
Lemma lem1353240 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353241 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1353240) (@lem1353239 x)). Qed.
Lemma lem1353242 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1353241 x)). Qed.
Lemma lem1353243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353244 : term10 = term10.
Proof. exact (MK_COMB (@lem1353243) (@lem1353242)). Qed.
Lemma lem1353245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1353246 : term9 = term9.
Proof. exact (MK_COMB (@lem1353245) (@lem1353244)). Qed.
Lemma lem1353251 (x : real) (y : real) (z : real) : (((real_add x y) = (real_add x z)) = (y = z)) = (((real_add x y) = (real_add x z)) = (y = z)).
Proof. exact (eq_refl (((real_add x y) = (real_add x z)) = (y = z))). Qed.
Lemma lem1353252 (x : real) (y : real) : (term19 x y) = (term19 x y).
Proof. exact (fun_ext (fun z : real => @lem1353251 x y z)). Qed.
Lemma lem1353253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353254 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1353253) (@lem1353252 x y)). Qed.
Lemma lem1353255 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1353254 x y)). Qed.
Lemma lem1353256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353257 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1353256) (@lem1353255 x)). Qed.
Lemma lem1353258 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1353257 x)). Qed.
Lemma lem1353259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353260 : term24 = term24.
Proof. exact (MK_COMB (@lem1353259) (@lem1353258)). Qed.
Lemma lem1353261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1353262 : term11 = term11.
Proof. exact (MK_COMB (@lem1353261) (@lem1353260)). Qed.
Lemma lem1353263 : term13 = term13.
Proof. exact (MK_COMB (@lem1353262) (@lem1353246)). Qed.
Lemma lem1353268 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (((real_add x z) = (real_add y z)) = (x = y)).
Proof. exact (eq_refl (((real_add x z) = (real_add y z)) = (x = y))). Qed.
Lemma lem1353269 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (fun_ext (fun z : real => @lem1353268 z x y)). Qed.
Lemma lem1353270 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353271 (x : real) (y : real) : (term26 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1353270) (@lem1353269 x y)). Qed.
Lemma lem1353272 (x : real) : (term27 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1353271 x y)). Qed.
Lemma lem1353273 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353274 (x : real) : (term28 x) = (term28 x).
Proof. exact (MK_COMB (@lem1353273) (@lem1353272 x)). Qed.
Lemma lem1353275 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1353274 x)). Qed.
Lemma lem1353276 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353277 : term1 = term1.
Proof. exact (MK_COMB (@lem1353276) (@lem1353275)). Qed.
Lemma lem1353278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1353279 : term3 = term3.
Proof. exact (MK_COMB (@lem1353278) (@lem1353277)). Qed.
Lemma lem1353280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1353281 : term14 = term14.
Proof. exact (MK_COMB (@lem1353280) (@lem1353279)). Qed.
Lemma lem1353282 : term15 = term15.
Proof. exact (MK_COMB (@lem1353281) (@lem1353263)). Qed.
Lemma lem1353337 : term4 = term15.
Proof. exact (TRANS (@lem1353237) (@lem1353282)). Qed.
Lemma lem1353338 : term15 = term4.
Proof. exact (SYM (@lem1353337)). Qed.
Lemma lem1353339 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1353340 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1353341 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1353356 (z : real) (x : real) (y : real) : (term30 z x y) = (term31 z x y).
Proof. exact (@lem17646 ((real_add x z) = (real_add y z)) (x = y)). Qed.
Lemma lem1353357 (P : real -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1353358 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (@lem1353357 (term25 x y)). Qed.
Lemma lem1353359 (z : real) (x : real) (y : real) : (term36 x y z) = (((real_add x z) = (real_add y z)) = (x = y)).
Proof. exact (eq_refl (term36 x y z)). Qed.
Lemma lem1353360 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1353361 (z : real) (x : real) (y : real) : (term37 x y z) = (term30 z x y).
Proof. exact (MK_COMB (@lem1353360) (@lem1353359 z x y)). Qed.
Lemma lem1353362 (z : real) (x : real) (y : real) : (term37 x y z) = (term31 z x y).
Proof. exact (TRANS (@lem1353361 z x y) (@lem1353356 z x y)). Qed.
Lemma lem1353363 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (fun_ext (fun z : real => @lem1353362 z x y)). Qed.
Lemma lem1353364 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353365 (x : real) (y : real) : (term35 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1353364) (@lem1353363 x y)). Qed.
Lemma lem1353366 (x : real) (y : real) : (term34 x y) = (term40 x y).
Proof. exact (TRANS (@lem1353358 x y) (@lem1353365 x y)). Qed.
Lemma lem1353367 (P : real -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1353368 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1353367 (term27 x)). Qed.
Lemma lem1353369 (x : real) (y : real) : (term43 x y) = (term26 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1353370 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1353371 (x : real) (y : real) : (term44 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1353370) (@lem1353369 x y)). Qed.
Lemma lem1353372 (x : real) (y : real) : (term44 x y) = (term40 x y).
Proof. exact (TRANS (@lem1353371 x y) (@lem1353366 x y)). Qed.
Lemma lem1353373 (x : real) : (term45 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1353372 x y)). Qed.
Lemma lem1353374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353375 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1353374) (@lem1353373 x)). Qed.
Lemma lem1353376 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1353368 x) (@lem1353375 x)). Qed.
Lemma lem1353377 (P : real -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1353378 : term3 = term48.
Proof. exact (@lem1353377 term29). Qed.
Lemma lem1353379 (x : real) : (term49 x) = (term28 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1353380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1353381 (x : real) : (term50 x) = (term41 x).
Proof. exact (MK_COMB (@lem1353380) (@lem1353379 x)). Qed.
Lemma lem1353382 (x : real) : (term50 x) = (term47 x).
Proof. exact (TRANS (@lem1353381 x) (@lem1353376 x)). Qed.
Lemma lem1353383 : term51 = term52.
Proof. exact (fun_ext (fun x : real => @lem1353382 x)). Qed.
Lemma lem1353384 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353385 : term48 = term53.
Proof. exact (MK_COMB (@lem1353384) (@lem1353383)). Qed.
Lemma lem1353386 : term3 = term53.
Proof. exact (TRANS (@lem1353378) (@lem1353385)). Qed.
Lemma lem1353396 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1353397 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1353396 real P Q). Qed.
Lemma lem1353398 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1353397 (term60 x y) (term61 x y)). Qed.
Lemma lem1353399 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1353400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353401 (z : real) (x : real) (y : real) : (term64 x y z) = (term65 z x y).
Proof. exact (MK_COMB (@lem1353400) (@lem1353399 z x y)). Qed.
Lemma lem1353402 (z : real) (x : real) (y : real) : (term66 x y z) = (term67 z x y).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem1353403 (z : real) (x : real) (y : real) : (term68 x y z) = (term31 z x y).
Proof. exact (MK_COMB (@lem1353401 z x y) (@lem1353402 z x y)). Qed.
Lemma lem1353404 (x : real) (y : real) : (term69 x y) = (term39 x y).
Proof. exact (fun_ext (fun z : real => @lem1353403 z x y)). Qed.
Lemma lem1353405 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353406 (x : real) (y : real) : (term58 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1353405) (@lem1353404 x y)). Qed.
Lemma lem1353407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353408 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1353407) (@lem1353406 x y)). Qed.
Lemma lem1353409 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1353410 (x : real) (y : real) : (term72 x y) = (term60 x y).
Proof. exact (fun_ext (fun z : real => @lem1353409 z x y)). Qed.
Lemma lem1353411 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353412 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1353411) (@lem1353410 x y)). Qed.
Lemma lem1353413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353414 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1353413) (@lem1353412 x y)). Qed.
Lemma lem1353415 (z : real) (x : real) (y : real) : (term66 x y z) = (term67 z x y).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem1353416 (x : real) (y : real) : (term77 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1353415 z x y)). Qed.
Lemma lem1353417 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353418 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1353417) (@lem1353416 x y)). Qed.
Lemma lem1353419 (x : real) (y : real) : (term59 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1353414 x y) (@lem1353418 x y)). Qed.
Lemma lem1353420 (x : real) (y : real) : ((term58 x y) = (term59 x y)) = ((term40 x y) = (term80 x y)).
Proof. exact (MK_COMB (@lem1353408 x y) (@lem1353419 x y)). Qed.
Lemma lem1353421 (x : real) (y : real) : (term40 x y) = (term80 x y).
Proof. exact (EQ_MP (@lem1353420 x y) (@lem1353398 x y)). Qed.
Lemma lem1353443 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem1353444 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1353443 real P Q). Qed.
Lemma lem1353445 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (@lem1353444 (term87 x y) (term88 x y)). Qed.
Lemma lem1353446 (x : real) (y : real) (z : real) : (term89 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1353447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353448 (x : real) (y : real) (z : real) : (term90 x y z) = (term91 x y z).
Proof. exact (MK_COMB (@lem1353447) (@lem1353446 x y z)). Qed.
Lemma lem1353449 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1353450 (z : real) (x : real) (y : real) : (term92 z x y) = (term63 z x y).
Proof. exact (MK_COMB (@lem1353448 x y z) (@lem1353449 x y)). Qed.
Lemma lem1353451 (x : real) (y : real) : (term93 x y) = (term60 x y).
Proof. exact (fun_ext (fun z : real => @lem1353450 z x y)). Qed.
Lemma lem1353452 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353453 (x : real) (y : real) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1353452) (@lem1353451 x y)). Qed.
Lemma lem1353454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353455 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1353454) (@lem1353453 x y)). Qed.
Lemma lem1353456 (x : real) (y : real) (z : real) : (term89 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1353457 (x : real) (y : real) : (term96 x y) = (term87 x y).
Proof. exact (fun_ext (fun z : real => @lem1353456 x y z)). Qed.
Lemma lem1353458 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353459 (x : real) (y : real) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1353458) (@lem1353457 x y)). Qed.
Lemma lem1353460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353461 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1353460) (@lem1353459 x y)). Qed.
Lemma lem1353462 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1353463 (x : real) (y : real) : (term86 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1353461 x y) (@lem1353462 x y)). Qed.
Lemma lem1353464 (x : real) (y : real) : ((term85 x y) = (term86 x y)) = ((term74 x y) = (term101 x y)).
Proof. exact (MK_COMB (@lem1353455 x y) (@lem1353463 x y)). Qed.
Lemma lem1353465 (x : real) (y : real) : (term74 x y) = (term101 x y).
Proof. exact (EQ_MP (@lem1353464 x y) (@lem1353445 x y)). Qed.
Lemma lem1353470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353471 (x : real) (y : real) : (term76 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1353470) (@lem1353465 x y)). Qed.
Lemma lem1353493 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem1353494 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1353493 real P Q). Qed.
Lemma lem1353495 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (@lem1353494 (term105 x y) (x = y)). Qed.
Lemma lem1353496 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1353497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353498 (x : real) (y : real) (z : real) : (term108 x y z) = (term109 x y z).
Proof. exact (MK_COMB (@lem1353497) (@lem1353496 x y z)). Qed.
Lemma lem1353499 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1353500 (z : real) (x : real) (y : real) : (term110 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1353498 x y z) (@lem1353499 x y)). Qed.
Lemma lem1353501 (x : real) (y : real) : (term111 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1353500 z x y)). Qed.
Lemma lem1353502 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353503 (x : real) (y : real) : (term103 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1353502) (@lem1353501 x y)). Qed.
Lemma lem1353504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353505 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1353504) (@lem1353503 x y)). Qed.
Lemma lem1353506 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1353507 (x : real) (y : real) : (term114 x y) = (term105 x y).
Proof. exact (fun_ext (fun z : real => @lem1353506 x y z)). Qed.
Lemma lem1353508 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353509 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1353508) (@lem1353507 x y)). Qed.
Lemma lem1353510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353511 (x : real) (y : real) : (term117 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1353510) (@lem1353509 x y)). Qed.
Lemma lem1353512 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1353513 (x : real) (y : real) : (term104 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1353511 x y) (@lem1353512 x y)). Qed.
Lemma lem1353514 (x : real) (y : real) : ((term103 x y) = (term104 x y)) = ((term79 x y) = (term119 x y)).
Proof. exact (MK_COMB (@lem1353505 x y) (@lem1353513 x y)). Qed.
Lemma lem1353515 (x : real) (y : real) : (term79 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem1353514 x y) (@lem1353495 x y)). Qed.
Lemma lem1353520 (x : real) (y : real) : (term80 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1353471 x y) (@lem1353515 x y)). Qed.
Lemma lem1353521 (x : real) (y : real) : (term40 x y) = (term120 x y).
Proof. exact (TRANS (@lem1353421 x y) (@lem1353520 x y)). Qed.
Lemma lem1353522 (x : real) : (term46 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1353521 x y)). Qed.
Lemma lem1353523 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353524 (x : real) : (term47 x) = (term122 x).
Proof. exact (MK_COMB (@lem1353523) (@lem1353522 x)). Qed.
Lemma lem1353526 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1353527 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1353526 real P Q). Qed.
Lemma lem1353528 (x : real) : (term123 x) = (term124 x).
Proof. exact (@lem1353527 (term125 x) (term126 x)). Qed.
Lemma lem1353529 (x : real) (y : real) : (term127 x y) = (term101 x y).
Proof. exact (eq_refl (term127 x y)). Qed.
Lemma lem1353530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353531 (x : real) (y : real) : (term128 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1353530) (@lem1353529 x y)). Qed.
Lemma lem1353532 (x : real) (y : real) : (term129 x y) = (term119 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1353533 (x : real) (y : real) : (term130 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1353531 x y) (@lem1353532 x y)). Qed.
Lemma lem1353534 (x : real) : (term131 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1353533 x y)). Qed.
Lemma lem1353535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353536 (x : real) : (term123 x) = (term122 x).
Proof. exact (MK_COMB (@lem1353535) (@lem1353534 x)). Qed.
Lemma lem1353537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353538 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1353537) (@lem1353536 x)). Qed.
Lemma lem1353539 (x : real) (y : real) : (term127 x y) = (term101 x y).
Proof. exact (eq_refl (term127 x y)). Qed.
Lemma lem1353540 (x : real) : (term134 x) = (term125 x).
Proof. exact (fun_ext (fun y : real => @lem1353539 x y)). Qed.
Lemma lem1353541 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353542 (x : real) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1353541) (@lem1353540 x)). Qed.
Lemma lem1353543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353544 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1353543) (@lem1353542 x)). Qed.
Lemma lem1353545 (x : real) (y : real) : (term129 x y) = (term119 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1353546 (x : real) : (term139 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1353545 x y)). Qed.
Lemma lem1353547 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353548 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1353547) (@lem1353546 x)). Qed.
Lemma lem1353549 (x : real) : (term124 x) = (term142 x).
Proof. exact (MK_COMB (@lem1353544 x) (@lem1353548 x)). Qed.
Lemma lem1353550 (x : real) : ((term123 x) = (term124 x)) = ((term122 x) = (term142 x)).
Proof. exact (MK_COMB (@lem1353538 x) (@lem1353549 x)). Qed.
Lemma lem1353551 (x : real) : (term122 x) = (term142 x).
Proof. exact (EQ_MP (@lem1353550 x) (@lem1353528 x)). Qed.
Lemma lem1353656 (x : real) : (term47 x) = (term142 x).
Proof. exact (TRANS (@lem1353524 x) (@lem1353551 x)). Qed.
Lemma lem1353657 : term52 = term143.
Proof. exact (fun_ext (fun x : real => @lem1353656 x)). Qed.
Lemma lem1353658 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353659 : term53 = term144.
Proof. exact (MK_COMB (@lem1353658) (@lem1353657)). Qed.
Lemma lem1353661 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1353662 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1353661 real P Q). Qed.
Lemma lem1353663 : term145 = term146.
Proof. exact (@lem1353662 term147 term148). Qed.
Lemma lem1353664 (x : real) : (term149 x) = (term136 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1353665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353666 (x : real) : (term150 x) = (term138 x).
Proof. exact (MK_COMB (@lem1353665) (@lem1353664 x)). Qed.
Lemma lem1353667 (x : real) : (term151 x) = (term141 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1353668 (x : real) : (term152 x) = (term142 x).
Proof. exact (MK_COMB (@lem1353666 x) (@lem1353667 x)). Qed.
Lemma lem1353669 : term153 = term143.
Proof. exact (fun_ext (fun x : real => @lem1353668 x)). Qed.
Lemma lem1353670 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353671 : term145 = term144.
Proof. exact (MK_COMB (@lem1353670) (@lem1353669)). Qed.
Lemma lem1353672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353673 : term154 = term155.
Proof. exact (MK_COMB (@lem1353672) (@lem1353671)). Qed.
Lemma lem1353674 (x : real) : (term149 x) = (term136 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1353675 : term156 = term147.
Proof. exact (fun_ext (fun x : real => @lem1353674 x)). Qed.
Lemma lem1353676 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353677 : term157 = term158.
Proof. exact (MK_COMB (@lem1353676) (@lem1353675)). Qed.
Lemma lem1353678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353679 : term159 = term160.
Proof. exact (MK_COMB (@lem1353678) (@lem1353677)). Qed.
Lemma lem1353680 (x : real) : (term151 x) = (term141 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1353681 : term161 = term148.
Proof. exact (fun_ext (fun x : real => @lem1353680 x)). Qed.
Lemma lem1353682 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353683 : term162 = term163.
Proof. exact (MK_COMB (@lem1353682) (@lem1353681)). Qed.
Lemma lem1353684 : term146 = term164.
Proof. exact (MK_COMB (@lem1353679) (@lem1353683)). Qed.
Lemma lem1353685 : (term145 = term146) = (term144 = term164).
Proof. exact (MK_COMB (@lem1353673) (@lem1353684)). Qed.
Lemma lem1353686 : term144 = term164.
Proof. exact (EQ_MP (@lem1353685) (@lem1353663)). Qed.
Lemma lem1353799 : term53 = term164.
Proof. exact (TRANS (@lem1353659) (@lem1353686)). Qed.
Lemma lem1353801 {A : Type'} (P : A -> Prop) (Q : Prop) : (term82 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1353802 (P : real -> Prop) (Q : Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem1353801 real P Q). Qed.
Lemma lem1353803 (x : real) (y : real) : (term86 x y) = (term85 x y).
Proof. exact (@lem1353802 (term87 x y) (term88 x y)). Qed.
Lemma lem1353804 (x : real) (y : real) (z : real) : (term89 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1353805 (x : real) (y : real) : (term96 x y) = (term87 x y).
Proof. exact (fun_ext (fun z : real => @lem1353804 x y z)). Qed.
Lemma lem1353806 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353807 (x : real) (y : real) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1353806) (@lem1353805 x y)). Qed.
Lemma lem1353808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353809 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1353808) (@lem1353807 x y)). Qed.
Lemma lem1353810 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1353811 (x : real) (y : real) : (term86 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1353809 x y) (@lem1353810 x y)). Qed.
Lemma lem1353812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353813 (x : real) (y : real) : (term165 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1353812) (@lem1353811 x y)). Qed.
Lemma lem1353814 (x : real) (y : real) (z : real) : (term89 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1353815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353816 (x : real) (y : real) (z : real) : (term90 x y z) = (term91 x y z).
Proof. exact (MK_COMB (@lem1353815) (@lem1353814 x y z)). Qed.
Lemma lem1353817 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1353818 (z : real) (x : real) (y : real) : (term92 z x y) = (term63 z x y).
Proof. exact (MK_COMB (@lem1353816 x y z) (@lem1353817 x y)). Qed.
Lemma lem1353819 (x : real) (y : real) : (term93 x y) = (term60 x y).
Proof. exact (fun_ext (fun z : real => @lem1353818 z x y)). Qed.
Lemma lem1353820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353821 (x : real) (y : real) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1353820) (@lem1353819 x y)). Qed.
Lemma lem1353822 (x : real) (y : real) : ((term86 x y) = (term85 x y)) = ((term101 x y) = (term74 x y)).
Proof. exact (MK_COMB (@lem1353813 x y) (@lem1353821 x y)). Qed.
Lemma lem1353823 (x : real) (y : real) : (term101 x y) = (term74 x y).
Proof. exact (EQ_MP (@lem1353822 x y) (@lem1353803 x y)). Qed.
Lemma lem1353824 (x : real) : (term125 x) = (term167 x).
Proof. exact (fun_ext (fun y : real => @lem1353823 x y)). Qed.
Lemma lem1353825 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353826 (x : real) : (term136 x) = (term168 x).
Proof. exact (MK_COMB (@lem1353825) (@lem1353824 x)). Qed.
Lemma lem1353827 : term147 = term169.
Proof. exact (fun_ext (fun x : real => @lem1353826 x)). Qed.
Lemma lem1353828 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353829 : term158 = term170.
Proof. exact (MK_COMB (@lem1353828) (@lem1353827)). Qed.
Lemma lem1353830 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353831 : term160 = term171.
Proof. exact (MK_COMB (@lem1353830) (@lem1353829)). Qed.
Lemma lem1353833 {A : Type'} (P : A -> Prop) (Q : Prop) : (term82 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1353834 (P : real -> Prop) (Q : Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem1353833 real P Q). Qed.
Lemma lem1353835 (x : real) (y : real) : (term104 x y) = (term103 x y).
Proof. exact (@lem1353834 (term105 x y) (x = y)). Qed.
Lemma lem1353836 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1353837 (x : real) (y : real) : (term114 x y) = (term105 x y).
Proof. exact (fun_ext (fun z : real => @lem1353836 x y z)). Qed.
Lemma lem1353838 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353839 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1353838) (@lem1353837 x y)). Qed.
Lemma lem1353840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353841 (x : real) (y : real) : (term117 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1353840) (@lem1353839 x y)). Qed.
Lemma lem1353842 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1353843 (x : real) (y : real) : (term104 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1353841 x y) (@lem1353842 x y)). Qed.
Lemma lem1353844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353845 (x : real) (y : real) : (term172 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1353844) (@lem1353843 x y)). Qed.
Lemma lem1353846 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1353847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353848 (x : real) (y : real) (z : real) : (term108 x y z) = (term109 x y z).
Proof. exact (MK_COMB (@lem1353847) (@lem1353846 x y z)). Qed.
Lemma lem1353849 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1353850 (z : real) (x : real) (y : real) : (term110 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1353848 x y z) (@lem1353849 x y)). Qed.
Lemma lem1353851 (x : real) (y : real) : (term111 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1353850 z x y)). Qed.
Lemma lem1353852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353853 (x : real) (y : real) : (term103 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1353852) (@lem1353851 x y)). Qed.
Lemma lem1353854 (x : real) (y : real) : ((term104 x y) = (term103 x y)) = ((term119 x y) = (term79 x y)).
Proof. exact (MK_COMB (@lem1353845 x y) (@lem1353853 x y)). Qed.
Lemma lem1353855 (x : real) (y : real) : (term119 x y) = (term79 x y).
Proof. exact (EQ_MP (@lem1353854 x y) (@lem1353835 x y)). Qed.
Lemma lem1353856 (x : real) : (term126 x) = (term174 x).
Proof. exact (fun_ext (fun y : real => @lem1353855 x y)). Qed.
Lemma lem1353857 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353858 (x : real) : (term141 x) = (term175 x).
Proof. exact (MK_COMB (@lem1353857) (@lem1353856 x)). Qed.
Lemma lem1353859 : term148 = term176.
Proof. exact (fun_ext (fun x : real => @lem1353858 x)). Qed.
Lemma lem1353860 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353861 : term163 = term177.
Proof. exact (MK_COMB (@lem1353860) (@lem1353859)). Qed.
Lemma lem1353862 : term164 = term178.
Proof. exact (MK_COMB (@lem1353831) (@lem1353861)). Qed.
Lemma lem1353864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1353865 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1353864 real P Q). Qed.
Lemma lem1353866 : term179 = term180.
Proof. exact (@lem1353865 term169 term176). Qed.
Lemma lem1353867 (x : real) : (term181 x) = (term168 x).
Proof. exact (eq_refl (term181 x)). Qed.
Lemma lem1353868 : term182 = term169.
Proof. exact (fun_ext (fun x : real => @lem1353867 x)). Qed.
Lemma lem1353869 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353870 : term183 = term170.
Proof. exact (MK_COMB (@lem1353869) (@lem1353868)). Qed.
Lemma lem1353871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353872 : term184 = term171.
Proof. exact (MK_COMB (@lem1353871) (@lem1353870)). Qed.
Lemma lem1353873 (x : real) : (term185 x) = (term175 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem1353874 : term186 = term176.
Proof. exact (fun_ext (fun x : real => @lem1353873 x)). Qed.
Lemma lem1353875 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353876 : term187 = term177.
Proof. exact (MK_COMB (@lem1353875) (@lem1353874)). Qed.
Lemma lem1353877 : term179 = term178.
Proof. exact (MK_COMB (@lem1353872) (@lem1353876)). Qed.
Lemma lem1353878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353879 : term188 = term189.
Proof. exact (MK_COMB (@lem1353878) (@lem1353877)). Qed.
Lemma lem1353880 (x : real) : (term181 x) = (term168 x).
Proof. exact (eq_refl (term181 x)). Qed.
Lemma lem1353881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353882 (x : real) : (term190 x) = (term191 x).
Proof. exact (MK_COMB (@lem1353881) (@lem1353880 x)). Qed.
Lemma lem1353883 (x : real) : (term185 x) = (term175 x).
Proof. exact (eq_refl (term185 x)). Qed.
Lemma lem1353884 (x : real) : (term192 x) = (term193 x).
Proof. exact (MK_COMB (@lem1353882 x) (@lem1353883 x)). Qed.
Lemma lem1353885 : term194 = term195.
Proof. exact (fun_ext (fun x : real => @lem1353884 x)). Qed.
Lemma lem1353886 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353887 : term180 = term196.
Proof. exact (MK_COMB (@lem1353886) (@lem1353885)). Qed.
Lemma lem1353888 : (term179 = term180) = (term178 = term196).
Proof. exact (MK_COMB (@lem1353879) (@lem1353887)). Qed.
Lemma lem1353889 : term178 = term196.
Proof. exact (EQ_MP (@lem1353888) (@lem1353866)). Qed.
Lemma lem1353891 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1353892 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1353891 real P Q). Qed.
Lemma lem1353893 (x : real) : (term197 x) = (term198 x).
Proof. exact (@lem1353892 (term167 x) (term174 x)). Qed.
Lemma lem1353894 (x : real) (y : real) : (term199 x y) = (term74 x y).
Proof. exact (eq_refl (term199 x y)). Qed.
Lemma lem1353895 (x : real) : (term200 x) = (term167 x).
Proof. exact (fun_ext (fun y : real => @lem1353894 x y)). Qed.
Lemma lem1353896 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353897 (x : real) : (term201 x) = (term168 x).
Proof. exact (MK_COMB (@lem1353896) (@lem1353895 x)). Qed.
Lemma lem1353898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353899 (x : real) : (term202 x) = (term191 x).
Proof. exact (MK_COMB (@lem1353898) (@lem1353897 x)). Qed.
Lemma lem1353900 (x : real) (y : real) : (term203 x y) = (term79 x y).
Proof. exact (eq_refl (term203 x y)). Qed.
Lemma lem1353901 (x : real) : (term204 x) = (term174 x).
Proof. exact (fun_ext (fun y : real => @lem1353900 x y)). Qed.
Lemma lem1353902 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353903 (x : real) : (term205 x) = (term175 x).
Proof. exact (MK_COMB (@lem1353902) (@lem1353901 x)). Qed.
Lemma lem1353904 (x : real) : (term197 x) = (term193 x).
Proof. exact (MK_COMB (@lem1353899 x) (@lem1353903 x)). Qed.
Lemma lem1353905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353906 (x : real) : (term206 x) = (term207 x).
Proof. exact (MK_COMB (@lem1353905) (@lem1353904 x)). Qed.
Lemma lem1353907 (x : real) (y : real) : (term199 x y) = (term74 x y).
Proof. exact (eq_refl (term199 x y)). Qed.
Lemma lem1353908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353909 (x : real) (y : real) : (term208 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1353908) (@lem1353907 x y)). Qed.
Lemma lem1353910 (x : real) (y : real) : (term203 x y) = (term79 x y).
Proof. exact (eq_refl (term203 x y)). Qed.
Lemma lem1353911 (x : real) (y : real) : (term209 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1353909 x y) (@lem1353910 x y)). Qed.
Lemma lem1353912 (x : real) : (term210 x) = (term211 x).
Proof. exact (fun_ext (fun y : real => @lem1353911 x y)). Qed.
Lemma lem1353913 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353914 (x : real) : (term198 x) = (term212 x).
Proof. exact (MK_COMB (@lem1353913) (@lem1353912 x)). Qed.
Lemma lem1353915 (x : real) : ((term197 x) = (term198 x)) = ((term193 x) = (term212 x)).
Proof. exact (MK_COMB (@lem1353906 x) (@lem1353914 x)). Qed.
Lemma lem1353916 (x : real) : (term193 x) = (term212 x).
Proof. exact (EQ_MP (@lem1353915 x) (@lem1353893 x)). Qed.
Lemma lem1353918 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1353919 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1353918 real P Q). Qed.
Lemma lem1353920 (x : real) (y : real) : (term59 x y) = (term58 x y).
Proof. exact (@lem1353919 (term60 x y) (term61 x y)). Qed.
Lemma lem1353921 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1353922 (x : real) (y : real) : (term72 x y) = (term60 x y).
Proof. exact (fun_ext (fun z : real => @lem1353921 z x y)). Qed.
Lemma lem1353923 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353924 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1353923) (@lem1353922 x y)). Qed.
Lemma lem1353925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353926 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1353925) (@lem1353924 x y)). Qed.
Lemma lem1353927 (z : real) (x : real) (y : real) : (term66 x y z) = (term67 z x y).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem1353928 (x : real) (y : real) : (term77 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1353927 z x y)). Qed.
Lemma lem1353929 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353930 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1353929) (@lem1353928 x y)). Qed.
Lemma lem1353931 (x : real) (y : real) : (term59 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1353926 x y) (@lem1353930 x y)). Qed.
Lemma lem1353932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1353933 (x : real) (y : real) : (term213 x y) = (term214 x y).
Proof. exact (MK_COMB (@lem1353932) (@lem1353931 x y)). Qed.
Lemma lem1353934 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1353935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1353936 (z : real) (x : real) (y : real) : (term64 x y z) = (term65 z x y).
Proof. exact (MK_COMB (@lem1353935) (@lem1353934 z x y)). Qed.
Lemma lem1353937 (z : real) (x : real) (y : real) : (term66 x y z) = (term67 z x y).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem1353938 (z : real) (x : real) (y : real) : (term68 x y z) = (term31 z x y).
Proof. exact (MK_COMB (@lem1353936 z x y) (@lem1353937 z x y)). Qed.
Lemma lem1353939 (x : real) (y : real) : (term69 x y) = (term39 x y).
Proof. exact (fun_ext (fun z : real => @lem1353938 z x y)). Qed.
Lemma lem1353940 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353941 (x : real) (y : real) : (term58 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1353940) (@lem1353939 x y)). Qed.
Lemma lem1353942 (x : real) (y : real) : ((term59 x y) = (term58 x y)) = ((term80 x y) = (term40 x y)).
Proof. exact (MK_COMB (@lem1353933 x y) (@lem1353941 x y)). Qed.
Lemma lem1353943 (x : real) (y : real) : (term80 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem1353942 x y) (@lem1353920 x y)). Qed.
Lemma lem1353944 (x : real) : (term211 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1353943 x y)). Qed.
Lemma lem1353945 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353946 (x : real) : (term212 x) = (term47 x).
Proof. exact (MK_COMB (@lem1353945) (@lem1353944 x)). Qed.
Lemma lem1353947 (x : real) : (term193 x) = (term47 x).
Proof. exact (TRANS (@lem1353916 x) (@lem1353946 x)). Qed.
Lemma lem1353948 : term195 = term52.
Proof. exact (fun_ext (fun x : real => @lem1353947 x)). Qed.
Lemma lem1353949 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1353950 : term196 = term53.
Proof. exact (MK_COMB (@lem1353949) (@lem1353948)). Qed.
Lemma lem1353951 : term178 = term53.
Proof. exact (TRANS (@lem1353889) (@lem1353950)). Qed.
Lemma lem1353952 : term164 = term53.
Proof. exact (TRANS (@lem1353862) (@lem1353951)). Qed.
Lemma lem1353953 : term53 = term53.
Proof. exact (TRANS (@lem1353799) (@lem1353952)). Qed.
Lemma lem1353954 : term3 = term53.
Proof. exact (TRANS (@lem1353386) (@lem1353953)). Qed.
Lemma lem1353955 (h1 : term3) : term53.
Proof. exact (EQ_MP (@lem1353954) (@lem1353339 h1)). Qed.
Lemma lem1353970 (x : real) (y : real) (z : real) : (((real_add x y) = (real_add x z)) = (y = z)) = (term215 x y z).
Proof. exact (@lem17784 ((real_add x y) = (real_add x z)) (y = z)). Qed.
Lemma lem1353971 (x : real) (y : real) : (term19 x y) = (term216 x y).
Proof. exact (fun_ext (fun z : real => @lem1353970 x y z)). Qed.
Lemma lem1353972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353973 (x : real) (y : real) : (term20 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1353972) (@lem1353971 x y)). Qed.
Lemma lem1353974 (x : real) : (term21 x) = (term218 x).
Proof. exact (fun_ext (fun y : real => @lem1353973 x y)). Qed.
Lemma lem1353975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353976 (x : real) : (term22 x) = (term219 x).
Proof. exact (MK_COMB (@lem1353975) (@lem1353974 x)). Qed.
Lemma lem1353977 : term23 = term220.
Proof. exact (fun_ext (fun x : real => @lem1353976 x)). Qed.
Lemma lem1353978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353979 : term24 = term221.
Proof. exact (MK_COMB (@lem1353978) (@lem1353977)). Qed.
Lemma lem1353989 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term223 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1353990 (P : real -> Prop) (Q : real -> Prop) : (term224 P Q) = (term225 P Q).
Proof. exact (@lem1353989 real P Q). Qed.
Lemma lem1353991 (x : real) (y : real) : (term226 x y) = (term227 x y).
Proof. exact (@lem1353990 (term228 x y) (term229 x y)). Qed.
Lemma lem1353992 (x : real) (y : real) (z : real) : (term230 x y z) = (term231 x y z).
Proof. exact (eq_refl (term230 x y z)). Qed.
Lemma lem1353993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1353994 (x : real) (y : real) (z : real) : (term232 x y z) = (term233 x y z).
Proof. exact (MK_COMB (@lem1353993) (@lem1353992 x y z)). Qed.
Lemma lem1353995 (x : real) (y : real) (z : real) : (term234 x y z) = (term235 x y z).
Proof. exact (eq_refl (term234 x y z)). Qed.
Lemma lem1353996 (x : real) (y : real) (z : real) : (term236 x y z) = (term215 x y z).
Proof. exact (MK_COMB (@lem1353994 x y z) (@lem1353995 x y z)). Qed.
Lemma lem1353997 (x : real) (y : real) : (term237 x y) = (term216 x y).
Proof. exact (fun_ext (fun z : real => @lem1353996 x y z)). Qed.
Lemma lem1353998 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1353999 (x : real) (y : real) : (term226 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1353998) (@lem1353997 x y)). Qed.
Lemma lem1354000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1354001 (x : real) (y : real) : (term238 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem1354000) (@lem1353999 x y)). Qed.
Lemma lem1354002 (x : real) (y : real) (z : real) : (term230 x y z) = (term231 x y z).
Proof. exact (eq_refl (term230 x y z)). Qed.
Lemma lem1354003 (x : real) (y : real) : (term240 x y) = (term228 x y).
Proof. exact (fun_ext (fun z : real => @lem1354002 x y z)). Qed.
Lemma lem1354004 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354005 (x : real) (y : real) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1354004) (@lem1354003 x y)). Qed.
Lemma lem1354006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354007 (x : real) (y : real) : (term243 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1354006) (@lem1354005 x y)). Qed.
Lemma lem1354008 (x : real) (y : real) (z : real) : (term234 x y z) = (term235 x y z).
Proof. exact (eq_refl (term234 x y z)). Qed.
Lemma lem1354009 (x : real) (y : real) : (term245 x y) = (term229 x y).
Proof. exact (fun_ext (fun z : real => @lem1354008 x y z)). Qed.
Lemma lem1354010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354011 (x : real) (y : real) : (term246 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1354010) (@lem1354009 x y)). Qed.
Lemma lem1354012 (x : real) (y : real) : (term227 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem1354007 x y) (@lem1354011 x y)). Qed.
Lemma lem1354013 (x : real) (y : real) : ((term226 x y) = (term227 x y)) = ((term217 x y) = (term248 x y)).
Proof. exact (MK_COMB (@lem1354001 x y) (@lem1354012 x y)). Qed.
Lemma lem1354014 (x : real) (y : real) : (term217 x y) = (term248 x y).
Proof. exact (EQ_MP (@lem1354013 x y) (@lem1353991 x y)). Qed.
Lemma lem1354111 (x : real) : (term218 x) = (term249 x).
Proof. exact (fun_ext (fun y : real => @lem1354014 x y)). Qed.
Lemma lem1354112 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354113 (x : real) : (term219 x) = (term250 x).
Proof. exact (MK_COMB (@lem1354112) (@lem1354111 x)). Qed.
Lemma lem1354115 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term223 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1354116 (P : real -> Prop) (Q : real -> Prop) : (term224 P Q) = (term225 P Q).
Proof. exact (@lem1354115 real P Q). Qed.
Lemma lem1354117 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1354116 (term253 x) (term254 x)). Qed.
Lemma lem1354118 (x : real) (y : real) : (term255 x y) = (term242 x y).
Proof. exact (eq_refl (term255 x y)). Qed.
Lemma lem1354119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354120 (x : real) (y : real) : (term256 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1354119) (@lem1354118 x y)). Qed.
Lemma lem1354121 (x : real) (y : real) : (term257 x y) = (term247 x y).
Proof. exact (eq_refl (term257 x y)). Qed.
Lemma lem1354122 (x : real) (y : real) : (term258 x y) = (term248 x y).
Proof. exact (MK_COMB (@lem1354120 x y) (@lem1354121 x y)). Qed.
Lemma lem1354123 (x : real) : (term259 x) = (term249 x).
Proof. exact (fun_ext (fun y : real => @lem1354122 x y)). Qed.
Lemma lem1354124 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354125 (x : real) : (term251 x) = (term250 x).
Proof. exact (MK_COMB (@lem1354124) (@lem1354123 x)). Qed.
Lemma lem1354126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1354127 (x : real) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem1354126) (@lem1354125 x)). Qed.
Lemma lem1354128 (x : real) (y : real) : (term255 x y) = (term242 x y).
Proof. exact (eq_refl (term255 x y)). Qed.
Lemma lem1354129 (x : real) : (term262 x) = (term253 x).
Proof. exact (fun_ext (fun y : real => @lem1354128 x y)). Qed.
Lemma lem1354130 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354131 (x : real) : (term263 x) = (term264 x).
Proof. exact (MK_COMB (@lem1354130) (@lem1354129 x)). Qed.
Lemma lem1354132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354133 (x : real) : (term265 x) = (term266 x).
Proof. exact (MK_COMB (@lem1354132) (@lem1354131 x)). Qed.
Lemma lem1354134 (x : real) (y : real) : (term257 x y) = (term247 x y).
Proof. exact (eq_refl (term257 x y)). Qed.
Lemma lem1354135 (x : real) : (term267 x) = (term254 x).
Proof. exact (fun_ext (fun y : real => @lem1354134 x y)). Qed.
Lemma lem1354136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354137 (x : real) : (term268 x) = (term269 x).
Proof. exact (MK_COMB (@lem1354136) (@lem1354135 x)). Qed.
Lemma lem1354138 (x : real) : (term252 x) = (term270 x).
Proof. exact (MK_COMB (@lem1354133 x) (@lem1354137 x)). Qed.
Lemma lem1354139 (x : real) : ((term251 x) = (term252 x)) = ((term250 x) = (term270 x)).
Proof. exact (MK_COMB (@lem1354127 x) (@lem1354138 x)). Qed.
Lemma lem1354140 (x : real) : (term250 x) = (term270 x).
Proof. exact (EQ_MP (@lem1354139 x) (@lem1354117 x)). Qed.
Lemma lem1354245 (x : real) : (term219 x) = (term270 x).
Proof. exact (TRANS (@lem1354113 x) (@lem1354140 x)). Qed.
Lemma lem1354246 : term220 = term271.
Proof. exact (fun_ext (fun x : real => @lem1354245 x)). Qed.
Lemma lem1354247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354248 : term221 = term272.
Proof. exact (MK_COMB (@lem1354247) (@lem1354246)). Qed.
Lemma lem1354250 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term223 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1354251 (P : real -> Prop) (Q : real -> Prop) : (term224 P Q) = (term225 P Q).
Proof. exact (@lem1354250 real P Q). Qed.
Lemma lem1354252 : term273 = term274.
Proof. exact (@lem1354251 term275 term276). Qed.
Lemma lem1354253 (x : real) : (term277 x) = (term264 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1354254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354255 (x : real) : (term278 x) = (term266 x).
Proof. exact (MK_COMB (@lem1354254) (@lem1354253 x)). Qed.
Lemma lem1354256 (x : real) : (term279 x) = (term269 x).
Proof. exact (eq_refl (term279 x)). Qed.
Lemma lem1354257 (x : real) : (term280 x) = (term270 x).
Proof. exact (MK_COMB (@lem1354255 x) (@lem1354256 x)). Qed.
Lemma lem1354258 : term281 = term271.
Proof. exact (fun_ext (fun x : real => @lem1354257 x)). Qed.
Lemma lem1354259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354260 : term273 = term272.
Proof. exact (MK_COMB (@lem1354259) (@lem1354258)). Qed.
Lemma lem1354261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1354262 : term282 = term283.
Proof. exact (MK_COMB (@lem1354261) (@lem1354260)). Qed.
Lemma lem1354263 (x : real) : (term277 x) = (term264 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1354264 : term284 = term275.
Proof. exact (fun_ext (fun x : real => @lem1354263 x)). Qed.
Lemma lem1354265 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354266 : term285 = term286.
Proof. exact (MK_COMB (@lem1354265) (@lem1354264)). Qed.
Lemma lem1354267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354268 : term287 = term288.
Proof. exact (MK_COMB (@lem1354267) (@lem1354266)). Qed.
Lemma lem1354269 (x : real) : (term279 x) = (term269 x).
Proof. exact (eq_refl (term279 x)). Qed.
Lemma lem1354270 : term289 = term276.
Proof. exact (fun_ext (fun x : real => @lem1354269 x)). Qed.
Lemma lem1354271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354272 : term290 = term291.
Proof. exact (MK_COMB (@lem1354271) (@lem1354270)). Qed.
Lemma lem1354273 : term274 = term292.
Proof. exact (MK_COMB (@lem1354268) (@lem1354272)). Qed.
Lemma lem1354274 : (term273 = term274) = (term272 = term292).
Proof. exact (MK_COMB (@lem1354262) (@lem1354273)). Qed.
Lemma lem1354275 : term272 = term292.
Proof. exact (EQ_MP (@lem1354274) (@lem1354252)). Qed.
Lemma lem1354390 : term221 = term292.
Proof. exact (TRANS (@lem1354248) (@lem1354275)). Qed.
Lemma lem1354391 : term24 = term292.
Proof. exact (TRANS (@lem1353979) (@lem1354390)). Qed.
Lemma lem1354392 (h1 : term24) : term292.
Proof. exact (EQ_MP (@lem1354391) (@lem1353340 h1)). Qed.
Lemma lem1354393 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1354394 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1354393 y x)). Qed.
Lemma lem1354395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354396 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1354395) (@lem1354394 x)). Qed.
Lemma lem1354397 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1354396 x)). Qed.
Lemma lem1354398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354411 : term10 = term10.
Proof. exact (MK_COMB (@lem1354398) (@lem1354397)). Qed.
Lemma lem1354412 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1354411) (@lem1353341 h1)). Qed.
Lemma lem1354413 (x : real) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1354414 (x : real) (y : real) (h1 : term40 x y) : term40 x y.
Proof. exact (h1). Qed.
Lemma lem1354438 (x : real) (y : real) (z : real) : (term235 x y z) = (term235 x y z).
Proof. exact (eq_refl (term235 x y z)). Qed.
Lemma lem1354439 (x : real) (y : real) : (term229 x y) = (term229 x y).
Proof. exact (fun_ext (fun z : real => @lem1354438 x y z)). Qed.
Lemma lem1354440 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354441 (x : real) (y : real) : (term247 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1354440) (@lem1354439 x y)). Qed.
Lemma lem1354442 (x : real) : (term254 x) = (term254 x).
Proof. exact (fun_ext (fun y : real => @lem1354441 x y)). Qed.
Lemma lem1354443 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354444 (x : real) : (term269 x) = (term269 x).
Proof. exact (MK_COMB (@lem1354443) (@lem1354442 x)). Qed.
Lemma lem1354445 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem1354444 x)). Qed.
Lemma lem1354446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354447 : term291 = term291.
Proof. exact (MK_COMB (@lem1354446) (@lem1354445)). Qed.
Lemma lem1354470 (x : real) (y : real) (z : real) : (term231 x y z) = (term231 x y z).
Proof. exact (eq_refl (term231 x y z)). Qed.
Lemma lem1354471 (x : real) (y : real) : (term228 x y) = (term228 x y).
Proof. exact (fun_ext (fun z : real => @lem1354470 x y z)). Qed.
Lemma lem1354472 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354473 (x : real) (y : real) : (term242 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1354472) (@lem1354471 x y)). Qed.
Lemma lem1354474 (x : real) : (term253 x) = (term253 x).
Proof. exact (fun_ext (fun y : real => @lem1354473 x y)). Qed.
Lemma lem1354475 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354476 (x : real) : (term264 x) = (term264 x).
Proof. exact (MK_COMB (@lem1354475) (@lem1354474 x)). Qed.
Lemma lem1354477 : term275 = term275.
Proof. exact (fun_ext (fun x : real => @lem1354476 x)). Qed.
Lemma lem1354478 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354479 : term286 = term286.
Proof. exact (MK_COMB (@lem1354478) (@lem1354477)). Qed.
Lemma lem1354480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354481 : term288 = term288.
Proof. exact (MK_COMB (@lem1354480) (@lem1354479)). Qed.
Lemma lem1354482 : term292 = term292.
Proof. exact (MK_COMB (@lem1354481) (@lem1354447)). Qed.
Lemma lem1354483 (h1 : term24) : term292.
Proof. exact (EQ_MP (@lem1354482) (@lem1354392 h1)). Qed.
Lemma lem1354496 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1354497 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1354496 y x)). Qed.
Lemma lem1354498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354499 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1354498) (@lem1354497 x)). Qed.
Lemma lem1354500 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1354499 x)). Qed.
Lemma lem1354501 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354502 : term10 = term10.
Proof. exact (MK_COMB (@lem1354501) (@lem1354500)). Qed.
Lemma lem1354503 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1354502) (@lem1354412 h1)). Qed.
Lemma lem1354553 (z : real) (x : real) (y : real) (h1 : term31 z x y) : term31 z x y.
Proof. exact (h1). Qed.
Lemma lem1354554 (h1 : term24) : term291.
Proof. exact (proj2 (@lem1354483 h1)). Qed.
Lemma lem1354556 (z : real) (x : real) (y : real) (h1 : term63 z x y) : term63 z x y.
Proof. exact (h1). Qed.
Lemma lem1354557 (z : real) (x : real) (y : real) (h1 : term67 z x y) : term67 z x y.
Proof. exact (h1). Qed.
Lemma lem1354563 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1354564 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1354563 y x)). Qed.
Lemma lem1354565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354566 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1354565) (@lem1354564 x)). Qed.
Lemma lem1354567 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1354566 x)). Qed.
Lemma lem1354568 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354570 : term10 = term10.
Proof. exact (MK_COMB (@lem1354568) (@lem1354567)). Qed.
Lemma lem1354571 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1354570) (@lem1354503 h1)). Qed.
Lemma lem1354598 (x : real) (y : real) (z : real) : (term235 x y z) = (term235 x y z).
Proof. exact (eq_refl (term235 x y z)). Qed.
Lemma lem1354599 (x : real) (y : real) : (term229 x y) = (term229 x y).
Proof. exact (fun_ext (fun z : real => @lem1354598 x y z)). Qed.
Lemma lem1354600 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354601 (x : real) (y : real) : (term247 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1354600) (@lem1354599 x y)). Qed.
Lemma lem1354602 (x : real) : (term254 x) = (term254 x).
Proof. exact (fun_ext (fun y : real => @lem1354601 x y)). Qed.
Lemma lem1354603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354604 (x : real) : (term269 x) = (term269 x).
Proof. exact (MK_COMB (@lem1354603) (@lem1354602 x)). Qed.
Lemma lem1354605 : term276 = term276.
Proof. exact (fun_ext (fun x : real => @lem1354604 x)). Qed.
Lemma lem1354606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1354608 : term291 = term291.
Proof. exact (MK_COMB (@lem1354606) (@lem1354605)). Qed.
Lemma lem1354609 (h1 : term24) : term291.
Proof. exact (EQ_MP (@lem1354608) (@lem1354554 h1)). Qed.
Lemma lem1354674 (_24083 : real) (h1 : term10) : term293 _24083.
Proof. exact (@lem1354571 h1 _24083). Qed.
Lemma lem1354675 (_24083 : real) : (term293 _24083) = (term17 _24083).
Proof. exact (eq_refl (term293 _24083)). Qed.
Lemma lem1354676 (_24083 : real) (h1 : term10) : term17 _24083.
Proof. exact (EQ_MP (@lem1354675 _24083) (@lem1354674 _24083 h1)). Qed.
Lemma lem1354677 (_24083 : real) (_24084 : real) (h1 : term10) : term294 _24083 _24084.
Proof. exact (@lem1354676 _24083 h1 _24084). Qed.
Lemma lem1354678 (_24084 : real) (_24083 : real) : (term294 _24083 _24084) = ((real_add _24083 _24084) = (real_add _24084 _24083)).
Proof. exact (eq_refl (term294 _24083 _24084)). Qed.
Lemma lem1354689 (_24088 : real) (h1 : term24) : term279 _24088.
Proof. exact (@lem1354609 h1 _24088). Qed.
Lemma lem1354690 (_24088 : real) : (term279 _24088) = (term269 _24088).
Proof. exact (eq_refl (term279 _24088)). Qed.
Lemma lem1354691 (_24088 : real) (h1 : term24) : term269 _24088.
Proof. exact (EQ_MP (@lem1354690 _24088) (@lem1354689 _24088 h1)). Qed.
Lemma lem1354692 (_24088 : real) (_24089 : real) (h1 : term24) : term257 _24088 _24089.
Proof. exact (@lem1354691 _24088 h1 _24089). Qed.
Lemma lem1354693 (_24088 : real) (_24089 : real) : (term257 _24088 _24089) = (term247 _24088 _24089).
Proof. exact (eq_refl (term257 _24088 _24089)). Qed.
Lemma lem1354694 (_24088 : real) (_24089 : real) (h1 : term24) : term247 _24088 _24089.
Proof. exact (EQ_MP (@lem1354693 _24088 _24089) (@lem1354692 _24088 _24089 h1)). Qed.
Lemma lem1354695 (_24088 : real) (_24089 : real) (_24090 : real) (h1 : term24) : term234 _24088 _24089 _24090.
Proof. exact (@lem1354694 _24088 _24089 h1 _24090). Qed.
Lemma lem1354696 (_24088 : real) (_24089 : real) (_24090 : real) : (term234 _24088 _24089 _24090) = (term235 _24088 _24089 _24090).
Proof. exact (eq_refl (term234 _24088 _24089 _24090)). Qed.
Lemma lem1354735 (_24088 : real) (_24089 : real) (_24090 : real) (h1 : term24) : term235 _24088 _24089 _24090.
Proof. exact (EQ_MP (@lem1354696 _24088 _24089 _24090) (@lem1354695 _24088 _24089 _24090 h1)). Qed.
Lemma lem1354739 (z : real) (x : real) (y : real) (h1 : term63 z x y) : term88 x y.
Proof. exact (proj2 (@lem1354556 z x y h1)). Qed.
Lemma lem1354755 (z : real) (x : real) (y : real) (h1 : term67 z x y) : term107 x y z.
Proof. exact (proj1 (@lem1354557 z x y h1)). Qed.
Lemma lem1354757 (z : real) (x : real) (y : real) (h1 : term67 z x y) : x = y.
Proof. exact (proj2 (@lem1354557 z x y h1)). Qed.
Lemma lem1354814 (y : real) (z : real) : (term295 y z) = (term295 y z).
Proof. exact (eq_refl (term295 y z)). Qed.
Lemma lem1354815 (z : real) (x : real) (y : real) (h1 : term67 z x y) : (term296 y z x) = (term297 z y).
Proof. exact (MK_COMB (@lem1354814 y z) (@lem1354757 z x y h1)). Qed.
Lemma lem1354816 (y : real) (z : real) : (term297 z y) = (term298 y z).
Proof. exact (eq_refl (term297 z y)). Qed.
Lemma lem1354817 (y : real) (z : real) (x : real) : (term299 y z x) = (term299 y z x).
Proof. exact (eq_refl (term299 y z x)). Qed.
Lemma lem1354818 (x : real) (y : real) (z : real) : ((term296 y z x) = (term297 z y)) = ((term296 y z x) = (term298 y z)).
Proof. exact (MK_COMB (@lem1354817 y z x) (@lem1354816 y z)). Qed.
Lemma lem1354819 (x : real) (y : real) (z : real) : (term296 y z x) = (term107 x y z).
Proof. exact (eq_refl (term296 y z x)). Qed.
Lemma lem1354820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1354821 (x : real) (y : real) (z : real) : (term299 y z x) = (term300 x y z).
Proof. exact (MK_COMB (@lem1354820) (@lem1354819 x y z)). Qed.
Lemma lem1354822 (y : real) (z : real) : (term298 y z) = (term298 y z).
Proof. exact (eq_refl (term298 y z)). Qed.
Lemma lem1354823 (x : real) (y : real) (z : real) : ((term296 y z x) = (term298 y z)) = ((term107 x y z) = (term298 y z)).
Proof. exact (MK_COMB (@lem1354821 x y z) (@lem1354822 y z)). Qed.
Lemma lem1354824 (x : real) (y : real) (z : real) : ((term296 y z x) = (term297 z y)) = ((term107 x y z) = (term298 y z)).
Proof. exact (TRANS (@lem1354818 x y z) (@lem1354823 x y z)). Qed.
Lemma lem1354825 (z : real) (x : real) (y : real) (h1 : term67 z x y) : (term107 x y z) = (term298 y z).
Proof. exact (EQ_MP (@lem1354824 x y z) (@lem1354815 z x y h1)). Qed.
Lemma lem1354826 (z : real) (x : real) (y : real) (h1 : term67 z x y) : term298 y z.
Proof. exact (EQ_MP (@lem1354825 z x y h1) (@lem1354755 z x y h1)). Qed.
Lemma lem1354843 (x : real) (y : real) (z : real) : term301 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1354845 (z : real) (x : real) (y : real) (h1 : term63 z x y) : (real_add x z) = (real_add y z).
Proof. exact (proj1 (@lem1354556 z x y h1)). Qed.
Lemma lem1354846 (z : real) (x : real) (y : real) (h1 : term63 z x y) : term302 x y z.
Proof. exact (fun h0 : term107 x y z => @lem1354845 z x y h1). Qed.
Lemma lem1354848 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1354849 (x : real) (y : real) (z : real) : (term302 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (@lem1354848 ((real_add x z) = (real_add y z))). Qed.
Lemma lem1354850 (z : real) (x : real) (y : real) (h1 : term63 z x y) : (real_add x z) = (real_add y z).
Proof. exact (EQ_MP (@lem1354849 x y z) (@lem1354846 z x y h1)). Qed.
Lemma lem1354852 (_24084 : real) (_24083 : real) (h1 : term10) : (real_add _24083 _24084) = (real_add _24084 _24083).
Proof. exact (EQ_MP (@lem1354678 _24084 _24083) (@lem1354677 _24083 _24084 h1)). Qed.
Lemma lem1354853 (z : real) (x : real) (h1 : term10) : (real_add x z) = (real_add z x).
Proof. exact (@lem1354852 z x h1). Qed.
Lemma lem1354854 (z : real) (x : real) (h1 : term10) : term304 z x.
Proof. exact (fun h0 : term305 z x => @lem1354853 z x h1). Qed.
Lemma lem1354856 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1354857 (z : real) (x : real) : (term304 z x) = ((real_add x z) = (real_add z x)).
Proof. exact (@lem1354856 ((real_add x z) = (real_add z x))). Qed.
Lemma lem1354858 (z : real) (x : real) (h1 : term10) : (real_add x z) = (real_add z x).
Proof. exact (EQ_MP (@lem1354857 z x) (@lem1354854 z x h1)). Qed.
Lemma lem1354876 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1354877 (y : real) (x : real) (z : real) : (term306 x y z) = (term307 y x z).
Proof. exact (@lem1354876 (y = z) (term88 x z)). Qed.
Lemma lem1354887 (x : real) (y : real) : (term308 x y) = (term308 x y).
Proof. exact (eq_refl (term308 x y)). Qed.
Lemma lem1354888 (y : real) (x : real) (z : real) : (term301 x y z) = (term309 y x z).
Proof. exact (MK_COMB (@lem1354887 x y) (@lem1354877 y x z)). Qed.
Lemma lem1354892 (q : Prop) (p : Prop) (r : Prop) : (term310 p q r) = (term310 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1354893 (y : real) (x : real) (z : real) : (term309 y x z) = (term311 y x z).
Proof. exact (@lem1354892 (y = z) (term88 x y) (term88 x z)). Qed.
Lemma lem1354915 (y : real) (x : real) (z : real) : (term301 x y z) = (term311 y x z).
Proof. exact (TRANS (@lem1354888 y x z) (@lem1354893 y x z)). Qed.
Lemma lem1354916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1354917 (y : real) (x : real) (z : real) : (term312 x y z) = (term313 y x z).
Proof. exact (MK_COMB (@lem1354916) (@lem1354915 y x z)). Qed.
Lemma lem1354939 (y : real) (x : real) (z : real) : (term311 y x z) = (term311 y x z).
Proof. exact (eq_refl (term311 y x z)). Qed.
Lemma lem1354940 (y : real) (x : real) (z : real) : ((term301 x y z) = (term311 y x z)) = ((term311 y x z) = (term311 y x z)).
Proof. exact (MK_COMB (@lem1354917 y x z) (@lem1354939 y x z)). Qed.
Lemma lem1354942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1354943 (x : Prop) : (x = x) = True.
Proof. exact (@lem1354942 Prop x). Qed.
Lemma lem1354944 (y : real) (x : real) (z : real) : ((term311 y x z) = (term311 y x z)) = True.
Proof. exact (@lem1354943 (term311 y x z)). Qed.
Lemma lem1354945 (y : real) (x : real) (z : real) : ((term301 x y z) = (term311 y x z)) = True.
Proof. exact (TRANS (@lem1354940 y x z) (@lem1354944 y x z)). Qed.
Lemma lem1354946 (y : real) (x : real) (z : real) : True = ((term301 x y z) = (term311 y x z)).
Proof. exact (SYM (@lem1354945 y x z)). Qed.
Lemma lem1354947 (y : real) (x : real) (z : real) : (term301 x y z) = (term311 y x z).
Proof. exact (EQ_MP (@lem1354946 y x z) (@lem0)). Qed.
Lemma lem1354948 (y : real) (x : real) (z : real) : term311 y x z.
Proof. exact (EQ_MP (@lem1354947 y x z) (@lem1354843 x y z)). Qed.
Lemma lem1354950 (b : Prop) (a : Prop) : (a \/ b) = (term314 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1354951 (x : real) (y : real) (z : real) : (term311 y x z) = (term315 x y z).
Proof. exact (@lem1354950 (term316 y x z) (y = z)). Qed.
Lemma lem1354953 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1354954 (y : real) (x : real) (z : real) : (term319 y x z) = (term320 y x z).
Proof. exact (@lem1354953 (term88 x y) (term88 x z)). Qed.
Lemma lem1354956 (a : Prop) : (term321 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1354957 (x : real) (y : real) : (term322 x y) = (x = y).
Proof. exact (@lem1354956 (x = y)). Qed.
Lemma lem1354958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1354959 (x : real) (y : real) : (term323 x y) = (term324 x y).
Proof. exact (MK_COMB (@lem1354958) (@lem1354957 x y)). Qed.
Lemma lem1354961 (a : Prop) : (term321 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1354962 (x : real) (z : real) : (term322 x z) = (x = z).
Proof. exact (@lem1354961 (x = z)). Qed.
Lemma lem1354963 (y : real) (x : real) (z : real) : (term320 y x z) = (term325 y x z).
Proof. exact (MK_COMB (@lem1354959 x y) (@lem1354962 x z)). Qed.
Lemma lem1354964 (y : real) (x : real) (z : real) : (term319 y x z) = (term325 y x z).
Proof. exact (TRANS (@lem1354954 y x z) (@lem1354963 y x z)). Qed.
Lemma lem1354965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1354966 (y : real) (x : real) (z : real) : (term326 y x z) = (term327 y x z).
Proof. exact (MK_COMB (@lem1354965) (@lem1354964 y x z)). Qed.
Lemma lem1354967 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1354968 (x : real) (y : real) (z : real) : (term315 x y z) = (term328 x y z).
Proof. exact (MK_COMB (@lem1354966 y x z) (@lem1354967 y z)). Qed.
Lemma lem1354969 (x : real) (y : real) (z : real) : (term311 y x z) = (term328 x y z).
Proof. exact (TRANS (@lem1354951 x y z) (@lem1354968 x y z)). Qed.
Lemma lem1354971 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : term329 y z x.
Proof. exact (conj (@lem1354850 z x y h2) (@lem1354858 z x h1)). Qed.
Lemma lem1354973 (x : real) (y : real) (z : real) : term328 x y z.
Proof. exact (EQ_MP (@lem1354969 x y z) (@lem1354948 y x z)). Qed.
Lemma lem1354974 (y : real) (z : real) (x : real) : term330 y z x.
Proof. exact (@lem1354973 (real_add x z) (real_add y z) (real_add z x)). Qed.
Lemma lem1354977 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : (real_add y z) = (real_add z x).
Proof. exact (@lem1354974 y z x (@lem1354971 z x y h1 h2)). Qed.
Lemma lem1354978 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : term331 y z x.
Proof. exact (fun h0 : term332 y z x => @lem1354977 z x y h1 h2). Qed.
Lemma lem1354980 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1354981 (y : real) (z : real) (x : real) : (term331 y z x) = ((real_add y z) = (real_add z x)).
Proof. exact (@lem1354980 ((real_add y z) = (real_add z x))). Qed.
Lemma lem1354982 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : (real_add y z) = (real_add z x).
Proof. exact (EQ_MP (@lem1354981 y z x) (@lem1354978 z x y h1 h2)). Qed.
Lemma lem1354984 (_24084 : real) (_24083 : real) (h1 : term10) : (real_add _24083 _24084) = (real_add _24084 _24083).
Proof. exact (EQ_MP (@lem1354678 _24084 _24083) (@lem1354677 _24083 _24084 h1)). Qed.
Lemma lem1354985 (z : real) (y : real) (h1 : term10) : (real_add y z) = (real_add z y).
Proof. exact (@lem1354984 z y h1). Qed.
Lemma lem1354986 (z : real) (y : real) (h1 : term10) : term304 z y.
Proof. exact (fun h0 : term305 z y => @lem1354985 z y h1). Qed.
Lemma lem1354988 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1354989 (z : real) (y : real) : (term304 z y) = ((real_add y z) = (real_add z y)).
Proof. exact (@lem1354988 ((real_add y z) = (real_add z y))). Qed.
Lemma lem1354990 (z : real) (y : real) (h1 : term10) : (real_add y z) = (real_add z y).
Proof. exact (EQ_MP (@lem1354989 z y) (@lem1354986 z y h1)). Qed.
Lemma lem1354991 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : term333 x z y.
Proof. exact (conj (@lem1354982 z x y h1 h2) (@lem1354990 z y h1)). Qed.
Lemma lem1354993 (x : real) (y : real) (z : real) : term328 x y z.
Proof. exact (EQ_MP (@lem1354969 x y z) (@lem1354948 y x z)). Qed.
Lemma lem1354994 (x : real) (z : real) (y : real) : term334 x z y.
Proof. exact (@lem1354993 (real_add y z) (real_add z x) (real_add z y)). Qed.
Lemma lem1354997 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : (real_add z x) = (real_add z y).
Proof. exact (@lem1354994 x z y (@lem1354991 z x y h1 h2)). Qed.
Lemma lem1354998 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : term335 x z y.
Proof. exact (fun h0 : term336 x z y => @lem1354997 z x y h1 h2). Qed.
Lemma lem1355000 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1355001 (x : real) (z : real) (y : real) : (term335 x z y) = ((real_add z x) = (real_add z y)).
Proof. exact (@lem1355000 ((real_add z x) = (real_add z y))). Qed.
Lemma lem1355002 (z : real) (x : real) (y : real) (h1 : term10) (h2 : term63 z x y) : (real_add z x) = (real_add z y).
Proof. exact (EQ_MP (@lem1355001 x z y) (@lem1354998 z x y h1 h2)). Qed.
Lemma lem1355008 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1355009 (_24089 : real) (_24088 : real) (_24090 : real) : (term235 _24088 _24089 _24090) = (term337 _24089 _24088 _24090).
Proof. exact (@lem1355008 (_24089 = _24090) (term336 _24089 _24088 _24090)). Qed.
Lemma lem1355019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1355020 (_24089 : real) (_24088 : real) (_24090 : real) : (term338 _24088 _24089 _24090) = (term339 _24089 _24088 _24090).
Proof. exact (MK_COMB (@lem1355019) (@lem1355009 _24089 _24088 _24090)). Qed.
Lemma lem1355030 (_24089 : real) (_24088 : real) (_24090 : real) : (term337 _24089 _24088 _24090) = (term337 _24089 _24088 _24090).
Proof. exact (eq_refl (term337 _24089 _24088 _24090)). Qed.
Lemma lem1355031 (_24089 : real) (_24088 : real) (_24090 : real) : ((term235 _24088 _24089 _24090) = (term337 _24089 _24088 _24090)) = ((term337 _24089 _24088 _24090) = (term337 _24089 _24088 _24090)).
Proof. exact (MK_COMB (@lem1355020 _24089 _24088 _24090) (@lem1355030 _24089 _24088 _24090)). Qed.
Lemma lem1355033 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1355034 (x : Prop) : (x = x) = True.
Proof. exact (@lem1355033 Prop x). Qed.
Lemma lem1355035 (_24089 : real) (_24088 : real) (_24090 : real) : ((term337 _24089 _24088 _24090) = (term337 _24089 _24088 _24090)) = True.
Proof. exact (@lem1355034 (term337 _24089 _24088 _24090)). Qed.
Lemma lem1355036 (_24089 : real) (_24088 : real) (_24090 : real) : ((term235 _24088 _24089 _24090) = (term337 _24089 _24088 _24090)) = True.
Proof. exact (TRANS (@lem1355031 _24089 _24088 _24090) (@lem1355035 _24089 _24088 _24090)). Qed.
Lemma lem1355037 (_24089 : real) (_24088 : real) (_24090 : real) : True = ((term235 _24088 _24089 _24090) = (term337 _24089 _24088 _24090)).
Proof. exact (SYM (@lem1355036 _24089 _24088 _24090)). Qed.
Lemma lem1355038 (_24089 : real) (_24088 : real) (_24090 : real) : (term235 _24088 _24089 _24090) = (term337 _24089 _24088 _24090).
Proof. exact (EQ_MP (@lem1355037 _24089 _24088 _24090) (@lem0)). Qed.
Lemma lem1355039 (_24089 : real) (_24088 : real) (_24090 : real) (h1 : term24) : term337 _24089 _24088 _24090.
Proof. exact (EQ_MP (@lem1355038 _24089 _24088 _24090) (@lem1354735 _24088 _24089 _24090 h1)). Qed.
Lemma lem1355041 (b : Prop) (a : Prop) : (a \/ b) = (term314 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1355042 (_24088 : real) (_24089 : real) (_24090 : real) : (term337 _24089 _24088 _24090) = (term340 _24088 _24089 _24090).
Proof. exact (@lem1355041 (term336 _24089 _24088 _24090) (_24089 = _24090)). Qed.
Lemma lem1355044 (a : Prop) : (term321 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1355045 (_24089 : real) (_24088 : real) (_24090 : real) : (term341 _24089 _24088 _24090) = ((real_add _24088 _24089) = (real_add _24088 _24090)).
Proof. exact (@lem1355044 ((real_add _24088 _24089) = (real_add _24088 _24090))). Qed.
Lemma lem1355046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1355047 (_24089 : real) (_24088 : real) (_24090 : real) : (term342 _24089 _24088 _24090) = (term343 _24089 _24088 _24090).
Proof. exact (MK_COMB (@lem1355046) (@lem1355045 _24089 _24088 _24090)). Qed.
Lemma lem1355048 (_24089 : real) (_24090 : real) : (_24089 = _24090) = (_24089 = _24090).
Proof. exact (eq_refl (_24089 = _24090)). Qed.
Lemma lem1355049 (_24088 : real) (_24089 : real) (_24090 : real) : (term340 _24088 _24089 _24090) = (term344 _24088 _24089 _24090).
Proof. exact (MK_COMB (@lem1355047 _24089 _24088 _24090) (@lem1355048 _24089 _24090)). Qed.
Lemma lem1355050 (_24088 : real) (_24089 : real) (_24090 : real) : (term337 _24089 _24088 _24090) = (term344 _24088 _24089 _24090).
Proof. exact (TRANS (@lem1355042 _24088 _24089 _24090) (@lem1355049 _24088 _24089 _24090)). Qed.
Lemma lem1355053 (_24088 : real) (_24089 : real) (_24090 : real) (h1 : term24) : term344 _24088 _24089 _24090.
Proof. exact (EQ_MP (@lem1355050 _24088 _24089 _24090) (@lem1355039 _24089 _24088 _24090 h1)). Qed.
Lemma lem1355054 (z : real) (x : real) (y : real) (h1 : term24) : term344 z x y.
Proof. exact (@lem1355053 z x y h1). Qed.
Lemma lem1355057 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : x = y.
Proof. exact (@lem1355054 z x y h1 (@lem1355002 z x y h2 h3)). Qed.
Lemma lem1355058 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : term345 x y.
Proof. exact (fun h0 : term88 x y => @lem1355057 z x y h1 h2 h3). Qed.
Lemma lem1355060 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1355061 (x : real) (y : real) : (term345 x y) = (x = y).
Proof. exact (@lem1355060 (x = y)). Qed.
Lemma lem1355062 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : x = y.
Proof. exact (EQ_MP (@lem1355061 x y) (@lem1355058 z x y h1 h2 h3)). Qed.
Lemma lem1355065 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1355067 (x : real) (y : real) : (term88 x y) = (term346 x y).
Proof. exact (@lem1355065 (x = y)). Qed.
Lemma lem1355070 (z : real) (x : real) (y : real) (h1 : term63 z x y) : term346 x y.
Proof. exact (EQ_MP (@lem1355067 x y) (@lem1354739 z x y h1)). Qed.
Lemma lem1355073 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : False.
Proof. exact (@lem1355070 z x y h3 (@lem1355062 z x y h1 h2 h3)). Qed.
Lemma lem1355074 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : term347.
Proof. exact (fun h0 : ~ False => @lem1355073 z x y h1 h2 h3). Qed.
Lemma lem1355076 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1355077 : term347 = False.
Proof. exact (@lem1355076 False). Qed.
Lemma lem1355078 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : False.
Proof. exact (EQ_MP (@lem1355077) (@lem1355074 z x y h1 h2 h3)). Qed.
Lemma lem1355097 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1355098 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (@lem1355097 (real_add y z)). Qed.
Lemma lem1355099 (y : real) (z : real) : term348 y z.
Proof. exact (fun h0 : term298 y z => @lem1355098 y z). Qed.
Lemma lem1355101 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1355102 (y : real) (z : real) : (term348 y z) = ((real_add y z) = (real_add y z)).
Proof. exact (@lem1355101 ((real_add y z) = (real_add y z))). Qed.
Lemma lem1355103 (y : real) (z : real) : (real_add y z) = (real_add y z).
Proof. exact (EQ_MP (@lem1355102 y z) (@lem1355099 y z)). Qed.
Lemma lem1355106 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1355108 (y : real) (z : real) : (term298 y z) = (term349 y z).
Proof. exact (@lem1355106 ((real_add y z) = (real_add y z))). Qed.
Lemma lem1355111 (z : real) (x : real) (y : real) (h1 : term67 z x y) : term349 y z.
Proof. exact (EQ_MP (@lem1355108 y z) (@lem1354826 z x y h1)). Qed.
Lemma lem1355114 (z : real) (x : real) (y : real) (h1 : term67 z x y) : False.
Proof. exact (@lem1355111 z x y h1 (@lem1355103 y z)). Qed.
Lemma lem1355115 (z : real) (x : real) (y : real) (h1 : term67 z x y) : term347.
Proof. exact (fun h0 : ~ False => @lem1355114 z x y h1). Qed.
Lemma lem1355117 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1355118 : term347 = False.
Proof. exact (@lem1355117 False). Qed.
Lemma lem1355120 (z : real) (x : real) (y : real) (h1 : term67 z x y) : False.
Proof. exact (EQ_MP (@lem1355118) (@lem1355115 z x y h1)). Qed.
Lemma lem1355121 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1355078 z x y h1 h2 h3) (fun h4 : False => @lem1354571 h2)). Qed.
Lemma lem1355122 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term63 z x y) : False.
Proof. exact (EQ_MP (@lem1355121 z x y h1 h2 h3) (@lem1354571 h2)). Qed.
Lemma lem1355123 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term31 z x y) : False.
Proof. exact (or_elim (@lem1354553 z x y h3) (fun h0 : term63 z x y => @lem1355122 z x y h1 h2 h0) (fun h0 : term67 z x y => @lem1355120 z x y h0)). Qed.
Lemma lem1355124 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term31 z x y) : (term31 z x y) = False.
Proof. exact (prop_ext (fun h4 : term31 z x y => @lem1355123 z x y h1 h2 h3) (fun h4 : False => @lem1354553 z x y h3)). Qed.
Lemma lem1355125 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term31 z x y) : False.
Proof. exact (EQ_MP (@lem1355124 z x y h1 h2 h3) (@lem1354553 z x y h3)). Qed.
Lemma lem1355126 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term31 z x y) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1355125 z x y h1 h2 h3) (fun h4 : False => @lem1354503 h2)). Qed.
Lemma lem1355127 (z : real) (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term31 z x y) : False.
Proof. exact (EQ_MP (@lem1355126 z x y h1 h2 h3) (@lem1354503 h2)). Qed.
Lemma lem1355128 (x : real) (y : real) (h1 : term24) (h2 : term10) (h3 : term40 x y) : False.
Proof. exact (ex_elim (@lem1354414 x y h3) (fun z : real => fun h0 : term39 x y z => @lem1355127 z x y h1 h2 h0)). Qed.
Lemma lem1355129 (x : real) (h1 : term24) (h2 : term10) (h3 : term47 x) : False.
Proof. exact (ex_elim (@lem1354413 x h3) (fun y : real => fun h0 : term46 x y => @lem1355128 x y h1 h2 h0)). Qed.
Lemma lem1355130 (h1 : term24) (h2 : term10) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1353955 h3) (fun x : real => fun h0 : term52 x => @lem1355129 x h1 h2 h0)). Qed.
Lemma lem1355131 (h1 : term24) (h2 : term10) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1355130 h1 h2 h3) (fun h4 : False => @lem1354412 h2)). Qed.
Lemma lem1355132 (h1 : term24) (h2 : term10) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1355131 h1 h2 h3) (@lem1354412 h2)). Qed.
Lemma lem1355133 (h1 : term24) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1355132 h1 h0 h2). Qed.
Lemma lem1355134 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1355135 (h1 : term24) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1355134) (@lem1355133 h1 h2)). Qed.
Lemma lem1355136 (h1 : term3) : term13.
Proof. exact (fun h0 : term24 => @lem1355135 h0 h1). Qed.
Lemma lem1355137 : term15.
Proof. exact (fun h0 : term3 => @lem1355136 h0). Qed.
Lemma lem1355138 : term4.
Proof. exact (EQ_MP (@lem1353338) (@lem1355137)). Qed.
Lemma lem1355140 : term4.
Proof. exact (@lem1353186 (@lem1355138)). Qed.
Lemma lem1355141 (h1 : term3) : term12.
Proof. exact (@lem1355140 (@lem1353171 h1)). Qed.
Lemma lem1355142 (h1 : term3) : term8.
Proof. exact (@lem1355141 h1 (@lem1353156)). Qed.
Lemma lem1355143 (h1 : term3) : False.
Proof. exact (@lem1355142 h1 (@lem1338238)). Qed.
Lemma lem1355144 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1355143 h1) (fun h2 : False => @lem1353171 h1)). Qed.
Lemma lem1355145 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1355144 h1) (@lem1353171 h1)). Qed.
Lemma lem1355146 : term2.
Proof. exact (fun h0 : term3 => @lem1355145 h0). Qed.
Lemma lem1355147 : term1.
Proof. exact (EQ_MP (@lem1353170) (@lem1355146)). Qed.
