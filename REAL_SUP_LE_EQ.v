Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_LE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5184173 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5184174 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5184175 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5184174 t1) (@lem5184173 t1)). Qed.
Lemma lem5184176 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5184175 t1 t2). Qed.
Lemma lem5184177 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5184178 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5184177 t1 t2) (@lem5184176 t1 t2)). Qed.
Lemma lem5184179 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5184178 t1 t2 t3). Qed.
Lemma lem5184180 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5184181 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5184180 t1 t2 t3) (@lem5184179 t1 t2 t3)). Qed.
Lemma lem5184182 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5184181 t1 t2 t3)). Qed.
Lemma lem5184184 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5184185 : term8 = term9.
Proof. exact (@lem5184184 term8). Qed.
Lemma lem5184186 : term9 = term8.
Proof. exact (SYM (@lem5184185)). Qed.
Lemma lem5184187 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5184190 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5184191 : term12.
Proof. exact (fun h0 : term11 => @lem5184190 h0). Qed.
Lemma lem5184192 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5184193 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5184194 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5184192 h2 (@lem5184193 h1)). Qed.
Lemma lem5184195 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5184194 h1 h0). Qed.
Lemma lem5184196 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5184197 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5184195 h1 (@lem5184196 h2)). Qed.
Lemma lem5184198 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5184197 h0 h1). Qed.
Lemma lem5184199 : term14.
Proof. exact (fun h0 : term12 => @lem5184198 h0). Qed.
Lemma lem5184202 : term12.
Proof. exact (@lem5184199 (@lem5184191)). Qed.
Lemma lem5184252 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5184253 : term15 = term16.
Proof. exact (@lem5184252 term17). Qed.
Lemma lem5184292 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5184293 : term19 = term20.
Proof. exact (MK_COMB (@lem5184292) (@lem5184253)). Qed.
Lemma lem5184296 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5184303 : term11 = term22.
Proof. exact (MK_COMB (@lem5184296) (@lem5184293)). Qed.
Lemma lem5184304 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5184309 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term24 s x b).
Proof. exact (eq_refl (term24 s x b)). Qed.
Lemma lem5184310 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5184309 s x b)). Qed.
Lemma lem5184311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184312 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5184311) (@lem5184310 s b)). Qed.
Lemma lem5184313 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184314 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5184313) (@lem5184312 s b)). Qed.
Lemma lem5184315 (s : real -> Prop) (b : real) : (term28 s b) = (term28 s b).
Proof. exact (MK_COMB (@lem5184314 s b) (@lem5184304 s b)). Qed.
Lemma lem5184316 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (fun_ext (fun b : real => @lem5184315 s b)). Qed.
Lemma lem5184317 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184318 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (MK_COMB (@lem5184317) (@lem5184316 s)). Qed.
Lemma lem5184323 (x : real) (s : real -> Prop) : (term31 x s) = (term31 x s).
Proof. exact (eq_refl (term31 x s)). Qed.
Lemma lem5184324 (s : real -> Prop) : (term32 s) = (term32 s).
Proof. exact (fun_ext (fun x : real => @lem5184323 x s)). Qed.
Lemma lem5184325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184326 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (MK_COMB (@lem5184325) (@lem5184324 s)). Qed.
Lemma lem5184327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5184328 (s : real -> Prop) : (term34 s) = (term34 s).
Proof. exact (MK_COMB (@lem5184327) (@lem5184326 s)). Qed.
Lemma lem5184329 (s : real -> Prop) : (term35 s) = (term35 s).
Proof. exact (MK_COMB (@lem5184328 s) (@lem5184318 s)). Qed.
Lemma lem5184334 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term24 s x b).
Proof. exact (eq_refl (term24 s x b)). Qed.
Lemma lem5184335 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5184334 s x b)). Qed.
Lemma lem5184336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184337 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5184336) (@lem5184335 s b)). Qed.
Lemma lem5184338 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (fun_ext (fun b : real => @lem5184337 s b)). Qed.
Lemma lem5184339 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184340 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (MK_COMB (@lem5184339) (@lem5184338 s)). Qed.
Lemma lem5184345 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5184346 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (MK_COMB (@lem5184345 s) (@lem5184340 s)). Qed.
Lemma lem5184347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184348 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5184347) (@lem5184346 s)). Qed.
Lemma lem5184349 (s : real -> Prop) : (term41 s) = (term41 s).
Proof. exact (MK_COMB (@lem5184348 s) (@lem5184329 s)). Qed.
Lemma lem5184350 : term42 = term42.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5184349 s)). Qed.
Lemma lem5184351 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5184352 : term17 = term17.
Proof. exact (MK_COMB (@lem5184351) (@lem5184350)). Qed.
Lemma lem5184353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5184354 : term16 = term16.
Proof. exact (MK_COMB (@lem5184353) (@lem5184352)). Qed.
Lemma lem5184363 (y : real) (x : real) (z : real) : (term43 y x z) = (term43 y x z).
Proof. exact (eq_refl (term43 y x z)). Qed.
Lemma lem5184364 (y : real) (x : real) : (term44 y x) = (term44 y x).
Proof. exact (fun_ext (fun z : real => @lem5184363 y x z)). Qed.
Lemma lem5184365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184366 (y : real) (x : real) : (term45 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem5184365) (@lem5184364 y x)). Qed.
Lemma lem5184367 (x : real) : (term46 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem5184366 y x)). Qed.
Lemma lem5184368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184369 (x : real) : (term47 x) = (term47 x).
Proof. exact (MK_COMB (@lem5184368) (@lem5184367 x)). Qed.
Lemma lem5184370 : term48 = term48.
Proof. exact (fun_ext (fun x : real => @lem5184369 x)). Qed.
Lemma lem5184371 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184372 : term49 = term49.
Proof. exact (MK_COMB (@lem5184371) (@lem5184370)). Qed.
Lemma lem5184373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184374 : term18 = term18.
Proof. exact (MK_COMB (@lem5184373) (@lem5184372)). Qed.
Lemma lem5184375 : term20 = term20.
Proof. exact (MK_COMB (@lem5184374) (@lem5184354)). Qed.
Lemma lem5184380 (s : real -> Prop) (x : real) (y : real) : (term24 s x y) = (term24 s x y).
Proof. exact (eq_refl (term24 s x y)). Qed.
Lemma lem5184381 (s : real -> Prop) (y : real) : (term25 s y) = (term25 s y).
Proof. exact (fun_ext (fun x : real => @lem5184380 s x y)). Qed.
Lemma lem5184382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184383 (s : real -> Prop) (y : real) : (term26 s y) = (term26 s y).
Proof. exact (MK_COMB (@lem5184382) (@lem5184381 s y)). Qed.
Lemma lem5184386 (s : real -> Prop) (y : real) : (term50 s y) = (term50 s y).
Proof. exact (eq_refl (term50 s y)). Qed.
Lemma lem5184387 (s : real -> Prop) (y : real) : ((term23 s y) = (term26 s y)) = ((term23 s y) = (term26 s y)).
Proof. exact (MK_COMB (@lem5184386 s y) (@lem5184383 s y)). Qed.
Lemma lem5184392 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term24 s x b).
Proof. exact (eq_refl (term24 s x b)). Qed.
Lemma lem5184393 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5184392 s x b)). Qed.
Lemma lem5184394 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184395 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5184394) (@lem5184393 s b)). Qed.
Lemma lem5184396 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (fun_ext (fun b : real => @lem5184395 s b)). Qed.
Lemma lem5184397 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184398 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (MK_COMB (@lem5184397) (@lem5184396 s)). Qed.
Lemma lem5184403 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5184404 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (MK_COMB (@lem5184403 s) (@lem5184398 s)). Qed.
Lemma lem5184405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184406 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5184405) (@lem5184404 s)). Qed.
Lemma lem5184407 (s : real -> Prop) (y : real) : (term51 s y) = (term51 s y).
Proof. exact (MK_COMB (@lem5184406 s) (@lem5184387 s y)). Qed.
Lemma lem5184408 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (fun_ext (fun y : real => @lem5184407 s y)). Qed.
Lemma lem5184409 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184410 (s : real -> Prop) : (term53 s) = (term53 s).
Proof. exact (MK_COMB (@lem5184409) (@lem5184408 s)). Qed.
Lemma lem5184411 : term54 = term54.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5184410 s)). Qed.
Lemma lem5184412 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5184413 : term8 = term8.
Proof. exact (MK_COMB (@lem5184412) (@lem5184411)). Qed.
Lemma lem5184414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5184415 : term10 = term10.
Proof. exact (MK_COMB (@lem5184414) (@lem5184413)). Qed.
Lemma lem5184416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5184417 : term21 = term21.
Proof. exact (MK_COMB (@lem5184416) (@lem5184415)). Qed.
Lemma lem5184418 : term22 = term22.
Proof. exact (MK_COMB (@lem5184417) (@lem5184375)). Qed.
Lemma lem5184535 : term11 = term22.
Proof. exact (TRANS (@lem5184303) (@lem5184418)). Qed.
Lemma lem5184536 : term22 = term11.
Proof. exact (SYM (@lem5184535)). Qed.
Lemma lem5184537 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5184538 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem5184539 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5184547 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term55 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5184548 (s : real -> Prop) (b : real) : (term25 s b) = (term56 s b).
Proof. exact (fun_ext (fun x : real => @lem5184547 s x b)). Qed.
Lemma lem5184549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184550 (s : real -> Prop) (b : real) : (term26 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5184549) (@lem5184548 s b)). Qed.
Lemma lem5184551 (s : real -> Prop) : (term36 s) = (term58 s).
Proof. exact (fun_ext (fun b : real => @lem5184550 s b)). Qed.
Lemma lem5184552 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184553 (s : real -> Prop) : (term37 s) = (term59 s).
Proof. exact (MK_COMB (@lem5184552) (@lem5184551 s)). Qed.
Lemma lem5184555 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5184556 (s : real -> Prop) : (term39 s) = (term60 s).
Proof. exact (MK_COMB (@lem5184555 s) (@lem5184553 s)). Qed.
Lemma lem5184567 (s : real -> Prop) (x : real) (y : real) : (term61 s x y) = (term62 s x y).
Proof. exact (@lem17362 (@IN real x s) (real_le x y)). Qed.
Lemma lem5184572 (s : real -> Prop) (x : real) (y : real) : (term24 s x y) = (term55 s x y).
Proof. exact (@lem17265 (@IN real x s) (real_le x y)). Qed.
Lemma lem5184573 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5184574 (s : real -> Prop) (y : real) : (term65 s y) = (term66 s y).
Proof. exact (@lem5184573 (term25 s y)). Qed.
Lemma lem5184575 (s : real -> Prop) (x : real) (y : real) : (term67 s y x) = (term24 s x y).
Proof. exact (eq_refl (term67 s y x)). Qed.
Lemma lem5184576 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5184577 (s : real -> Prop) (x : real) (y : real) : (term68 s y x) = (term61 s x y).
Proof. exact (MK_COMB (@lem5184576) (@lem5184575 s x y)). Qed.
Lemma lem5184578 (s : real -> Prop) (x : real) (y : real) : (term68 s y x) = (term62 s x y).
Proof. exact (TRANS (@lem5184577 s x y) (@lem5184567 s x y)). Qed.
Lemma lem5184579 (s : real -> Prop) (y : real) : (term69 s y) = (term70 s y).
Proof. exact (fun_ext (fun x : real => @lem5184578 s x y)). Qed.
Lemma lem5184580 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184581 (s : real -> Prop) (y : real) : (term66 s y) = (term71 s y).
Proof. exact (MK_COMB (@lem5184580) (@lem5184579 s y)). Qed.
Lemma lem5184582 (s : real -> Prop) (y : real) : (term65 s y) = (term71 s y).
Proof. exact (TRANS (@lem5184574 s y) (@lem5184581 s y)). Qed.
Lemma lem5184583 (s : real -> Prop) (y : real) : (term25 s y) = (term56 s y).
Proof. exact (fun_ext (fun x : real => @lem5184572 s x y)). Qed.
Lemma lem5184584 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5184585 (s : real -> Prop) (y : real) : (term26 s y) = (term57 s y).
Proof. exact (MK_COMB (@lem5184584) (@lem5184583 s y)). Qed.
Lemma lem5184587 (s : real -> Prop) (y : real) : (term72 s y) = (term72 s y).
Proof. exact (eq_refl (term72 s y)). Qed.
Lemma lem5184588 (s : real -> Prop) (y : real) : (term73 s y) = (term74 s y).
Proof. exact (MK_COMB (@lem5184587 s y) (@lem5184585 s y)). Qed.
Lemma lem5184590 (s : real -> Prop) (y : real) : (term75 s y) = (term75 s y).
Proof. exact (eq_refl (term75 s y)). Qed.
Lemma lem5184591 (s : real -> Prop) (y : real) : (term76 s y) = (term77 s y).
Proof. exact (MK_COMB (@lem5184590 s y) (@lem5184582 s y)). Qed.
Lemma lem5184592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5184593 (s : real -> Prop) (y : real) : (term78 s y) = (term79 s y).
Proof. exact (MK_COMB (@lem5184592) (@lem5184591 s y)). Qed.
Lemma lem5184594 (s : real -> Prop) (y : real) : (term80 s y) = (term81 s y).
Proof. exact (MK_COMB (@lem5184593 s y) (@lem5184588 s y)). Qed.
Lemma lem5184595 (s : real -> Prop) (y : real) : (term82 s y) = (term80 s y).
Proof. exact (@lem17646 (term23 s y) (term26 s y)). Qed.
Lemma lem5184596 (s : real -> Prop) (y : real) : (term82 s y) = (term81 s y).
Proof. exact (TRANS (@lem5184595 s y) (@lem5184594 s y)). Qed.
Lemma lem5184597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5184598 (s : real -> Prop) : (term83 s) = (term84 s).
Proof. exact (MK_COMB (@lem5184597) (@lem5184556 s)). Qed.
Lemma lem5184599 (s : real -> Prop) (y : real) : (term85 s y) = (term86 s y).
Proof. exact (MK_COMB (@lem5184598 s) (@lem5184596 s y)). Qed.
Lemma lem5184600 (s : real -> Prop) (y : real) : (term87 s y) = (term85 s y).
Proof. exact (@lem17362 (term39 s) ((term23 s y) = (term26 s y))). Qed.
Lemma lem5184601 (s : real -> Prop) (y : real) : (term87 s y) = (term86 s y).
Proof. exact (TRANS (@lem5184600 s y) (@lem5184599 s y)). Qed.
Lemma lem5184602 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5184603 (s : real -> Prop) : (term88 s) = (term89 s).
Proof. exact (@lem5184602 (term52 s)). Qed.
Lemma lem5184604 (s : real -> Prop) (y : real) : (term90 s y) = (term51 s y).
Proof. exact (eq_refl (term90 s y)). Qed.
Lemma lem5184605 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5184606 (s : real -> Prop) (y : real) : (term91 s y) = (term87 s y).
Proof. exact (MK_COMB (@lem5184605) (@lem5184604 s y)). Qed.
Lemma lem5184607 (s : real -> Prop) (y : real) : (term91 s y) = (term86 s y).
Proof. exact (TRANS (@lem5184606 s y) (@lem5184601 s y)). Qed.
Lemma lem5184608 (s : real -> Prop) : (term92 s) = (term93 s).
Proof. exact (fun_ext (fun y : real => @lem5184607 s y)). Qed.
Lemma lem5184609 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184610 (s : real -> Prop) : (term89 s) = (term94 s).
Proof. exact (MK_COMB (@lem5184609) (@lem5184608 s)). Qed.
Lemma lem5184611 (s : real -> Prop) : (term88 s) = (term94 s).
Proof. exact (TRANS (@lem5184603 s) (@lem5184610 s)). Qed.
Lemma lem5184612 (P : type1022) : (term95 P) = (term96 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5184613 : term10 = term97.
Proof. exact (@lem5184612 term54). Qed.
Lemma lem5184614 (s : real -> Prop) : (term98 s) = (term53 s).
Proof. exact (eq_refl (term98 s)). Qed.
Lemma lem5184615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5184616 (s : real -> Prop) : (term99 s) = (term88 s).
Proof. exact (MK_COMB (@lem5184615) (@lem5184614 s)). Qed.
Lemma lem5184617 (s : real -> Prop) : (term99 s) = (term94 s).
Proof. exact (TRANS (@lem5184616 s) (@lem5184611 s)). Qed.
Lemma lem5184618 : term100 = term101.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5184617 s)). Qed.
Lemma lem5184619 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5184620 : term97 = term102.
Proof. exact (MK_COMB (@lem5184619) (@lem5184618)). Qed.
Lemma lem5184621 : term10 = term102.
Proof. exact (TRANS (@lem5184613) (@lem5184620)). Qed.
Lemma lem5184627 {A : Type'} (P : Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5184628 (P : Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem5184627 real P Q). Qed.
Lemma lem5184629 (s : real -> Prop) : (term107 s) = (term108 s).
Proof. exact (@lem5184628 (term60 s) (term109 s)). Qed.
Lemma lem5184630 (s : real -> Prop) (y : real) : (term110 s y) = (term81 s y).
Proof. exact (eq_refl (term110 s y)). Qed.
Lemma lem5184631 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5184632 (s : real -> Prop) (y : real) : (term111 s y) = (term86 s y).
Proof. exact (MK_COMB (@lem5184631 s) (@lem5184630 s y)). Qed.
Lemma lem5184633 (s : real -> Prop) : (term112 s) = (term93 s).
Proof. exact (fun_ext (fun y : real => @lem5184632 s y)). Qed.
Lemma lem5184634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184635 (s : real -> Prop) : (term107 s) = (term94 s).
Proof. exact (MK_COMB (@lem5184634) (@lem5184633 s)). Qed.
Lemma lem5184636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5184637 (s : real -> Prop) : (term113 s) = (term114 s).
Proof. exact (MK_COMB (@lem5184636) (@lem5184635 s)). Qed.
Lemma lem5184638 (s : real -> Prop) (y : real) : (term110 s y) = (term81 s y).
Proof. exact (eq_refl (term110 s y)). Qed.
Lemma lem5184639 (s : real -> Prop) : (term115 s) = (term109 s).
Proof. exact (fun_ext (fun y : real => @lem5184638 s y)). Qed.
Lemma lem5184640 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184641 (s : real -> Prop) : (term116 s) = (term117 s).
Proof. exact (MK_COMB (@lem5184640) (@lem5184639 s)). Qed.
Lemma lem5184642 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5184643 (s : real -> Prop) : (term108 s) = (term118 s).
Proof. exact (MK_COMB (@lem5184642 s) (@lem5184641 s)). Qed.
Lemma lem5184644 (s : real -> Prop) : ((term107 s) = (term108 s)) = ((term94 s) = (term118 s)).
Proof. exact (MK_COMB (@lem5184637 s) (@lem5184643 s)). Qed.
Lemma lem5184645 (s : real -> Prop) : (term94 s) = (term118 s).
Proof. exact (EQ_MP (@lem5184644 s) (@lem5184629 s)). Qed.
Lemma lem5184699 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5184700 (P : real -> Prop) (Q : real -> Prop) : (term121 P Q) = (term122 P Q).
Proof. exact (@lem5184699 real P Q). Qed.
Lemma lem5184701 (s : real -> Prop) : (term123 s) = (term124 s).
Proof. exact (@lem5184700 (term125 s) (term126 s)). Qed.
Lemma lem5184702 (s : real -> Prop) (y : real) : (term127 s y) = (term77 s y).
Proof. exact (eq_refl (term127 s y)). Qed.
Lemma lem5184703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5184704 (s : real -> Prop) (y : real) : (term128 s y) = (term79 s y).
Proof. exact (MK_COMB (@lem5184703) (@lem5184702 s y)). Qed.
Lemma lem5184705 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5184706 (s : real -> Prop) (y : real) : (term130 s y) = (term81 s y).
Proof. exact (MK_COMB (@lem5184704 s y) (@lem5184705 s y)). Qed.
Lemma lem5184707 (s : real -> Prop) : (term131 s) = (term109 s).
Proof. exact (fun_ext (fun y : real => @lem5184706 s y)). Qed.
Lemma lem5184708 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184709 (s : real -> Prop) : (term123 s) = (term117 s).
Proof. exact (MK_COMB (@lem5184708) (@lem5184707 s)). Qed.
Lemma lem5184710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5184711 (s : real -> Prop) : (term132 s) = (term133 s).
Proof. exact (MK_COMB (@lem5184710) (@lem5184709 s)). Qed.
Lemma lem5184712 (s : real -> Prop) (y : real) : (term127 s y) = (term77 s y).
Proof. exact (eq_refl (term127 s y)). Qed.
Lemma lem5184713 (s : real -> Prop) : (term134 s) = (term125 s).
Proof. exact (fun_ext (fun y : real => @lem5184712 s y)). Qed.
Lemma lem5184714 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184715 (s : real -> Prop) : (term135 s) = (term136 s).
Proof. exact (MK_COMB (@lem5184714) (@lem5184713 s)). Qed.
Lemma lem5184716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5184717 (s : real -> Prop) : (term137 s) = (term138 s).
Proof. exact (MK_COMB (@lem5184716) (@lem5184715 s)). Qed.
Lemma lem5184718 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5184719 (s : real -> Prop) : (term139 s) = (term126 s).
Proof. exact (fun_ext (fun y : real => @lem5184718 s y)). Qed.
Lemma lem5184720 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184721 (s : real -> Prop) : (term140 s) = (term141 s).
Proof. exact (MK_COMB (@lem5184720) (@lem5184719 s)). Qed.
Lemma lem5184722 (s : real -> Prop) : (term124 s) = (term142 s).
Proof. exact (MK_COMB (@lem5184717 s) (@lem5184721 s)). Qed.
Lemma lem5184723 (s : real -> Prop) : ((term123 s) = (term124 s)) = ((term117 s) = (term142 s)).
Proof. exact (MK_COMB (@lem5184711 s) (@lem5184722 s)). Qed.
Lemma lem5184724 (s : real -> Prop) : (term117 s) = (term142 s).
Proof. exact (EQ_MP (@lem5184723 s) (@lem5184701 s)). Qed.
Lemma lem5184917 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5184918 (s : real -> Prop) : (term118 s) = (term143 s).
Proof. exact (MK_COMB (@lem5184917 s) (@lem5184724 s)). Qed.
Lemma lem5184919 (s : real -> Prop) : (term94 s) = (term143 s).
Proof. exact (TRANS (@lem5184645 s) (@lem5184918 s)). Qed.
Lemma lem5184920 : term101 = term144.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5184919 s)). Qed.
Lemma lem5184921 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5184922 : term102 = term145.
Proof. exact (MK_COMB (@lem5184921) (@lem5184920)). Qed.
Lemma lem5184972 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5184973 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5184972 real P Q). Qed.
Lemma lem5184974 (s : real -> Prop) : (term146 s) = (term147 s).
Proof. exact (@lem5184973 (term148 s) (term58 s)). Qed.
Lemma lem5184975 (s : real -> Prop) (b : real) : (term149 s b) = (term57 s b).
Proof. exact (eq_refl (term149 s b)). Qed.
Lemma lem5184976 (s : real -> Prop) : (term150 s) = (term58 s).
Proof. exact (fun_ext (fun b : real => @lem5184975 s b)). Qed.
Lemma lem5184977 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184978 (s : real -> Prop) : (term151 s) = (term59 s).
Proof. exact (MK_COMB (@lem5184977) (@lem5184976 s)). Qed.
Lemma lem5184979 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5184980 (s : real -> Prop) : (term146 s) = (term60 s).
Proof. exact (MK_COMB (@lem5184979 s) (@lem5184978 s)). Qed.
Lemma lem5184981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5184982 (s : real -> Prop) : (term152 s) = (term153 s).
Proof. exact (MK_COMB (@lem5184981) (@lem5184980 s)). Qed.
Lemma lem5184983 (s : real -> Prop) (b : real) : (term149 s b) = (term57 s b).
Proof. exact (eq_refl (term149 s b)). Qed.
Lemma lem5184984 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5184985 (s : real -> Prop) (b : real) : (term154 s b) = (term155 s b).
Proof. exact (MK_COMB (@lem5184984 s) (@lem5184983 s b)). Qed.
Lemma lem5184986 (s : real -> Prop) : (term156 s) = (term157 s).
Proof. exact (fun_ext (fun b : real => @lem5184985 s b)). Qed.
Lemma lem5184987 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5184988 (s : real -> Prop) : (term147 s) = (term158 s).
Proof. exact (MK_COMB (@lem5184987) (@lem5184986 s)). Qed.
Lemma lem5184989 (s : real -> Prop) : ((term146 s) = (term147 s)) = ((term60 s) = (term158 s)).
Proof. exact (MK_COMB (@lem5184982 s) (@lem5184988 s)). Qed.
Lemma lem5184990 (s : real -> Prop) : (term60 s) = (term158 s).
Proof. exact (EQ_MP (@lem5184989 s) (@lem5184974 s)). Qed.
Lemma lem5184991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5184992 (s : real -> Prop) : (term84 s) = (term159 s).
Proof. exact (MK_COMB (@lem5184991) (@lem5184990 s)). Qed.
Lemma lem5184994 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5184995 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5184994 real P Q). Qed.
Lemma lem5184996 (s : real -> Prop) (y : real) : (term160 s y) = (term161 s y).
Proof. exact (@lem5184995 (term23 s y) (term70 s y)). Qed.
Lemma lem5184997 (s : real -> Prop) (x : real) (y : real) : (term162 s y x) = (term62 s x y).
Proof. exact (eq_refl (term162 s y x)). Qed.
Lemma lem5184998 (s : real -> Prop) (y : real) : (term163 s y) = (term70 s y).
Proof. exact (fun_ext (fun x : real => @lem5184997 s x y)). Qed.
Lemma lem5184999 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185000 (s : real -> Prop) (y : real) : (term164 s y) = (term71 s y).
Proof. exact (MK_COMB (@lem5184999) (@lem5184998 s y)). Qed.
Lemma lem5185001 (s : real -> Prop) (y : real) : (term75 s y) = (term75 s y).
Proof. exact (eq_refl (term75 s y)). Qed.
Lemma lem5185002 (s : real -> Prop) (y : real) : (term160 s y) = (term77 s y).
Proof. exact (MK_COMB (@lem5185001 s y) (@lem5185000 s y)). Qed.
Lemma lem5185003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185004 (s : real -> Prop) (y : real) : (term165 s y) = (term166 s y).
Proof. exact (MK_COMB (@lem5185003) (@lem5185002 s y)). Qed.
Lemma lem5185005 (s : real -> Prop) (x : real) (y : real) : (term162 s y x) = (term62 s x y).
Proof. exact (eq_refl (term162 s y x)). Qed.
Lemma lem5185006 (s : real -> Prop) (y : real) : (term75 s y) = (term75 s y).
Proof. exact (eq_refl (term75 s y)). Qed.
Lemma lem5185007 (s : real -> Prop) (x : real) (y : real) : (term167 s y x) = (term168 s x y).
Proof. exact (MK_COMB (@lem5185006 s y) (@lem5185005 s x y)). Qed.
Lemma lem5185008 (s : real -> Prop) (y : real) : (term169 s y) = (term170 s y).
Proof. exact (fun_ext (fun x : real => @lem5185007 s x y)). Qed.
Lemma lem5185009 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185010 (s : real -> Prop) (y : real) : (term161 s y) = (term171 s y).
Proof. exact (MK_COMB (@lem5185009) (@lem5185008 s y)). Qed.
Lemma lem5185011 (s : real -> Prop) (y : real) : ((term160 s y) = (term161 s y)) = ((term77 s y) = (term171 s y)).
Proof. exact (MK_COMB (@lem5185004 s y) (@lem5185010 s y)). Qed.
Lemma lem5185012 (s : real -> Prop) (y : real) : (term77 s y) = (term171 s y).
Proof. exact (EQ_MP (@lem5185011 s y) (@lem5184996 s y)). Qed.
Lemma lem5185013 (s : real -> Prop) : (term125 s) = (term172 s).
Proof. exact (fun_ext (fun y : real => @lem5185012 s y)). Qed.
Lemma lem5185014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185015 (s : real -> Prop) : (term136 s) = (term173 s).
Proof. exact (MK_COMB (@lem5185014) (@lem5185013 s)). Qed.
Lemma lem5185016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185017 (s : real -> Prop) : (term138 s) = (term174 s).
Proof. exact (MK_COMB (@lem5185016) (@lem5185015 s)). Qed.
Lemma lem5185018 (s : real -> Prop) : (term141 s) = (term141 s).
Proof. exact (eq_refl (term141 s)). Qed.
Lemma lem5185019 (s : real -> Prop) : (term142 s) = (term175 s).
Proof. exact (MK_COMB (@lem5185017 s) (@lem5185018 s)). Qed.
Lemma lem5185021 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5185022 (P : real -> Prop) (Q : real -> Prop) : (term122 P Q) = (term121 P Q).
Proof. exact (@lem5185021 real P Q). Qed.
Lemma lem5185023 (s : real -> Prop) : (term176 s) = (term177 s).
Proof. exact (@lem5185022 (term172 s) (term126 s)). Qed.
Lemma lem5185024 (s : real -> Prop) (y : real) : (term178 s y) = (term171 s y).
Proof. exact (eq_refl (term178 s y)). Qed.
Lemma lem5185025 (s : real -> Prop) : (term179 s) = (term172 s).
Proof. exact (fun_ext (fun y : real => @lem5185024 s y)). Qed.
Lemma lem5185026 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185027 (s : real -> Prop) : (term180 s) = (term173 s).
Proof. exact (MK_COMB (@lem5185026) (@lem5185025 s)). Qed.
Lemma lem5185028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185029 (s : real -> Prop) : (term181 s) = (term174 s).
Proof. exact (MK_COMB (@lem5185028) (@lem5185027 s)). Qed.
Lemma lem5185030 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5185031 (s : real -> Prop) : (term139 s) = (term126 s).
Proof. exact (fun_ext (fun y : real => @lem5185030 s y)). Qed.
Lemma lem5185032 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185033 (s : real -> Prop) : (term140 s) = (term141 s).
Proof. exact (MK_COMB (@lem5185032) (@lem5185031 s)). Qed.
Lemma lem5185034 (s : real -> Prop) : (term176 s) = (term175 s).
Proof. exact (MK_COMB (@lem5185029 s) (@lem5185033 s)). Qed.
Lemma lem5185035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185036 (s : real -> Prop) : (term182 s) = (term183 s).
Proof. exact (MK_COMB (@lem5185035) (@lem5185034 s)). Qed.
Lemma lem5185037 (s : real -> Prop) (y : real) : (term178 s y) = (term171 s y).
Proof. exact (eq_refl (term178 s y)). Qed.
Lemma lem5185038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185039 (s : real -> Prop) (y : real) : (term184 s y) = (term185 s y).
Proof. exact (MK_COMB (@lem5185038) (@lem5185037 s y)). Qed.
Lemma lem5185040 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5185041 (s : real -> Prop) (y : real) : (term186 s y) = (term187 s y).
Proof. exact (MK_COMB (@lem5185039 s y) (@lem5185040 s y)). Qed.
Lemma lem5185042 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun y : real => @lem5185041 s y)). Qed.
Lemma lem5185043 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185044 (s : real -> Prop) : (term177 s) = (term190 s).
Proof. exact (MK_COMB (@lem5185043) (@lem5185042 s)). Qed.
Lemma lem5185045 (s : real -> Prop) : ((term176 s) = (term177 s)) = ((term175 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5185036 s) (@lem5185044 s)). Qed.
Lemma lem5185046 (s : real -> Prop) : (term175 s) = (term190 s).
Proof. exact (EQ_MP (@lem5185045 s) (@lem5185023 s)). Qed.
Lemma lem5185048 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5185049 (P : real -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem5185048 real P Q). Qed.
Lemma lem5185050 (s : real -> Prop) (y : real) : (term195 s y) = (term196 s y).
Proof. exact (@lem5185049 (term170 s y) (term74 s y)). Qed.
Lemma lem5185051 (s : real -> Prop) (x : real) (y : real) : (term197 s y x) = (term168 s x y).
Proof. exact (eq_refl (term197 s y x)). Qed.
Lemma lem5185052 (s : real -> Prop) (y : real) : (term198 s y) = (term170 s y).
Proof. exact (fun_ext (fun x : real => @lem5185051 s x y)). Qed.
Lemma lem5185053 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185054 (s : real -> Prop) (y : real) : (term199 s y) = (term171 s y).
Proof. exact (MK_COMB (@lem5185053) (@lem5185052 s y)). Qed.
Lemma lem5185055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185056 (s : real -> Prop) (y : real) : (term200 s y) = (term185 s y).
Proof. exact (MK_COMB (@lem5185055) (@lem5185054 s y)). Qed.
Lemma lem5185057 (s : real -> Prop) (y : real) : (term74 s y) = (term74 s y).
Proof. exact (eq_refl (term74 s y)). Qed.
Lemma lem5185058 (s : real -> Prop) (y : real) : (term195 s y) = (term187 s y).
Proof. exact (MK_COMB (@lem5185056 s y) (@lem5185057 s y)). Qed.
Lemma lem5185059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185060 (s : real -> Prop) (y : real) : (term201 s y) = (term202 s y).
Proof. exact (MK_COMB (@lem5185059) (@lem5185058 s y)). Qed.
Lemma lem5185061 (s : real -> Prop) (x : real) (y : real) : (term197 s y x) = (term168 s x y).
Proof. exact (eq_refl (term197 s y x)). Qed.
Lemma lem5185062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185063 (s : real -> Prop) (x : real) (y : real) : (term203 s y x) = (term204 s x y).
Proof. exact (MK_COMB (@lem5185062) (@lem5185061 s x y)). Qed.
Lemma lem5185064 (s : real -> Prop) (y : real) : (term74 s y) = (term74 s y).
Proof. exact (eq_refl (term74 s y)). Qed.
Lemma lem5185065 (x : real) (s : real -> Prop) (y : real) : (term205 x s y) = (term206 x s y).
Proof. exact (MK_COMB (@lem5185063 s x y) (@lem5185064 s y)). Qed.
Lemma lem5185066 (s : real -> Prop) (y : real) : (term207 s y) = (term208 s y).
Proof. exact (fun_ext (fun x : real => @lem5185065 x s y)). Qed.
Lemma lem5185067 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185068 (s : real -> Prop) (y : real) : (term196 s y) = (term209 s y).
Proof. exact (MK_COMB (@lem5185067) (@lem5185066 s y)). Qed.
Lemma lem5185069 (s : real -> Prop) (y : real) : ((term195 s y) = (term196 s y)) = ((term187 s y) = (term209 s y)).
Proof. exact (MK_COMB (@lem5185060 s y) (@lem5185068 s y)). Qed.
Lemma lem5185070 (s : real -> Prop) (y : real) : (term187 s y) = (term209 s y).
Proof. exact (EQ_MP (@lem5185069 s y) (@lem5185050 s y)). Qed.
Lemma lem5185071 (s : real -> Prop) : (term189 s) = (term210 s).
Proof. exact (fun_ext (fun y : real => @lem5185070 s y)). Qed.
Lemma lem5185072 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185073 (s : real -> Prop) : (term190 s) = (term211 s).
Proof. exact (MK_COMB (@lem5185072) (@lem5185071 s)). Qed.
Lemma lem5185074 (s : real -> Prop) : (term175 s) = (term211 s).
Proof. exact (TRANS (@lem5185046 s) (@lem5185073 s)). Qed.
Lemma lem5185075 (s : real -> Prop) : (term142 s) = (term211 s).
Proof. exact (TRANS (@lem5185019 s) (@lem5185074 s)). Qed.
Lemma lem5185076 (s : real -> Prop) : (term143 s) = (term212 s).
Proof. exact (MK_COMB (@lem5184992 s) (@lem5185075 s)). Qed.
Lemma lem5185078 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5185079 (P : real -> Prop) (Q : Prop) : (term215 P Q) = (term216 P Q).
Proof. exact (@lem5185078 real P Q). Qed.
Lemma lem5185080 (s : real -> Prop) : (term217 s) = (term218 s).
Proof. exact (@lem5185079 (term157 s) (term211 s)). Qed.
Lemma lem5185081 (s : real -> Prop) (b : real) : (term219 s b) = (term155 s b).
Proof. exact (eq_refl (term219 s b)). Qed.
Lemma lem5185082 (s : real -> Prop) : (term220 s) = (term157 s).
Proof. exact (fun_ext (fun b : real => @lem5185081 s b)). Qed.
Lemma lem5185083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185084 (s : real -> Prop) : (term221 s) = (term158 s).
Proof. exact (MK_COMB (@lem5185083) (@lem5185082 s)). Qed.
Lemma lem5185085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5185086 (s : real -> Prop) : (term222 s) = (term159 s).
Proof. exact (MK_COMB (@lem5185085) (@lem5185084 s)). Qed.
Lemma lem5185087 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5185088 (s : real -> Prop) : (term217 s) = (term212 s).
Proof. exact (MK_COMB (@lem5185086 s) (@lem5185087 s)). Qed.
Lemma lem5185089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185090 (s : real -> Prop) : (term223 s) = (term224 s).
Proof. exact (MK_COMB (@lem5185089) (@lem5185088 s)). Qed.
Lemma lem5185091 (s : real -> Prop) (b : real) : (term219 s b) = (term155 s b).
Proof. exact (eq_refl (term219 s b)). Qed.
Lemma lem5185092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5185093 (s : real -> Prop) (b : real) : (term225 s b) = (term226 s b).
Proof. exact (MK_COMB (@lem5185092) (@lem5185091 s b)). Qed.
Lemma lem5185094 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5185095 (b : real) (s : real -> Prop) : (term227 b s) = (term228 b s).
Proof. exact (MK_COMB (@lem5185093 s b) (@lem5185094 s)). Qed.
Lemma lem5185096 (s : real -> Prop) : (term229 s) = (term230 s).
Proof. exact (fun_ext (fun b : real => @lem5185095 b s)). Qed.
Lemma lem5185097 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185098 (s : real -> Prop) : (term218 s) = (term231 s).
Proof. exact (MK_COMB (@lem5185097) (@lem5185096 s)). Qed.
Lemma lem5185099 (s : real -> Prop) : ((term217 s) = (term218 s)) = ((term212 s) = (term231 s)).
Proof. exact (MK_COMB (@lem5185090 s) (@lem5185098 s)). Qed.
Lemma lem5185100 (s : real -> Prop) : (term212 s) = (term231 s).
Proof. exact (EQ_MP (@lem5185099 s) (@lem5185080 s)). Qed.
Lemma lem5185102 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5185103 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5185102 real P Q). Qed.
Lemma lem5185104 (b : real) (s : real -> Prop) : (term232 b s) = (term233 b s).
Proof. exact (@lem5185103 (term155 s b) (term210 s)). Qed.
Lemma lem5185105 (s : real -> Prop) (y : real) : (term234 s y) = (term209 s y).
Proof. exact (eq_refl (term234 s y)). Qed.
Lemma lem5185106 (s : real -> Prop) : (term235 s) = (term210 s).
Proof. exact (fun_ext (fun y : real => @lem5185105 s y)). Qed.
Lemma lem5185107 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185108 (s : real -> Prop) : (term236 s) = (term211 s).
Proof. exact (MK_COMB (@lem5185107) (@lem5185106 s)). Qed.
Lemma lem5185109 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5185110 (b : real) (s : real -> Prop) : (term232 b s) = (term228 b s).
Proof. exact (MK_COMB (@lem5185109 s b) (@lem5185108 s)). Qed.
Lemma lem5185111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185112 (b : real) (s : real -> Prop) : (term237 b s) = (term238 b s).
Proof. exact (MK_COMB (@lem5185111) (@lem5185110 b s)). Qed.
Lemma lem5185113 (s : real -> Prop) (y : real) : (term234 s y) = (term209 s y).
Proof. exact (eq_refl (term234 s y)). Qed.
Lemma lem5185114 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5185115 (b : real) (s : real -> Prop) (y : real) : (term239 b s y) = (term240 b s y).
Proof. exact (MK_COMB (@lem5185114 s b) (@lem5185113 s y)). Qed.
Lemma lem5185116 (b : real) (s : real -> Prop) : (term241 b s) = (term242 b s).
Proof. exact (fun_ext (fun y : real => @lem5185115 b s y)). Qed.
Lemma lem5185117 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185118 (b : real) (s : real -> Prop) : (term233 b s) = (term243 b s).
Proof. exact (MK_COMB (@lem5185117) (@lem5185116 b s)). Qed.
Lemma lem5185119 (b : real) (s : real -> Prop) : ((term232 b s) = (term233 b s)) = ((term228 b s) = (term243 b s)).
Proof. exact (MK_COMB (@lem5185112 b s) (@lem5185118 b s)). Qed.
Lemma lem5185120 (b : real) (s : real -> Prop) : (term228 b s) = (term243 b s).
Proof. exact (EQ_MP (@lem5185119 b s) (@lem5185104 b s)). Qed.
Lemma lem5185122 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5185123 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5185122 real P Q). Qed.
Lemma lem5185124 (b : real) (s : real -> Prop) (y : real) : (term244 b s y) = (term245 b s y).
Proof. exact (@lem5185123 (term155 s b) (term208 s y)). Qed.
Lemma lem5185125 (x : real) (s : real -> Prop) (y : real) : (term246 s y x) = (term206 x s y).
Proof. exact (eq_refl (term246 s y x)). Qed.
Lemma lem5185126 (s : real -> Prop) (y : real) : (term247 s y) = (term208 s y).
Proof. exact (fun_ext (fun x : real => @lem5185125 x s y)). Qed.
Lemma lem5185127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185128 (s : real -> Prop) (y : real) : (term248 s y) = (term209 s y).
Proof. exact (MK_COMB (@lem5185127) (@lem5185126 s y)). Qed.
Lemma lem5185129 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5185130 (b : real) (s : real -> Prop) (y : real) : (term244 b s y) = (term240 b s y).
Proof. exact (MK_COMB (@lem5185129 s b) (@lem5185128 s y)). Qed.
Lemma lem5185131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185132 (b : real) (s : real -> Prop) (y : real) : (term249 b s y) = (term250 b s y).
Proof. exact (MK_COMB (@lem5185131) (@lem5185130 b s y)). Qed.
Lemma lem5185133 (x : real) (s : real -> Prop) (y : real) : (term246 s y x) = (term206 x s y).
Proof. exact (eq_refl (term246 s y x)). Qed.
Lemma lem5185134 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5185135 (b : real) (x : real) (s : real -> Prop) (y : real) : (term251 b s y x) = (term252 b x s y).
Proof. exact (MK_COMB (@lem5185134 s b) (@lem5185133 x s y)). Qed.
Lemma lem5185136 (b : real) (s : real -> Prop) (y : real) : (term253 b s y) = (term254 b s y).
Proof. exact (fun_ext (fun x : real => @lem5185135 b x s y)). Qed.
Lemma lem5185137 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185138 (b : real) (s : real -> Prop) (y : real) : (term245 b s y) = (term255 b s y).
Proof. exact (MK_COMB (@lem5185137) (@lem5185136 b s y)). Qed.
Lemma lem5185139 (b : real) (s : real -> Prop) (y : real) : ((term244 b s y) = (term245 b s y)) = ((term240 b s y) = (term255 b s y)).
Proof. exact (MK_COMB (@lem5185132 b s y) (@lem5185138 b s y)). Qed.
Lemma lem5185140 (b : real) (s : real -> Prop) (y : real) : (term240 b s y) = (term255 b s y).
Proof. exact (EQ_MP (@lem5185139 b s y) (@lem5185124 b s y)). Qed.
Lemma lem5185141 (b : real) (s : real -> Prop) : (term242 b s) = (term256 b s).
Proof. exact (fun_ext (fun y : real => @lem5185140 b s y)). Qed.
Lemma lem5185142 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185143 (b : real) (s : real -> Prop) : (term243 b s) = (term257 b s).
Proof. exact (MK_COMB (@lem5185142) (@lem5185141 b s)). Qed.
Lemma lem5185144 (b : real) (s : real -> Prop) : (term228 b s) = (term257 b s).
Proof. exact (TRANS (@lem5185120 b s) (@lem5185143 b s)). Qed.
Lemma lem5185145 (s : real -> Prop) : (term230 s) = (term258 s).
Proof. exact (fun_ext (fun b : real => @lem5185144 b s)). Qed.
Lemma lem5185146 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185147 (s : real -> Prop) : (term231 s) = (term259 s).
Proof. exact (MK_COMB (@lem5185146) (@lem5185145 s)). Qed.
Lemma lem5185148 (s : real -> Prop) : (term212 s) = (term259 s).
Proof. exact (TRANS (@lem5185100 s) (@lem5185147 s)). Qed.
Lemma lem5185149 (s : real -> Prop) : (term143 s) = (term259 s).
Proof. exact (TRANS (@lem5185076 s) (@lem5185148 s)). Qed.
Lemma lem5185150 : term144 = term260.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5185149 s)). Qed.
Lemma lem5185151 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5185152 : term145 = term261.
Proof. exact (MK_COMB (@lem5185151) (@lem5185150)). Qed.
Lemma lem5185153 : term102 = term261.
Proof. exact (TRANS (@lem5184922) (@lem5185152)). Qed.
Lemma lem5185154 : term10 = term261.
Proof. exact (TRANS (@lem5184621) (@lem5185153)). Qed.
Lemma lem5185155 (h1 : term10) : term261.
Proof. exact (EQ_MP (@lem5185154) (@lem5184537 h1)). Qed.
Lemma lem5185162 (x : real) (y : real) (z : real) : (term262 x y z) = (term263 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5185163 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5185164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185165 (x : real) (y : real) (z : real) : (term264 x y z) = (term265 x y z).
Proof. exact (MK_COMB (@lem5185164) (@lem5185162 x y z)). Qed.
Lemma lem5185166 (y : real) (x : real) (z : real) : (term266 y x z) = (term267 y x z).
Proof. exact (MK_COMB (@lem5185165 x y z) (@lem5185163 x z)). Qed.
Lemma lem5185167 (y : real) (x : real) (z : real) : (term43 y x z) = (term266 y x z).
Proof. exact (@lem17265 (term268 x y z) (real_le x z)). Qed.
Lemma lem5185168 (y : real) (x : real) (z : real) : (term43 y x z) = (term267 y x z).
Proof. exact (TRANS (@lem5185167 y x z) (@lem5185166 y x z)). Qed.
Lemma lem5185169 (y : real) (x : real) : (term44 y x) = (term269 y x).
Proof. exact (fun_ext (fun z : real => @lem5185168 y x z)). Qed.
Lemma lem5185170 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185171 (y : real) (x : real) : (term45 y x) = (term270 y x).
Proof. exact (MK_COMB (@lem5185170) (@lem5185169 y x)). Qed.
Lemma lem5185172 (x : real) : (term46 x) = (term271 x).
Proof. exact (fun_ext (fun y : real => @lem5185171 y x)). Qed.
Lemma lem5185173 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185174 (x : real) : (term47 x) = (term272 x).
Proof. exact (MK_COMB (@lem5185173) (@lem5185172 x)). Qed.
Lemma lem5185175 : term48 = term273.
Proof. exact (fun_ext (fun x : real => @lem5185174 x)). Qed.
Lemma lem5185176 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185237 : term49 = term274.
Proof. exact (MK_COMB (@lem5185176) (@lem5185175)). Qed.
Lemma lem5185238 (h1 : term49) : term274.
Proof. exact (EQ_MP (@lem5185237) (@lem5184538 h1)). Qed.
Lemma lem5185241 (s : real -> Prop) : (term275 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5185248 (s : real -> Prop) (x : real) (b : real) : (term61 s x b) = (term62 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5185249 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5185250 (s : real -> Prop) (b : real) : (term65 s b) = (term66 s b).
Proof. exact (@lem5185249 (term25 s b)). Qed.
Lemma lem5185251 (s : real -> Prop) (x : real) (b : real) : (term67 s b x) = (term24 s x b).
Proof. exact (eq_refl (term67 s b x)). Qed.
Lemma lem5185252 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5185253 (s : real -> Prop) (x : real) (b : real) : (term68 s b x) = (term61 s x b).
Proof. exact (MK_COMB (@lem5185252) (@lem5185251 s x b)). Qed.
Lemma lem5185254 (s : real -> Prop) (x : real) (b : real) : (term68 s b x) = (term62 s x b).
Proof. exact (TRANS (@lem5185253 s x b) (@lem5185248 s x b)). Qed.
Lemma lem5185255 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5185254 s x b)). Qed.
Lemma lem5185256 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185257 (s : real -> Prop) (b : real) : (term66 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5185256) (@lem5185255 s b)). Qed.
Lemma lem5185258 (s : real -> Prop) (b : real) : (term65 s b) = (term71 s b).
Proof. exact (TRANS (@lem5185250 s b) (@lem5185257 s b)). Qed.
Lemma lem5185259 (P : real -> Prop) : (term276 P) = (term277 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5185260 (s : real -> Prop) : (term278 s) = (term279 s).
Proof. exact (@lem5185259 (term36 s)). Qed.
Lemma lem5185261 (s : real -> Prop) (b : real) : (term280 s b) = (term26 s b).
Proof. exact (eq_refl (term280 s b)). Qed.
Lemma lem5185262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5185263 (s : real -> Prop) (b : real) : (term281 s b) = (term65 s b).
Proof. exact (MK_COMB (@lem5185262) (@lem5185261 s b)). Qed.
Lemma lem5185264 (s : real -> Prop) (b : real) : (term281 s b) = (term71 s b).
Proof. exact (TRANS (@lem5185263 s b) (@lem5185258 s b)). Qed.
Lemma lem5185265 (s : real -> Prop) : (term282 s) = (term283 s).
Proof. exact (fun_ext (fun b : real => @lem5185264 s b)). Qed.
Lemma lem5185266 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185267 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5185266) (@lem5185265 s)). Qed.
Lemma lem5185268 (s : real -> Prop) : (term278 s) = (term284 s).
Proof. exact (TRANS (@lem5185260 s) (@lem5185267 s)). Qed.
Lemma lem5185269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185270 (s : real -> Prop) : (term285 s) = (term286 s).
Proof. exact (MK_COMB (@lem5185269) (@lem5185241 s)). Qed.
Lemma lem5185271 (s : real -> Prop) : (term287 s) = (term288 s).
Proof. exact (MK_COMB (@lem5185270 s) (@lem5185268 s)). Qed.
Lemma lem5185272 (s : real -> Prop) : (term289 s) = (term287 s).
Proof. exact (@lem17045 (term148 s) (term37 s)). Qed.
Lemma lem5185273 (s : real -> Prop) : (term289 s) = (term288 s).
Proof. exact (TRANS (@lem5185272 s) (@lem5185271 s)). Qed.
Lemma lem5185280 (x : real) (s : real -> Prop) : (term31 x s) = (term290 x s).
Proof. exact (@lem17265 (@IN real x s) (term291 x s)). Qed.
Lemma lem5185281 (s : real -> Prop) : (term32 s) = (term292 s).
Proof. exact (fun_ext (fun x : real => @lem5185280 x s)). Qed.
Lemma lem5185282 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185283 (s : real -> Prop) : (term33 s) = (term293 s).
Proof. exact (MK_COMB (@lem5185282) (@lem5185281 s)). Qed.
Lemma lem5185290 (s : real -> Prop) (x : real) (b : real) : (term61 s x b) = (term62 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5185291 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5185292 (s : real -> Prop) (b : real) : (term65 s b) = (term66 s b).
Proof. exact (@lem5185291 (term25 s b)). Qed.
Lemma lem5185293 (s : real -> Prop) (x : real) (b : real) : (term67 s b x) = (term24 s x b).
Proof. exact (eq_refl (term67 s b x)). Qed.
Lemma lem5185294 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5185295 (s : real -> Prop) (x : real) (b : real) : (term68 s b x) = (term61 s x b).
Proof. exact (MK_COMB (@lem5185294) (@lem5185293 s x b)). Qed.
Lemma lem5185296 (s : real -> Prop) (x : real) (b : real) : (term68 s b x) = (term62 s x b).
Proof. exact (TRANS (@lem5185295 s x b) (@lem5185290 s x b)). Qed.
Lemma lem5185297 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5185296 s x b)). Qed.
Lemma lem5185298 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185299 (s : real -> Prop) (b : real) : (term66 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5185298) (@lem5185297 s b)). Qed.
Lemma lem5185300 (s : real -> Prop) (b : real) : (term65 s b) = (term71 s b).
Proof. exact (TRANS (@lem5185292 s b) (@lem5185299 s b)). Qed.
Lemma lem5185301 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5185302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185303 (s : real -> Prop) (b : real) : (term294 s b) = (term295 s b).
Proof. exact (MK_COMB (@lem5185302) (@lem5185300 s b)). Qed.
Lemma lem5185304 (s : real -> Prop) (b : real) : (term296 s b) = (term297 s b).
Proof. exact (MK_COMB (@lem5185303 s b) (@lem5185301 s b)). Qed.
Lemma lem5185305 (s : real -> Prop) (b : real) : (term28 s b) = (term296 s b).
Proof. exact (@lem17265 (term26 s b) (term23 s b)). Qed.
Lemma lem5185306 (s : real -> Prop) (b : real) : (term28 s b) = (term297 s b).
Proof. exact (TRANS (@lem5185305 s b) (@lem5185304 s b)). Qed.
Lemma lem5185307 (s : real -> Prop) : (term29 s) = (term298 s).
Proof. exact (fun_ext (fun b : real => @lem5185306 s b)). Qed.
Lemma lem5185308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185309 (s : real -> Prop) : (term30 s) = (term299 s).
Proof. exact (MK_COMB (@lem5185308) (@lem5185307 s)). Qed.
Lemma lem5185310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5185311 (s : real -> Prop) : (term34 s) = (term300 s).
Proof. exact (MK_COMB (@lem5185310) (@lem5185283 s)). Qed.
Lemma lem5185312 (s : real -> Prop) : (term35 s) = (term301 s).
Proof. exact (MK_COMB (@lem5185311 s) (@lem5185309 s)). Qed.
Lemma lem5185313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185314 (s : real -> Prop) : (term302 s) = (term303 s).
Proof. exact (MK_COMB (@lem5185313) (@lem5185273 s)). Qed.
Lemma lem5185315 (s : real -> Prop) : (term304 s) = (term305 s).
Proof. exact (MK_COMB (@lem5185314 s) (@lem5185312 s)). Qed.
Lemma lem5185316 (s : real -> Prop) : (term41 s) = (term304 s).
Proof. exact (@lem17265 (term39 s) (term35 s)). Qed.
Lemma lem5185317 (s : real -> Prop) : (term41 s) = (term305 s).
Proof. exact (TRANS (@lem5185316 s) (@lem5185315 s)). Qed.
Lemma lem5185318 : term42 = term306.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5185317 s)). Qed.
Lemma lem5185319 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5185320 : term17 = term307.
Proof. exact (MK_COMB (@lem5185319) (@lem5185318)). Qed.
Lemma lem5185567 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5185568 (P : type1626) : (term310 P) = (term311 P).
Proof. exact (@lem5185567 real real P). Qed.
Lemma lem5185569 (s : real -> Prop) : (term312 s) = (term313 s).
Proof. exact (@lem5185568 (term314 s)). Qed.
Lemma lem5185570 (s : real -> Prop) (b : real) : (term315 s b) = (term70 s b).
Proof. exact (eq_refl (term315 s b)). Qed.
Lemma lem5185571 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5185572 (s : real -> Prop) (b : real) (x : real) : (term316 s b x) = (term162 s b x).
Proof. exact (MK_COMB (@lem5185570 s b) (@lem5185571 x)). Qed.
Lemma lem5185573 (s : real -> Prop) (x : real) (b : real) : (term162 s b x) = (term62 s x b).
Proof. exact (eq_refl (term162 s b x)). Qed.
Lemma lem5185574 (s : real -> Prop) (x : real) (b : real) : (term316 s b x) = (term62 s x b).
Proof. exact (TRANS (@lem5185572 s b x) (@lem5185573 s x b)). Qed.
Lemma lem5185575 (s : real -> Prop) (b : real) : (term317 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5185574 s x b)). Qed.
Lemma lem5185576 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185577 (s : real -> Prop) (b : real) : (term318 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5185576) (@lem5185575 s b)). Qed.
Lemma lem5185578 (s : real -> Prop) : (term319 s) = (term283 s).
Proof. exact (fun_ext (fun b : real => @lem5185577 s b)). Qed.
Lemma lem5185579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185580 (s : real -> Prop) : (term312 s) = (term284 s).
Proof. exact (MK_COMB (@lem5185579) (@lem5185578 s)). Qed.
Lemma lem5185581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185582 (s : real -> Prop) : (term320 s) = (term321 s).
Proof. exact (MK_COMB (@lem5185581) (@lem5185580 s)). Qed.
Lemma lem5185583 (s : real -> Prop) (b : real) : (term315 s b) = (term70 s b).
Proof. exact (eq_refl (term315 s b)). Qed.
Lemma lem5185584 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5185585 (s : real -> Prop) (x : real -> real) (b : real) : (term322 s x b) = (term323 s x b).
Proof. exact (MK_COMB (@lem5185583 s b) (@lem5185584 x b)). Qed.
Lemma lem5185586 (s : real -> Prop) (x : real -> real) (b : real) : (term323 s x b) = (term324 s x b).
Proof. exact (eq_refl (term323 s x b)). Qed.
Lemma lem5185587 (s : real -> Prop) (x : real -> real) (b : real) : (term322 s x b) = (term324 s x b).
Proof. exact (TRANS (@lem5185585 s x b) (@lem5185586 s x b)). Qed.
Lemma lem5185588 (s : real -> Prop) (x : real -> real) : (term325 s x) = (term326 s x).
Proof. exact (fun_ext (fun b : real => @lem5185587 s x b)). Qed.
Lemma lem5185589 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185590 (s : real -> Prop) (x : real -> real) : (term327 s x) = (term328 s x).
Proof. exact (MK_COMB (@lem5185589) (@lem5185588 s x)). Qed.
Lemma lem5185591 (s : real -> Prop) : (term329 s) = (term330 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185590 s x)). Qed.
Lemma lem5185592 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185593 (s : real -> Prop) : (term313 s) = (term331 s).
Proof. exact (MK_COMB (@lem5185592) (@lem5185591 s)). Qed.
Lemma lem5185594 (s : real -> Prop) : ((term312 s) = (term313 s)) = ((term284 s) = (term331 s)).
Proof. exact (MK_COMB (@lem5185582 s) (@lem5185593 s)). Qed.
Lemma lem5185595 (s : real -> Prop) : (term284 s) = (term331 s).
Proof. exact (EQ_MP (@lem5185594 s) (@lem5185569 s)). Qed.
Lemma lem5185596 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5185597 (s : real -> Prop) : (term288 s) = (term332 s).
Proof. exact (MK_COMB (@lem5185596 s) (@lem5185595 s)). Qed.
Lemma lem5185599 {A : Type'} (P : Prop) (Q : A -> Prop) : (term333 A P Q) = (term334 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5185600 (P : Prop) (Q : type1028) : (term335 P Q) = (term336 P Q).
Proof. exact (@lem5185599 (real -> real) P Q). Qed.
Lemma lem5185601 (s : real -> Prop) : (term337 s) = (term338 s).
Proof. exact (@lem5185600 (s = (@EMPTY real)) (term330 s)). Qed.
Lemma lem5185602 (s : real -> Prop) (x : real -> real) : (term339 s x) = (term328 s x).
Proof. exact (eq_refl (term339 s x)). Qed.
Lemma lem5185603 (s : real -> Prop) : (term340 s) = (term330 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185602 s x)). Qed.
Lemma lem5185604 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185605 (s : real -> Prop) : (term341 s) = (term331 s).
Proof. exact (MK_COMB (@lem5185604) (@lem5185603 s)). Qed.
Lemma lem5185606 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5185607 (s : real -> Prop) : (term337 s) = (term332 s).
Proof. exact (MK_COMB (@lem5185606 s) (@lem5185605 s)). Qed.
Lemma lem5185608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185609 (s : real -> Prop) : (term342 s) = (term343 s).
Proof. exact (MK_COMB (@lem5185608) (@lem5185607 s)). Qed.
Lemma lem5185610 (s : real -> Prop) (x : real -> real) : (term339 s x) = (term328 s x).
Proof. exact (eq_refl (term339 s x)). Qed.
Lemma lem5185611 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5185612 (s : real -> Prop) (x : real -> real) : (term344 s x) = (term345 s x).
Proof. exact (MK_COMB (@lem5185611 s) (@lem5185610 s x)). Qed.
Lemma lem5185613 (s : real -> Prop) : (term346 s) = (term347 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185612 s x)). Qed.
Lemma lem5185614 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185615 (s : real -> Prop) : (term338 s) = (term348 s).
Proof. exact (MK_COMB (@lem5185614) (@lem5185613 s)). Qed.
Lemma lem5185616 (s : real -> Prop) : ((term337 s) = (term338 s)) = ((term332 s) = (term348 s)).
Proof. exact (MK_COMB (@lem5185609 s) (@lem5185615 s)). Qed.
Lemma lem5185617 (s : real -> Prop) : (term332 s) = (term348 s).
Proof. exact (EQ_MP (@lem5185616 s) (@lem5185601 s)). Qed.
Lemma lem5185618 (s : real -> Prop) : (term288 s) = (term348 s).
Proof. exact (TRANS (@lem5185597 s) (@lem5185617 s)). Qed.
Lemma lem5185619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185620 (s : real -> Prop) : (term303 s) = (term349 s).
Proof. exact (MK_COMB (@lem5185619) (@lem5185618 s)). Qed.
Lemma lem5185622 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5185623 (P : real -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem5185622 real P Q). Qed.
Lemma lem5185624 (s : real -> Prop) (b : real) : (term350 s b) = (term351 s b).
Proof. exact (@lem5185623 (term70 s b) (term23 s b)). Qed.
Lemma lem5185625 (s : real -> Prop) (x : real) (b : real) : (term162 s b x) = (term62 s x b).
Proof. exact (eq_refl (term162 s b x)). Qed.
Lemma lem5185626 (s : real -> Prop) (b : real) : (term163 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5185625 s x b)). Qed.
Lemma lem5185627 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185628 (s : real -> Prop) (b : real) : (term164 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5185627) (@lem5185626 s b)). Qed.
Lemma lem5185629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185630 (s : real -> Prop) (b : real) : (term352 s b) = (term295 s b).
Proof. exact (MK_COMB (@lem5185629) (@lem5185628 s b)). Qed.
Lemma lem5185631 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5185632 (s : real -> Prop) (b : real) : (term350 s b) = (term297 s b).
Proof. exact (MK_COMB (@lem5185630 s b) (@lem5185631 s b)). Qed.
Lemma lem5185633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185634 (s : real -> Prop) (b : real) : (term353 s b) = (term354 s b).
Proof. exact (MK_COMB (@lem5185633) (@lem5185632 s b)). Qed.
Lemma lem5185635 (s : real -> Prop) (x : real) (b : real) : (term162 s b x) = (term62 s x b).
Proof. exact (eq_refl (term162 s b x)). Qed.
Lemma lem5185636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185637 (s : real -> Prop) (x : real) (b : real) : (term355 s b x) = (term356 s x b).
Proof. exact (MK_COMB (@lem5185636) (@lem5185635 s x b)). Qed.
Lemma lem5185638 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5185639 (x : real) (s : real -> Prop) (b : real) : (term357 x s b) = (term358 x s b).
Proof. exact (MK_COMB (@lem5185637 s x b) (@lem5185638 s b)). Qed.
Lemma lem5185640 (s : real -> Prop) (b : real) : (term359 s b) = (term360 s b).
Proof. exact (fun_ext (fun x : real => @lem5185639 x s b)). Qed.
Lemma lem5185641 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185642 (s : real -> Prop) (b : real) : (term351 s b) = (term361 s b).
Proof. exact (MK_COMB (@lem5185641) (@lem5185640 s b)). Qed.
Lemma lem5185643 (s : real -> Prop) (b : real) : ((term350 s b) = (term351 s b)) = ((term297 s b) = (term361 s b)).
Proof. exact (MK_COMB (@lem5185634 s b) (@lem5185642 s b)). Qed.
Lemma lem5185644 (s : real -> Prop) (b : real) : (term297 s b) = (term361 s b).
Proof. exact (EQ_MP (@lem5185643 s b) (@lem5185624 s b)). Qed.
Lemma lem5185645 (s : real -> Prop) : (term298 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5185644 s b)). Qed.
Lemma lem5185646 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185647 (s : real -> Prop) : (term299 s) = (term363 s).
Proof. exact (MK_COMB (@lem5185646) (@lem5185645 s)). Qed.
Lemma lem5185649 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5185650 (P : type1626) : (term310 P) = (term311 P).
Proof. exact (@lem5185649 real real P). Qed.
Lemma lem5185651 (s : real -> Prop) : (term364 s) = (term365 s).
Proof. exact (@lem5185650 (term366 s)). Qed.
Lemma lem5185652 (s : real -> Prop) (b : real) : (term367 s b) = (term360 s b).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5185653 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5185654 (s : real -> Prop) (b : real) (x : real) : (term368 s b x) = (term369 s b x).
Proof. exact (MK_COMB (@lem5185652 s b) (@lem5185653 x)). Qed.
Lemma lem5185655 (x : real) (s : real -> Prop) (b : real) : (term369 s b x) = (term358 x s b).
Proof. exact (eq_refl (term369 s b x)). Qed.
Lemma lem5185656 (x : real) (s : real -> Prop) (b : real) : (term368 s b x) = (term358 x s b).
Proof. exact (TRANS (@lem5185654 s b x) (@lem5185655 x s b)). Qed.
Lemma lem5185657 (s : real -> Prop) (b : real) : (term370 s b) = (term360 s b).
Proof. exact (fun_ext (fun x : real => @lem5185656 x s b)). Qed.
Lemma lem5185658 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5185659 (s : real -> Prop) (b : real) : (term371 s b) = (term361 s b).
Proof. exact (MK_COMB (@lem5185658) (@lem5185657 s b)). Qed.
Lemma lem5185660 (s : real -> Prop) : (term372 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5185659 s b)). Qed.
Lemma lem5185661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185662 (s : real -> Prop) : (term364 s) = (term363 s).
Proof. exact (MK_COMB (@lem5185661) (@lem5185660 s)). Qed.
Lemma lem5185663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185664 (s : real -> Prop) : (term373 s) = (term374 s).
Proof. exact (MK_COMB (@lem5185663) (@lem5185662 s)). Qed.
Lemma lem5185665 (s : real -> Prop) (b : real) : (term367 s b) = (term360 s b).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5185666 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5185667 (s : real -> Prop) (x : real -> real) (b : real) : (term375 s x b) = (term376 s x b).
Proof. exact (MK_COMB (@lem5185665 s b) (@lem5185666 x b)). Qed.
Lemma lem5185668 (x : real -> real) (s : real -> Prop) (b : real) : (term376 s x b) = (term377 x s b).
Proof. exact (eq_refl (term376 s x b)). Qed.
Lemma lem5185669 (x : real -> real) (s : real -> Prop) (b : real) : (term375 s x b) = (term377 x s b).
Proof. exact (TRANS (@lem5185667 s x b) (@lem5185668 x s b)). Qed.
Lemma lem5185670 (x : real -> real) (s : real -> Prop) : (term378 s x) = (term379 x s).
Proof. exact (fun_ext (fun b : real => @lem5185669 x s b)). Qed.
Lemma lem5185671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185672 (x : real -> real) (s : real -> Prop) : (term380 s x) = (term381 x s).
Proof. exact (MK_COMB (@lem5185671) (@lem5185670 x s)). Qed.
Lemma lem5185673 (s : real -> Prop) : (term382 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185672 x s)). Qed.
Lemma lem5185674 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185675 (s : real -> Prop) : (term365 s) = (term384 s).
Proof. exact (MK_COMB (@lem5185674) (@lem5185673 s)). Qed.
Lemma lem5185676 (s : real -> Prop) : ((term364 s) = (term365 s)) = ((term363 s) = (term384 s)).
Proof. exact (MK_COMB (@lem5185664 s) (@lem5185675 s)). Qed.
Lemma lem5185677 (s : real -> Prop) : (term363 s) = (term384 s).
Proof. exact (EQ_MP (@lem5185676 s) (@lem5185651 s)). Qed.
Lemma lem5185678 (s : real -> Prop) : (term299 s) = (term384 s).
Proof. exact (TRANS (@lem5185647 s) (@lem5185677 s)). Qed.
Lemma lem5185679 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (eq_refl (term300 s)). Qed.
Lemma lem5185680 (s : real -> Prop) : (term301 s) = (term385 s).
Proof. exact (MK_COMB (@lem5185679 s) (@lem5185678 s)). Qed.
Lemma lem5185682 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5185683 (P : Prop) (Q : type1028) : (term386 P Q) = (term387 P Q).
Proof. exact (@lem5185682 (real -> real) P Q). Qed.
Lemma lem5185684 (s : real -> Prop) : (term388 s) = (term389 s).
Proof. exact (@lem5185683 (term293 s) (term383 s)). Qed.
Lemma lem5185685 (x : real -> real) (s : real -> Prop) : (term390 s x) = (term381 x s).
Proof. exact (eq_refl (term390 s x)). Qed.
Lemma lem5185686 (s : real -> Prop) : (term391 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185685 x s)). Qed.
Lemma lem5185687 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185688 (s : real -> Prop) : (term392 s) = (term384 s).
Proof. exact (MK_COMB (@lem5185687) (@lem5185686 s)). Qed.
Lemma lem5185689 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (eq_refl (term300 s)). Qed.
Lemma lem5185690 (s : real -> Prop) : (term388 s) = (term385 s).
Proof. exact (MK_COMB (@lem5185689 s) (@lem5185688 s)). Qed.
Lemma lem5185691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185692 (s : real -> Prop) : (term393 s) = (term394 s).
Proof. exact (MK_COMB (@lem5185691) (@lem5185690 s)). Qed.
Lemma lem5185693 (x : real -> real) (s : real -> Prop) : (term390 s x) = (term381 x s).
Proof. exact (eq_refl (term390 s x)). Qed.
Lemma lem5185694 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (eq_refl (term300 s)). Qed.
Lemma lem5185695 (x : real -> real) (s : real -> Prop) : (term395 s x) = (term396 x s).
Proof. exact (MK_COMB (@lem5185694 s) (@lem5185693 x s)). Qed.
Lemma lem5185696 (s : real -> Prop) : (term397 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185695 x s)). Qed.
Lemma lem5185697 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185698 (s : real -> Prop) : (term389 s) = (term399 s).
Proof. exact (MK_COMB (@lem5185697) (@lem5185696 s)). Qed.
Lemma lem5185699 (s : real -> Prop) : ((term388 s) = (term389 s)) = ((term385 s) = (term399 s)).
Proof. exact (MK_COMB (@lem5185692 s) (@lem5185698 s)). Qed.
Lemma lem5185700 (s : real -> Prop) : (term385 s) = (term399 s).
Proof. exact (EQ_MP (@lem5185699 s) (@lem5185684 s)). Qed.
Lemma lem5185701 (s : real -> Prop) : (term301 s) = (term399 s).
Proof. exact (TRANS (@lem5185680 s) (@lem5185700 s)). Qed.
Lemma lem5185702 (s : real -> Prop) : (term305 s) = (term400 s).
Proof. exact (MK_COMB (@lem5185620 s) (@lem5185701 s)). Qed.
Lemma lem5185704 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5185705 (P : type1028) (Q : type1028) : (term401 P Q) = (term402 P Q).
Proof. exact (@lem5185704 (real -> real) P Q). Qed.
Lemma lem5185706 (s : real -> Prop) : (term403 s) = (term404 s).
Proof. exact (@lem5185705 (term347 s) (term398 s)). Qed.
Lemma lem5185707 (s : real -> Prop) (x : real -> real) : (term405 s x) = (term345 s x).
Proof. exact (eq_refl (term405 s x)). Qed.
Lemma lem5185708 (s : real -> Prop) : (term406 s) = (term347 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185707 s x)). Qed.
Lemma lem5185709 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185710 (s : real -> Prop) : (term407 s) = (term348 s).
Proof. exact (MK_COMB (@lem5185709) (@lem5185708 s)). Qed.
Lemma lem5185711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185712 (s : real -> Prop) : (term408 s) = (term349 s).
Proof. exact (MK_COMB (@lem5185711) (@lem5185710 s)). Qed.
Lemma lem5185713 (x : real -> real) (s : real -> Prop) : (term409 s x) = (term396 x s).
Proof. exact (eq_refl (term409 s x)). Qed.
Lemma lem5185714 (s : real -> Prop) : (term410 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185713 x s)). Qed.
Lemma lem5185715 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185716 (s : real -> Prop) : (term411 s) = (term399 s).
Proof. exact (MK_COMB (@lem5185715) (@lem5185714 s)). Qed.
Lemma lem5185717 (s : real -> Prop) : (term403 s) = (term400 s).
Proof. exact (MK_COMB (@lem5185712 s) (@lem5185716 s)). Qed.
Lemma lem5185718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185719 (s : real -> Prop) : (term412 s) = (term413 s).
Proof. exact (MK_COMB (@lem5185718) (@lem5185717 s)). Qed.
Lemma lem5185720 (s : real -> Prop) (x : real -> real) : (term405 s x) = (term345 s x).
Proof. exact (eq_refl (term405 s x)). Qed.
Lemma lem5185721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185722 (s : real -> Prop) (x : real -> real) : (term414 s x) = (term415 s x).
Proof. exact (MK_COMB (@lem5185721) (@lem5185720 s x)). Qed.
Lemma lem5185723 (x : real -> real) (s : real -> Prop) : (term409 s x) = (term396 x s).
Proof. exact (eq_refl (term409 s x)). Qed.
Lemma lem5185724 (x : real -> real) (s : real -> Prop) : (term416 s x) = (term417 x s).
Proof. exact (MK_COMB (@lem5185722 s x) (@lem5185723 x s)). Qed.
Lemma lem5185725 (s : real -> Prop) : (term418 s) = (term419 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185724 x s)). Qed.
Lemma lem5185726 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185727 (s : real -> Prop) : (term404 s) = (term420 s).
Proof. exact (MK_COMB (@lem5185726) (@lem5185725 s)). Qed.
Lemma lem5185728 (s : real -> Prop) : ((term403 s) = (term404 s)) = ((term400 s) = (term420 s)).
Proof. exact (MK_COMB (@lem5185719 s) (@lem5185727 s)). Qed.
Lemma lem5185729 (s : real -> Prop) : (term400 s) = (term420 s).
Proof. exact (EQ_MP (@lem5185728 s) (@lem5185706 s)). Qed.
Lemma lem5185730 (s : real -> Prop) : (term305 s) = (term420 s).
Proof. exact (TRANS (@lem5185702 s) (@lem5185729 s)). Qed.
Lemma lem5185731 : term306 = term421.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5185730 s)). Qed.
Lemma lem5185732 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5185733 : term307 = term422.
Proof. exact (MK_COMB (@lem5185732) (@lem5185731)). Qed.
Lemma lem5185735 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5185736 (P : type1017) : (term423 P) = (term424 P).
Proof. exact (@lem5185735 (real -> Prop) (real -> real) P). Qed.
Lemma lem5185737 : term425 = term426.
Proof. exact (@lem5185736 term427). Qed.
Lemma lem5185738 (s : real -> Prop) : (term428 s) = (term419 s).
Proof. exact (eq_refl (term428 s)). Qed.
Lemma lem5185739 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5185740 (s : real -> Prop) (x : real -> real) : (term429 s x) = (term430 s x).
Proof. exact (MK_COMB (@lem5185738 s) (@lem5185739 x)). Qed.
Lemma lem5185741 (x : real -> real) (s : real -> Prop) : (term430 s x) = (term417 x s).
Proof. exact (eq_refl (term430 s x)). Qed.
Lemma lem5185742 (x : real -> real) (s : real -> Prop) : (term429 s x) = (term417 x s).
Proof. exact (TRANS (@lem5185740 s x) (@lem5185741 x s)). Qed.
Lemma lem5185743 (s : real -> Prop) : (term431 s) = (term419 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5185742 x s)). Qed.
Lemma lem5185744 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5185745 (s : real -> Prop) : (term432 s) = (term420 s).
Proof. exact (MK_COMB (@lem5185744) (@lem5185743 s)). Qed.
Lemma lem5185746 : term433 = term421.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5185745 s)). Qed.
Lemma lem5185747 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5185748 : term425 = term422.
Proof. exact (MK_COMB (@lem5185747) (@lem5185746)). Qed.
Lemma lem5185749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5185750 : term434 = term435.
Proof. exact (MK_COMB (@lem5185749) (@lem5185748)). Qed.
Lemma lem5185751 (s : real -> Prop) : (term428 s) = (term419 s).
Proof. exact (eq_refl (term428 s)). Qed.
Lemma lem5185752 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5185753 (x : type1021) (s : real -> Prop) : (term436 x s) = (term437 x s).
Proof. exact (MK_COMB (@lem5185751 s) (@lem5185752 x s)). Qed.
Lemma lem5185754 (x : type1021) (s : real -> Prop) : (term437 x s) = (term438 x s).
Proof. exact (eq_refl (term437 x s)). Qed.
Lemma lem5185755 (x : type1021) (s : real -> Prop) : (term436 x s) = (term438 x s).
Proof. exact (TRANS (@lem5185753 x s) (@lem5185754 x s)). Qed.
Lemma lem5185756 (x : type1021) : (term439 x) = (term440 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5185755 x s)). Qed.
Lemma lem5185757 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5185758 (x : type1021) : (term441 x) = (term442 x).
Proof. exact (MK_COMB (@lem5185757) (@lem5185756 x)). Qed.
Lemma lem5185759 : term443 = term444.
Proof. exact (fun_ext (fun x : type1021 => @lem5185758 x)). Qed.
Lemma lem5185760 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5185761 : term426 = term445.
Proof. exact (MK_COMB (@lem5185760) (@lem5185759)). Qed.
Lemma lem5185762 : (term425 = term426) = (term422 = term445).
Proof. exact (MK_COMB (@lem5185750) (@lem5185761)). Qed.
Lemma lem5185763 : term422 = term445.
Proof. exact (EQ_MP (@lem5185762) (@lem5185737)). Qed.
Lemma lem5185765 : term307 = term445.
Proof. exact (TRANS (@lem5185733) (@lem5185763)). Qed.
Lemma lem5185766 : term17 = term445.
Proof. exact (TRANS (@lem5185320) (@lem5185765)). Qed.
Lemma lem5185767 (h1 : term17) : term445.
Proof. exact (EQ_MP (@lem5185766) (@lem5184539 h1)). Qed.
Lemma lem5185768 (x : type1021) (h1 : term442 x) : term442 x.
Proof. exact (h1). Qed.
Lemma lem5185769 (s : real -> Prop) (h1 : term259 s) : term259 s.
Proof. exact (h1). Qed.
Lemma lem5185770 (b : real) (s : real -> Prop) (h1 : term257 b s) : term257 b s.
Proof. exact (h1). Qed.
Lemma lem5185771 (b : real) (s : real -> Prop) (y : real) (h1 : term255 b s y) : term255 b s y.
Proof. exact (h1). Qed.
Lemma lem5185772 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term252 b x' s y.
Proof. exact (h1). Qed.
Lemma lem5185797 (y : real) (x : real) (z : real) : (term267 y x z) = (term267 y x z).
Proof. exact (eq_refl (term267 y x z)). Qed.
Lemma lem5185798 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (fun_ext (fun z : real => @lem5185797 y x z)). Qed.
Lemma lem5185799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185800 (y : real) (x : real) : (term270 y x) = (term270 y x).
Proof. exact (MK_COMB (@lem5185799) (@lem5185798 y x)). Qed.
Lemma lem5185801 (x : real) : (term271 x) = (term271 x).
Proof. exact (fun_ext (fun y : real => @lem5185800 y x)). Qed.
Lemma lem5185802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185803 (x : real) : (term272 x) = (term272 x).
Proof. exact (MK_COMB (@lem5185802) (@lem5185801 x)). Qed.
Lemma lem5185804 : term273 = term273.
Proof. exact (fun_ext (fun x : real => @lem5185803 x)). Qed.
Lemma lem5185805 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185806 : term274 = term274.
Proof. exact (MK_COMB (@lem5185805) (@lem5185804)). Qed.
Lemma lem5185807 (h1 : term49) : term274.
Proof. exact (EQ_MP (@lem5185806) (@lem5185238 h1)). Qed.
Lemma lem5185840 (x : type1021) (s : real -> Prop) (b : real) : (term446 x s b) = (term446 x s b).
Proof. exact (eq_refl (term446 x s b)). Qed.
Lemma lem5185841 (x : type1021) (s : real -> Prop) : (term447 x s) = (term447 x s).
Proof. exact (fun_ext (fun b : real => @lem5185840 x s b)). Qed.
Lemma lem5185842 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185843 (x : type1021) (s : real -> Prop) : (term448 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5185842) (@lem5185841 x s)). Qed.
Lemma lem5185860 (x : real) (s : real -> Prop) : (term290 x s) = (term290 x s).
Proof. exact (eq_refl (term290 x s)). Qed.
Lemma lem5185861 (s : real -> Prop) : (term292 s) = (term292 s).
Proof. exact (fun_ext (fun x : real => @lem5185860 x s)). Qed.
Lemma lem5185862 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185863 (s : real -> Prop) : (term293 s) = (term293 s).
Proof. exact (MK_COMB (@lem5185862) (@lem5185861 s)). Qed.
Lemma lem5185864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5185865 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (MK_COMB (@lem5185864) (@lem5185863 s)). Qed.
Lemma lem5185866 (x : type1021) (s : real -> Prop) : (term449 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5185865 s) (@lem5185843 x s)). Qed.
Lemma lem5185889 (x : type1021) (s : real -> Prop) (b : real) : (term450 x s b) = (term450 x s b).
Proof. exact (eq_refl (term450 x s b)). Qed.
Lemma lem5185890 (x : type1021) (s : real -> Prop) : (term451 x s) = (term451 x s).
Proof. exact (fun_ext (fun b : real => @lem5185889 x s b)). Qed.
Lemma lem5185891 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185892 (x : type1021) (s : real -> Prop) : (term452 x s) = (term452 x s).
Proof. exact (MK_COMB (@lem5185891) (@lem5185890 x s)). Qed.
Lemma lem5185899 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5185900 (x : type1021) (s : real -> Prop) : (term453 x s) = (term453 x s).
Proof. exact (MK_COMB (@lem5185899 s) (@lem5185892 x s)). Qed.
Lemma lem5185901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5185902 (x : type1021) (s : real -> Prop) : (term454 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5185901) (@lem5185900 x s)). Qed.
Lemma lem5185903 (x : type1021) (s : real -> Prop) : (term438 x s) = (term438 x s).
Proof. exact (MK_COMB (@lem5185902 x s) (@lem5185866 x s)). Qed.
Lemma lem5185904 (x : type1021) : (term440 x) = (term440 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5185903 x s)). Qed.
Lemma lem5185905 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5185906 (x : type1021) : (term442 x) = (term442 x).
Proof. exact (MK_COMB (@lem5185905) (@lem5185904 x)). Qed.
Lemma lem5185907 (x : type1021) (h1 : term442 x) : term442 x.
Proof. exact (EQ_MP (@lem5185906 x) (@lem5185768 x h1)). Qed.
Lemma lem5185922 (s : real -> Prop) (x : real) (y : real) : (term55 s x y) = (term55 s x y).
Proof. exact (eq_refl (term55 s x y)). Qed.
Lemma lem5185923 (s : real -> Prop) (y : real) : (term56 s y) = (term56 s y).
Proof. exact (fun_ext (fun x : real => @lem5185922 s x y)). Qed.
Lemma lem5185924 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185925 (s : real -> Prop) (y : real) : (term57 s y) = (term57 s y).
Proof. exact (MK_COMB (@lem5185924) (@lem5185923 s y)). Qed.
Lemma lem5185936 (s : real -> Prop) (y : real) : (term72 s y) = (term72 s y).
Proof. exact (eq_refl (term72 s y)). Qed.
Lemma lem5185937 (s : real -> Prop) (y : real) : (term74 s y) = (term74 s y).
Proof. exact (MK_COMB (@lem5185936 s y) (@lem5185925 s y)). Qed.
Lemma lem5185964 (s : real -> Prop) (x' : real) (y : real) : (term204 s x' y) = (term204 s x' y).
Proof. exact (eq_refl (term204 s x' y)). Qed.
Lemma lem5185965 (x' : real) (s : real -> Prop) (y : real) : (term206 x' s y) = (term206 x' s y).
Proof. exact (MK_COMB (@lem5185964 s x' y) (@lem5185937 s y)). Qed.
Lemma lem5185980 (s : real -> Prop) (x : real) (b : real) : (term55 s x b) = (term55 s x b).
Proof. exact (eq_refl (term55 s x b)). Qed.
Lemma lem5185981 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (fun_ext (fun x : real => @lem5185980 s x b)). Qed.
Lemma lem5185982 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5185983 (s : real -> Prop) (b : real) : (term57 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5185982) (@lem5185981 s b)). Qed.
Lemma lem5185992 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5185993 (s : real -> Prop) (b : real) : (term155 s b) = (term155 s b).
Proof. exact (MK_COMB (@lem5185992 s) (@lem5185983 s b)). Qed.
Lemma lem5185994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5185995 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (MK_COMB (@lem5185994) (@lem5185993 s b)). Qed.
Lemma lem5185996 (b : real) (x' : real) (s : real -> Prop) (y : real) : (term252 b x' s y) = (term252 b x' s y).
Proof. exact (MK_COMB (@lem5185995 s b) (@lem5185965 x' s y)). Qed.
Lemma lem5185997 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term252 b x' s y.
Proof. exact (EQ_MP (@lem5185996 b x' s y) (@lem5185772 b x' s y h1)). Qed.
Lemma lem5185998 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term206 x' s y.
Proof. exact (proj2 (@lem5185997 b x' s y h1)). Qed.
Lemma lem5185999 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term155 s b.
Proof. exact (proj1 (@lem5185997 b x' s y h1)). Qed.
Lemma lem5186000 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term57 s b.
Proof. exact (proj2 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5186002 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term168 s x' y.
Proof. exact (h1). Qed.
Lemma lem5186003 (s : real -> Prop) (y : real) (h1 : term74 s y) : term74 s y.
Proof. exact (h1). Qed.
Lemma lem5186004 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term62 s x' y.
Proof. exact (proj2 (@lem5186002 s x' y h1)). Qed.
Lemma lem5186008 (s : real -> Prop) (y : real) (h1 : term74 s y) : term57 s y.
Proof. exact (proj2 (@lem5186003 s y h1)). Qed.
Lemma lem5186023 (y : real) (x : real) (z : real) : (term267 y x z) = (term267 y x z).
Proof. exact (eq_refl (term267 y x z)). Qed.
Lemma lem5186024 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (fun_ext (fun z : real => @lem5186023 y x z)). Qed.
Lemma lem5186025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186026 (y : real) (x : real) : (term270 y x) = (term270 y x).
Proof. exact (MK_COMB (@lem5186025) (@lem5186024 y x)). Qed.
Lemma lem5186027 (x : real) : (term271 x) = (term271 x).
Proof. exact (fun_ext (fun y : real => @lem5186026 y x)). Qed.
Lemma lem5186028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186029 (x : real) : (term272 x) = (term272 x).
Proof. exact (MK_COMB (@lem5186028) (@lem5186027 x)). Qed.
Lemma lem5186030 : term273 = term273.
Proof. exact (fun_ext (fun x : real => @lem5186029 x)). Qed.
Lemma lem5186031 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186033 : term274 = term274.
Proof. exact (MK_COMB (@lem5186031) (@lem5186030)). Qed.
Lemma lem5186034 (h1 : term49) : term274.
Proof. exact (EQ_MP (@lem5186033) (@lem5185807 h1)). Qed.
Lemma lem5186036 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5186037 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5186036 real P Q). Qed.
Lemma lem5186038 (x : type1021) (s : real -> Prop) : (term459 x s) = (term460 x s).
Proof. exact (@lem5186037 (s = (@EMPTY real)) (term451 x s)). Qed.
Lemma lem5186039 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5186040 (x : type1021) (s : real -> Prop) : (term462 x s) = (term451 x s).
Proof. exact (fun_ext (fun b : real => @lem5186039 x s b)). Qed.
Lemma lem5186041 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186042 (x : type1021) (s : real -> Prop) : (term463 x s) = (term452 x s).
Proof. exact (MK_COMB (@lem5186041) (@lem5186040 x s)). Qed.
Lemma lem5186043 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5186044 (x : type1021) (s : real -> Prop) : (term459 x s) = (term453 x s).
Proof. exact (MK_COMB (@lem5186043 s) (@lem5186042 x s)). Qed.
Lemma lem5186045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186046 (x : type1021) (s : real -> Prop) : (term464 x s) = (term465 x s).
Proof. exact (MK_COMB (@lem5186045) (@lem5186044 x s)). Qed.
Lemma lem5186047 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5186048 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5186049 (x : type1021) (s : real -> Prop) (b : real) : (term466 x s b) = (term467 x s b).
Proof. exact (MK_COMB (@lem5186048 s) (@lem5186047 x s b)). Qed.
Lemma lem5186050 (x : type1021) (s : real -> Prop) : (term468 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5186049 x s b)). Qed.
Lemma lem5186051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186052 (x : type1021) (s : real -> Prop) : (term460 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5186051) (@lem5186050 x s)). Qed.
Lemma lem5186053 (x : type1021) (s : real -> Prop) : ((term459 x s) = (term460 x s)) = ((term453 x s) = (term470 x s)).
Proof. exact (MK_COMB (@lem5186046 x s) (@lem5186052 x s)). Qed.
Lemma lem5186054 (x : type1021) (s : real -> Prop) : (term453 x s) = (term470 x s).
Proof. exact (EQ_MP (@lem5186053 x s) (@lem5186038 x s)). Qed.
Lemma lem5186055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186056 (x : type1021) (s : real -> Prop) : (term454 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5186055) (@lem5186054 x s)). Qed.
Lemma lem5186058 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term472 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5186059 (P : real -> Prop) (Q : real -> Prop) : (term474 P Q) = (term475 P Q).
Proof. exact (@lem5186058 real P Q). Qed.
Lemma lem5186060 (x : type1021) (s : real -> Prop) : (term476 x s) = (term477 x s).
Proof. exact (@lem5186059 (term292 s) (term447 x s)). Qed.
Lemma lem5186061 (b : real) (s : real -> Prop) : (term478 s b) = (term290 b s).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5186062 (s : real -> Prop) : (term479 s) = (term292 s).
Proof. exact (fun_ext (fun b : real => @lem5186061 b s)). Qed.
Lemma lem5186063 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186064 (s : real -> Prop) : (term480 s) = (term293 s).
Proof. exact (MK_COMB (@lem5186063) (@lem5186062 s)). Qed.
Lemma lem5186065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186066 (s : real -> Prop) : (term481 s) = (term300 s).
Proof. exact (MK_COMB (@lem5186065) (@lem5186064 s)). Qed.
Lemma lem5186067 (x : type1021) (s : real -> Prop) (b : real) : (term482 x s b) = (term446 x s b).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5186068 (x : type1021) (s : real -> Prop) : (term483 x s) = (term447 x s).
Proof. exact (fun_ext (fun b : real => @lem5186067 x s b)). Qed.
Lemma lem5186069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186070 (x : type1021) (s : real -> Prop) : (term484 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5186069) (@lem5186068 x s)). Qed.
Lemma lem5186071 (x : type1021) (s : real -> Prop) : (term476 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5186066 s) (@lem5186070 x s)). Qed.
Lemma lem5186072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186073 (x : type1021) (s : real -> Prop) : (term485 x s) = (term486 x s).
Proof. exact (MK_COMB (@lem5186072) (@lem5186071 x s)). Qed.
Lemma lem5186074 (b : real) (s : real -> Prop) : (term478 s b) = (term290 b s).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5186075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186076 (b : real) (s : real -> Prop) : (term487 s b) = (term488 b s).
Proof. exact (MK_COMB (@lem5186075) (@lem5186074 b s)). Qed.
Lemma lem5186077 (x : type1021) (s : real -> Prop) (b : real) : (term482 x s b) = (term446 x s b).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5186078 (x : type1021) (s : real -> Prop) (b : real) : (term489 x s b) = (term490 x s b).
Proof. exact (MK_COMB (@lem5186076 b s) (@lem5186077 x s b)). Qed.
Lemma lem5186079 (x : type1021) (s : real -> Prop) : (term491 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5186078 x s b)). Qed.
Lemma lem5186080 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186081 (x : type1021) (s : real -> Prop) : (term477 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5186080) (@lem5186079 x s)). Qed.
Lemma lem5186082 (x : type1021) (s : real -> Prop) : ((term476 x s) = (term477 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (MK_COMB (@lem5186073 x s) (@lem5186081 x s)). Qed.
Lemma lem5186083 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5186082 x s) (@lem5186060 x s)). Qed.
Lemma lem5186086 (x : type1021) (s : real -> Prop) : (term494 x s) = (term494 x s).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5186087 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5186088 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5186089 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = ((term494 x s) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5186088 x s) (@lem5186087 x s)). Qed.
Lemma lem5186090 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5186091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186092 (x : type1021) (s : real -> Prop) : (term495 x s) = (term496 x s).
Proof. exact (MK_COMB (@lem5186091) (@lem5186090 x s)). Qed.
Lemma lem5186093 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl ((term449 x s) = (term493 x s))). Qed.
Lemma lem5186094 (x : type1021) (s : real -> Prop) : ((term494 x s) = ((term449 x s) = (term493 x s))) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5186092 x s) (@lem5186093 x s)). Qed.
Lemma lem5186095 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (TRANS (@lem5186089 x s) (@lem5186094 x s)). Qed.
Lemma lem5186096 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (EQ_MP (@lem5186095 x s) (@lem5186086 x s)). Qed.
Lemma lem5186097 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5186096 x s) (@lem5186083 x s)). Qed.
Lemma lem5186098 (x : type1021) (s : real -> Prop) : (term438 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5186056 x s) (@lem5186097 x s)). Qed.
Lemma lem5186100 {A : Type'} (P : A -> Prop) (Q : Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5186101 (P : real -> Prop) (Q : Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem5186100 real P Q). Qed.
Lemma lem5186102 (x : type1021) (s : real -> Prop) : (term502 x s) = (term503 x s).
Proof. exact (@lem5186101 (term469 x s) (term493 x s)). Qed.
Lemma lem5186103 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5186104 (x : type1021) (s : real -> Prop) : (term505 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5186103 x s b)). Qed.
Lemma lem5186105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186106 (x : type1021) (s : real -> Prop) : (term506 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5186105) (@lem5186104 x s)). Qed.
Lemma lem5186107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186108 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5186107) (@lem5186106 x s)). Qed.
Lemma lem5186109 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5186110 (x : type1021) (s : real -> Prop) : (term502 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5186108 x s) (@lem5186109 x s)). Qed.
Lemma lem5186111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186112 (x : type1021) (s : real -> Prop) : (term508 x s) = (term509 x s).
Proof. exact (MK_COMB (@lem5186111) (@lem5186110 x s)). Qed.
Lemma lem5186113 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5186114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186115 (x : type1021) (s : real -> Prop) (b : real) : (term510 x s b) = (term511 x s b).
Proof. exact (MK_COMB (@lem5186114) (@lem5186113 x s b)). Qed.
Lemma lem5186116 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5186117 (b : real) (x : type1021) (s : real -> Prop) : (term512 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5186115 x s b) (@lem5186116 x s)). Qed.
Lemma lem5186118 (x : type1021) (s : real -> Prop) : (term514 x s) = (term515 x s).
Proof. exact (fun_ext (fun b : real => @lem5186117 b x s)). Qed.
Lemma lem5186119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186120 (x : type1021) (s : real -> Prop) : (term503 x s) = (term516 x s).
Proof. exact (MK_COMB (@lem5186119) (@lem5186118 x s)). Qed.
Lemma lem5186121 (x : type1021) (s : real -> Prop) : ((term502 x s) = (term503 x s)) = ((term497 x s) = (term516 x s)).
Proof. exact (MK_COMB (@lem5186112 x s) (@lem5186120 x s)). Qed.
Lemma lem5186122 (x : type1021) (s : real -> Prop) : (term497 x s) = (term516 x s).
Proof. exact (EQ_MP (@lem5186121 x s) (@lem5186102 x s)). Qed.
Lemma lem5186124 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5186125 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5186124 real P Q). Qed.
Lemma lem5186126 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term518 b x s).
Proof. exact (@lem5186125 (term467 x s b) (term492 x s)). Qed.
Lemma lem5186127 (x : type1021) (s : real -> Prop) (b : real) : (term519 x s b) = (term490 x s b).
Proof. exact (eq_refl (term519 x s b)). Qed.
Lemma lem5186128 (x : type1021) (s : real -> Prop) : (term520 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5186127 x s b)). Qed.
Lemma lem5186129 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186130 (x : type1021) (s : real -> Prop) : (term521 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5186129) (@lem5186128 x s)). Qed.
Lemma lem5186131 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5186132 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5186131 x s b) (@lem5186130 x s)). Qed.
Lemma lem5186133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186134 (b : real) (x : type1021) (s : real -> Prop) : (term522 b x s) = (term523 b x s).
Proof. exact (MK_COMB (@lem5186133) (@lem5186132 b x s)). Qed.
Lemma lem5186135 (x : type1021) (s : real -> Prop) (b' : real) : (term519 x s b') = (term490 x s b').
Proof. exact (eq_refl (term519 x s b')). Qed.
Lemma lem5186136 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5186137 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term524 b x s b') = (term525 b x s b').
Proof. exact (MK_COMB (@lem5186136 x s b) (@lem5186135 x s b')). Qed.
Lemma lem5186138 (b : real) (x : type1021) (s : real -> Prop) : (term526 b x s) = (term527 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5186137 b x s b')). Qed.
Lemma lem5186139 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186140 (b : real) (x : type1021) (s : real -> Prop) : (term518 b x s) = (term528 b x s).
Proof. exact (MK_COMB (@lem5186139) (@lem5186138 b x s)). Qed.
Lemma lem5186141 (b : real) (x : type1021) (s : real -> Prop) : ((term517 b x s) = (term518 b x s)) = ((term513 b x s) = (term528 b x s)).
Proof. exact (MK_COMB (@lem5186134 b x s) (@lem5186140 b x s)). Qed.
Lemma lem5186142 (b : real) (x : type1021) (s : real -> Prop) : (term513 b x s) = (term528 b x s).
Proof. exact (EQ_MP (@lem5186141 b x s) (@lem5186126 b x s)). Qed.
Lemma lem5186143 (x : type1021) (s : real -> Prop) : (term515 x s) = (term529 x s).
Proof. exact (fun_ext (fun b : real => @lem5186142 b x s)). Qed.
Lemma lem5186144 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186145 (x : type1021) (s : real -> Prop) : (term516 x s) = (term530 x s).
Proof. exact (MK_COMB (@lem5186144) (@lem5186143 x s)). Qed.
Lemma lem5186146 (x : type1021) (s : real -> Prop) : (term497 x s) = (term530 x s).
Proof. exact (TRANS (@lem5186122 x s) (@lem5186145 x s)). Qed.
Lemma lem5186147 (x : type1021) (s : real -> Prop) : (term438 x s) = (term530 x s).
Proof. exact (TRANS (@lem5186098 x s) (@lem5186146 x s)). Qed.
Lemma lem5186148 (x : type1021) : (term440 x) = (term531 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5186147 x s)). Qed.
Lemma lem5186149 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5186150 (x : type1021) : (term442 x) = (term532 x).
Proof. exact (MK_COMB (@lem5186149) (@lem5186148 x)). Qed.
Lemma lem5186167 (x : type1021) (s : real -> Prop) (b' : real) : (term446 x s b') = (term533 x s b').
Proof. exact (@lem19699 (term534 x b' s) (term535 x s b') (term23 s b')). Qed.
Lemma lem5186176 (b' : real) (s : real -> Prop) : (term488 b' s) = (term488 b' s).
Proof. exact (eq_refl (term488 b' s)). Qed.
Lemma lem5186177 (x : type1021) (s : real -> Prop) (b' : real) : (term490 x s b') = (term536 x s b').
Proof. exact (MK_COMB (@lem5186176 b' s) (@lem5186167 x s b')). Qed.
Lemma lem5186194 (x : type1021) (s : real -> Prop) (b : real) : (term467 x s b) = (term537 x s b).
Proof. exact (@lem19490 (term534 x b s) (s = (@EMPTY real)) (term535 x s b)). Qed.
Lemma lem5186195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186196 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term538 x s b).
Proof. exact (MK_COMB (@lem5186195) (@lem5186194 x s b)). Qed.
Lemma lem5186197 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term525 b x s b') = (term539 b x s b').
Proof. exact (MK_COMB (@lem5186196 x s b) (@lem5186177 x s b')). Qed.
Lemma lem5186198 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term539 b x s b') = (term540 b x s b').
Proof. exact (@lem19490 (term290 b' s) (term537 x s b) (term533 x s b')). Qed.
Lemma lem5186199 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (@lem19490 (term543 x s b') (term537 x s b) (term544 x s b')). Qed.
Lemma lem5186206 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term545 b x s b') = (term546 b x s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term544 x s b')). Qed.
Lemma lem5186213 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term549 b x s b') = (term550 b x s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term543 x s b')). Qed.
Lemma lem5186214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186215 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term551 b x s b') = (term552 b x s b').
Proof. exact (MK_COMB (@lem5186214) (@lem5186213 b x s b')). Qed.
Lemma lem5186216 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term553 b x s b').
Proof. exact (MK_COMB (@lem5186215 b x s b') (@lem5186206 b x s b')). Qed.
Lemma lem5186217 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term553 b x s b').
Proof. exact (TRANS (@lem5186199 b x s b') (@lem5186216 b x s b')). Qed.
Lemma lem5186224 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term554 x b b' s) = (term555 x b b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term290 b' s)). Qed.
Lemma lem5186225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186226 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term556 x b b' s) = (term557 x b b' s).
Proof. exact (MK_COMB (@lem5186225) (@lem5186224 x b b' s)). Qed.
Lemma lem5186227 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term540 b x s b') = (term558 b x s b').
Proof. exact (MK_COMB (@lem5186226 x b b' s) (@lem5186217 b x s b')). Qed.
Lemma lem5186228 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term539 b x s b') = (term558 b x s b').
Proof. exact (TRANS (@lem5186198 b x s b') (@lem5186227 b x s b')). Qed.
Lemma lem5186229 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term525 b x s b') = (term558 b x s b').
Proof. exact (TRANS (@lem5186197 b x s b') (@lem5186228 b x s b')). Qed.
Lemma lem5186230 (b : real) (x : type1021) (s : real -> Prop) : (term527 b x s) = (term559 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5186229 b x s b')). Qed.
Lemma lem5186231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186232 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term560 b x s).
Proof. exact (MK_COMB (@lem5186231) (@lem5186230 b x s)). Qed.
Lemma lem5186233 (x : type1021) (s : real -> Prop) : (term529 x s) = (term561 x s).
Proof. exact (fun_ext (fun b : real => @lem5186232 b x s)). Qed.
Lemma lem5186234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186235 (x : type1021) (s : real -> Prop) : (term530 x s) = (term562 x s).
Proof. exact (MK_COMB (@lem5186234) (@lem5186233 x s)). Qed.
Lemma lem5186236 (x : type1021) : (term531 x) = (term563 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5186235 x s)). Qed.
Lemma lem5186237 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5186238 (x : type1021) : (term532 x) = (term564 x).
Proof. exact (MK_COMB (@lem5186237) (@lem5186236 x)). Qed.
Lemma lem5186239 (x : type1021) : (term442 x) = (term564 x).
Proof. exact (TRANS (@lem5186150 x) (@lem5186238 x)). Qed.
Lemma lem5186240 (x : type1021) (h1 : term442 x) : term564 x.
Proof. exact (EQ_MP (@lem5186239 x) (@lem5185907 x h1)). Qed.
Lemma lem5186252 (s : real -> Prop) (x : real) (b : real) : (term55 s x b) = (term55 s x b).
Proof. exact (eq_refl (term55 s x b)). Qed.
Lemma lem5186253 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (fun_ext (fun x : real => @lem5186252 s x b)). Qed.
Lemma lem5186254 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186256 (s : real -> Prop) (b : real) : (term57 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5186254) (@lem5186253 s b)). Qed.
Lemma lem5186257 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term57 s b.
Proof. exact (EQ_MP (@lem5186256 s b) (@lem5186000 b x' s y h1)). Qed.
Lemma lem5186296 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5186297 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5186296 real P Q). Qed.
Lemma lem5186298 (x : type1021) (s : real -> Prop) : (term459 x s) = (term460 x s).
Proof. exact (@lem5186297 (s = (@EMPTY real)) (term451 x s)). Qed.
Lemma lem5186299 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5186300 (x : type1021) (s : real -> Prop) : (term462 x s) = (term451 x s).
Proof. exact (fun_ext (fun b : real => @lem5186299 x s b)). Qed.
Lemma lem5186301 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186302 (x : type1021) (s : real -> Prop) : (term463 x s) = (term452 x s).
Proof. exact (MK_COMB (@lem5186301) (@lem5186300 x s)). Qed.
Lemma lem5186303 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5186304 (x : type1021) (s : real -> Prop) : (term459 x s) = (term453 x s).
Proof. exact (MK_COMB (@lem5186303 s) (@lem5186302 x s)). Qed.
Lemma lem5186305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186306 (x : type1021) (s : real -> Prop) : (term464 x s) = (term465 x s).
Proof. exact (MK_COMB (@lem5186305) (@lem5186304 x s)). Qed.
Lemma lem5186307 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5186308 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5186309 (x : type1021) (s : real -> Prop) (b : real) : (term466 x s b) = (term467 x s b).
Proof. exact (MK_COMB (@lem5186308 s) (@lem5186307 x s b)). Qed.
Lemma lem5186310 (x : type1021) (s : real -> Prop) : (term468 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5186309 x s b)). Qed.
Lemma lem5186311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186312 (x : type1021) (s : real -> Prop) : (term460 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5186311) (@lem5186310 x s)). Qed.
Lemma lem5186313 (x : type1021) (s : real -> Prop) : ((term459 x s) = (term460 x s)) = ((term453 x s) = (term470 x s)).
Proof. exact (MK_COMB (@lem5186306 x s) (@lem5186312 x s)). Qed.
Lemma lem5186314 (x : type1021) (s : real -> Prop) : (term453 x s) = (term470 x s).
Proof. exact (EQ_MP (@lem5186313 x s) (@lem5186298 x s)). Qed.
Lemma lem5186315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186316 (x : type1021) (s : real -> Prop) : (term454 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5186315) (@lem5186314 x s)). Qed.
Lemma lem5186318 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term472 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5186319 (P : real -> Prop) (Q : real -> Prop) : (term474 P Q) = (term475 P Q).
Proof. exact (@lem5186318 real P Q). Qed.
Lemma lem5186320 (x : type1021) (s : real -> Prop) : (term476 x s) = (term477 x s).
Proof. exact (@lem5186319 (term292 s) (term447 x s)). Qed.
Lemma lem5186321 (b : real) (s : real -> Prop) : (term478 s b) = (term290 b s).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5186322 (s : real -> Prop) : (term479 s) = (term292 s).
Proof. exact (fun_ext (fun b : real => @lem5186321 b s)). Qed.
Lemma lem5186323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186324 (s : real -> Prop) : (term480 s) = (term293 s).
Proof. exact (MK_COMB (@lem5186323) (@lem5186322 s)). Qed.
Lemma lem5186325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186326 (s : real -> Prop) : (term481 s) = (term300 s).
Proof. exact (MK_COMB (@lem5186325) (@lem5186324 s)). Qed.
Lemma lem5186327 (x : type1021) (s : real -> Prop) (b : real) : (term482 x s b) = (term446 x s b).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5186328 (x : type1021) (s : real -> Prop) : (term483 x s) = (term447 x s).
Proof. exact (fun_ext (fun b : real => @lem5186327 x s b)). Qed.
Lemma lem5186329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186330 (x : type1021) (s : real -> Prop) : (term484 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5186329) (@lem5186328 x s)). Qed.
Lemma lem5186331 (x : type1021) (s : real -> Prop) : (term476 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5186326 s) (@lem5186330 x s)). Qed.
Lemma lem5186332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186333 (x : type1021) (s : real -> Prop) : (term485 x s) = (term486 x s).
Proof. exact (MK_COMB (@lem5186332) (@lem5186331 x s)). Qed.
Lemma lem5186334 (b : real) (s : real -> Prop) : (term478 s b) = (term290 b s).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5186335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186336 (b : real) (s : real -> Prop) : (term487 s b) = (term488 b s).
Proof. exact (MK_COMB (@lem5186335) (@lem5186334 b s)). Qed.
Lemma lem5186337 (x : type1021) (s : real -> Prop) (b : real) : (term482 x s b) = (term446 x s b).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5186338 (x : type1021) (s : real -> Prop) (b : real) : (term489 x s b) = (term490 x s b).
Proof. exact (MK_COMB (@lem5186336 b s) (@lem5186337 x s b)). Qed.
Lemma lem5186339 (x : type1021) (s : real -> Prop) : (term491 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5186338 x s b)). Qed.
Lemma lem5186340 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186341 (x : type1021) (s : real -> Prop) : (term477 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5186340) (@lem5186339 x s)). Qed.
Lemma lem5186342 (x : type1021) (s : real -> Prop) : ((term476 x s) = (term477 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (MK_COMB (@lem5186333 x s) (@lem5186341 x s)). Qed.
Lemma lem5186343 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5186342 x s) (@lem5186320 x s)). Qed.
Lemma lem5186346 (x : type1021) (s : real -> Prop) : (term494 x s) = (term494 x s).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5186347 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5186348 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5186349 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = ((term494 x s) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5186348 x s) (@lem5186347 x s)). Qed.
Lemma lem5186350 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5186351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186352 (x : type1021) (s : real -> Prop) : (term495 x s) = (term496 x s).
Proof. exact (MK_COMB (@lem5186351) (@lem5186350 x s)). Qed.
Lemma lem5186353 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl ((term449 x s) = (term493 x s))). Qed.
Lemma lem5186354 (x : type1021) (s : real -> Prop) : ((term494 x s) = ((term449 x s) = (term493 x s))) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5186352 x s) (@lem5186353 x s)). Qed.
Lemma lem5186355 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (TRANS (@lem5186349 x s) (@lem5186354 x s)). Qed.
Lemma lem5186356 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (EQ_MP (@lem5186355 x s) (@lem5186346 x s)). Qed.
Lemma lem5186357 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5186356 x s) (@lem5186343 x s)). Qed.
Lemma lem5186358 (x : type1021) (s : real -> Prop) : (term438 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5186316 x s) (@lem5186357 x s)). Qed.
Lemma lem5186360 {A : Type'} (P : A -> Prop) (Q : Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5186361 (P : real -> Prop) (Q : Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem5186360 real P Q). Qed.
Lemma lem5186362 (x : type1021) (s : real -> Prop) : (term502 x s) = (term503 x s).
Proof. exact (@lem5186361 (term469 x s) (term493 x s)). Qed.
Lemma lem5186363 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5186364 (x : type1021) (s : real -> Prop) : (term505 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5186363 x s b)). Qed.
Lemma lem5186365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186366 (x : type1021) (s : real -> Prop) : (term506 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5186365) (@lem5186364 x s)). Qed.
Lemma lem5186367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186368 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5186367) (@lem5186366 x s)). Qed.
Lemma lem5186369 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5186370 (x : type1021) (s : real -> Prop) : (term502 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5186368 x s) (@lem5186369 x s)). Qed.
Lemma lem5186371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186372 (x : type1021) (s : real -> Prop) : (term508 x s) = (term509 x s).
Proof. exact (MK_COMB (@lem5186371) (@lem5186370 x s)). Qed.
Lemma lem5186373 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5186374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186375 (x : type1021) (s : real -> Prop) (b : real) : (term510 x s b) = (term511 x s b).
Proof. exact (MK_COMB (@lem5186374) (@lem5186373 x s b)). Qed.
Lemma lem5186376 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5186377 (b : real) (x : type1021) (s : real -> Prop) : (term512 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5186375 x s b) (@lem5186376 x s)). Qed.
Lemma lem5186378 (x : type1021) (s : real -> Prop) : (term514 x s) = (term515 x s).
Proof. exact (fun_ext (fun b : real => @lem5186377 b x s)). Qed.
Lemma lem5186379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186380 (x : type1021) (s : real -> Prop) : (term503 x s) = (term516 x s).
Proof. exact (MK_COMB (@lem5186379) (@lem5186378 x s)). Qed.
Lemma lem5186381 (x : type1021) (s : real -> Prop) : ((term502 x s) = (term503 x s)) = ((term497 x s) = (term516 x s)).
Proof. exact (MK_COMB (@lem5186372 x s) (@lem5186380 x s)). Qed.
Lemma lem5186382 (x : type1021) (s : real -> Prop) : (term497 x s) = (term516 x s).
Proof. exact (EQ_MP (@lem5186381 x s) (@lem5186362 x s)). Qed.
Lemma lem5186384 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5186385 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5186384 real P Q). Qed.
Lemma lem5186386 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term518 b x s).
Proof. exact (@lem5186385 (term467 x s b) (term492 x s)). Qed.
Lemma lem5186387 (x : type1021) (s : real -> Prop) (b : real) : (term519 x s b) = (term490 x s b).
Proof. exact (eq_refl (term519 x s b)). Qed.
Lemma lem5186388 (x : type1021) (s : real -> Prop) : (term520 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5186387 x s b)). Qed.
Lemma lem5186389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186390 (x : type1021) (s : real -> Prop) : (term521 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5186389) (@lem5186388 x s)). Qed.
Lemma lem5186391 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5186392 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5186391 x s b) (@lem5186390 x s)). Qed.
Lemma lem5186393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186394 (b : real) (x : type1021) (s : real -> Prop) : (term522 b x s) = (term523 b x s).
Proof. exact (MK_COMB (@lem5186393) (@lem5186392 b x s)). Qed.
Lemma lem5186395 (x : type1021) (s : real -> Prop) (b' : real) : (term519 x s b') = (term490 x s b').
Proof. exact (eq_refl (term519 x s b')). Qed.
Lemma lem5186396 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5186397 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term524 b x s b') = (term525 b x s b').
Proof. exact (MK_COMB (@lem5186396 x s b) (@lem5186395 x s b')). Qed.
Lemma lem5186398 (b : real) (x : type1021) (s : real -> Prop) : (term526 b x s) = (term527 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5186397 b x s b')). Qed.
Lemma lem5186399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186400 (b : real) (x : type1021) (s : real -> Prop) : (term518 b x s) = (term528 b x s).
Proof. exact (MK_COMB (@lem5186399) (@lem5186398 b x s)). Qed.
Lemma lem5186401 (b : real) (x : type1021) (s : real -> Prop) : ((term517 b x s) = (term518 b x s)) = ((term513 b x s) = (term528 b x s)).
Proof. exact (MK_COMB (@lem5186394 b x s) (@lem5186400 b x s)). Qed.
Lemma lem5186402 (b : real) (x : type1021) (s : real -> Prop) : (term513 b x s) = (term528 b x s).
Proof. exact (EQ_MP (@lem5186401 b x s) (@lem5186386 b x s)). Qed.
Lemma lem5186403 (x : type1021) (s : real -> Prop) : (term515 x s) = (term529 x s).
Proof. exact (fun_ext (fun b : real => @lem5186402 b x s)). Qed.
Lemma lem5186404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186405 (x : type1021) (s : real -> Prop) : (term516 x s) = (term530 x s).
Proof. exact (MK_COMB (@lem5186404) (@lem5186403 x s)). Qed.
Lemma lem5186406 (x : type1021) (s : real -> Prop) : (term497 x s) = (term530 x s).
Proof. exact (TRANS (@lem5186382 x s) (@lem5186405 x s)). Qed.
Lemma lem5186407 (x : type1021) (s : real -> Prop) : (term438 x s) = (term530 x s).
Proof. exact (TRANS (@lem5186358 x s) (@lem5186406 x s)). Qed.
Lemma lem5186408 (x : type1021) : (term440 x) = (term531 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5186407 x s)). Qed.
Lemma lem5186409 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5186410 (x : type1021) : (term442 x) = (term532 x).
Proof. exact (MK_COMB (@lem5186409) (@lem5186408 x)). Qed.
Lemma lem5186427 (x : type1021) (s : real -> Prop) (b' : real) : (term446 x s b') = (term533 x s b').
Proof. exact (@lem19699 (term534 x b' s) (term535 x s b') (term23 s b')). Qed.
Lemma lem5186436 (b' : real) (s : real -> Prop) : (term488 b' s) = (term488 b' s).
Proof. exact (eq_refl (term488 b' s)). Qed.
Lemma lem5186437 (x : type1021) (s : real -> Prop) (b' : real) : (term490 x s b') = (term536 x s b').
Proof. exact (MK_COMB (@lem5186436 b' s) (@lem5186427 x s b')). Qed.
Lemma lem5186454 (x : type1021) (s : real -> Prop) (b : real) : (term467 x s b) = (term537 x s b).
Proof. exact (@lem19490 (term534 x b s) (s = (@EMPTY real)) (term535 x s b)). Qed.
Lemma lem5186455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5186456 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term538 x s b).
Proof. exact (MK_COMB (@lem5186455) (@lem5186454 x s b)). Qed.
Lemma lem5186457 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term525 b x s b') = (term539 b x s b').
Proof. exact (MK_COMB (@lem5186456 x s b) (@lem5186437 x s b')). Qed.
Lemma lem5186458 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term539 b x s b') = (term540 b x s b').
Proof. exact (@lem19490 (term290 b' s) (term537 x s b) (term533 x s b')). Qed.
Lemma lem5186459 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term542 b x s b').
Proof. exact (@lem19490 (term543 x s b') (term537 x s b) (term544 x s b')). Qed.
Lemma lem5186466 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term545 b x s b') = (term546 b x s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term544 x s b')). Qed.
Lemma lem5186473 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term549 b x s b') = (term550 b x s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term543 x s b')). Qed.
Lemma lem5186474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186475 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term551 b x s b') = (term552 b x s b').
Proof. exact (MK_COMB (@lem5186474) (@lem5186473 b x s b')). Qed.
Lemma lem5186476 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term542 b x s b') = (term553 b x s b').
Proof. exact (MK_COMB (@lem5186475 b x s b') (@lem5186466 b x s b')). Qed.
Lemma lem5186477 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term541 b x s b') = (term553 b x s b').
Proof. exact (TRANS (@lem5186459 b x s b') (@lem5186476 b x s b')). Qed.
Lemma lem5186484 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term554 x b b' s) = (term555 x b b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term290 b' s)). Qed.
Lemma lem5186485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5186486 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term556 x b b' s) = (term557 x b b' s).
Proof. exact (MK_COMB (@lem5186485) (@lem5186484 x b b' s)). Qed.
Lemma lem5186487 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term540 b x s b') = (term558 b x s b').
Proof. exact (MK_COMB (@lem5186486 x b b' s) (@lem5186477 b x s b')). Qed.
Lemma lem5186488 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term539 b x s b') = (term558 b x s b').
Proof. exact (TRANS (@lem5186458 b x s b') (@lem5186487 b x s b')). Qed.
Lemma lem5186489 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term525 b x s b') = (term558 b x s b').
Proof. exact (TRANS (@lem5186457 b x s b') (@lem5186488 b x s b')). Qed.
Lemma lem5186490 (b : real) (x : type1021) (s : real -> Prop) : (term527 b x s) = (term559 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5186489 b x s b')). Qed.
Lemma lem5186491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186492 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term560 b x s).
Proof. exact (MK_COMB (@lem5186491) (@lem5186490 b x s)). Qed.
Lemma lem5186493 (x : type1021) (s : real -> Prop) : (term529 x s) = (term561 x s).
Proof. exact (fun_ext (fun b : real => @lem5186492 b x s)). Qed.
Lemma lem5186494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186495 (x : type1021) (s : real -> Prop) : (term530 x s) = (term562 x s).
Proof. exact (MK_COMB (@lem5186494) (@lem5186493 x s)). Qed.
Lemma lem5186496 (x : type1021) : (term531 x) = (term563 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5186495 x s)). Qed.
Lemma lem5186497 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5186498 (x : type1021) : (term532 x) = (term564 x).
Proof. exact (MK_COMB (@lem5186497) (@lem5186496 x)). Qed.
Lemma lem5186499 (x : type1021) : (term442 x) = (term564 x).
Proof. exact (TRANS (@lem5186410 x) (@lem5186498 x)). Qed.
Lemma lem5186500 (x : type1021) (h1 : term442 x) : term564 x.
Proof. exact (EQ_MP (@lem5186499 x) (@lem5185907 x h1)). Qed.
Lemma lem5186529 (s : real -> Prop) (x : real) (y : real) : (term55 s x y) = (term55 s x y).
Proof. exact (eq_refl (term55 s x y)). Qed.
Lemma lem5186530 (s : real -> Prop) (y : real) : (term56 s y) = (term56 s y).
Proof. exact (fun_ext (fun x : real => @lem5186529 s x y)). Qed.
Lemma lem5186531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5186533 (s : real -> Prop) (y : real) : (term57 s y) = (term57 s y).
Proof. exact (MK_COMB (@lem5186531) (@lem5186530 s y)). Qed.
Lemma lem5186534 (s : real -> Prop) (y : real) (h1 : term74 s y) : term57 s y.
Proof. exact (EQ_MP (@lem5186533 s y) (@lem5186008 s y h1)). Qed.
Lemma lem5186535 (_67683 : real) (h1 : term49) : term565 _67683.
Proof. exact (@lem5186034 h1 _67683). Qed.
Lemma lem5186536 (_67683 : real) : (term565 _67683) = (term272 _67683).
Proof. exact (eq_refl (term565 _67683)). Qed.
Lemma lem5186537 (_67683 : real) (h1 : term49) : term272 _67683.
Proof. exact (EQ_MP (@lem5186536 _67683) (@lem5186535 _67683 h1)). Qed.
Lemma lem5186538 (_67683 : real) (_67684 : real) (h1 : term49) : term566 _67683 _67684.
Proof. exact (@lem5186537 _67683 h1 _67684). Qed.
Lemma lem5186539 (_67684 : real) (_67683 : real) : (term566 _67683 _67684) = (term270 _67684 _67683).
Proof. exact (eq_refl (term566 _67683 _67684)). Qed.
Lemma lem5186540 (_67684 : real) (_67683 : real) (h1 : term49) : term270 _67684 _67683.
Proof. exact (EQ_MP (@lem5186539 _67684 _67683) (@lem5186538 _67683 _67684 h1)). Qed.
Lemma lem5186541 (_67684 : real) (_67683 : real) (_67685 : real) (h1 : term49) : term567 _67684 _67683 _67685.
Proof. exact (@lem5186540 _67684 _67683 h1 _67685). Qed.
Lemma lem5186542 (_67684 : real) (_67683 : real) (_67685 : real) : (term567 _67684 _67683 _67685) = (term267 _67684 _67683 _67685).
Proof. exact (eq_refl (term567 _67684 _67683 _67685)). Qed.
Lemma lem5186543 (_67684 : real) (_67683 : real) (_67685 : real) (h1 : term49) : term267 _67684 _67683 _67685.
Proof. exact (EQ_MP (@lem5186542 _67684 _67683 _67685) (@lem5186541 _67684 _67683 _67685 h1)). Qed.
Lemma lem5186544 (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term568 x _67686.
Proof. exact (@lem5186240 x h1 _67686). Qed.
Lemma lem5186545 (x : type1021) (_67686 : real -> Prop) : (term568 x _67686) = (term562 x _67686).
Proof. exact (eq_refl (term568 x _67686)). Qed.
Lemma lem5186546 (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term562 x _67686.
Proof. exact (EQ_MP (@lem5186545 x _67686) (@lem5186544 _67686 x h1)). Qed.
Lemma lem5186547 (_67686 : real -> Prop) (_67687 : real) (x : type1021) (h1 : term442 x) : term569 x _67686 _67687.
Proof. exact (@lem5186546 _67686 x h1 _67687). Qed.
Lemma lem5186548 (_67687 : real) (x : type1021) (_67686 : real -> Prop) : (term569 x _67686 _67687) = (term560 _67687 x _67686).
Proof. exact (eq_refl (term569 x _67686 _67687)). Qed.
Lemma lem5186549 (_67687 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term560 _67687 x _67686.
Proof. exact (EQ_MP (@lem5186548 _67687 x _67686) (@lem5186547 _67686 _67687 x h1)). Qed.
Lemma lem5186550 (_67687 : real) (_67686 : real -> Prop) (_67688 : real) (x : type1021) (h1 : term442 x) : term570 _67687 x _67686 _67688.
Proof. exact (@lem5186549 _67687 _67686 x h1 _67688). Qed.
Lemma lem5186551 (_67687 : real) (x : type1021) (_67686 : real -> Prop) (_67688 : real) : (term570 _67687 x _67686 _67688) = (term558 _67687 x _67686 _67688).
Proof. exact (eq_refl (term570 _67687 x _67686 _67688)). Qed.
Lemma lem5186552 (_67687 : real) (_67686 : real -> Prop) (_67688 : real) (x : type1021) (h1 : term442 x) : term558 _67687 x _67686 _67688.
Proof. exact (EQ_MP (@lem5186551 _67687 x _67686 _67688) (@lem5186550 _67687 _67686 _67688 x h1)). Qed.
Lemma lem5186553 (_67689 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term571 s b _67689.
Proof. exact (@lem5186257 b x' s y h1 _67689). Qed.
Lemma lem5186554 (s : real -> Prop) (_67689 : real) (b : real) : (term571 s b _67689) = (term55 s _67689 b).
Proof. exact (eq_refl (term571 s b _67689)). Qed.
Lemma lem5186565 (_67693 : real -> Prop) (x : type1021) (h1 : term442 x) : term568 x _67693.
Proof. exact (@lem5186500 x h1 _67693). Qed.
Lemma lem5186566 (x : type1021) (_67693 : real -> Prop) : (term568 x _67693) = (term562 x _67693).
Proof. exact (eq_refl (term568 x _67693)). Qed.
Lemma lem5186567 (_67693 : real -> Prop) (x : type1021) (h1 : term442 x) : term562 x _67693.
Proof. exact (EQ_MP (@lem5186566 x _67693) (@lem5186565 _67693 x h1)). Qed.
Lemma lem5186568 (_67693 : real -> Prop) (_67694 : real) (x : type1021) (h1 : term442 x) : term569 x _67693 _67694.
Proof. exact (@lem5186567 _67693 x h1 _67694). Qed.
Lemma lem5186569 (_67694 : real) (x : type1021) (_67693 : real -> Prop) : (term569 x _67693 _67694) = (term560 _67694 x _67693).
Proof. exact (eq_refl (term569 x _67693 _67694)). Qed.
Lemma lem5186570 (_67694 : real) (_67693 : real -> Prop) (x : type1021) (h1 : term442 x) : term560 _67694 x _67693.
Proof. exact (EQ_MP (@lem5186569 _67694 x _67693) (@lem5186568 _67693 _67694 x h1)). Qed.
Lemma lem5186571 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term570 _67694 x _67693 _67695.
Proof. exact (@lem5186570 _67694 _67693 x h1 _67695). Qed.
Lemma lem5186572 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term570 _67694 x _67693 _67695) = (term558 _67694 x _67693 _67695).
Proof. exact (eq_refl (term570 _67694 x _67693 _67695)). Qed.
Lemma lem5186573 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term558 _67694 x _67693 _67695.
Proof. exact (EQ_MP (@lem5186572 _67694 x _67693 _67695) (@lem5186571 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186577 (_67697 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term571 s y _67697.
Proof. exact (@lem5186534 s y h1 _67697). Qed.
Lemma lem5186578 (s : real -> Prop) (_67697 : real) (y : real) : (term571 s y _67697) = (term55 s _67697 y).
Proof. exact (eq_refl (term571 s y _67697)). Qed.
Lemma lem5186581 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term555 x _67687 _67688 _67686.
Proof. exact (proj1 (@lem5186552 _67687 _67686 _67688 x h1)). Qed.
Lemma lem5186588 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term572 x _67687 _67688 _67686.
Proof. exact (proj2 (@lem5186581 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5186589 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term573 x _67687 _67688 _67686.
Proof. exact (proj1 (@lem5186581 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5186590 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term553 _67694 x _67693 _67695.
Proof. exact (proj2 (@lem5186573 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186592 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term546 _67694 x _67693 _67695.
Proof. exact (proj2 (@lem5186590 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186593 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term550 _67694 x _67693 _67695.
Proof. exact (proj1 (@lem5186590 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186594 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term574 _67694 x _67693 _67695.
Proof. exact (proj2 (@lem5186592 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186596 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term575 _67694 x _67693 _67695.
Proof. exact (proj2 (@lem5186593 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186597 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term576 _67694 x _67693 _67695.
Proof. exact (proj1 (@lem5186593 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186610 (_67684 : real) (_67683 : real) (_67685 : real) : (term267 _67684 _67683 _67685) = (term577 _67684 _67683 _67685).
Proof. exact (@lem5184182 (term578 _67683 _67684) (term578 _67684 _67685) (real_le _67683 _67685)). Qed.
Lemma lem5186611 (_67684 : real) (_67683 : real) (_67685 : real) (h1 : term49) : term577 _67684 _67683 _67685.
Proof. exact (EQ_MP (@lem5186610 _67684 _67683 _67685) (@lem5186543 _67684 _67683 _67685 h1)). Qed.
Lemma lem5186619 (_67689 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term55 s _67689 b.
Proof. exact (EQ_MP (@lem5186554 s _67689 b) (@lem5186553 _67689 b x' s y h1)). Qed.
Lemma lem5186625 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term578 x' y.
Proof. exact (proj2 (@lem5186004 s x' y h1)). Qed.
Lemma lem5186704 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term573 x _67687 _67688 _67686) = (term579 x _67687 _67688 _67686).
Proof. exact (@lem5184182 (_67686 = (@EMPTY real)) (term534 x _67687 _67686) (term290 _67688 _67686)). Qed.
Lemma lem5186705 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term579 x _67687 _67688 _67686.
Proof. exact (EQ_MP (@lem5186704 x _67687 _67688 _67686) (@lem5186589 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5186720 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term572 x _67687 _67688 _67686) = (term580 x _67687 _67688 _67686).
Proof. exact (@lem5184182 (_67686 = (@EMPTY real)) (term535 x _67686 _67687) (term290 _67688 _67686)). Qed.
Lemma lem5186721 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term580 x _67687 _67688 _67686.
Proof. exact (EQ_MP (@lem5186720 x _67687 _67688 _67686) (@lem5186588 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5186743 (s : real -> Prop) (y : real) (h1 : term74 s y) : term581 s y.
Proof. exact (proj1 (@lem5186003 s y h1)). Qed.
Lemma lem5186749 (_67697 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term55 s _67697 y.
Proof. exact (EQ_MP (@lem5186578 s _67697 y) (@lem5186577 _67697 s y h1)). Qed.
Lemma lem5186780 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term574 _67694 x _67693 _67695) = (term582 _67694 x _67693 _67695).
Proof. exact (@lem5184182 (_67693 = (@EMPTY real)) (term535 x _67693 _67694) (term544 x _67693 _67695)). Qed.
Lemma lem5186781 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term582 _67694 x _67693 _67695.
Proof. exact (EQ_MP (@lem5186780 _67694 x _67693 _67695) (@lem5186594 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186796 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term576 _67694 x _67693 _67695) = (term583 _67694 x _67693 _67695).
Proof. exact (@lem5184182 (_67693 = (@EMPTY real)) (term534 x _67694 _67693) (term543 x _67693 _67695)). Qed.
Lemma lem5186797 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term583 _67694 x _67693 _67695.
Proof. exact (EQ_MP (@lem5186796 _67694 x _67693 _67695) (@lem5186597 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186812 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term575 _67694 x _67693 _67695) = (term584 _67694 x _67693 _67695).
Proof. exact (@lem5184182 (_67693 = (@EMPTY real)) (term535 x _67693 _67694) (term543 x _67693 _67695)). Qed.
Lemma lem5186813 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term584 _67694 x _67693 _67695.
Proof. exact (EQ_MP (@lem5186812 _67694 x _67693 _67695) (@lem5186596 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5186912 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5186913 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term585 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5186912 b x' s y h1). Qed.
Lemma lem5186915 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5186916 (s : real -> Prop) : (term585 s) = (term148 s).
Proof. exact (@lem5186915 (s = (@EMPTY real))). Qed.
Lemma lem5186917 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5186916 s) (@lem5186913 b x' s y h1)). Qed.
Lemma lem5186919 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5186920 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term585 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5186919 b x' s y h1). Qed.
Lemma lem5186922 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5186923 (s : real -> Prop) : (term585 s) = (term148 s).
Proof. exact (@lem5186922 (s = (@EMPTY real))). Qed.
Lemma lem5186924 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5186923 s) (@lem5186920 b x' s y h1)). Qed.
Lemma lem5186926 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : @IN real x' s.
Proof. exact (proj1 (@lem5186004 s x' y h1)). Qed.
Lemma lem5186927 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term587 x' s.
Proof. exact (fun h0 : term588 x' s => @lem5186926 s x' y h1). Qed.
Lemma lem5186929 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5186930 (x' : real) (s : real -> Prop) : (term587 x' s) = (@IN real x' s).
Proof. exact (@lem5186929 (@IN real x' s)). Qed.
Lemma lem5186931 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : @IN real x' s.
Proof. exact (EQ_MP (@lem5186930 x' s) (@lem5186927 s x' y h1)). Qed.
Lemma lem5186934 (x' : real) (s : real -> Prop) (h1 : term590 x' s) : term590 x' s.
Proof. exact (h1). Qed.
Lemma lem5186935 (x' : real) (s : real -> Prop) (h1 : term590 x' s) : term591 x' s.
Proof. exact (fun h0 : term291 x' s => @lem5186934 x' s h1). Qed.
Lemma lem5186937 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5186938 (x' : real) (s : real -> Prop) : (term591 x' s) = (term590 x' s).
Proof. exact (@lem5186937 (term291 x' s)). Qed.
Lemma lem5186939 (x' : real) (s : real -> Prop) (h1 : term590 x' s) : term590 x' s.
Proof. exact (EQ_MP (@lem5186938 x' s) (@lem5186935 x' s h1)). Qed.
Lemma lem5186967 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5186968 (_67688 : real) (_67686 : real -> Prop) : (term290 _67688 _67686) = (term592 _67688 _67686).
Proof. exact (@lem5186967 (term291 _67688 _67686) (term588 _67688 _67686)). Qed.
Lemma lem5186974 (x : type1021) (_67687 : real) (_67686 : real -> Prop) : (term593 x _67687 _67686) = (term593 x _67687 _67686).
Proof. exact (eq_refl (term593 x _67687 _67686)). Qed.
Lemma lem5186975 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term594 x _67687 _67688 _67686) = (term595 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5186974 x _67687 _67686) (@lem5186968 _67688 _67686)). Qed.
Lemma lem5186986 (_67686 : real -> Prop) : (term286 _67686) = (term286 _67686).
Proof. exact (eq_refl (term286 _67686)). Qed.
Lemma lem5186987 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term579 x _67687 _67688 _67686) = (term596 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5186986 _67686) (@lem5186975 x _67687 _67688 _67686)). Qed.
Lemma lem5186998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5186999 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term597 x _67687 _67688 _67686) = (term598 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5186998) (@lem5186987 x _67687 _67688 _67686)). Qed.
Lemma lem5187003 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187004 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term599 x _67687 _67688 _67686) = (term579 x _67687 _67688 _67686).
Proof. exact (@lem5187003 (_67686 = (@EMPTY real)) (term534 x _67687 _67686) (term290 _67688 _67686)). Qed.
Lemma lem5187030 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187031 (_67688 : real) (_67686 : real -> Prop) : (term290 _67688 _67686) = (term592 _67688 _67686).
Proof. exact (@lem5187030 (term291 _67688 _67686) (term588 _67688 _67686)). Qed.
Lemma lem5187037 (x : type1021) (_67687 : real) (_67686 : real -> Prop) : (term593 x _67687 _67686) = (term593 x _67687 _67686).
Proof. exact (eq_refl (term593 x _67687 _67686)). Qed.
Lemma lem5187038 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term594 x _67687 _67688 _67686) = (term595 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5187037 x _67687 _67686) (@lem5187031 _67688 _67686)). Qed.
Lemma lem5187049 (_67686 : real -> Prop) : (term286 _67686) = (term286 _67686).
Proof. exact (eq_refl (term286 _67686)). Qed.
Lemma lem5187050 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term579 x _67687 _67688 _67686) = (term596 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5187049 _67686) (@lem5187038 x _67687 _67688 _67686)). Qed.
Lemma lem5187061 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term599 x _67687 _67688 _67686) = (term596 x _67687 _67688 _67686).
Proof. exact (TRANS (@lem5187004 x _67687 _67688 _67686) (@lem5187050 x _67687 _67688 _67686)). Qed.
Lemma lem5187062 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : ((term579 x _67687 _67688 _67686) = (term599 x _67687 _67688 _67686)) = ((term596 x _67687 _67688 _67686) = (term596 x _67687 _67688 _67686)).
Proof. exact (MK_COMB (@lem5186999 x _67687 _67688 _67686) (@lem5187061 x _67687 _67688 _67686)). Qed.
Lemma lem5187064 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187065 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187064 Prop x). Qed.
Lemma lem5187066 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : ((term596 x _67687 _67688 _67686) = (term596 x _67687 _67688 _67686)) = True.
Proof. exact (@lem5187065 (term596 x _67687 _67688 _67686)). Qed.
Lemma lem5187067 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : ((term579 x _67687 _67688 _67686) = (term599 x _67687 _67688 _67686)) = True.
Proof. exact (TRANS (@lem5187062 x _67687 _67688 _67686) (@lem5187066 x _67687 _67688 _67686)). Qed.
Lemma lem5187068 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : True = ((term579 x _67687 _67688 _67686) = (term599 x _67687 _67688 _67686)).
Proof. exact (SYM (@lem5187067 x _67687 _67688 _67686)). Qed.
Lemma lem5187069 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term579 x _67687 _67688 _67686) = (term599 x _67687 _67688 _67686).
Proof. exact (EQ_MP (@lem5187068 x _67687 _67688 _67686) (@lem0)). Qed.
Lemma lem5187070 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term599 x _67687 _67688 _67686.
Proof. exact (EQ_MP (@lem5187069 x _67687 _67688 _67686) (@lem5186705 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5187072 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187073 (_67688 : real) (x : type1021) (_67687 : real) (_67686 : real -> Prop) : (term599 x _67687 _67688 _67686) = (term601 _67688 x _67687 _67686).
Proof. exact (@lem5187072 (term602 _67688 _67686) (term534 x _67687 _67686)). Qed.
Lemma lem5187075 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187076 (_67688 : real) (_67686 : real -> Prop) : (term605 _67688 _67686) = (term606 _67688 _67686).
Proof. exact (@lem5187075 (_67686 = (@EMPTY real)) (term290 _67688 _67686)). Qed.
Lemma lem5187078 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187079 (_67688 : real) (_67686 : real -> Prop) : (term607 _67688 _67686) = (term608 _67688 _67686).
Proof. exact (@lem5187078 (term588 _67688 _67686) (term291 _67688 _67686)). Qed.
Lemma lem5187081 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187082 (_67688 : real) (_67686 : real -> Prop) : (term610 _67688 _67686) = (@IN real _67688 _67686).
Proof. exact (@lem5187081 (@IN real _67688 _67686)). Qed.
Lemma lem5187083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5187084 (_67688 : real) (_67686 : real -> Prop) : (term611 _67688 _67686) = (term612 _67688 _67686).
Proof. exact (MK_COMB (@lem5187083) (@lem5187082 _67688 _67686)). Qed.
Lemma lem5187085 (_67688 : real) (_67686 : real -> Prop) : (term590 _67688 _67686) = (term590 _67688 _67686).
Proof. exact (eq_refl (term590 _67688 _67686)). Qed.
Lemma lem5187086 (_67688 : real) (_67686 : real -> Prop) : (term608 _67688 _67686) = (term613 _67688 _67686).
Proof. exact (MK_COMB (@lem5187084 _67688 _67686) (@lem5187085 _67688 _67686)). Qed.
Lemma lem5187087 (_67688 : real) (_67686 : real -> Prop) : (term607 _67688 _67686) = (term613 _67688 _67686).
Proof. exact (TRANS (@lem5187079 _67688 _67686) (@lem5187086 _67688 _67686)). Qed.
Lemma lem5187088 (_67686 : real -> Prop) : (term38 _67686) = (term38 _67686).
Proof. exact (eq_refl (term38 _67686)). Qed.
Lemma lem5187089 (_67688 : real) (_67686 : real -> Prop) : (term606 _67688 _67686) = (term614 _67688 _67686).
Proof. exact (MK_COMB (@lem5187088 _67686) (@lem5187087 _67688 _67686)). Qed.
Lemma lem5187090 (_67688 : real) (_67686 : real -> Prop) : (term605 _67688 _67686) = (term614 _67688 _67686).
Proof. exact (TRANS (@lem5187076 _67688 _67686) (@lem5187089 _67688 _67686)). Qed.
Lemma lem5187091 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187092 (_67688 : real) (_67686 : real -> Prop) : (term615 _67688 _67686) = (term616 _67688 _67686).
Proof. exact (MK_COMB (@lem5187091) (@lem5187090 _67688 _67686)). Qed.
Lemma lem5187093 (x : type1021) (_67687 : real) (_67686 : real -> Prop) : (term534 x _67687 _67686) = (term534 x _67687 _67686).
Proof. exact (eq_refl (term534 x _67687 _67686)). Qed.
Lemma lem5187094 (_67688 : real) (x : type1021) (_67687 : real) (_67686 : real -> Prop) : (term601 _67688 x _67687 _67686) = (term617 _67688 x _67687 _67686).
Proof. exact (MK_COMB (@lem5187092 _67688 _67686) (@lem5187093 x _67687 _67686)). Qed.
Lemma lem5187095 (_67688 : real) (x : type1021) (_67687 : real) (_67686 : real -> Prop) : (term599 x _67687 _67688 _67686) = (term617 _67688 x _67687 _67686).
Proof. exact (TRANS (@lem5187073 _67688 x _67687 _67686) (@lem5187094 _67688 x _67687 _67686)). Qed.
Lemma lem5187097 (s : real -> Prop) (x' : real) (y : real) (h1 : term590 x' s) (h2 : term168 s x' y) : term613 x' s.
Proof. exact (conj (@lem5186931 s x' y h2) (@lem5186939 x' s h1)). Qed.
Lemma lem5187098 (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term590 x' s) (h2 : term252 b x' s y) (h3 : term168 s x' y) : term614 x' s.
Proof. exact (conj (@lem5186924 b x' s y h2) (@lem5187097 s x' y h1 h3)). Qed.
Lemma lem5187100 (_67688 : real) (_67687 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term617 _67688 x _67687 _67686.
Proof. exact (EQ_MP (@lem5187095 _67688 x _67687 _67686) (@lem5187070 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5187101 (x' : real) (_67687 : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term617 x' x _67687 s.
Proof. exact (@lem5187100 x' _67687 s x h1). Qed.
Lemma lem5187104 (_67687 : real) (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term534 x _67687 s.
Proof. exact (@lem5187101 x' _67687 s x h1 (@lem5187098 b s x' y h2 h3 h4)). Qed.
Lemma lem5187105 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term534 x b s.
Proof. exact (@lem5187104 b x b s x' y h1 h2 h3 h4). Qed.
Lemma lem5187106 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term618 x b s.
Proof. exact (fun h0 : term619 x b s => @lem5187105 x b s x' y h1 h2 h3 h4). Qed.
Lemma lem5187108 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187109 (x : type1021) (b : real) (s : real -> Prop) : (term618 x b s) = (term534 x b s).
Proof. exact (@lem5187108 (term534 x b s)). Qed.
Lemma lem5187110 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term534 x b s.
Proof. exact (EQ_MP (@lem5187109 x b s) (@lem5187106 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187116 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187117 (b : real) (_67689 : real) (s : real -> Prop) : (term55 s _67689 b) = (term620 b _67689 s).
Proof. exact (@lem5187116 (real_le _67689 b) (term588 _67689 s)). Qed.
Lemma lem5187123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5187124 (b : real) (_67689 : real) (s : real -> Prop) : (term621 s _67689 b) = (term622 b _67689 s).
Proof. exact (MK_COMB (@lem5187123) (@lem5187117 b _67689 s)). Qed.
Lemma lem5187130 (b : real) (_67689 : real) (s : real -> Prop) : (term620 b _67689 s) = (term620 b _67689 s).
Proof. exact (eq_refl (term620 b _67689 s)). Qed.
Lemma lem5187131 (b : real) (_67689 : real) (s : real -> Prop) : ((term55 s _67689 b) = (term620 b _67689 s)) = ((term620 b _67689 s) = (term620 b _67689 s)).
Proof. exact (MK_COMB (@lem5187124 b _67689 s) (@lem5187130 b _67689 s)). Qed.
Lemma lem5187133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187134 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187133 Prop x). Qed.
Lemma lem5187135 (b : real) (_67689 : real) (s : real -> Prop) : ((term620 b _67689 s) = (term620 b _67689 s)) = True.
Proof. exact (@lem5187134 (term620 b _67689 s)). Qed.
Lemma lem5187136 (b : real) (_67689 : real) (s : real -> Prop) : ((term55 s _67689 b) = (term620 b _67689 s)) = True.
Proof. exact (TRANS (@lem5187131 b _67689 s) (@lem5187135 b _67689 s)). Qed.
Lemma lem5187137 (b : real) (_67689 : real) (s : real -> Prop) : True = ((term55 s _67689 b) = (term620 b _67689 s)).
Proof. exact (SYM (@lem5187136 b _67689 s)). Qed.
Lemma lem5187138 (b : real) (_67689 : real) (s : real -> Prop) : (term55 s _67689 b) = (term620 b _67689 s).
Proof. exact (EQ_MP (@lem5187137 b _67689 s) (@lem0)). Qed.
Lemma lem5187139 (_67689 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term620 b _67689 s.
Proof. exact (EQ_MP (@lem5187138 b _67689 s) (@lem5186619 _67689 b x' s y h1)). Qed.
Lemma lem5187141 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187142 (s : real -> Prop) (_67689 : real) (b : real) : (term620 b _67689 s) = (term623 s _67689 b).
Proof. exact (@lem5187141 (term588 _67689 s) (real_le _67689 b)). Qed.
Lemma lem5187144 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187145 (_67689 : real) (s : real -> Prop) : (term610 _67689 s) = (@IN real _67689 s).
Proof. exact (@lem5187144 (@IN real _67689 s)). Qed.
Lemma lem5187146 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187147 (_67689 : real) (s : real -> Prop) : (term624 _67689 s) = (term625 _67689 s).
Proof. exact (MK_COMB (@lem5187146) (@lem5187145 _67689 s)). Qed.
Lemma lem5187148 (_67689 : real) (b : real) : (real_le _67689 b) = (real_le _67689 b).
Proof. exact (eq_refl (real_le _67689 b)). Qed.
Lemma lem5187149 (s : real -> Prop) (_67689 : real) (b : real) : (term623 s _67689 b) = (term24 s _67689 b).
Proof. exact (MK_COMB (@lem5187147 _67689 s) (@lem5187148 _67689 b)). Qed.
Lemma lem5187150 (s : real -> Prop) (_67689 : real) (b : real) : (term620 b _67689 s) = (term24 s _67689 b).
Proof. exact (TRANS (@lem5187142 s _67689 b) (@lem5187149 s _67689 b)). Qed.
Lemma lem5187153 (_67689 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term24 s _67689 b.
Proof. exact (EQ_MP (@lem5187150 s _67689 b) (@lem5187139 _67689 b x' s y h1)). Qed.
Lemma lem5187154 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term626 x s b.
Proof. exact (@lem5187153 (x s b) b x' s y h1). Qed.
Lemma lem5187157 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term627 x s b.
Proof. exact (@lem5187154 x b x' s y h3 (@lem5187110 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187158 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term628 x s b.
Proof. exact (fun h0 : term535 x s b => @lem5187157 x b s x' y h1 h2 h3 h4). Qed.
Lemma lem5187160 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187161 (x : type1021) (s : real -> Prop) (b : real) : (term628 x s b) = (term627 x s b).
Proof. exact (@lem5187160 (term627 x s b)). Qed.
Lemma lem5187162 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term627 x s b.
Proof. exact (EQ_MP (@lem5187161 x s b) (@lem5187158 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187164 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : @IN real x' s.
Proof. exact (proj1 (@lem5186004 s x' y h1)). Qed.
Lemma lem5187165 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term587 x' s.
Proof. exact (fun h0 : term588 x' s => @lem5187164 s x' y h1). Qed.
Lemma lem5187167 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187168 (x' : real) (s : real -> Prop) : (term587 x' s) = (@IN real x' s).
Proof. exact (@lem5187167 (@IN real x' s)). Qed.
Lemma lem5187169 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : @IN real x' s.
Proof. exact (EQ_MP (@lem5187168 x' s) (@lem5187165 s x' y h1)). Qed.
Lemma lem5187187 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187188 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term629 x _67687 _67688 _67686) = (term630 x _67687 _67688 _67686).
Proof. exact (@lem5187187 (term588 _67688 _67686) (term535 x _67686 _67687) (term291 _67688 _67686)). Qed.
Lemma lem5187202 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187203 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term631 x _67687 _67688 _67686) = (term632 _67688 x _67686 _67687).
Proof. exact (@lem5187202 (term291 _67688 _67686) (term535 x _67686 _67687)). Qed.
Lemma lem5187209 (_67688 : real) (_67686 : real -> Prop) : (term633 _67688 _67686) = (term633 _67688 _67686).
Proof. exact (eq_refl (term633 _67688 _67686)). Qed.
Lemma lem5187210 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term630 x _67687 _67688 _67686) = (term634 _67688 x _67686 _67687).
Proof. exact (MK_COMB (@lem5187209 _67688 _67686) (@lem5187203 _67688 x _67686 _67687)). Qed.
Lemma lem5187214 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187215 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term634 _67688 x _67686 _67687) = (term635 _67688 x _67686 _67687).
Proof. exact (@lem5187214 (term291 _67688 _67686) (term588 _67688 _67686) (term535 x _67686 _67687)). Qed.
Lemma lem5187231 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term630 x _67687 _67688 _67686) = (term635 _67688 x _67686 _67687).
Proof. exact (TRANS (@lem5187210 _67688 x _67686 _67687) (@lem5187215 _67688 x _67686 _67687)). Qed.
Lemma lem5187232 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term629 x _67687 _67688 _67686) = (term635 _67688 x _67686 _67687).
Proof. exact (TRANS (@lem5187188 x _67687 _67688 _67686) (@lem5187231 _67688 x _67686 _67687)). Qed.
Lemma lem5187233 (_67686 : real -> Prop) : (term286 _67686) = (term286 _67686).
Proof. exact (eq_refl (term286 _67686)). Qed.
Lemma lem5187234 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term580 x _67687 _67688 _67686) = (term636 _67688 x _67686 _67687).
Proof. exact (MK_COMB (@lem5187233 _67686) (@lem5187232 _67688 x _67686 _67687)). Qed.
Lemma lem5187245 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5187246 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term637 x _67687 _67688 _67686) = (term638 _67688 x _67686 _67687).
Proof. exact (MK_COMB (@lem5187245) (@lem5187234 _67688 x _67686 _67687)). Qed.
Lemma lem5187250 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187251 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term639 x _67687 _67688 _67686) = (term640 x _67687 _67688 _67686).
Proof. exact (@lem5187250 (_67686 = (@EMPTY real)) (term291 _67688 _67686) (term641 x _67687 _67688 _67686)). Qed.
Lemma lem5187277 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187278 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term641 x _67687 _67688 _67686) = (term642 _67688 x _67686 _67687).
Proof. exact (@lem5187277 (term588 _67688 _67686) (term535 x _67686 _67687)). Qed.
Lemma lem5187284 (_67688 : real) (_67686 : real -> Prop) : (term643 _67688 _67686) = (term643 _67688 _67686).
Proof. exact (eq_refl (term643 _67688 _67686)). Qed.
Lemma lem5187285 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term644 x _67687 _67688 _67686) = (term635 _67688 x _67686 _67687).
Proof. exact (MK_COMB (@lem5187284 _67688 _67686) (@lem5187278 _67688 x _67686 _67687)). Qed.
Lemma lem5187296 (_67686 : real -> Prop) : (term286 _67686) = (term286 _67686).
Proof. exact (eq_refl (term286 _67686)). Qed.
Lemma lem5187297 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term640 x _67687 _67688 _67686) = (term636 _67688 x _67686 _67687).
Proof. exact (MK_COMB (@lem5187296 _67686) (@lem5187285 _67688 x _67686 _67687)). Qed.
Lemma lem5187308 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term639 x _67687 _67688 _67686) = (term636 _67688 x _67686 _67687).
Proof. exact (TRANS (@lem5187251 x _67687 _67688 _67686) (@lem5187297 _67688 x _67686 _67687)). Qed.
Lemma lem5187309 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : ((term580 x _67687 _67688 _67686) = (term639 x _67687 _67688 _67686)) = ((term636 _67688 x _67686 _67687) = (term636 _67688 x _67686 _67687)).
Proof. exact (MK_COMB (@lem5187246 _67688 x _67686 _67687) (@lem5187308 _67688 x _67686 _67687)). Qed.
Lemma lem5187311 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187312 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187311 Prop x). Qed.
Lemma lem5187313 (_67688 : real) (x : type1021) (_67686 : real -> Prop) (_67687 : real) : ((term636 _67688 x _67686 _67687) = (term636 _67688 x _67686 _67687)) = True.
Proof. exact (@lem5187312 (term636 _67688 x _67686 _67687)). Qed.
Lemma lem5187314 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : ((term580 x _67687 _67688 _67686) = (term639 x _67687 _67688 _67686)) = True.
Proof. exact (TRANS (@lem5187309 _67688 x _67686 _67687) (@lem5187313 _67688 x _67686 _67687)). Qed.
Lemma lem5187315 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : True = ((term580 x _67687 _67688 _67686) = (term639 x _67687 _67688 _67686)).
Proof. exact (SYM (@lem5187314 x _67687 _67688 _67686)). Qed.
Lemma lem5187316 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term580 x _67687 _67688 _67686) = (term639 x _67687 _67688 _67686).
Proof. exact (EQ_MP (@lem5187315 x _67687 _67688 _67686) (@lem0)). Qed.
Lemma lem5187317 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term639 x _67687 _67688 _67686.
Proof. exact (EQ_MP (@lem5187316 x _67687 _67688 _67686) (@lem5186721 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5187319 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187320 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term639 x _67687 _67688 _67686) = (term645 x _67687 _67688 _67686).
Proof. exact (@lem5187319 (term646 x _67687 _67688 _67686) (term291 _67688 _67686)). Qed.
Lemma lem5187322 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187323 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term647 x _67687 _67688 _67686) = (term648 x _67687 _67688 _67686).
Proof. exact (@lem5187322 (_67686 = (@EMPTY real)) (term641 x _67687 _67688 _67686)). Qed.
Lemma lem5187325 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187326 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term649 x _67687 _67688 _67686) = (term650 x _67687 _67688 _67686).
Proof. exact (@lem5187325 (term535 x _67686 _67687) (term588 _67688 _67686)). Qed.
Lemma lem5187328 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187329 (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term651 x _67686 _67687) = (term627 x _67686 _67687).
Proof. exact (@lem5187328 (term627 x _67686 _67687)). Qed.
Lemma lem5187330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5187331 (x : type1021) (_67686 : real -> Prop) (_67687 : real) : (term652 x _67686 _67687) = (term653 x _67686 _67687).
Proof. exact (MK_COMB (@lem5187330) (@lem5187329 x _67686 _67687)). Qed.
Lemma lem5187333 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187334 (_67688 : real) (_67686 : real -> Prop) : (term610 _67688 _67686) = (@IN real _67688 _67686).
Proof. exact (@lem5187333 (@IN real _67688 _67686)). Qed.
Lemma lem5187335 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term650 x _67687 _67688 _67686) = (term654 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5187331 x _67686 _67687) (@lem5187334 _67688 _67686)). Qed.
Lemma lem5187336 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term649 x _67687 _67688 _67686) = (term654 x _67687 _67688 _67686).
Proof. exact (TRANS (@lem5187326 x _67687 _67688 _67686) (@lem5187335 x _67687 _67688 _67686)). Qed.
Lemma lem5187337 (_67686 : real -> Prop) : (term38 _67686) = (term38 _67686).
Proof. exact (eq_refl (term38 _67686)). Qed.
Lemma lem5187338 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term648 x _67687 _67688 _67686) = (term655 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5187337 _67686) (@lem5187336 x _67687 _67688 _67686)). Qed.
Lemma lem5187339 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term647 x _67687 _67688 _67686) = (term655 x _67687 _67688 _67686).
Proof. exact (TRANS (@lem5187323 x _67687 _67688 _67686) (@lem5187338 x _67687 _67688 _67686)). Qed.
Lemma lem5187340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187341 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term656 x _67687 _67688 _67686) = (term657 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5187340) (@lem5187339 x _67687 _67688 _67686)). Qed.
Lemma lem5187342 (_67688 : real) (_67686 : real -> Prop) : (term291 _67688 _67686) = (term291 _67688 _67686).
Proof. exact (eq_refl (term291 _67688 _67686)). Qed.
Lemma lem5187343 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term645 x _67687 _67688 _67686) = (term658 x _67687 _67688 _67686).
Proof. exact (MK_COMB (@lem5187341 x _67687 _67688 _67686) (@lem5187342 _67688 _67686)). Qed.
Lemma lem5187344 (x : type1021) (_67687 : real) (_67688 : real) (_67686 : real -> Prop) : (term639 x _67687 _67688 _67686) = (term658 x _67687 _67688 _67686).
Proof. exact (TRANS (@lem5187320 x _67687 _67688 _67686) (@lem5187343 x _67687 _67688 _67686)). Qed.
Lemma lem5187346 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term654 x b x' s.
Proof. exact (conj (@lem5187162 x b s x' y h1 h2 h3 h4) (@lem5187169 s x' y h4)). Qed.
Lemma lem5187347 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term655 x b x' s.
Proof. exact (conj (@lem5186917 b x' s y h3) (@lem5187346 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187349 (_67687 : real) (_67688 : real) (_67686 : real -> Prop) (x : type1021) (h1 : term442 x) : term658 x _67687 _67688 _67686.
Proof. exact (EQ_MP (@lem5187344 x _67687 _67688 _67686) (@lem5187317 _67687 _67688 _67686 x h1)). Qed.
Lemma lem5187350 (b : real) (x' : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term658 x b x' s.
Proof. exact (@lem5187349 b x' s x h1). Qed.
Lemma lem5187353 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term590 x' s) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term291 x' s.
Proof. exact (@lem5187350 b x' s x h1 (@lem5187347 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187354 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term252 b x' s y) (h3 : term168 s x' y) : term659 x' s.
Proof. exact (fun h0 : term590 x' s => @lem5187353 x b s x' y h1 h0 h2 h3). Qed.
Lemma lem5187356 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187357 (x' : real) (s : real -> Prop) : (term659 x' s) = (term291 x' s).
Proof. exact (@lem5187356 (term291 x' s)). Qed.
Lemma lem5187358 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term252 b x' s y) (h3 : term168 s x' y) : term291 x' s.
Proof. exact (EQ_MP (@lem5187357 x' s) (@lem5187354 x b s x' y h1 h2 h3)). Qed.
Lemma lem5187360 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term23 s y.
Proof. exact (proj1 (@lem5186002 s x' y h1)). Qed.
Lemma lem5187361 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term660 s y.
Proof. exact (fun h0 : term581 s y => @lem5187360 s x' y h1). Qed.
Lemma lem5187363 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187364 (s : real -> Prop) (y : real) : (term660 s y) = (term23 s y).
Proof. exact (@lem5187363 (term23 s y)). Qed.
Lemma lem5187365 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term23 s y.
Proof. exact (EQ_MP (@lem5187364 s y) (@lem5187361 s x' y h1)). Qed.
Lemma lem5187381 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187382 (_67683 : real) (_67684 : real) (_67685 : real) : (term661 _67684 _67683 _67685) = (term662 _67683 _67684 _67685).
Proof. exact (@lem5187381 (real_le _67683 _67685) (term578 _67684 _67685)). Qed.
Lemma lem5187388 (_67683 : real) (_67684 : real) : (term663 _67683 _67684) = (term663 _67683 _67684).
Proof. exact (eq_refl (term663 _67683 _67684)). Qed.
Lemma lem5187389 (_67683 : real) (_67684 : real) (_67685 : real) : (term577 _67684 _67683 _67685) = (term664 _67683 _67684 _67685).
Proof. exact (MK_COMB (@lem5187388 _67683 _67684) (@lem5187382 _67683 _67684 _67685)). Qed.
Lemma lem5187393 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187394 (_67683 : real) (_67684 : real) (_67685 : real) : (term664 _67683 _67684 _67685) = (term665 _67683 _67684 _67685).
Proof. exact (@lem5187393 (real_le _67683 _67685) (term578 _67683 _67684) (term578 _67684 _67685)). Qed.
Lemma lem5187410 (_67683 : real) (_67684 : real) (_67685 : real) : (term577 _67684 _67683 _67685) = (term665 _67683 _67684 _67685).
Proof. exact (TRANS (@lem5187389 _67683 _67684 _67685) (@lem5187394 _67683 _67684 _67685)). Qed.
Lemma lem5187411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5187412 (_67683 : real) (_67684 : real) (_67685 : real) : (term666 _67684 _67683 _67685) = (term667 _67683 _67684 _67685).
Proof. exact (MK_COMB (@lem5187411) (@lem5187410 _67683 _67684 _67685)). Qed.
Lemma lem5187428 (_67683 : real) (_67684 : real) (_67685 : real) : (term665 _67683 _67684 _67685) = (term665 _67683 _67684 _67685).
Proof. exact (eq_refl (term665 _67683 _67684 _67685)). Qed.
Lemma lem5187429 (_67683 : real) (_67684 : real) (_67685 : real) : ((term577 _67684 _67683 _67685) = (term665 _67683 _67684 _67685)) = ((term665 _67683 _67684 _67685) = (term665 _67683 _67684 _67685)).
Proof. exact (MK_COMB (@lem5187412 _67683 _67684 _67685) (@lem5187428 _67683 _67684 _67685)). Qed.
Lemma lem5187431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187432 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187431 Prop x). Qed.
Lemma lem5187433 (_67683 : real) (_67684 : real) (_67685 : real) : ((term665 _67683 _67684 _67685) = (term665 _67683 _67684 _67685)) = True.
Proof. exact (@lem5187432 (term665 _67683 _67684 _67685)). Qed.
Lemma lem5187434 (_67683 : real) (_67684 : real) (_67685 : real) : ((term577 _67684 _67683 _67685) = (term665 _67683 _67684 _67685)) = True.
Proof. exact (TRANS (@lem5187429 _67683 _67684 _67685) (@lem5187433 _67683 _67684 _67685)). Qed.
Lemma lem5187435 (_67683 : real) (_67684 : real) (_67685 : real) : True = ((term577 _67684 _67683 _67685) = (term665 _67683 _67684 _67685)).
Proof. exact (SYM (@lem5187434 _67683 _67684 _67685)). Qed.
Lemma lem5187436 (_67683 : real) (_67684 : real) (_67685 : real) : (term577 _67684 _67683 _67685) = (term665 _67683 _67684 _67685).
Proof. exact (EQ_MP (@lem5187435 _67683 _67684 _67685) (@lem0)). Qed.
Lemma lem5187437 (_67683 : real) (_67684 : real) (_67685 : real) (h1 : term49) : term665 _67683 _67684 _67685.
Proof. exact (EQ_MP (@lem5187436 _67683 _67684 _67685) (@lem5186611 _67684 _67683 _67685 h1)). Qed.
Lemma lem5187439 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187440 (_67684 : real) (_67683 : real) (_67685 : real) : (term665 _67683 _67684 _67685) = (term668 _67684 _67683 _67685).
Proof. exact (@lem5187439 (term263 _67683 _67684 _67685) (real_le _67683 _67685)). Qed.
Lemma lem5187442 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187443 (_67683 : real) (_67684 : real) (_67685 : real) : (term669 _67683 _67684 _67685) = (term670 _67683 _67684 _67685).
Proof. exact (@lem5187442 (term578 _67683 _67684) (term578 _67684 _67685)). Qed.
Lemma lem5187445 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187446 (_67683 : real) (_67684 : real) : (term671 _67683 _67684) = (real_le _67683 _67684).
Proof. exact (@lem5187445 (real_le _67683 _67684)). Qed.
Lemma lem5187447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5187448 (_67683 : real) (_67684 : real) : (term672 _67683 _67684) = (term673 _67683 _67684).
Proof. exact (MK_COMB (@lem5187447) (@lem5187446 _67683 _67684)). Qed.
Lemma lem5187450 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187451 (_67684 : real) (_67685 : real) : (term671 _67684 _67685) = (real_le _67684 _67685).
Proof. exact (@lem5187450 (real_le _67684 _67685)). Qed.
Lemma lem5187452 (_67683 : real) (_67684 : real) (_67685 : real) : (term670 _67683 _67684 _67685) = (term268 _67683 _67684 _67685).
Proof. exact (MK_COMB (@lem5187448 _67683 _67684) (@lem5187451 _67684 _67685)). Qed.
Lemma lem5187453 (_67683 : real) (_67684 : real) (_67685 : real) : (term669 _67683 _67684 _67685) = (term268 _67683 _67684 _67685).
Proof. exact (TRANS (@lem5187443 _67683 _67684 _67685) (@lem5187452 _67683 _67684 _67685)). Qed.
Lemma lem5187454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187455 (_67683 : real) (_67684 : real) (_67685 : real) : (term674 _67683 _67684 _67685) = (term675 _67683 _67684 _67685).
Proof. exact (MK_COMB (@lem5187454) (@lem5187453 _67683 _67684 _67685)). Qed.
Lemma lem5187456 (_67683 : real) (_67685 : real) : (real_le _67683 _67685) = (real_le _67683 _67685).
Proof. exact (eq_refl (real_le _67683 _67685)). Qed.
Lemma lem5187457 (_67684 : real) (_67683 : real) (_67685 : real) : (term668 _67684 _67683 _67685) = (term43 _67684 _67683 _67685).
Proof. exact (MK_COMB (@lem5187455 _67683 _67684 _67685) (@lem5187456 _67683 _67685)). Qed.
Lemma lem5187458 (_67684 : real) (_67683 : real) (_67685 : real) : (term665 _67683 _67684 _67685) = (term43 _67684 _67683 _67685).
Proof. exact (TRANS (@lem5187440 _67684 _67683 _67685) (@lem5187457 _67684 _67683 _67685)). Qed.
Lemma lem5187460 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term252 b x' s y) (h3 : term168 s x' y) : term676 x' s y.
Proof. exact (conj (@lem5187358 x b s x' y h1 h2 h3) (@lem5187365 s x' y h3)). Qed.
Lemma lem5187462 (_67684 : real) (_67683 : real) (_67685 : real) (h1 : term49) : term43 _67684 _67683 _67685.
Proof. exact (EQ_MP (@lem5187458 _67684 _67683 _67685) (@lem5187437 _67683 _67684 _67685 h1)). Qed.
Lemma lem5187463 (s : real -> Prop) (x' : real) (y : real) (h1 : term49) : term677 s x' y.
Proof. exact (@lem5187462 (sup s) x' y h1). Qed.
Lemma lem5187466 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s x' y) : real_le x' y.
Proof. exact (@lem5187463 s x' y h2 (@lem5187460 x b s x' y h1 h3 h4)). Qed.
Lemma lem5187467 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term678 x' y.
Proof. exact (fun h0 : term578 x' y => @lem5187466 x b s x' y h1 h2 h3 h4). Qed.
Lemma lem5187469 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187470 (x' : real) (y : real) : (term678 x' y) = (real_le x' y).
Proof. exact (@lem5187469 (real_le x' y)). Qed.
Lemma lem5187471 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s x' y) : real_le x' y.
Proof. exact (EQ_MP (@lem5187470 x' y) (@lem5187467 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187474 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5187476 (x' : real) (y : real) : (term578 x' y) = (term679 x' y).
Proof. exact (@lem5187474 (real_le x' y)). Qed.
Lemma lem5187479 (s : real -> Prop) (x' : real) (y : real) (h1 : term168 s x' y) : term679 x' y.
Proof. exact (EQ_MP (@lem5187476 x' y) (@lem5186625 s x' y h1)). Qed.
Lemma lem5187482 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s x' y) : False.
Proof. exact (@lem5187479 s x' y h4 (@lem5187471 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187483 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s x' y) : term680.
Proof. exact (fun h0 : ~ False => @lem5187482 x b s x' y h1 h2 h3 h4). Qed.
Lemma lem5187485 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187486 : term680 = False.
Proof. exact (@lem5187485 False). Qed.
Lemma lem5187487 (x : type1021) (b : real) (s : real -> Prop) (x' : real) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s x' y) : False.
Proof. exact (EQ_MP (@lem5187486) (@lem5187483 x b s x' y h1 h2 h3 h4)). Qed.
Lemma lem5187554 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5187555 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term585 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5187554 b x' s y h1). Qed.
Lemma lem5187557 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187558 (s : real -> Prop) : (term585 s) = (term148 s).
Proof. exact (@lem5187557 (s = (@EMPTY real))). Qed.
Lemma lem5187559 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5187558 s) (@lem5187555 b x' s y h1)). Qed.
Lemma lem5187561 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5187562 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term585 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5187561 b x' s y h1). Qed.
Lemma lem5187564 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187565 (s : real -> Prop) : (term585 s) = (term148 s).
Proof. exact (@lem5187564 (s = (@EMPTY real))). Qed.
Lemma lem5187566 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5187565 s) (@lem5187562 b x' s y h1)). Qed.
Lemma lem5187569 (x : type1021) (y : real) (s : real -> Prop) (h1 : term619 x y s) : term619 x y s.
Proof. exact (h1). Qed.
Lemma lem5187570 (x : type1021) (y : real) (s : real -> Prop) (h1 : term619 x y s) : term681 x y s.
Proof. exact (fun h0 : term534 x y s => @lem5187569 x y s h1). Qed.
Lemma lem5187572 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187573 (x : type1021) (y : real) (s : real -> Prop) : (term681 x y s) = (term619 x y s).
Proof. exact (@lem5187572 (term534 x y s)). Qed.
Lemma lem5187574 (x : type1021) (y : real) (s : real -> Prop) (h1 : term619 x y s) : term619 x y s.
Proof. exact (EQ_MP (@lem5187573 x y s) (@lem5187570 x y s h1)). Qed.
Lemma lem5187577 (s : real -> Prop) (y : real) (h1 : term581 s y) : term581 s y.
Proof. exact (h1). Qed.
Lemma lem5187578 (s : real -> Prop) (y : real) (h1 : term581 s y) : term682 s y.
Proof. exact (fun h0 : term23 s y => @lem5187577 s y h1). Qed.
Lemma lem5187580 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187581 (s : real -> Prop) (y : real) : (term682 s y) = (term581 s y).
Proof. exact (@lem5187580 (term23 s y)). Qed.
Lemma lem5187582 (s : real -> Prop) (y : real) (h1 : term581 s y) : term581 s y.
Proof. exact (EQ_MP (@lem5187581 s y) (@lem5187578 s y h1)). Qed.
Lemma lem5187615 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187616 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term683 x _67694 _67693 _67695) = (term684 x _67694 _67693 _67695).
Proof. exact (@lem5187615 (_67693 = (@EMPTY real)) (term534 x _67695 _67693) (term685 x _67694 _67693 _67695)). Qed.
Lemma lem5187632 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187633 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term686 x _67694 _67693 _67695) = (term687 _67694 x _67693 _67695).
Proof. exact (@lem5187632 (term534 x _67694 _67693) (term534 x _67695 _67693) (term23 _67693 _67695)). Qed.
Lemma lem5187649 (_67693 : real -> Prop) : (term286 _67693) = (term286 _67693).
Proof. exact (eq_refl (term286 _67693)). Qed.
Lemma lem5187650 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term684 x _67694 _67693 _67695) = (term583 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187649 _67693) (@lem5187633 _67694 x _67693 _67695)). Qed.
Lemma lem5187661 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term683 x _67694 _67693 _67695) = (term583 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5187616 x _67694 _67693 _67695) (@lem5187650 _67694 x _67693 _67695)). Qed.
Lemma lem5187662 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term688 _67694 x _67693 _67695) = (term688 _67694 x _67693 _67695).
Proof. exact (eq_refl (term688 _67694 x _67693 _67695)). Qed.
Lemma lem5187663 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : ((term583 _67694 x _67693 _67695) = (term683 x _67694 _67693 _67695)) = ((term583 _67694 x _67693 _67695) = (term583 _67694 x _67693 _67695)).
Proof. exact (MK_COMB (@lem5187662 _67694 x _67693 _67695) (@lem5187661 _67694 x _67693 _67695)). Qed.
Lemma lem5187665 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187666 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187665 Prop x). Qed.
Lemma lem5187667 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : ((term583 _67694 x _67693 _67695) = (term583 _67694 x _67693 _67695)) = True.
Proof. exact (@lem5187666 (term583 _67694 x _67693 _67695)). Qed.
Lemma lem5187668 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : ((term583 _67694 x _67693 _67695) = (term683 x _67694 _67693 _67695)) = True.
Proof. exact (TRANS (@lem5187663 _67694 x _67693 _67695) (@lem5187667 _67694 x _67693 _67695)). Qed.
Lemma lem5187669 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : True = ((term583 _67694 x _67693 _67695) = (term683 x _67694 _67693 _67695)).
Proof. exact (SYM (@lem5187668 x _67694 _67693 _67695)). Qed.
Lemma lem5187670 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term583 _67694 x _67693 _67695) = (term683 x _67694 _67693 _67695).
Proof. exact (EQ_MP (@lem5187669 x _67694 _67693 _67695) (@lem0)). Qed.
Lemma lem5187671 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term683 x _67694 _67693 _67695.
Proof. exact (EQ_MP (@lem5187670 x _67694 _67693 _67695) (@lem5186797 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5187673 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187674 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term683 x _67694 _67693 _67695) = (term689 _67694 x _67695 _67693).
Proof. exact (@lem5187673 (term690 x _67694 _67693 _67695) (term534 x _67695 _67693)). Qed.
Lemma lem5187676 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187677 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term691 x _67694 _67693 _67695) = (term692 x _67694 _67693 _67695).
Proof. exact (@lem5187676 (_67693 = (@EMPTY real)) (term685 x _67694 _67693 _67695)). Qed.
Lemma lem5187679 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187680 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term693 x _67694 _67693 _67695) = (term694 x _67694 _67693 _67695).
Proof. exact (@lem5187679 (term534 x _67694 _67693) (term23 _67693 _67695)). Qed.
Lemma lem5187681 (_67693 : real -> Prop) : (term38 _67693) = (term38 _67693).
Proof. exact (eq_refl (term38 _67693)). Qed.
Lemma lem5187682 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term692 x _67694 _67693 _67695) = (term695 x _67694 _67693 _67695).
Proof. exact (MK_COMB (@lem5187681 _67693) (@lem5187680 x _67694 _67693 _67695)). Qed.
Lemma lem5187683 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term691 x _67694 _67693 _67695) = (term695 x _67694 _67693 _67695).
Proof. exact (TRANS (@lem5187677 x _67694 _67693 _67695) (@lem5187682 x _67694 _67693 _67695)). Qed.
Lemma lem5187684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187685 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term696 x _67694 _67693 _67695) = (term697 x _67694 _67693 _67695).
Proof. exact (MK_COMB (@lem5187684) (@lem5187683 x _67694 _67693 _67695)). Qed.
Lemma lem5187686 (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term534 x _67695 _67693) = (term534 x _67695 _67693).
Proof. exact (eq_refl (term534 x _67695 _67693)). Qed.
Lemma lem5187687 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term689 _67694 x _67695 _67693) = (term698 _67694 x _67695 _67693).
Proof. exact (MK_COMB (@lem5187685 x _67694 _67693 _67695) (@lem5187686 x _67695 _67693)). Qed.
Lemma lem5187688 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term683 x _67694 _67693 _67695) = (term698 _67694 x _67695 _67693).
Proof. exact (TRANS (@lem5187674 _67694 x _67695 _67693) (@lem5187687 _67694 x _67695 _67693)). Qed.
Lemma lem5187690 (x : type1021) (s : real -> Prop) (y : real) (h1 : term619 x y s) (h2 : term581 s y) : term699 x s y.
Proof. exact (conj (@lem5187574 x y s h1) (@lem5187582 s y h2)). Qed.
Lemma lem5187691 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term619 x y s) (h2 : term581 s y) (h3 : term252 b x' s y) : term700 x s y.
Proof. exact (conj (@lem5187566 b x' s y h3) (@lem5187690 x s y h1 h2)). Qed.
Lemma lem5187693 (_67694 : real) (_67695 : real) (_67693 : real -> Prop) (x : type1021) (h1 : term442 x) : term698 _67694 x _67695 _67693.
Proof. exact (EQ_MP (@lem5187688 _67694 x _67695 _67693) (@lem5187671 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5187694 (y : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term701 x y s.
Proof. exact (@lem5187693 y y s x h1). Qed.
Lemma lem5187697 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term619 x y s) (h3 : term581 s y) (h4 : term252 b x' s y) : term534 x y s.
Proof. exact (@lem5187694 y s x h1 (@lem5187691 x b x' s y h2 h3 h4)). Qed.
Lemma lem5187698 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term252 b x' s y) : term618 x y s.
Proof. exact (fun h0 : term619 x y s => @lem5187697 x b x' s y h1 h0 h2 h3). Qed.
Lemma lem5187700 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187701 (x : type1021) (y : real) (s : real -> Prop) : (term618 x y s) = (term534 x y s).
Proof. exact (@lem5187700 (term534 x y s)). Qed.
Lemma lem5187702 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term252 b x' s y) : term534 x y s.
Proof. exact (EQ_MP (@lem5187701 x y s) (@lem5187698 x b x' s y h1 h2 h3)). Qed.
Lemma lem5187708 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187709 (y : real) (_67697 : real) (s : real -> Prop) : (term55 s _67697 y) = (term620 y _67697 s).
Proof. exact (@lem5187708 (real_le _67697 y) (term588 _67697 s)). Qed.
Lemma lem5187715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5187716 (y : real) (_67697 : real) (s : real -> Prop) : (term621 s _67697 y) = (term622 y _67697 s).
Proof. exact (MK_COMB (@lem5187715) (@lem5187709 y _67697 s)). Qed.
Lemma lem5187722 (y : real) (_67697 : real) (s : real -> Prop) : (term620 y _67697 s) = (term620 y _67697 s).
Proof. exact (eq_refl (term620 y _67697 s)). Qed.
Lemma lem5187723 (y : real) (_67697 : real) (s : real -> Prop) : ((term55 s _67697 y) = (term620 y _67697 s)) = ((term620 y _67697 s) = (term620 y _67697 s)).
Proof. exact (MK_COMB (@lem5187716 y _67697 s) (@lem5187722 y _67697 s)). Qed.
Lemma lem5187725 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187726 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187725 Prop x). Qed.
Lemma lem5187727 (y : real) (_67697 : real) (s : real -> Prop) : ((term620 y _67697 s) = (term620 y _67697 s)) = True.
Proof. exact (@lem5187726 (term620 y _67697 s)). Qed.
Lemma lem5187728 (y : real) (_67697 : real) (s : real -> Prop) : ((term55 s _67697 y) = (term620 y _67697 s)) = True.
Proof. exact (TRANS (@lem5187723 y _67697 s) (@lem5187727 y _67697 s)). Qed.
Lemma lem5187729 (y : real) (_67697 : real) (s : real -> Prop) : True = ((term55 s _67697 y) = (term620 y _67697 s)).
Proof. exact (SYM (@lem5187728 y _67697 s)). Qed.
Lemma lem5187730 (y : real) (_67697 : real) (s : real -> Prop) : (term55 s _67697 y) = (term620 y _67697 s).
Proof. exact (EQ_MP (@lem5187729 y _67697 s) (@lem0)). Qed.
Lemma lem5187731 (_67697 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term620 y _67697 s.
Proof. exact (EQ_MP (@lem5187730 y _67697 s) (@lem5186749 _67697 s y h1)). Qed.
Lemma lem5187733 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187734 (s : real -> Prop) (_67697 : real) (y : real) : (term620 y _67697 s) = (term623 s _67697 y).
Proof. exact (@lem5187733 (term588 _67697 s) (real_le _67697 y)). Qed.
Lemma lem5187736 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187737 (_67697 : real) (s : real -> Prop) : (term610 _67697 s) = (@IN real _67697 s).
Proof. exact (@lem5187736 (@IN real _67697 s)). Qed.
Lemma lem5187738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187739 (_67697 : real) (s : real -> Prop) : (term624 _67697 s) = (term625 _67697 s).
Proof. exact (MK_COMB (@lem5187738) (@lem5187737 _67697 s)). Qed.
Lemma lem5187740 (_67697 : real) (y : real) : (real_le _67697 y) = (real_le _67697 y).
Proof. exact (eq_refl (real_le _67697 y)). Qed.
Lemma lem5187741 (s : real -> Prop) (_67697 : real) (y : real) : (term623 s _67697 y) = (term24 s _67697 y).
Proof. exact (MK_COMB (@lem5187739 _67697 s) (@lem5187740 _67697 y)). Qed.
Lemma lem5187742 (s : real -> Prop) (_67697 : real) (y : real) : (term620 y _67697 s) = (term24 s _67697 y).
Proof. exact (TRANS (@lem5187734 s _67697 y) (@lem5187741 s _67697 y)). Qed.
Lemma lem5187745 (_67697 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term24 s _67697 y.
Proof. exact (EQ_MP (@lem5187742 s _67697 y) (@lem5187731 _67697 s y h1)). Qed.
Lemma lem5187746 (x : type1021) (s : real -> Prop) (y : real) (h1 : term74 s y) : term626 x s y.
Proof. exact (@lem5187745 (x s y) s y h1). Qed.
Lemma lem5187749 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term627 x s y.
Proof. exact (@lem5187746 x s y h3 (@lem5187702 x b x' s y h1 h2 h4)). Qed.
Lemma lem5187750 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term628 x s y.
Proof. exact (fun h0 : term535 x s y => @lem5187749 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5187752 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187753 (x : type1021) (s : real -> Prop) (y : real) : (term628 x s y) = (term627 x s y).
Proof. exact (@lem5187752 (term627 x s y)). Qed.
Lemma lem5187754 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term627 x s y.
Proof. exact (EQ_MP (@lem5187753 x s y) (@lem5187750 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5187756 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5187757 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term585 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5187756 b x' s y h1). Qed.
Lemma lem5187759 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187760 (s : real -> Prop) : (term585 s) = (term148 s).
Proof. exact (@lem5187759 (s = (@EMPTY real))). Qed.
Lemma lem5187761 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5187760 s) (@lem5187757 b x' s y h1)). Qed.
Lemma lem5187763 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5185999 b x' s y h1)). Qed.
Lemma lem5187764 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term585 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5187763 b x' s y h1). Qed.
Lemma lem5187766 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187767 (s : real -> Prop) : (term585 s) = (term148 s).
Proof. exact (@lem5187766 (s = (@EMPTY real))). Qed.
Lemma lem5187768 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5187767 s) (@lem5187764 b x' s y h1)). Qed.
Lemma lem5187771 (x : type1021) (y : real) (s : real -> Prop) (h1 : term619 x y s) : term619 x y s.
Proof. exact (h1). Qed.
Lemma lem5187772 (x : type1021) (y : real) (s : real -> Prop) (h1 : term619 x y s) : term681 x y s.
Proof. exact (fun h0 : term534 x y s => @lem5187771 x y s h1). Qed.
Lemma lem5187774 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187775 (x : type1021) (y : real) (s : real -> Prop) : (term681 x y s) = (term619 x y s).
Proof. exact (@lem5187774 (term534 x y s)). Qed.
Lemma lem5187776 (x : type1021) (y : real) (s : real -> Prop) (h1 : term619 x y s) : term619 x y s.
Proof. exact (EQ_MP (@lem5187775 x y s) (@lem5187772 x y s h1)). Qed.
Lemma lem5187779 (s : real -> Prop) (y : real) (h1 : term581 s y) : term581 s y.
Proof. exact (h1). Qed.
Lemma lem5187780 (s : real -> Prop) (y : real) (h1 : term581 s y) : term682 s y.
Proof. exact (fun h0 : term23 s y => @lem5187779 s y h1). Qed.
Lemma lem5187782 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187783 (s : real -> Prop) (y : real) : (term682 s y) = (term581 s y).
Proof. exact (@lem5187782 (term23 s y)). Qed.
Lemma lem5187784 (s : real -> Prop) (y : real) (h1 : term581 s y) : term581 s y.
Proof. exact (EQ_MP (@lem5187783 s y) (@lem5187780 s y h1)). Qed.
Lemma lem5187785 (x : type1021) (s : real -> Prop) (y : real) (h1 : term619 x y s) (h2 : term581 s y) : term699 x s y.
Proof. exact (conj (@lem5187776 x y s h1) (@lem5187784 s y h2)). Qed.
Lemma lem5187786 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term619 x y s) (h2 : term581 s y) (h3 : term252 b x' s y) : term700 x s y.
Proof. exact (conj (@lem5187768 b x' s y h3) (@lem5187785 x s y h1 h2)). Qed.
Lemma lem5187788 (_67694 : real) (_67695 : real) (_67693 : real -> Prop) (x : type1021) (h1 : term442 x) : term698 _67694 x _67695 _67693.
Proof. exact (EQ_MP (@lem5187688 _67694 x _67695 _67693) (@lem5187671 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5187789 (y : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term701 x y s.
Proof. exact (@lem5187788 y y s x h1). Qed.
Lemma lem5187792 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term619 x y s) (h3 : term581 s y) (h4 : term252 b x' s y) : term534 x y s.
Proof. exact (@lem5187789 y s x h1 (@lem5187786 x b x' s y h2 h3 h4)). Qed.
Lemma lem5187793 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term252 b x' s y) : term618 x y s.
Proof. exact (fun h0 : term619 x y s => @lem5187792 x b x' s y h1 h0 h2 h3). Qed.
Lemma lem5187795 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187796 (x : type1021) (y : real) (s : real -> Prop) : (term618 x y s) = (term534 x y s).
Proof. exact (@lem5187795 (term534 x y s)). Qed.
Lemma lem5187797 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term252 b x' s y) : term534 x y s.
Proof. exact (EQ_MP (@lem5187796 x y s) (@lem5187793 x b x' s y h1 h2 h3)). Qed.
Lemma lem5187799 (_67697 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term24 s _67697 y.
Proof. exact (EQ_MP (@lem5187742 s _67697 y) (@lem5187731 _67697 s y h1)). Qed.
Lemma lem5187800 (x : type1021) (s : real -> Prop) (y : real) (h1 : term74 s y) : term626 x s y.
Proof. exact (@lem5187799 (x s y) s y h1). Qed.
Lemma lem5187803 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term627 x s y.
Proof. exact (@lem5187800 x s y h3 (@lem5187797 x b x' s y h1 h2 h4)). Qed.
Lemma lem5187804 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term628 x s y.
Proof. exact (fun h0 : term535 x s y => @lem5187803 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5187806 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5187807 (x : type1021) (s : real -> Prop) (y : real) : (term628 x s y) = (term627 x s y).
Proof. exact (@lem5187806 (term627 x s y)). Qed.
Lemma lem5187808 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term627 x s y.
Proof. exact (EQ_MP (@lem5187807 x s y) (@lem5187804 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5187811 (s : real -> Prop) (y : real) (h1 : term581 s y) : term581 s y.
Proof. exact (h1). Qed.
Lemma lem5187812 (s : real -> Prop) (y : real) (h1 : term581 s y) : term682 s y.
Proof. exact (fun h0 : term23 s y => @lem5187811 s y h1). Qed.
Lemma lem5187814 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5187815 (s : real -> Prop) (y : real) : (term682 s y) = (term581 s y).
Proof. exact (@lem5187814 (term23 s y)). Qed.
Lemma lem5187816 (s : real -> Prop) (y : real) (h1 : term581 s y) : term581 s y.
Proof. exact (EQ_MP (@lem5187815 s y) (@lem5187812 s y h1)). Qed.
Lemma lem5187844 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187845 (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term544 x _67693 _67695) = (term702 x _67693 _67695).
Proof. exact (@lem5187844 (term23 _67693 _67695) (term535 x _67693 _67695)). Qed.
Lemma lem5187851 (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term703 x _67693 _67694) = (term703 x _67693 _67694).
Proof. exact (eq_refl (term703 x _67693 _67694)). Qed.
Lemma lem5187852 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term704 _67694 x _67693 _67695) = (term705 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187851 x _67693 _67694) (@lem5187845 x _67693 _67695)). Qed.
Lemma lem5187856 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187857 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term705 _67694 x _67693 _67695) = (term706 _67694 x _67693 _67695).
Proof. exact (@lem5187856 (term23 _67693 _67695) (term535 x _67693 _67694) (term535 x _67693 _67695)). Qed.
Lemma lem5187873 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term704 _67694 x _67693 _67695) = (term706 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5187852 _67694 x _67693 _67695) (@lem5187857 _67694 x _67693 _67695)). Qed.
Lemma lem5187874 (_67693 : real -> Prop) : (term286 _67693) = (term286 _67693).
Proof. exact (eq_refl (term286 _67693)). Qed.
Lemma lem5187875 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term582 _67694 x _67693 _67695) = (term707 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187874 _67693) (@lem5187873 _67694 x _67693 _67695)). Qed.
Lemma lem5187886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5187887 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term708 _67694 x _67693 _67695) = (term709 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187886) (@lem5187875 _67694 x _67693 _67695)). Qed.
Lemma lem5187891 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187892 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term710 x _67694 _67693 _67695) = (term711 x _67694 _67693 _67695).
Proof. exact (@lem5187891 (_67693 = (@EMPTY real)) (term535 x _67693 _67695) (term712 x _67694 _67693 _67695)). Qed.
Lemma lem5187908 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187909 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term713 x _67694 _67693 _67695) = (term704 _67694 x _67693 _67695).
Proof. exact (@lem5187908 (term535 x _67693 _67694) (term535 x _67693 _67695) (term23 _67693 _67695)). Qed.
Lemma lem5187923 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5187924 (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term544 x _67693 _67695) = (term702 x _67693 _67695).
Proof. exact (@lem5187923 (term23 _67693 _67695) (term535 x _67693 _67695)). Qed.
Lemma lem5187930 (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term703 x _67693 _67694) = (term703 x _67693 _67694).
Proof. exact (eq_refl (term703 x _67693 _67694)). Qed.
Lemma lem5187931 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term704 _67694 x _67693 _67695) = (term705 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187930 x _67693 _67694) (@lem5187924 x _67693 _67695)). Qed.
Lemma lem5187935 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5187936 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term705 _67694 x _67693 _67695) = (term706 _67694 x _67693 _67695).
Proof. exact (@lem5187935 (term23 _67693 _67695) (term535 x _67693 _67694) (term535 x _67693 _67695)). Qed.
Lemma lem5187952 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term704 _67694 x _67693 _67695) = (term706 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5187931 _67694 x _67693 _67695) (@lem5187936 _67694 x _67693 _67695)). Qed.
Lemma lem5187953 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term713 x _67694 _67693 _67695) = (term706 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5187909 _67694 x _67693 _67695) (@lem5187952 _67694 x _67693 _67695)). Qed.
Lemma lem5187954 (_67693 : real -> Prop) : (term286 _67693) = (term286 _67693).
Proof. exact (eq_refl (term286 _67693)). Qed.
Lemma lem5187955 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term711 x _67694 _67693 _67695) = (term707 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187954 _67693) (@lem5187953 _67694 x _67693 _67695)). Qed.
Lemma lem5187966 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term710 x _67694 _67693 _67695) = (term707 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5187892 x _67694 _67693 _67695) (@lem5187955 _67694 x _67693 _67695)). Qed.
Lemma lem5187967 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : ((term582 _67694 x _67693 _67695) = (term710 x _67694 _67693 _67695)) = ((term707 _67694 x _67693 _67695) = (term707 _67694 x _67693 _67695)).
Proof. exact (MK_COMB (@lem5187887 _67694 x _67693 _67695) (@lem5187966 _67694 x _67693 _67695)). Qed.
Lemma lem5187969 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5187970 (x : Prop) : (x = x) = True.
Proof. exact (@lem5187969 Prop x). Qed.
Lemma lem5187971 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : ((term707 _67694 x _67693 _67695) = (term707 _67694 x _67693 _67695)) = True.
Proof. exact (@lem5187970 (term707 _67694 x _67693 _67695)). Qed.
Lemma lem5187972 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : ((term582 _67694 x _67693 _67695) = (term710 x _67694 _67693 _67695)) = True.
Proof. exact (TRANS (@lem5187967 _67694 x _67693 _67695) (@lem5187971 _67694 x _67693 _67695)). Qed.
Lemma lem5187973 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : True = ((term582 _67694 x _67693 _67695) = (term710 x _67694 _67693 _67695)).
Proof. exact (SYM (@lem5187972 x _67694 _67693 _67695)). Qed.
Lemma lem5187974 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term582 _67694 x _67693 _67695) = (term710 x _67694 _67693 _67695).
Proof. exact (EQ_MP (@lem5187973 x _67694 _67693 _67695) (@lem0)). Qed.
Lemma lem5187975 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term710 x _67694 _67693 _67695.
Proof. exact (EQ_MP (@lem5187974 x _67694 _67693 _67695) (@lem5186781 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5187977 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5187978 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term710 x _67694 _67693 _67695) = (term714 _67694 x _67693 _67695).
Proof. exact (@lem5187977 (term715 x _67694 _67693 _67695) (term535 x _67693 _67695)). Qed.
Lemma lem5187980 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187981 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term716 x _67694 _67693 _67695) = (term717 x _67694 _67693 _67695).
Proof. exact (@lem5187980 (_67693 = (@EMPTY real)) (term712 x _67694 _67693 _67695)). Qed.
Lemma lem5187983 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5187984 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term718 x _67694 _67693 _67695) = (term719 x _67694 _67693 _67695).
Proof. exact (@lem5187983 (term535 x _67693 _67694) (term23 _67693 _67695)). Qed.
Lemma lem5187986 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5187987 (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term651 x _67693 _67694) = (term627 x _67693 _67694).
Proof. exact (@lem5187986 (term627 x _67693 _67694)). Qed.
Lemma lem5187988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5187989 (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term652 x _67693 _67694) = (term653 x _67693 _67694).
Proof. exact (MK_COMB (@lem5187988) (@lem5187987 x _67693 _67694)). Qed.
Lemma lem5187990 (_67693 : real -> Prop) (_67695 : real) : (term581 _67693 _67695) = (term581 _67693 _67695).
Proof. exact (eq_refl (term581 _67693 _67695)). Qed.
Lemma lem5187991 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term719 x _67694 _67693 _67695) = (term720 x _67694 _67693 _67695).
Proof. exact (MK_COMB (@lem5187989 x _67693 _67694) (@lem5187990 _67693 _67695)). Qed.
Lemma lem5187992 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term718 x _67694 _67693 _67695) = (term720 x _67694 _67693 _67695).
Proof. exact (TRANS (@lem5187984 x _67694 _67693 _67695) (@lem5187991 x _67694 _67693 _67695)). Qed.
Lemma lem5187993 (_67693 : real -> Prop) : (term38 _67693) = (term38 _67693).
Proof. exact (eq_refl (term38 _67693)). Qed.
Lemma lem5187994 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term717 x _67694 _67693 _67695) = (term721 x _67694 _67693 _67695).
Proof. exact (MK_COMB (@lem5187993 _67693) (@lem5187992 x _67694 _67693 _67695)). Qed.
Lemma lem5187995 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term716 x _67694 _67693 _67695) = (term721 x _67694 _67693 _67695).
Proof. exact (TRANS (@lem5187981 x _67694 _67693 _67695) (@lem5187994 x _67694 _67693 _67695)). Qed.
Lemma lem5187996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5187997 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term722 x _67694 _67693 _67695) = (term723 x _67694 _67693 _67695).
Proof. exact (MK_COMB (@lem5187996) (@lem5187995 x _67694 _67693 _67695)). Qed.
Lemma lem5187998 (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term535 x _67693 _67695) = (term535 x _67693 _67695).
Proof. exact (eq_refl (term535 x _67693 _67695)). Qed.
Lemma lem5187999 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term714 _67694 x _67693 _67695) = (term724 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5187997 x _67694 _67693 _67695) (@lem5187998 x _67693 _67695)). Qed.
Lemma lem5188000 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term710 x _67694 _67693 _67695) = (term724 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5187978 _67694 x _67693 _67695) (@lem5187999 _67694 x _67693 _67695)). Qed.
Lemma lem5188002 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term725 x s y.
Proof. exact (conj (@lem5187808 x b x' s y h1 h2 h3 h4) (@lem5187816 s y h2)). Qed.
Lemma lem5188003 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term726 x s y.
Proof. exact (conj (@lem5187761 b x' s y h4) (@lem5188002 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188005 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term724 _67694 x _67693 _67695.
Proof. exact (EQ_MP (@lem5188000 _67694 x _67693 _67695) (@lem5187975 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5188006 (s : real -> Prop) (y : real) (x : type1021) (h1 : term442 x) : term727 x s y.
Proof. exact (@lem5188005 y s y x h1). Qed.
Lemma lem5188009 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term535 x s y.
Proof. exact (@lem5188006 s y x h1 (@lem5188003 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188010 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term728 x s y.
Proof. exact (fun h0 : term627 x s y => @lem5188009 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5188012 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5188013 (x : type1021) (s : real -> Prop) (y : real) : (term728 x s y) = (term535 x s y).
Proof. exact (@lem5188012 (term627 x s y)). Qed.
Lemma lem5188014 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term535 x s y.
Proof. exact (EQ_MP (@lem5188013 x s y) (@lem5188010 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188016 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5188019 (y : real) (_67697 : real) (s : real -> Prop) : (term55 s _67697 y) = (term729 y _67697 s).
Proof. exact (@lem5188016 (real_le _67697 y) (term588 _67697 s)). Qed.
Lemma lem5188022 (_67697 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term729 y _67697 s.
Proof. exact (EQ_MP (@lem5188019 y _67697 s) (@lem5186749 _67697 s y h1)). Qed.
Lemma lem5188023 (x : type1021) (s : real -> Prop) (y : real) (h1 : term74 s y) : term730 x y s.
Proof. exact (@lem5188022 (x s y) s y h1). Qed.
Lemma lem5188026 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term619 x y s.
Proof. exact (@lem5188023 x s y h3 (@lem5188014 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188027 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term681 x y s.
Proof. exact (fun h0 : term534 x y s => @lem5188026 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5188029 (p : Prop) : (term586 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5188030 (x : type1021) (y : real) (s : real -> Prop) : (term681 x y s) = (term619 x y s).
Proof. exact (@lem5188029 (term534 x y s)). Qed.
Lemma lem5188031 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term619 x y s.
Proof. exact (EQ_MP (@lem5188030 x y s) (@lem5188027 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188049 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5188050 (x : type1021) (_67694 : real) (_67693 : real -> Prop) (_67695 : real) : (term731 _67694 x _67693 _67695) = (term732 x _67694 _67693 _67695).
Proof. exact (@lem5188049 (term534 x _67695 _67693) (term535 x _67693 _67694) (term23 _67693 _67695)). Qed.
Lemma lem5188064 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5188065 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term712 x _67694 _67693 _67695) = (term733 _67695 x _67693 _67694).
Proof. exact (@lem5188064 (term23 _67693 _67695) (term535 x _67693 _67694)). Qed.
Lemma lem5188071 (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term593 x _67695 _67693) = (term593 x _67695 _67693).
Proof. exact (eq_refl (term593 x _67695 _67693)). Qed.
Lemma lem5188072 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term732 x _67694 _67693 _67695) = (term734 _67695 x _67693 _67694).
Proof. exact (MK_COMB (@lem5188071 x _67695 _67693) (@lem5188065 _67695 x _67693 _67694)). Qed.
Lemma lem5188083 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term731 _67694 x _67693 _67695) = (term734 _67695 x _67693 _67694).
Proof. exact (TRANS (@lem5188050 x _67694 _67693 _67695) (@lem5188072 _67695 x _67693 _67694)). Qed.
Lemma lem5188084 (_67693 : real -> Prop) : (term286 _67693) = (term286 _67693).
Proof. exact (eq_refl (term286 _67693)). Qed.
Lemma lem5188085 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term584 _67694 x _67693 _67695) = (term735 _67695 x _67693 _67694).
Proof. exact (MK_COMB (@lem5188084 _67693) (@lem5188083 _67695 x _67693 _67694)). Qed.
Lemma lem5188096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5188097 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term736 _67694 x _67693 _67695) = (term737 _67695 x _67693 _67694).
Proof. exact (MK_COMB (@lem5188096) (@lem5188085 _67695 x _67693 _67694)). Qed.
Lemma lem5188101 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5188102 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term738 _67694 x _67695 _67693) = (term739 _67694 x _67695 _67693).
Proof. exact (@lem5188101 (_67693 = (@EMPTY real)) (term23 _67693 _67695) (term740 _67694 x _67695 _67693)). Qed.
Lemma lem5188128 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5188129 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term740 _67694 x _67695 _67693) = (term741 _67695 x _67693 _67694).
Proof. exact (@lem5188128 (term534 x _67695 _67693) (term535 x _67693 _67694)). Qed.
Lemma lem5188135 (_67693 : real -> Prop) (_67695 : real) : (term742 _67693 _67695) = (term742 _67693 _67695).
Proof. exact (eq_refl (term742 _67693 _67695)). Qed.
Lemma lem5188136 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term743 _67694 x _67695 _67693) = (term744 _67695 x _67693 _67694).
Proof. exact (MK_COMB (@lem5188135 _67693 _67695) (@lem5188129 _67695 x _67693 _67694)). Qed.
Lemma lem5188140 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5188141 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term744 _67695 x _67693 _67694) = (term734 _67695 x _67693 _67694).
Proof. exact (@lem5188140 (term534 x _67695 _67693) (term23 _67693 _67695) (term535 x _67693 _67694)). Qed.
Lemma lem5188157 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term743 _67694 x _67695 _67693) = (term734 _67695 x _67693 _67694).
Proof. exact (TRANS (@lem5188136 _67695 x _67693 _67694) (@lem5188141 _67695 x _67693 _67694)). Qed.
Lemma lem5188158 (_67693 : real -> Prop) : (term286 _67693) = (term286 _67693).
Proof. exact (eq_refl (term286 _67693)). Qed.
Lemma lem5188159 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term739 _67694 x _67695 _67693) = (term735 _67695 x _67693 _67694).
Proof. exact (MK_COMB (@lem5188158 _67693) (@lem5188157 _67695 x _67693 _67694)). Qed.
Lemma lem5188170 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term738 _67694 x _67695 _67693) = (term735 _67695 x _67693 _67694).
Proof. exact (TRANS (@lem5188102 _67694 x _67695 _67693) (@lem5188159 _67695 x _67693 _67694)). Qed.
Lemma lem5188171 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : ((term584 _67694 x _67693 _67695) = (term738 _67694 x _67695 _67693)) = ((term735 _67695 x _67693 _67694) = (term735 _67695 x _67693 _67694)).
Proof. exact (MK_COMB (@lem5188097 _67695 x _67693 _67694) (@lem5188170 _67695 x _67693 _67694)). Qed.
Lemma lem5188173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5188174 (x : Prop) : (x = x) = True.
Proof. exact (@lem5188173 Prop x). Qed.
Lemma lem5188175 (_67695 : real) (x : type1021) (_67693 : real -> Prop) (_67694 : real) : ((term735 _67695 x _67693 _67694) = (term735 _67695 x _67693 _67694)) = True.
Proof. exact (@lem5188174 (term735 _67695 x _67693 _67694)). Qed.
Lemma lem5188176 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : ((term584 _67694 x _67693 _67695) = (term738 _67694 x _67695 _67693)) = True.
Proof. exact (TRANS (@lem5188171 _67695 x _67693 _67694) (@lem5188175 _67695 x _67693 _67694)). Qed.
Lemma lem5188177 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : True = ((term584 _67694 x _67693 _67695) = (term738 _67694 x _67695 _67693)).
Proof. exact (SYM (@lem5188176 _67694 x _67695 _67693)). Qed.
Lemma lem5188178 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term584 _67694 x _67693 _67695) = (term738 _67694 x _67695 _67693).
Proof. exact (EQ_MP (@lem5188177 _67694 x _67695 _67693) (@lem0)). Qed.
Lemma lem5188179 (_67694 : real) (_67695 : real) (_67693 : real -> Prop) (x : type1021) (h1 : term442 x) : term738 _67694 x _67695 _67693.
Proof. exact (EQ_MP (@lem5188178 _67694 x _67695 _67693) (@lem5186813 _67694 _67693 _67695 x h1)). Qed.
Lemma lem5188181 (b : Prop) (a : Prop) : (a \/ b) = (term600 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5188182 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term738 _67694 x _67695 _67693) = (term745 _67694 x _67693 _67695).
Proof. exact (@lem5188181 (term746 _67694 x _67695 _67693) (term23 _67693 _67695)). Qed.
Lemma lem5188184 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5188185 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term747 _67694 x _67695 _67693) = (term748 _67694 x _67695 _67693).
Proof. exact (@lem5188184 (_67693 = (@EMPTY real)) (term740 _67694 x _67695 _67693)). Qed.
Lemma lem5188187 (a : Prop) (b : Prop) : (term603 a b) = (term604 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5188188 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term749 _67694 x _67695 _67693) = (term750 _67694 x _67695 _67693).
Proof. exact (@lem5188187 (term535 x _67693 _67694) (term534 x _67695 _67693)). Qed.
Lemma lem5188190 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5188191 (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term651 x _67693 _67694) = (term627 x _67693 _67694).
Proof. exact (@lem5188190 (term627 x _67693 _67694)). Qed.
Lemma lem5188192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5188193 (x : type1021) (_67693 : real -> Prop) (_67694 : real) : (term652 x _67693 _67694) = (term653 x _67693 _67694).
Proof. exact (MK_COMB (@lem5188192) (@lem5188191 x _67693 _67694)). Qed.
Lemma lem5188194 (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term619 x _67695 _67693) = (term619 x _67695 _67693).
Proof. exact (eq_refl (term619 x _67695 _67693)). Qed.
Lemma lem5188195 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term750 _67694 x _67695 _67693) = (term751 _67694 x _67695 _67693).
Proof. exact (MK_COMB (@lem5188193 x _67693 _67694) (@lem5188194 x _67695 _67693)). Qed.
Lemma lem5188196 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term749 _67694 x _67695 _67693) = (term751 _67694 x _67695 _67693).
Proof. exact (TRANS (@lem5188188 _67694 x _67695 _67693) (@lem5188195 _67694 x _67695 _67693)). Qed.
Lemma lem5188197 (_67693 : real -> Prop) : (term38 _67693) = (term38 _67693).
Proof. exact (eq_refl (term38 _67693)). Qed.
Lemma lem5188198 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term748 _67694 x _67695 _67693) = (term752 _67694 x _67695 _67693).
Proof. exact (MK_COMB (@lem5188197 _67693) (@lem5188196 _67694 x _67695 _67693)). Qed.
Lemma lem5188199 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term747 _67694 x _67695 _67693) = (term752 _67694 x _67695 _67693).
Proof. exact (TRANS (@lem5188185 _67694 x _67695 _67693) (@lem5188198 _67694 x _67695 _67693)). Qed.
Lemma lem5188200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5188201 (_67694 : real) (x : type1021) (_67695 : real) (_67693 : real -> Prop) : (term753 _67694 x _67695 _67693) = (term754 _67694 x _67695 _67693).
Proof. exact (MK_COMB (@lem5188200) (@lem5188199 _67694 x _67695 _67693)). Qed.
Lemma lem5188202 (_67693 : real -> Prop) (_67695 : real) : (term23 _67693 _67695) = (term23 _67693 _67695).
Proof. exact (eq_refl (term23 _67693 _67695)). Qed.
Lemma lem5188203 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term745 _67694 x _67693 _67695) = (term755 _67694 x _67693 _67695).
Proof. exact (MK_COMB (@lem5188201 _67694 x _67695 _67693) (@lem5188202 _67693 _67695)). Qed.
Lemma lem5188204 (_67694 : real) (x : type1021) (_67693 : real -> Prop) (_67695 : real) : (term738 _67694 x _67695 _67693) = (term755 _67694 x _67693 _67695).
Proof. exact (TRANS (@lem5188182 _67694 x _67693 _67695) (@lem5188203 _67694 x _67693 _67695)). Qed.
Lemma lem5188206 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term756 x y s.
Proof. exact (conj (@lem5187754 x b x' s y h1 h2 h3 h4) (@lem5188031 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188207 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term757 x y s.
Proof. exact (conj (@lem5187559 b x' s y h4) (@lem5188206 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188209 (_67694 : real) (_67693 : real -> Prop) (_67695 : real) (x : type1021) (h1 : term442 x) : term755 _67694 x _67693 _67695.
Proof. exact (EQ_MP (@lem5188204 _67694 x _67693 _67695) (@lem5188179 _67694 _67695 _67693 x h1)). Qed.
Lemma lem5188210 (s : real -> Prop) (y : real) (x : type1021) (h1 : term442 x) : term758 x s y.
Proof. exact (@lem5188209 y s y x h1). Qed.
Lemma lem5188213 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 s y) (h3 : term74 s y) (h4 : term252 b x' s y) : term23 s y.
Proof. exact (@lem5188210 s y x h1 (@lem5188207 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5188214 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : term660 s y.
Proof. exact (fun h0 : term581 s y => @lem5188213 x b x' s y h1 h0 h2 h3). Qed.
Lemma lem5188216 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5188217 (s : real -> Prop) (y : real) : (term660 s y) = (term23 s y).
Proof. exact (@lem5188216 (term23 s y)). Qed.
Lemma lem5188218 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : term23 s y.
Proof. exact (EQ_MP (@lem5188217 s y) (@lem5188214 x b x' s y h1 h2 h3)). Qed.
Lemma lem5188221 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5188223 (s : real -> Prop) (y : real) : (term581 s y) = (term759 s y).
Proof. exact (@lem5188221 (term23 s y)). Qed.
Lemma lem5188226 (s : real -> Prop) (y : real) (h1 : term74 s y) : term759 s y.
Proof. exact (EQ_MP (@lem5188223 s y) (@lem5186743 s y h1)). Qed.
Lemma lem5188229 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : False.
Proof. exact (@lem5188226 s y h2 (@lem5188218 x b x' s y h1 h2 h3)). Qed.
Lemma lem5188230 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : term680.
Proof. exact (fun h0 : ~ False => @lem5188229 x b x' s y h1 h2 h3). Qed.
Lemma lem5188232 (p : Prop) : (term589 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5188233 : term680 = False.
Proof. exact (@lem5188232 False). Qed.
Lemma lem5188234 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : False.
Proof. exact (EQ_MP (@lem5188233) (@lem5188230 x b x' s y h1 h2 h3)). Qed.
Lemma lem5188235 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : False.
Proof. exact (or_elim (@lem5185998 b x' s y h3) (fun h0 : term168 s x' y => @lem5187487 x b s x' y h1 h2 h3 h0) (fun h0 : term74 s y => @lem5188234 x b x' s y h1 h0 h3)). Qed.
Lemma lem5188236 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : (term252 b x' s y) = False.
Proof. exact (prop_ext (fun h4 : term252 b x' s y => @lem5188235 x b x' s y h1 h2 h3) (fun h4 : False => @lem5185997 b x' s y h3)). Qed.
Lemma lem5188237 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : False.
Proof. exact (EQ_MP (@lem5188236 x b x' s y h1 h2 h3) (@lem5185997 b x' s y h3)). Qed.
Lemma lem5188238 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : (term442 x) = False.
Proof. exact (prop_ext (fun h4 : term442 x => @lem5188237 x b x' s y h1 h2 h3) (fun h4 : False => @lem5185907 x h1)). Qed.
Lemma lem5188239 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : False.
Proof. exact (EQ_MP (@lem5188238 x b x' s y h1 h2 h3) (@lem5185907 x h1)). Qed.
Lemma lem5188240 (x : type1021) (b : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term255 b s y) : False.
Proof. exact (ex_elim (@lem5185771 b s y h3) (fun x' : real => fun h0 : term254 b s y x' => @lem5188239 x b x' s y h1 h2 h0)). Qed.
Lemma lem5188241 (x : type1021) (b : real) (s : real -> Prop) (h1 : term442 x) (h2 : term49) (h3 : term257 b s) : False.
Proof. exact (ex_elim (@lem5185770 b s h3) (fun y : real => fun h0 : term256 b s y => @lem5188240 x b s y h1 h2 h0)). Qed.
Lemma lem5188242 (x : type1021) (s : real -> Prop) (h1 : term442 x) (h2 : term49) (h3 : term259 s) : False.
Proof. exact (ex_elim (@lem5185769 s h3) (fun b : real => fun h0 : term258 s b => @lem5188241 x b s h1 h2 h0)). Qed.
Lemma lem5188243 (x : type1021) (h1 : term442 x) (h2 : term49) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5185155 h3) (fun s : real -> Prop => fun h0 : term260 s => @lem5188242 x s h1 h2 h0)). Qed.
Lemma lem5188244 (h1 : term17) (h2 : term49) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5185767 h1) (fun x : type1021 => fun h0 : term444 x => @lem5188243 x h0 h2 h3)). Qed.
Lemma lem5188245 (h1 : term49) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5188244 h0 h1 h2). Qed.
Lemma lem5188246 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5188247 (h1 : term49) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5188246) (@lem5188245 h1 h2)). Qed.
Lemma lem5188248 (h1 : term10) : term20.
Proof. exact (fun h0 : term49 => @lem5188247 h0 h1). Qed.
Lemma lem5188249 : term22.
Proof. exact (fun h0 : term10 => @lem5188248 h0). Qed.
Lemma lem5188250 : term11.
Proof. exact (EQ_MP (@lem5184536) (@lem5188249)). Qed.
Lemma lem5188252 : term11.
Proof. exact (@lem5184202 (@lem5188250)). Qed.
Lemma lem5188253 (h1 : term10) : term19.
Proof. exact (@lem5188252 (@lem5184187 h1)). Qed.
Lemma lem5188254 (h1 : term10) : term15.
Proof. exact (@lem5188253 h1 (@lem1339577)). Qed.
Lemma lem5188255 (h1 : term10) : False.
Proof. exact (@lem5188254 h1 (@lem5136700)). Qed.
Lemma lem5188256 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5188255 h1) (fun h2 : False => @lem5184187 h1)). Qed.
Lemma lem5188257 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5188256 h1) (@lem5184187 h1)). Qed.
Lemma lem5188258 : term9.
Proof. exact (fun h0 : term10 => @lem5188257 h0). Qed.
Lemma lem5188259 : term8.
Proof. exact (EQ_MP (@lem5184186) (@lem5188258)). Qed.
