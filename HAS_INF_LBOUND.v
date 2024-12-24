Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_INF_LBOUND_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import has_inf_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm69_spec.
Lemma lem5291215 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5291216 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5291217 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5291216 t1) (@lem5291215 t1)). Qed.
Lemma lem5291218 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5291217 t1 t2). Qed.
Lemma lem5291219 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5291220 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5291219 t1 t2) (@lem5291218 t1 t2)). Qed.
Lemma lem5291221 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5291220 t1 t2 t3). Qed.
Lemma lem5291222 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5291223 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5291222 t1 t2 t3) (@lem5291221 t1 t2 t3)). Qed.
Lemma lem5291224 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5291223 t1 t2 t3)). Qed.
Lemma lem5291225 (s : real -> Prop) : term7 s.
Proof. exact (@lem5289985 s). Qed.
Lemma lem5291226 (s : real -> Prop) : (term7 s) = (term8 s).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5291227 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5291226 s) (@lem5291225 s)). Qed.
Lemma lem5291228 (s : real -> Prop) (b : real) : term9 s b.
Proof. exact (@lem5291227 s b). Qed.
Lemma lem5291229 (s : real -> Prop) (b : real) : (term9 s b) = ((has_inf s b) = (term10 s b)).
Proof. exact (eq_refl (term9 s b)). Qed.
Lemma lem5291236 (s : real -> Prop) (b : real) : (has_inf s b) = (term10 s b).
Proof. exact (EQ_MP (@lem5291229 s b) (@lem5291228 s b)). Qed.
Lemma lem5291249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291250 (s : real -> Prop) (b : real) : (term11 s b) = (term12 s b).
Proof. exact (MK_COMB (@lem5291249) (@lem5291236 s b)). Qed.
Lemma lem5291251 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291252 (b : real) (x : real) (s : real -> Prop) : (term13 b x s) = (term14 b x s).
Proof. exact (MK_COMB (@lem5291250 s b) (@lem5291251 x s)). Qed.
Lemma lem5291255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5291256 (b : real) (x : real) (s : real -> Prop) : (term15 b x s) = (term16 b x s).
Proof. exact (MK_COMB (@lem5291255) (@lem5291252 b x s)). Qed.
Lemma lem5291257 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5291258 (s : real -> Prop) (b : real) (x : real) : (term17 s b x) = (term18 s b x).
Proof. exact (MK_COMB (@lem5291256 b x s) (@lem5291257 b x)). Qed.
Lemma lem5291261 (s : real -> Prop) (b : real) (x : real) : (term18 s b x) = (term17 s b x).
Proof. exact (SYM (@lem5291258 s b x)). Qed.
Lemma lem5291263 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5291264 (s : real -> Prop) (b : real) (x : real) : (term18 s b x) = (term20 s b x).
Proof. exact (@lem5291263 (term18 s b x)). Qed.
Lemma lem5291265 (s : real -> Prop) (b : real) (x : real) : (term20 s b x) = (term18 s b x).
Proof. exact (SYM (@lem5291264 s b x)). Qed.
Lemma lem5291266 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : term21 s b x.
Proof. exact (h1). Qed.
Lemma lem5291269 (s : real -> Prop) (b : real) (x : real) (h1 : term22 s b x) : term22 s b x.
Proof. exact (h1). Qed.
Lemma lem5291270 (s : real -> Prop) (b : real) (x : real) : term23 s b x.
Proof. exact (fun h0 : term22 s b x => @lem5291269 s b x h0). Qed.
Lemma lem5291271 (s : real -> Prop) (b : real) (x : real) (h1 : term23 s b x) : term23 s b x.
Proof. exact (h1). Qed.
Lemma lem5291272 (s : real -> Prop) (b : real) (x : real) (h1 : term22 s b x) : term22 s b x.
Proof. exact (h1). Qed.
Lemma lem5291273 (s : real -> Prop) (b : real) (x : real) (h1 : term22 s b x) (h2 : term23 s b x) : term22 s b x.
Proof. exact (@lem5291271 s b x h2 (@lem5291272 s b x h1)). Qed.
Lemma lem5291274 (s : real -> Prop) (b : real) (x : real) (h1 : term22 s b x) : term24 s b x.
Proof. exact (fun h0 : term23 s b x => @lem5291273 s b x h1 h0). Qed.
Lemma lem5291275 (s : real -> Prop) (b : real) (x : real) (h1 : term23 s b x) : term23 s b x.
Proof. exact (h1). Qed.
Lemma lem5291276 (s : real -> Prop) (b : real) (x : real) (h1 : term22 s b x) (h2 : term23 s b x) : term22 s b x.
Proof. exact (@lem5291274 s b x h1 (@lem5291275 s b x h2)). Qed.
Lemma lem5291277 (s : real -> Prop) (b : real) (x : real) (h1 : term23 s b x) : term23 s b x.
Proof. exact (fun h0 : term22 s b x => @lem5291276 s b x h0 h1). Qed.
Lemma lem5291278 (s : real -> Prop) (b : real) (x : real) : term25 s b x.
Proof. exact (fun h0 : term23 s b x => @lem5291277 s b x h0). Qed.
Lemma lem5291281 (s : real -> Prop) (b : real) (x : real) : term23 s b x.
Proof. exact (@lem5291278 s b x (@lem5291270 s b x)). Qed.
Lemma lem5291311 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5291312 : term26 = term27.
Proof. exact (@lem5291311 term28). Qed.
Lemma lem5291317 (s : real -> Prop) (b : real) (x : real) : (term29 s b x) = (term29 s b x).
Proof. exact (eq_refl (term29 s b x)). Qed.
Lemma lem5291318 (s : real -> Prop) (b : real) (x : real) : (term22 s b x) = (term30 s b x).
Proof. exact (MK_COMB (@lem5291317 s b x) (@lem5291312)). Qed.
Lemma lem5291321 (b : real) (x : real) : (term31 b x) = (term32 b x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5291318 s b x)). Qed.
Lemma lem5291322 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5291323 (b : real) (x : real) : (term33 b x) = (term34 b x).
Proof. exact (MK_COMB (@lem5291322) (@lem5291321 b x)). Qed.
Lemma lem5291328 (x : real) : (term35 x) = (term36 x).
Proof. exact (fun_ext (fun b : real => @lem5291323 b x)). Qed.
Lemma lem5291329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291330 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem5291329) (@lem5291328 x)). Qed.
Lemma lem5291335 : term39 = term40.
Proof. exact (fun_ext (fun x : real => @lem5291330 x)). Qed.
Lemma lem5291336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291345 : term41 = term42.
Proof. exact (MK_COMB (@lem5291336) (@lem5291335)). Qed.
Lemma lem5291346 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5291347 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5291346 x)). Qed.
Lemma lem5291348 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291349 : term28 = term28.
Proof. exact (MK_COMB (@lem5291348) (@lem5291347)). Qed.
Lemma lem5291350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5291351 : term27 = term27.
Proof. exact (MK_COMB (@lem5291350) (@lem5291349)). Qed.
Lemma lem5291352 (b : real) (x : real) : (real_le b x) = (real_le b x).
Proof. exact (eq_refl (real_le b x)). Qed.
Lemma lem5291353 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291354 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5291359 (s : real -> Prop) (c : real) (x : real) : (term44 s c x) = (term44 s c x).
Proof. exact (eq_refl (term44 s c x)). Qed.
Lemma lem5291360 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5291359 s c x)). Qed.
Lemma lem5291361 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291362 (s : real -> Prop) (c : real) : (term46 s c) = (term46 s c).
Proof. exact (MK_COMB (@lem5291361) (@lem5291360 s c)). Qed.
Lemma lem5291363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291364 (s : real -> Prop) (c : real) : (term47 s c) = (term47 s c).
Proof. exact (MK_COMB (@lem5291363) (@lem5291362 s c)). Qed.
Lemma lem5291365 (s : real -> Prop) (c : real) (b : real) : ((term46 s c) = (real_le c b)) = ((term46 s c) = (real_le c b)).
Proof. exact (MK_COMB (@lem5291364 s c) (@lem5291354 c b)). Qed.
Lemma lem5291366 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun c : real => @lem5291365 s c b)). Qed.
Lemma lem5291367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291368 (s : real -> Prop) (b : real) : (term10 s b) = (term10 s b).
Proof. exact (MK_COMB (@lem5291367) (@lem5291366 s b)). Qed.
Lemma lem5291369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291370 (s : real -> Prop) (b : real) : (term12 s b) = (term12 s b).
Proof. exact (MK_COMB (@lem5291369) (@lem5291368 s b)). Qed.
Lemma lem5291371 (b : real) (x : real) (s : real -> Prop) : (term14 b x s) = (term14 b x s).
Proof. exact (MK_COMB (@lem5291370 s b) (@lem5291353 x s)). Qed.
Lemma lem5291372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5291373 (b : real) (x : real) (s : real -> Prop) : (term16 b x s) = (term16 b x s).
Proof. exact (MK_COMB (@lem5291372) (@lem5291371 b x s)). Qed.
Lemma lem5291374 (s : real -> Prop) (b : real) (x : real) : (term18 s b x) = (term18 s b x).
Proof. exact (MK_COMB (@lem5291373 b x s) (@lem5291352 b x)). Qed.
Lemma lem5291375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5291376 (s : real -> Prop) (b : real) (x : real) : (term21 s b x) = (term21 s b x).
Proof. exact (MK_COMB (@lem5291375) (@lem5291374 s b x)). Qed.
Lemma lem5291377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5291378 (s : real -> Prop) (b : real) (x : real) : (term29 s b x) = (term29 s b x).
Proof. exact (MK_COMB (@lem5291377) (@lem5291376 s b x)). Qed.
Lemma lem5291379 (s : real -> Prop) (b : real) (x : real) : (term30 s b x) = (term30 s b x).
Proof. exact (MK_COMB (@lem5291378 s b x) (@lem5291351)). Qed.
Lemma lem5291380 (b : real) (x : real) : (term32 b x) = (term32 b x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5291379 s b x)). Qed.
Lemma lem5291381 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5291382 (b : real) (x : real) : (term34 b x) = (term34 b x).
Proof. exact (MK_COMB (@lem5291381) (@lem5291380 b x)). Qed.
Lemma lem5291383 (x : real) : (term36 x) = (term36 x).
Proof. exact (fun_ext (fun b : real => @lem5291382 b x)). Qed.
Lemma lem5291384 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291385 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem5291384) (@lem5291383 x)). Qed.
Lemma lem5291386 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5291385 x)). Qed.
Lemma lem5291387 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291388 : term42 = term42.
Proof. exact (MK_COMB (@lem5291387) (@lem5291386)). Qed.
Lemma lem5291435 : term41 = term42.
Proof. exact (TRANS (@lem5291345) (@lem5291388)). Qed.
Lemma lem5291436 : term42 = term41.
Proof. exact (SYM (@lem5291435)). Qed.
Lemma lem5291437 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : term21 s b x.
Proof. exact (h1). Qed.
Lemma lem5291438 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem5291447 (s : real -> Prop) (c : real) (x : real) : (term49 s c x) = (term50 s c x).
Proof. exact (@lem17362 (@IN real x s) (real_le c x)). Qed.
Lemma lem5291452 (s : real -> Prop) (c : real) (x : real) : (term44 s c x) = (term51 s c x).
Proof. exact (@lem17265 (@IN real x s) (real_le c x)). Qed.
Lemma lem5291453 (P : real -> Prop) : (term52 P) = (term53 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5291454 (s : real -> Prop) (c : real) : (term54 s c) = (term55 s c).
Proof. exact (@lem5291453 (term45 s c)). Qed.
Lemma lem5291455 (s : real -> Prop) (c : real) (x : real) : (term56 s c x) = (term44 s c x).
Proof. exact (eq_refl (term56 s c x)). Qed.
Lemma lem5291456 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5291457 (s : real -> Prop) (c : real) (x : real) : (term57 s c x) = (term49 s c x).
Proof. exact (MK_COMB (@lem5291456) (@lem5291455 s c x)). Qed.
Lemma lem5291458 (s : real -> Prop) (c : real) (x : real) : (term57 s c x) = (term50 s c x).
Proof. exact (TRANS (@lem5291457 s c x) (@lem5291447 s c x)). Qed.
Lemma lem5291459 (s : real -> Prop) (c : real) : (term58 s c) = (term59 s c).
Proof. exact (fun_ext (fun x : real => @lem5291458 s c x)). Qed.
Lemma lem5291460 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5291461 (s : real -> Prop) (c : real) : (term55 s c) = (term60 s c).
Proof. exact (MK_COMB (@lem5291460) (@lem5291459 s c)). Qed.
Lemma lem5291462 (s : real -> Prop) (c : real) : (term54 s c) = (term60 s c).
Proof. exact (TRANS (@lem5291454 s c) (@lem5291461 s c)). Qed.
Lemma lem5291463 (s : real -> Prop) (c : real) : (term45 s c) = (term61 s c).
Proof. exact (fun_ext (fun x : real => @lem5291452 s c x)). Qed.
Lemma lem5291464 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291465 (s : real -> Prop) (c : real) : (term46 s c) = (term62 s c).
Proof. exact (MK_COMB (@lem5291464) (@lem5291463 s c)). Qed.
Lemma lem5291466 (c : real) (b : real) : (term63 c b) = (term63 c b).
Proof. exact (eq_refl (term63 c b)). Qed.
Lemma lem5291467 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5291468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5291469 (s : real -> Prop) (c : real) : (term64 s c) = (term65 s c).
Proof. exact (MK_COMB (@lem5291468) (@lem5291462 s c)). Qed.
Lemma lem5291470 (s : real -> Prop) (c : real) (b : real) : (term66 s c b) = (term67 s c b).
Proof. exact (MK_COMB (@lem5291469 s c) (@lem5291467 c b)). Qed.
Lemma lem5291471 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5291472 (s : real -> Prop) (c : real) : (term68 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5291471) (@lem5291465 s c)). Qed.
Lemma lem5291473 (s : real -> Prop) (c : real) (b : real) : (term70 s c b) = (term71 s c b).
Proof. exact (MK_COMB (@lem5291472 s c) (@lem5291466 c b)). Qed.
Lemma lem5291474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291475 (s : real -> Prop) (c : real) (b : real) : (term72 s c b) = (term73 s c b).
Proof. exact (MK_COMB (@lem5291474) (@lem5291473 s c b)). Qed.
Lemma lem5291476 (s : real -> Prop) (c : real) (b : real) : (term74 s c b) = (term75 s c b).
Proof. exact (MK_COMB (@lem5291475 s c b) (@lem5291470 s c b)). Qed.
Lemma lem5291477 (s : real -> Prop) (c : real) (b : real) : ((term46 s c) = (real_le c b)) = (term74 s c b).
Proof. exact (@lem17784 (term46 s c) (real_le c b)). Qed.
Lemma lem5291478 (s : real -> Prop) (c : real) (b : real) : ((term46 s c) = (real_le c b)) = (term75 s c b).
Proof. exact (TRANS (@lem5291477 s c b) (@lem5291476 s c b)). Qed.
Lemma lem5291479 (s : real -> Prop) (b : real) : (term48 s b) = (term76 s b).
Proof. exact (fun_ext (fun c : real => @lem5291478 s c b)). Qed.
Lemma lem5291480 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291481 (s : real -> Prop) (b : real) : (term10 s b) = (term77 s b).
Proof. exact (MK_COMB (@lem5291480) (@lem5291479 s b)). Qed.
Lemma lem5291482 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291484 (s : real -> Prop) (b : real) : (term12 s b) = (term78 s b).
Proof. exact (MK_COMB (@lem5291483) (@lem5291481 s b)). Qed.
Lemma lem5291485 (b : real) (x : real) (s : real -> Prop) : (term14 b x s) = (term79 b x s).
Proof. exact (MK_COMB (@lem5291484 s b) (@lem5291482 x s)). Qed.
Lemma lem5291486 (b : real) (x : real) : (term63 b x) = (term63 b x).
Proof. exact (eq_refl (term63 b x)). Qed.
Lemma lem5291487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291488 (b : real) (x : real) (s : real -> Prop) : (term80 b x s) = (term81 b x s).
Proof. exact (MK_COMB (@lem5291487) (@lem5291485 b x s)). Qed.
Lemma lem5291489 (s : real -> Prop) (b : real) (x : real) : (term82 s b x) = (term83 s b x).
Proof. exact (MK_COMB (@lem5291488 b x s) (@lem5291486 b x)). Qed.
Lemma lem5291490 (s : real -> Prop) (b : real) (x : real) : (term21 s b x) = (term82 s b x).
Proof. exact (@lem17362 (term14 b x s) (real_le b x)). Qed.
Lemma lem5291491 (s : real -> Prop) (b : real) (x : real) : (term21 s b x) = (term83 s b x).
Proof. exact (TRANS (@lem5291490 s b x) (@lem5291489 s b x)). Qed.
Lemma lem5291493 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term84 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5291494 (P : real -> Prop) (Q : real -> Prop) : (term86 P Q) = (term87 P Q).
Proof. exact (@lem5291493 real P Q). Qed.
Lemma lem5291495 (s : real -> Prop) (b : real) : (term88 s b) = (term89 s b).
Proof. exact (@lem5291494 (term90 s b) (term91 s b)). Qed.
Lemma lem5291496 (s : real -> Prop) (c : real) (b : real) : (term92 s b c) = (term71 s c b).
Proof. exact (eq_refl (term92 s b c)). Qed.
Lemma lem5291497 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291498 (s : real -> Prop) (c : real) (b : real) : (term93 s b c) = (term73 s c b).
Proof. exact (MK_COMB (@lem5291497) (@lem5291496 s c b)). Qed.
Lemma lem5291499 (s : real -> Prop) (c : real) (b : real) : (term94 s b c) = (term67 s c b).
Proof. exact (eq_refl (term94 s b c)). Qed.
Lemma lem5291500 (s : real -> Prop) (c : real) (b : real) : (term95 s b c) = (term75 s c b).
Proof. exact (MK_COMB (@lem5291498 s c b) (@lem5291499 s c b)). Qed.
Lemma lem5291501 (s : real -> Prop) (b : real) : (term96 s b) = (term76 s b).
Proof. exact (fun_ext (fun c : real => @lem5291500 s c b)). Qed.
Lemma lem5291502 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291503 (s : real -> Prop) (b : real) : (term88 s b) = (term77 s b).
Proof. exact (MK_COMB (@lem5291502) (@lem5291501 s b)). Qed.
Lemma lem5291504 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291505 (s : real -> Prop) (b : real) : (term97 s b) = (term98 s b).
Proof. exact (MK_COMB (@lem5291504) (@lem5291503 s b)). Qed.
Lemma lem5291506 (s : real -> Prop) (c : real) (b : real) : (term92 s b c) = (term71 s c b).
Proof. exact (eq_refl (term92 s b c)). Qed.
Lemma lem5291507 (s : real -> Prop) (b : real) : (term99 s b) = (term90 s b).
Proof. exact (fun_ext (fun c : real => @lem5291506 s c b)). Qed.
Lemma lem5291508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291509 (s : real -> Prop) (b : real) : (term100 s b) = (term101 s b).
Proof. exact (MK_COMB (@lem5291508) (@lem5291507 s b)). Qed.
Lemma lem5291510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291511 (s : real -> Prop) (b : real) : (term102 s b) = (term103 s b).
Proof. exact (MK_COMB (@lem5291510) (@lem5291509 s b)). Qed.
Lemma lem5291512 (s : real -> Prop) (c : real) (b : real) : (term94 s b c) = (term67 s c b).
Proof. exact (eq_refl (term94 s b c)). Qed.
Lemma lem5291513 (s : real -> Prop) (b : real) : (term104 s b) = (term91 s b).
Proof. exact (fun_ext (fun c : real => @lem5291512 s c b)). Qed.
Lemma lem5291514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291515 (s : real -> Prop) (b : real) : (term105 s b) = (term106 s b).
Proof. exact (MK_COMB (@lem5291514) (@lem5291513 s b)). Qed.
Lemma lem5291516 (s : real -> Prop) (b : real) : (term89 s b) = (term107 s b).
Proof. exact (MK_COMB (@lem5291511 s b) (@lem5291515 s b)). Qed.
Lemma lem5291517 (s : real -> Prop) (b : real) : ((term88 s b) = (term89 s b)) = ((term77 s b) = (term107 s b)).
Proof. exact (MK_COMB (@lem5291505 s b) (@lem5291516 s b)). Qed.
Lemma lem5291518 (s : real -> Prop) (b : real) : (term77 s b) = (term107 s b).
Proof. exact (EQ_MP (@lem5291517 s b) (@lem5291495 s b)). Qed.
Lemma lem5291711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291712 (s : real -> Prop) (b : real) : (term78 s b) = (term108 s b).
Proof. exact (MK_COMB (@lem5291711) (@lem5291518 s b)). Qed.
Lemma lem5291713 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291714 (b : real) (x : real) (s : real -> Prop) : (term79 b x s) = (term109 b x s).
Proof. exact (MK_COMB (@lem5291712 s b) (@lem5291713 x s)). Qed.
Lemma lem5291715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291716 (b : real) (x : real) (s : real -> Prop) : (term81 b x s) = (term110 b x s).
Proof. exact (MK_COMB (@lem5291715) (@lem5291714 b x s)). Qed.
Lemma lem5291717 (b : real) (x : real) : (term63 b x) = (term63 b x).
Proof. exact (eq_refl (term63 b x)). Qed.
Lemma lem5291718 (s : real -> Prop) (b : real) (x : real) : (term83 s b x) = (term111 s b x).
Proof. exact (MK_COMB (@lem5291716 b x s) (@lem5291717 b x)). Qed.
Lemma lem5291720 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5291721 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5291720 real P Q). Qed.
Lemma lem5291722 (s : real -> Prop) (c : real) (b : real) : (term116 s c b) = (term117 s c b).
Proof. exact (@lem5291721 (term59 s c) (real_le c b)). Qed.
Lemma lem5291723 (s : real -> Prop) (c : real) (x : real) : (term118 s c x) = (term50 s c x).
Proof. exact (eq_refl (term118 s c x)). Qed.
Lemma lem5291724 (s : real -> Prop) (c : real) : (term119 s c) = (term59 s c).
Proof. exact (fun_ext (fun x : real => @lem5291723 s c x)). Qed.
Lemma lem5291725 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5291726 (s : real -> Prop) (c : real) : (term120 s c) = (term60 s c).
Proof. exact (MK_COMB (@lem5291725) (@lem5291724 s c)). Qed.
Lemma lem5291727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5291728 (s : real -> Prop) (c : real) : (term121 s c) = (term65 s c).
Proof. exact (MK_COMB (@lem5291727) (@lem5291726 s c)). Qed.
Lemma lem5291729 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5291730 (s : real -> Prop) (c : real) (b : real) : (term116 s c b) = (term67 s c b).
Proof. exact (MK_COMB (@lem5291728 s c) (@lem5291729 c b)). Qed.
Lemma lem5291731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291732 (s : real -> Prop) (c : real) (b : real) : (term122 s c b) = (term123 s c b).
Proof. exact (MK_COMB (@lem5291731) (@lem5291730 s c b)). Qed.
Lemma lem5291733 (s : real -> Prop) (c : real) (x : real) : (term118 s c x) = (term50 s c x).
Proof. exact (eq_refl (term118 s c x)). Qed.
Lemma lem5291734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5291735 (s : real -> Prop) (c : real) (x : real) : (term124 s c x) = (term125 s c x).
Proof. exact (MK_COMB (@lem5291734) (@lem5291733 s c x)). Qed.
Lemma lem5291736 (c : real) (b : real) : (real_le c b) = (real_le c b).
Proof. exact (eq_refl (real_le c b)). Qed.
Lemma lem5291737 (s : real -> Prop) (x : real) (c : real) (b : real) : (term126 s x c b) = (term127 s x c b).
Proof. exact (MK_COMB (@lem5291735 s c x) (@lem5291736 c b)). Qed.
Lemma lem5291738 (s : real -> Prop) (c : real) (b : real) : (term128 s c b) = (term129 s c b).
Proof. exact (fun_ext (fun x : real => @lem5291737 s x c b)). Qed.
Lemma lem5291739 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5291740 (s : real -> Prop) (c : real) (b : real) : (term117 s c b) = (term130 s c b).
Proof. exact (MK_COMB (@lem5291739) (@lem5291738 s c b)). Qed.
Lemma lem5291741 (s : real -> Prop) (c : real) (b : real) : ((term116 s c b) = (term117 s c b)) = ((term67 s c b) = (term130 s c b)).
Proof. exact (MK_COMB (@lem5291732 s c b) (@lem5291740 s c b)). Qed.
Lemma lem5291742 (s : real -> Prop) (c : real) (b : real) : (term67 s c b) = (term130 s c b).
Proof. exact (EQ_MP (@lem5291741 s c b) (@lem5291722 s c b)). Qed.
Lemma lem5291743 (s : real -> Prop) (b : real) : (term91 s b) = (term131 s b).
Proof. exact (fun_ext (fun c : real => @lem5291742 s c b)). Qed.
Lemma lem5291744 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291745 (s : real -> Prop) (b : real) : (term106 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5291744) (@lem5291743 s b)). Qed.
Lemma lem5291747 {A B : Type'} (P : type1413 A B) : (term133 A B P) = (term134 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5291748 (P : type1626) : (term135 P) = (term136 P).
Proof. exact (@lem5291747 real real P). Qed.
Lemma lem5291749 (s : real -> Prop) (b : real) : (term137 s b) = (term138 s b).
Proof. exact (@lem5291748 (term139 s b)). Qed.
Lemma lem5291750 (s : real -> Prop) (c : real) (b : real) : (term140 s b c) = (term129 s c b).
Proof. exact (eq_refl (term140 s b c)). Qed.
Lemma lem5291751 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5291752 (s : real -> Prop) (c : real) (b : real) (x : real) : (term141 s b c x) = (term142 s c b x).
Proof. exact (MK_COMB (@lem5291750 s c b) (@lem5291751 x)). Qed.
Lemma lem5291753 (s : real -> Prop) (x : real) (c : real) (b : real) : (term142 s c b x) = (term127 s x c b).
Proof. exact (eq_refl (term142 s c b x)). Qed.
Lemma lem5291754 (s : real -> Prop) (x : real) (c : real) (b : real) : (term141 s b c x) = (term127 s x c b).
Proof. exact (TRANS (@lem5291752 s c b x) (@lem5291753 s x c b)). Qed.
Lemma lem5291755 (s : real -> Prop) (c : real) (b : real) : (term143 s b c) = (term129 s c b).
Proof. exact (fun_ext (fun x : real => @lem5291754 s x c b)). Qed.
Lemma lem5291756 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5291757 (s : real -> Prop) (c : real) (b : real) : (term144 s b c) = (term130 s c b).
Proof. exact (MK_COMB (@lem5291756) (@lem5291755 s c b)). Qed.
Lemma lem5291758 (s : real -> Prop) (b : real) : (term145 s b) = (term131 s b).
Proof. exact (fun_ext (fun c : real => @lem5291757 s c b)). Qed.
Lemma lem5291759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291760 (s : real -> Prop) (b : real) : (term137 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5291759) (@lem5291758 s b)). Qed.
Lemma lem5291761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291762 (s : real -> Prop) (b : real) : (term146 s b) = (term147 s b).
Proof. exact (MK_COMB (@lem5291761) (@lem5291760 s b)). Qed.
Lemma lem5291763 (s : real -> Prop) (c : real) (b : real) : (term140 s b c) = (term129 s c b).
Proof. exact (eq_refl (term140 s b c)). Qed.
Lemma lem5291764 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5291765 (s : real -> Prop) (b : real) (x : real -> real) (c : real) : (term148 s b x c) = (term149 s b x c).
Proof. exact (MK_COMB (@lem5291763 s c b) (@lem5291764 x c)). Qed.
Lemma lem5291766 (s : real -> Prop) (x : real -> real) (c : real) (b : real) : (term149 s b x c) = (term150 s x c b).
Proof. exact (eq_refl (term149 s b x c)). Qed.
Lemma lem5291767 (s : real -> Prop) (x : real -> real) (c : real) (b : real) : (term148 s b x c) = (term150 s x c b).
Proof. exact (TRANS (@lem5291765 s b x c) (@lem5291766 s x c b)). Qed.
Lemma lem5291768 (s : real -> Prop) (x : real -> real) (b : real) : (term151 s b x) = (term152 s x b).
Proof. exact (fun_ext (fun c : real => @lem5291767 s x c b)). Qed.
Lemma lem5291769 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291770 (s : real -> Prop) (x : real -> real) (b : real) : (term153 s b x) = (term154 s x b).
Proof. exact (MK_COMB (@lem5291769) (@lem5291768 s x b)). Qed.
Lemma lem5291771 (s : real -> Prop) (b : real) : (term155 s b) = (term156 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5291770 s x b)). Qed.
Lemma lem5291772 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291773 (s : real -> Prop) (b : real) : (term138 s b) = (term157 s b).
Proof. exact (MK_COMB (@lem5291772) (@lem5291771 s b)). Qed.
Lemma lem5291774 (s : real -> Prop) (b : real) : ((term137 s b) = (term138 s b)) = ((term132 s b) = (term157 s b)).
Proof. exact (MK_COMB (@lem5291762 s b) (@lem5291773 s b)). Qed.
Lemma lem5291775 (s : real -> Prop) (b : real) : (term132 s b) = (term157 s b).
Proof. exact (EQ_MP (@lem5291774 s b) (@lem5291749 s b)). Qed.
Lemma lem5291776 (s : real -> Prop) (b : real) : (term106 s b) = (term157 s b).
Proof. exact (TRANS (@lem5291745 s b) (@lem5291775 s b)). Qed.
Lemma lem5291777 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (eq_refl (term103 s b)). Qed.
Lemma lem5291778 (s : real -> Prop) (b : real) : (term107 s b) = (term158 s b).
Proof. exact (MK_COMB (@lem5291777 s b) (@lem5291776 s b)). Qed.
Lemma lem5291780 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5291781 (P : Prop) (Q : type1028) : (term161 P Q) = (term162 P Q).
Proof. exact (@lem5291780 (real -> real) P Q). Qed.
Lemma lem5291782 (s : real -> Prop) (b : real) : (term163 s b) = (term164 s b).
Proof. exact (@lem5291781 (term101 s b) (term156 s b)). Qed.
Lemma lem5291783 (s : real -> Prop) (x : real -> real) (b : real) : (term165 s b x) = (term154 s x b).
Proof. exact (eq_refl (term165 s b x)). Qed.
Lemma lem5291784 (s : real -> Prop) (b : real) : (term166 s b) = (term156 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5291783 s x b)). Qed.
Lemma lem5291785 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291786 (s : real -> Prop) (b : real) : (term167 s b) = (term157 s b).
Proof. exact (MK_COMB (@lem5291785) (@lem5291784 s b)). Qed.
Lemma lem5291787 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (eq_refl (term103 s b)). Qed.
Lemma lem5291788 (s : real -> Prop) (b : real) : (term163 s b) = (term158 s b).
Proof. exact (MK_COMB (@lem5291787 s b) (@lem5291786 s b)). Qed.
Lemma lem5291789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291790 (s : real -> Prop) (b : real) : (term168 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5291789) (@lem5291788 s b)). Qed.
Lemma lem5291791 (s : real -> Prop) (x : real -> real) (b : real) : (term165 s b x) = (term154 s x b).
Proof. exact (eq_refl (term165 s b x)). Qed.
Lemma lem5291792 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (eq_refl (term103 s b)). Qed.
Lemma lem5291793 (s : real -> Prop) (x : real -> real) (b : real) : (term170 s b x) = (term171 s x b).
Proof. exact (MK_COMB (@lem5291792 s b) (@lem5291791 s x b)). Qed.
Lemma lem5291794 (s : real -> Prop) (b : real) : (term172 s b) = (term173 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5291793 s x b)). Qed.
Lemma lem5291795 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291796 (s : real -> Prop) (b : real) : (term164 s b) = (term174 s b).
Proof. exact (MK_COMB (@lem5291795) (@lem5291794 s b)). Qed.
Lemma lem5291797 (s : real -> Prop) (b : real) : ((term163 s b) = (term164 s b)) = ((term158 s b) = (term174 s b)).
Proof. exact (MK_COMB (@lem5291790 s b) (@lem5291796 s b)). Qed.
Lemma lem5291798 (s : real -> Prop) (b : real) : (term158 s b) = (term174 s b).
Proof. exact (EQ_MP (@lem5291797 s b) (@lem5291782 s b)). Qed.
Lemma lem5291799 (s : real -> Prop) (b : real) : (term107 s b) = (term174 s b).
Proof. exact (TRANS (@lem5291778 s b) (@lem5291798 s b)). Qed.
Lemma lem5291800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291801 (s : real -> Prop) (b : real) : (term108 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5291800) (@lem5291799 s b)). Qed.
Lemma lem5291802 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291803 (b : real) (x : real) (s : real -> Prop) : (term109 b x s) = (term176 b x s).
Proof. exact (MK_COMB (@lem5291801 s b) (@lem5291802 x s)). Qed.
Lemma lem5291805 {A : Type'} (P : A -> Prop) (Q : Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5291806 (P : type1028) (Q : Prop) : (term179 P Q) = (term180 P Q).
Proof. exact (@lem5291805 (real -> real) P Q). Qed.
Lemma lem5291807 (b : real) (x : real) (s : real -> Prop) : (term181 b x s) = (term182 b x s).
Proof. exact (@lem5291806 (term173 s b) (@IN real x s)). Qed.
Lemma lem5291808 (s : real -> Prop) (x : real -> real) (b : real) : (term183 s b x) = (term171 s x b).
Proof. exact (eq_refl (term183 s b x)). Qed.
Lemma lem5291809 (s : real -> Prop) (b : real) : (term184 s b) = (term173 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5291808 s x b)). Qed.
Lemma lem5291810 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291811 (s : real -> Prop) (b : real) : (term185 s b) = (term174 s b).
Proof. exact (MK_COMB (@lem5291810) (@lem5291809 s b)). Qed.
Lemma lem5291812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291813 (s : real -> Prop) (b : real) : (term186 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5291812) (@lem5291811 s b)). Qed.
Lemma lem5291814 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291815 (b : real) (x : real) (s : real -> Prop) : (term181 b x s) = (term176 b x s).
Proof. exact (MK_COMB (@lem5291813 s b) (@lem5291814 x s)). Qed.
Lemma lem5291816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291817 (b : real) (x : real) (s : real -> Prop) : (term187 b x s) = (term188 b x s).
Proof. exact (MK_COMB (@lem5291816) (@lem5291815 b x s)). Qed.
Lemma lem5291818 (s : real -> Prop) (x : real -> real) (b : real) : (term183 s b x) = (term171 s x b).
Proof. exact (eq_refl (term183 s b x)). Qed.
Lemma lem5291819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291820 (s : real -> Prop) (x : real -> real) (b : real) : (term189 s b x) = (term190 s x b).
Proof. exact (MK_COMB (@lem5291819) (@lem5291818 s x b)). Qed.
Lemma lem5291821 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291822 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term191 b x x' s) = (term192 x b x' s).
Proof. exact (MK_COMB (@lem5291820 s x b) (@lem5291821 x' s)). Qed.
Lemma lem5291823 (b : real) (x : real) (s : real -> Prop) : (term193 b x s) = (term194 b x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5291822 x' b x s)). Qed.
Lemma lem5291824 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291825 (b : real) (x : real) (s : real -> Prop) : (term182 b x s) = (term195 b x s).
Proof. exact (MK_COMB (@lem5291824) (@lem5291823 b x s)). Qed.
Lemma lem5291826 (b : real) (x : real) (s : real -> Prop) : ((term181 b x s) = (term182 b x s)) = ((term176 b x s) = (term195 b x s)).
Proof. exact (MK_COMB (@lem5291817 b x s) (@lem5291825 b x s)). Qed.
Lemma lem5291827 (b : real) (x : real) (s : real -> Prop) : (term176 b x s) = (term195 b x s).
Proof. exact (EQ_MP (@lem5291826 b x s) (@lem5291807 b x s)). Qed.
Lemma lem5291828 (b : real) (x : real) (s : real -> Prop) : (term109 b x s) = (term195 b x s).
Proof. exact (TRANS (@lem5291803 b x s) (@lem5291827 b x s)). Qed.
Lemma lem5291829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291830 (b : real) (x : real) (s : real -> Prop) : (term110 b x s) = (term196 b x s).
Proof. exact (MK_COMB (@lem5291829) (@lem5291828 b x s)). Qed.
Lemma lem5291831 (b : real) (x : real) : (term63 b x) = (term63 b x).
Proof. exact (eq_refl (term63 b x)). Qed.
Lemma lem5291832 (s : real -> Prop) (b : real) (x : real) : (term111 s b x) = (term197 s b x).
Proof. exact (MK_COMB (@lem5291830 b x s) (@lem5291831 b x)). Qed.
Lemma lem5291834 {A : Type'} (P : A -> Prop) (Q : Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5291835 (P : type1028) (Q : Prop) : (term179 P Q) = (term180 P Q).
Proof. exact (@lem5291834 (real -> real) P Q). Qed.
Lemma lem5291836 (s : real -> Prop) (b : real) (x : real) : (term198 s b x) = (term199 s b x).
Proof. exact (@lem5291835 (term194 b x s) (term63 b x)). Qed.
Lemma lem5291837 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term200 b x' s x) = (term192 x b x' s).
Proof. exact (eq_refl (term200 b x' s x)). Qed.
Lemma lem5291838 (b : real) (x : real) (s : real -> Prop) : (term201 b x s) = (term194 b x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5291837 x' b x s)). Qed.
Lemma lem5291839 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291840 (b : real) (x : real) (s : real -> Prop) : (term202 b x s) = (term195 b x s).
Proof. exact (MK_COMB (@lem5291839) (@lem5291838 b x s)). Qed.
Lemma lem5291841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291842 (b : real) (x : real) (s : real -> Prop) : (term203 b x s) = (term196 b x s).
Proof. exact (MK_COMB (@lem5291841) (@lem5291840 b x s)). Qed.
Lemma lem5291843 (b : real) (x : real) : (term63 b x) = (term63 b x).
Proof. exact (eq_refl (term63 b x)). Qed.
Lemma lem5291844 (s : real -> Prop) (b : real) (x : real) : (term198 s b x) = (term197 s b x).
Proof. exact (MK_COMB (@lem5291842 b x s) (@lem5291843 b x)). Qed.
Lemma lem5291845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5291846 (s : real -> Prop) (b : real) (x : real) : (term204 s b x) = (term205 s b x).
Proof. exact (MK_COMB (@lem5291845) (@lem5291844 s b x)). Qed.
Lemma lem5291847 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term200 b x' s x) = (term192 x b x' s).
Proof. exact (eq_refl (term200 b x' s x)). Qed.
Lemma lem5291848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291849 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term206 b x' s x) = (term207 x b x' s).
Proof. exact (MK_COMB (@lem5291848) (@lem5291847 x b x' s)). Qed.
Lemma lem5291850 (b : real) (x : real) : (term63 b x) = (term63 b x).
Proof. exact (eq_refl (term63 b x)). Qed.
Lemma lem5291851 (x : real -> real) (s : real -> Prop) (b : real) (x' : real) : (term208 s x b x') = (term209 x s b x').
Proof. exact (MK_COMB (@lem5291849 x b x' s) (@lem5291850 b x')). Qed.
Lemma lem5291852 (s : real -> Prop) (b : real) (x : real) : (term210 s b x) = (term211 s b x).
Proof. exact (fun_ext (fun x' : real -> real => @lem5291851 x' s b x)). Qed.
Lemma lem5291853 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5291854 (s : real -> Prop) (b : real) (x : real) : (term199 s b x) = (term212 s b x).
Proof. exact (MK_COMB (@lem5291853) (@lem5291852 s b x)). Qed.
Lemma lem5291855 (s : real -> Prop) (b : real) (x : real) : ((term198 s b x) = (term199 s b x)) = ((term197 s b x) = (term212 s b x)).
Proof. exact (MK_COMB (@lem5291846 s b x) (@lem5291854 s b x)). Qed.
Lemma lem5291856 (s : real -> Prop) (b : real) (x : real) : (term197 s b x) = (term212 s b x).
Proof. exact (EQ_MP (@lem5291855 s b x) (@lem5291836 s b x)). Qed.
Lemma lem5291857 (s : real -> Prop) (b : real) (x : real) : (term111 s b x) = (term212 s b x).
Proof. exact (TRANS (@lem5291832 s b x) (@lem5291856 s b x)). Qed.
Lemma lem5291858 (s : real -> Prop) (b : real) (x : real) : (term83 s b x) = (term212 s b x).
Proof. exact (TRANS (@lem5291718 s b x) (@lem5291857 s b x)). Qed.
Lemma lem5291859 (s : real -> Prop) (b : real) (x : real) : (term21 s b x) = (term212 s b x).
Proof. exact (TRANS (@lem5291491 s b x) (@lem5291858 s b x)). Qed.
Lemma lem5291860 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : term212 s b x.
Proof. exact (EQ_MP (@lem5291859 s b x) (@lem5291437 s b x h1)). Qed.
Lemma lem5291861 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5291862 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5291861 x)). Qed.
Lemma lem5291863 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291872 : term28 = term28.
Proof. exact (MK_COMB (@lem5291863) (@lem5291862)). Qed.
Lemma lem5291873 (h1 : term28) : term28.
Proof. exact (EQ_MP (@lem5291872) (@lem5291438 h1)). Qed.
Lemma lem5291874 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term209 x' s b x.
Proof. exact (h1). Qed.
Lemma lem5291879 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5291880 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5291879 x)). Qed.
Lemma lem5291881 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291882 : term28 = term28.
Proof. exact (MK_COMB (@lem5291881) (@lem5291880)). Qed.
Lemma lem5291883 (h1 : term28) : term28.
Proof. exact (EQ_MP (@lem5291882) (@lem5291873 h1)). Qed.
Lemma lem5291890 (b : real) (x : real) : (term63 b x) = (term63 b x).
Proof. exact (eq_refl (term63 b x)). Qed.
Lemma lem5291895 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5291922 (s : real -> Prop) (x' : real -> real) (c : real) (b : real) : (term150 s x' c b) = (term150 s x' c b).
Proof. exact (eq_refl (term150 s x' c b)). Qed.
Lemma lem5291923 (s : real -> Prop) (x' : real -> real) (b : real) : (term152 s x' b) = (term152 s x' b).
Proof. exact (fun_ext (fun c : real => @lem5291922 s x' c b)). Qed.
Lemma lem5291924 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291925 (s : real -> Prop) (x' : real -> real) (b : real) : (term154 s x' b) = (term154 s x' b).
Proof. exact (MK_COMB (@lem5291924) (@lem5291923 s x' b)). Qed.
Lemma lem5291932 (c : real) (b : real) : (term63 c b) = (term63 c b).
Proof. exact (eq_refl (term63 c b)). Qed.
Lemma lem5291947 (s : real -> Prop) (c : real) (x : real) : (term51 s c x) = (term51 s c x).
Proof. exact (eq_refl (term51 s c x)). Qed.
Lemma lem5291948 (s : real -> Prop) (c : real) : (term61 s c) = (term61 s c).
Proof. exact (fun_ext (fun x : real => @lem5291947 s c x)). Qed.
Lemma lem5291949 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291950 (s : real -> Prop) (c : real) : (term62 s c) = (term62 s c).
Proof. exact (MK_COMB (@lem5291949) (@lem5291948 s c)). Qed.
Lemma lem5291951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5291952 (s : real -> Prop) (c : real) : (term69 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5291951) (@lem5291950 s c)). Qed.
Lemma lem5291953 (s : real -> Prop) (c : real) (b : real) : (term71 s c b) = (term71 s c b).
Proof. exact (MK_COMB (@lem5291952 s c) (@lem5291932 c b)). Qed.
Lemma lem5291954 (s : real -> Prop) (b : real) : (term90 s b) = (term90 s b).
Proof. exact (fun_ext (fun c : real => @lem5291953 s c b)). Qed.
Lemma lem5291955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291956 (s : real -> Prop) (b : real) : (term101 s b) = (term101 s b).
Proof. exact (MK_COMB (@lem5291955) (@lem5291954 s b)). Qed.
Lemma lem5291957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291958 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (MK_COMB (@lem5291957) (@lem5291956 s b)). Qed.
Lemma lem5291959 (s : real -> Prop) (x' : real -> real) (b : real) : (term171 s x' b) = (term171 s x' b).
Proof. exact (MK_COMB (@lem5291958 s b) (@lem5291925 s x' b)). Qed.
Lemma lem5291960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291961 (s : real -> Prop) (x' : real -> real) (b : real) : (term190 s x' b) = (term190 s x' b).
Proof. exact (MK_COMB (@lem5291960) (@lem5291959 s x' b)). Qed.
Lemma lem5291962 (x' : real -> real) (b : real) (x : real) (s : real -> Prop) : (term192 x' b x s) = (term192 x' b x s).
Proof. exact (MK_COMB (@lem5291961 s x' b) (@lem5291895 x s)). Qed.
Lemma lem5291963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5291964 (x' : real -> real) (b : real) (x : real) (s : real -> Prop) : (term207 x' b x s) = (term207 x' b x s).
Proof. exact (MK_COMB (@lem5291963) (@lem5291962 x' b x s)). Qed.
Lemma lem5291965 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) : (term209 x' s b x) = (term209 x' s b x).
Proof. exact (MK_COMB (@lem5291964 x' b x s) (@lem5291890 b x)). Qed.
Lemma lem5291966 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term209 x' s b x.
Proof. exact (EQ_MP (@lem5291965 x' s b x) (@lem5291874 x' s b x h1)). Qed.
Lemma lem5291968 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term192 x' b x s.
Proof. exact (proj1 (@lem5291966 x' s b x h1)). Qed.
Lemma lem5291970 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term171 s x' b.
Proof. exact (proj1 (@lem5291968 x' s b x h1)). Qed.
Lemma lem5291972 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term101 s b.
Proof. exact (proj1 (@lem5291970 x' s b x h1)). Qed.
Lemma lem5291974 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5291975 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5291974 x)). Qed.
Lemma lem5291976 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291978 : term28 = term28.
Proof. exact (MK_COMB (@lem5291976) (@lem5291975)). Qed.
Lemma lem5291979 (h1 : term28) : term28.
Proof. exact (EQ_MP (@lem5291978) (@lem5291883 h1)). Qed.
Lemma lem5291989 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5291990 (P : real -> Prop) (Q : Prop) : (term215 P Q) = (term216 P Q).
Proof. exact (@lem5291989 real P Q). Qed.
Lemma lem5291991 (s : real -> Prop) (c : real) (b : real) : (term217 s c b) = (term218 s c b).
Proof. exact (@lem5291990 (term61 s c) (term63 c b)). Qed.
Lemma lem5291992 (s : real -> Prop) (c : real) (x : real) : (term219 s c x) = (term51 s c x).
Proof. exact (eq_refl (term219 s c x)). Qed.
Lemma lem5291993 (s : real -> Prop) (c : real) : (term220 s c) = (term61 s c).
Proof. exact (fun_ext (fun x : real => @lem5291992 s c x)). Qed.
Lemma lem5291994 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5291995 (s : real -> Prop) (c : real) : (term221 s c) = (term62 s c).
Proof. exact (MK_COMB (@lem5291994) (@lem5291993 s c)). Qed.
Lemma lem5291996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5291997 (s : real -> Prop) (c : real) : (term222 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5291996) (@lem5291995 s c)). Qed.
Lemma lem5291998 (c : real) (b : real) : (term63 c b) = (term63 c b).
Proof. exact (eq_refl (term63 c b)). Qed.
Lemma lem5291999 (s : real -> Prop) (c : real) (b : real) : (term217 s c b) = (term71 s c b).
Proof. exact (MK_COMB (@lem5291997 s c) (@lem5291998 c b)). Qed.
Lemma lem5292000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292001 (s : real -> Prop) (c : real) (b : real) : (term223 s c b) = (term224 s c b).
Proof. exact (MK_COMB (@lem5292000) (@lem5291999 s c b)). Qed.
Lemma lem5292002 (s : real -> Prop) (c : real) (x : real) : (term219 s c x) = (term51 s c x).
Proof. exact (eq_refl (term219 s c x)). Qed.
Lemma lem5292003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5292004 (s : real -> Prop) (c : real) (x : real) : (term225 s c x) = (term226 s c x).
Proof. exact (MK_COMB (@lem5292003) (@lem5292002 s c x)). Qed.
Lemma lem5292005 (c : real) (b : real) : (term63 c b) = (term63 c b).
Proof. exact (eq_refl (term63 c b)). Qed.
Lemma lem5292006 (s : real -> Prop) (x : real) (c : real) (b : real) : (term227 s x c b) = (term228 s x c b).
Proof. exact (MK_COMB (@lem5292004 s c x) (@lem5292005 c b)). Qed.
Lemma lem5292007 (s : real -> Prop) (c : real) (b : real) : (term229 s c b) = (term230 s c b).
Proof. exact (fun_ext (fun x : real => @lem5292006 s x c b)). Qed.
Lemma lem5292008 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292009 (s : real -> Prop) (c : real) (b : real) : (term218 s c b) = (term231 s c b).
Proof. exact (MK_COMB (@lem5292008) (@lem5292007 s c b)). Qed.
Lemma lem5292010 (s : real -> Prop) (c : real) (b : real) : ((term217 s c b) = (term218 s c b)) = ((term71 s c b) = (term231 s c b)).
Proof. exact (MK_COMB (@lem5292001 s c b) (@lem5292009 s c b)). Qed.
Lemma lem5292011 (s : real -> Prop) (c : real) (b : real) : (term71 s c b) = (term231 s c b).
Proof. exact (EQ_MP (@lem5292010 s c b) (@lem5291991 s c b)). Qed.
Lemma lem5292012 (s : real -> Prop) (b : real) : (term90 s b) = (term232 s b).
Proof. exact (fun_ext (fun c : real => @lem5292011 s c b)). Qed.
Lemma lem5292013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292014 (s : real -> Prop) (b : real) : (term101 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5292013) (@lem5292012 s b)). Qed.
Lemma lem5292027 (s : real -> Prop) (x : real) (c : real) (b : real) : (term228 s x c b) = (term228 s x c b).
Proof. exact (eq_refl (term228 s x c b)). Qed.
Lemma lem5292028 (s : real -> Prop) (c : real) (b : real) : (term230 s c b) = (term230 s c b).
Proof. exact (fun_ext (fun x : real => @lem5292027 s x c b)). Qed.
Lemma lem5292029 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292030 (s : real -> Prop) (c : real) (b : real) : (term231 s c b) = (term231 s c b).
Proof. exact (MK_COMB (@lem5292029) (@lem5292028 s c b)). Qed.
Lemma lem5292031 (s : real -> Prop) (b : real) : (term232 s b) = (term232 s b).
Proof. exact (fun_ext (fun c : real => @lem5292030 s c b)). Qed.
Lemma lem5292032 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292033 (s : real -> Prop) (b : real) : (term233 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5292032) (@lem5292031 s b)). Qed.
Lemma lem5292034 (s : real -> Prop) (b : real) : (term101 s b) = (term233 s b).
Proof. exact (TRANS (@lem5292014 s b) (@lem5292033 s b)). Qed.
Lemma lem5292035 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term233 s b.
Proof. exact (EQ_MP (@lem5292034 s b) (@lem5291972 x' s b x h1)). Qed.
Lemma lem5292059 (_69278 : real) (h1 : term28) : term234 _69278.
Proof. exact (@lem5291979 h1 _69278). Qed.
Lemma lem5292060 (_69278 : real) : (term234 _69278) = (real_le _69278 _69278).
Proof. exact (eq_refl (term234 _69278)). Qed.
Lemma lem5292062 (_69279 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term235 s b _69279.
Proof. exact (@lem5292035 x' s b x h1 _69279). Qed.
Lemma lem5292063 (s : real -> Prop) (_69279 : real) (b : real) : (term235 s b _69279) = (term231 s _69279 b).
Proof. exact (eq_refl (term235 s b _69279)). Qed.
Lemma lem5292064 (_69279 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term231 s _69279 b.
Proof. exact (EQ_MP (@lem5292063 s _69279 b) (@lem5292062 _69279 x' s b x h1)). Qed.
Lemma lem5292065 (_69279 : real) (_69280 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term236 s _69279 b _69280.
Proof. exact (@lem5292064 _69279 x' s b x h1 _69280). Qed.
Lemma lem5292066 (s : real -> Prop) (_69280 : real) (_69279 : real) (b : real) : (term236 s _69279 b _69280) = (term228 s _69280 _69279 b).
Proof. exact (eq_refl (term236 s _69279 b _69280)). Qed.
Lemma lem5292067 (_69280 : real) (_69279 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term228 s _69280 _69279 b.
Proof. exact (EQ_MP (@lem5292066 s _69280 _69279 b) (@lem5292065 _69279 _69280 x' s b x h1)). Qed.
Lemma lem5292076 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term63 b x.
Proof. exact (proj2 (@lem5291966 x' s b x h1)). Qed.
Lemma lem5292089 (s : real -> Prop) (_69280 : real) (_69279 : real) (b : real) : (term228 s _69280 _69279 b) = (term237 s _69280 _69279 b).
Proof. exact (@lem5291224 (term238 _69280 s) (real_le _69279 _69280) (term63 _69279 b)). Qed.
Lemma lem5292090 (_69280 : real) (_69279 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term237 s _69280 _69279 b.
Proof. exact (EQ_MP (@lem5292089 s _69280 _69279 b) (@lem5292067 _69280 _69279 x' s b x h1)). Qed.
Lemma lem5292104 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : @IN real x s.
Proof. exact (proj2 (@lem5291968 x' s b x h1)). Qed.
Lemma lem5292105 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term239 x s.
Proof. exact (fun h0 : term238 x s => @lem5292104 x' s b x h1). Qed.
Lemma lem5292107 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5292108 (x : real) (s : real -> Prop) : (term239 x s) = (@IN real x s).
Proof. exact (@lem5292107 (@IN real x s)). Qed.
Lemma lem5292109 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : @IN real x s.
Proof. exact (EQ_MP (@lem5292108 x s) (@lem5292105 x' s b x h1)). Qed.
Lemma lem5292111 (_69278 : real) (h1 : term28) : real_le _69278 _69278.
Proof. exact (EQ_MP (@lem5292060 _69278) (@lem5292059 _69278 h1)). Qed.
Lemma lem5292112 (b : real) (h1 : term28) : real_le b b.
Proof. exact (@lem5292111 b h1). Qed.
Lemma lem5292113 (b : real) (h1 : term28) : term241 b.
Proof. exact (fun h0 : term242 b => @lem5292112 b h1). Qed.
Lemma lem5292115 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5292116 (b : real) : (term241 b) = (real_le b b).
Proof. exact (@lem5292115 (real_le b b)). Qed.
Lemma lem5292117 (b : real) (h1 : term28) : real_le b b.
Proof. exact (EQ_MP (@lem5292116 b) (@lem5292113 b h1)). Qed.
Lemma lem5292123 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5292124 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term237 s _69280 _69279 b) = (term243 _69280 s _69279 b).
Proof. exact (@lem5292123 (real_le _69279 _69280) (term238 _69280 s) (term63 _69279 b)). Qed.
Lemma lem5292140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292141 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term244 s _69280 _69279 b) = (term245 _69280 s _69279 b).
Proof. exact (MK_COMB (@lem5292140) (@lem5292124 _69280 s _69279 b)). Qed.
Lemma lem5292157 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term243 _69280 s _69279 b) = (term243 _69280 s _69279 b).
Proof. exact (eq_refl (term243 _69280 s _69279 b)). Qed.
Lemma lem5292158 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : ((term237 s _69280 _69279 b) = (term243 _69280 s _69279 b)) = ((term243 _69280 s _69279 b) = (term243 _69280 s _69279 b)).
Proof. exact (MK_COMB (@lem5292141 _69280 s _69279 b) (@lem5292157 _69280 s _69279 b)). Qed.
Lemma lem5292160 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5292161 (x : Prop) : (x = x) = True.
Proof. exact (@lem5292160 Prop x). Qed.
Lemma lem5292162 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : ((term243 _69280 s _69279 b) = (term243 _69280 s _69279 b)) = True.
Proof. exact (@lem5292161 (term243 _69280 s _69279 b)). Qed.
Lemma lem5292163 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : ((term237 s _69280 _69279 b) = (term243 _69280 s _69279 b)) = True.
Proof. exact (TRANS (@lem5292158 _69280 s _69279 b) (@lem5292162 _69280 s _69279 b)). Qed.
Lemma lem5292164 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : True = ((term237 s _69280 _69279 b) = (term243 _69280 s _69279 b)).
Proof. exact (SYM (@lem5292163 _69280 s _69279 b)). Qed.
Lemma lem5292165 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term237 s _69280 _69279 b) = (term243 _69280 s _69279 b).
Proof. exact (EQ_MP (@lem5292164 _69280 s _69279 b) (@lem0)). Qed.
Lemma lem5292166 (_69280 : real) (_69279 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term243 _69280 s _69279 b.
Proof. exact (EQ_MP (@lem5292165 _69280 s _69279 b) (@lem5292090 _69280 _69279 x' s b x h1)). Qed.
Lemma lem5292168 (b : Prop) (a : Prop) : (a \/ b) = (term246 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5292169 (s : real -> Prop) (b : real) (_69279 : real) (_69280 : real) : (term243 _69280 s _69279 b) = (term247 s b _69279 _69280).
Proof. exact (@lem5292168 (term248 _69280 s _69279 b) (real_le _69279 _69280)). Qed.
Lemma lem5292171 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5292172 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term251 _69280 s _69279 b) = (term252 _69280 s _69279 b).
Proof. exact (@lem5292171 (term238 _69280 s) (term63 _69279 b)). Qed.
Lemma lem5292174 (a : Prop) : (term253 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5292175 (_69280 : real) (s : real -> Prop) : (term254 _69280 s) = (@IN real _69280 s).
Proof. exact (@lem5292174 (@IN real _69280 s)). Qed.
Lemma lem5292176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292177 (_69280 : real) (s : real -> Prop) : (term255 _69280 s) = (term256 _69280 s).
Proof. exact (MK_COMB (@lem5292176) (@lem5292175 _69280 s)). Qed.
Lemma lem5292179 (a : Prop) : (term253 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5292180 (_69279 : real) (b : real) : (term257 _69279 b) = (real_le _69279 b).
Proof. exact (@lem5292179 (real_le _69279 b)). Qed.
Lemma lem5292181 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term252 _69280 s _69279 b) = (term258 _69280 s _69279 b).
Proof. exact (MK_COMB (@lem5292177 _69280 s) (@lem5292180 _69279 b)). Qed.
Lemma lem5292182 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term251 _69280 s _69279 b) = (term258 _69280 s _69279 b).
Proof. exact (TRANS (@lem5292172 _69280 s _69279 b) (@lem5292181 _69280 s _69279 b)). Qed.
Lemma lem5292183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5292184 (_69280 : real) (s : real -> Prop) (_69279 : real) (b : real) : (term259 _69280 s _69279 b) = (term260 _69280 s _69279 b).
Proof. exact (MK_COMB (@lem5292183) (@lem5292182 _69280 s _69279 b)). Qed.
Lemma lem5292185 (_69279 : real) (_69280 : real) : (real_le _69279 _69280) = (real_le _69279 _69280).
Proof. exact (eq_refl (real_le _69279 _69280)). Qed.
Lemma lem5292186 (s : real -> Prop) (b : real) (_69279 : real) (_69280 : real) : (term247 s b _69279 _69280) = (term261 s b _69279 _69280).
Proof. exact (MK_COMB (@lem5292184 _69280 s _69279 b) (@lem5292185 _69279 _69280)). Qed.
Lemma lem5292187 (s : real -> Prop) (b : real) (_69279 : real) (_69280 : real) : (term243 _69280 s _69279 b) = (term261 s b _69279 _69280).
Proof. exact (TRANS (@lem5292169 s b _69279 _69280) (@lem5292186 s b _69279 _69280)). Qed.
Lemma lem5292189 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : term262 x s b.
Proof. exact (conj (@lem5292109 x' s b x h2) (@lem5292117 b h1)). Qed.
Lemma lem5292191 (_69279 : real) (_69280 : real) (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term261 s b _69279 _69280.
Proof. exact (EQ_MP (@lem5292187 s b _69279 _69280) (@lem5292166 _69280 _69279 x' s b x h1)). Qed.
Lemma lem5292192 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term263 s b x.
Proof. exact (@lem5292191 b x x' s b x h1). Qed.
Lemma lem5292195 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : real_le b x.
Proof. exact (@lem5292192 x' s b x h2 (@lem5292189 x' s b x h1 h2)). Qed.
Lemma lem5292196 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : term264 b x.
Proof. exact (fun h0 : term63 b x => @lem5292195 x' s b x h1 h2). Qed.
Lemma lem5292198 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5292199 (b : real) (x : real) : (term264 b x) = (real_le b x).
Proof. exact (@lem5292198 (real_le b x)). Qed.
Lemma lem5292200 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : real_le b x.
Proof. exact (EQ_MP (@lem5292199 b x) (@lem5292196 x' s b x h1 h2)). Qed.
Lemma lem5292203 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5292205 (b : real) (x : real) : (term63 b x) = (term265 b x).
Proof. exact (@lem5292203 (real_le b x)). Qed.
Lemma lem5292208 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term209 x' s b x) : term265 b x.
Proof. exact (EQ_MP (@lem5292205 b x) (@lem5292076 x' s b x h1)). Qed.
Lemma lem5292211 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : False.
Proof. exact (@lem5292208 x' s b x h2 (@lem5292200 x' s b x h1 h2)). Qed.
Lemma lem5292212 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : term266.
Proof. exact (fun h0 : ~ False => @lem5292211 x' s b x h1 h2). Qed.
Lemma lem5292214 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5292215 : term266 = False.
Proof. exact (@lem5292214 False). Qed.
Lemma lem5292216 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : False.
Proof. exact (EQ_MP (@lem5292215) (@lem5292212 x' s b x h1 h2)). Qed.
Lemma lem5292217 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : term28 = False.
Proof. exact (prop_ext (fun h3 : term28 => @lem5292216 x' s b x h1 h2) (fun h3 : False => @lem5291979 h1)). Qed.
Lemma lem5292218 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : False.
Proof. exact (EQ_MP (@lem5292217 x' s b x h1 h2) (@lem5291979 h1)). Qed.
Lemma lem5292219 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : (term209 x' s b x) = False.
Proof. exact (prop_ext (fun h3 : term209 x' s b x => @lem5292218 x' s b x h1 h2) (fun h3 : False => @lem5291966 x' s b x h2)). Qed.
Lemma lem5292220 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : False.
Proof. exact (EQ_MP (@lem5292219 x' s b x h1 h2) (@lem5291966 x' s b x h2)). Qed.
Lemma lem5292221 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : term28 = False.
Proof. exact (prop_ext (fun h3 : term28 => @lem5292220 x' s b x h1 h2) (fun h3 : False => @lem5291883 h1)). Qed.
Lemma lem5292222 (x' : real -> real) (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term209 x' s b x) : False.
Proof. exact (EQ_MP (@lem5292221 x' s b x h1 h2) (@lem5291883 h1)). Qed.
Lemma lem5292223 (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term21 s b x) : False.
Proof. exact (ex_elim (@lem5291860 s b x h2) (fun x' : real -> real => fun h0 : term211 s b x x' => @lem5292222 x' s b x h1 h0)). Qed.
Lemma lem5292224 (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term21 s b x) : term28 = False.
Proof. exact (prop_ext (fun h3 : term28 => @lem5292223 s b x h1 h2) (fun h3 : False => @lem5291873 h1)). Qed.
Lemma lem5292225 (s : real -> Prop) (b : real) (x : real) (h1 : term28) (h2 : term21 s b x) : False.
Proof. exact (EQ_MP (@lem5292224 s b x h1 h2) (@lem5291873 h1)). Qed.
Lemma lem5292226 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : term26.
Proof. exact (fun h0 : term28 => @lem5292225 s b x h0 h1). Qed.
Lemma lem5292227 : term26 = term27.
Proof. exact (@lem69 term28). Qed.
Lemma lem5292228 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : term27.
Proof. exact (EQ_MP (@lem5292227) (@lem5292226 s b x h1)). Qed.
Lemma lem5292229 (s : real -> Prop) (b : real) (x : real) : term30 s b x.
Proof. exact (fun h0 : term21 s b x => @lem5292228 s b x h0). Qed.
Lemma lem5292234 (b : real) (x : real) : term34 b x.
Proof. exact (fun s : real -> Prop => @lem5292229 s b x). Qed.
Lemma lem5292239 (x : real) : term38 x.
Proof. exact (fun b : real => @lem5292234 b x). Qed.
Lemma lem5292244 : term42.
Proof. exact (fun x : real => @lem5292239 x). Qed.
Lemma lem5292245 : term41.
Proof. exact (EQ_MP (@lem5291436) (@lem5292244)). Qed.
Lemma lem5292246 (x : real) : term267 x.
Proof. exact (@lem5292245 x). Qed.
Lemma lem5292247 (x : real) : (term267 x) = (term37 x).
Proof. exact (eq_refl (term267 x)). Qed.
Lemma lem5292248 (x : real) : term37 x.
Proof. exact (EQ_MP (@lem5292247 x) (@lem5292246 x)). Qed.
Lemma lem5292249 (x : real) (b : real) : term268 x b.
Proof. exact (@lem5292248 x b). Qed.
Lemma lem5292250 (b : real) (x : real) : (term268 x b) = (term33 b x).
Proof. exact (eq_refl (term268 x b)). Qed.
Lemma lem5292251 (b : real) (x : real) : term33 b x.
Proof. exact (EQ_MP (@lem5292250 b x) (@lem5292249 x b)). Qed.
Lemma lem5292252 (b : real) (x : real) (s : real -> Prop) : term269 b x s.
Proof. exact (@lem5292251 b x s). Qed.
Lemma lem5292253 (s : real -> Prop) (b : real) (x : real) : (term269 b x s) = (term22 s b x).
Proof. exact (eq_refl (term269 b x s)). Qed.
Lemma lem5292254 (s : real -> Prop) (b : real) (x : real) : term22 s b x.
Proof. exact (EQ_MP (@lem5292253 s b x) (@lem5292252 b x s)). Qed.
Lemma lem5292256 (s : real -> Prop) (b : real) (x : real) : term22 s b x.
Proof. exact (@lem5291281 s b x (@lem5292254 s b x)). Qed.
Lemma lem5292257 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : term26.
Proof. exact (@lem5292256 s b x (@lem5291266 s b x h1)). Qed.
Lemma lem5292258 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : False.
Proof. exact (@lem5292257 s b x h1 (@lem1339240)). Qed.
Lemma lem5292259 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : (term21 s b x) = False.
Proof. exact (prop_ext (fun h2 : term21 s b x => @lem5292258 s b x h1) (fun h2 : False => @lem5291266 s b x h1)). Qed.
Lemma lem5292260 (s : real -> Prop) (b : real) (x : real) (h1 : term21 s b x) : False.
Proof. exact (EQ_MP (@lem5292259 s b x h1) (@lem5291266 s b x h1)). Qed.
Lemma lem5292261 (s : real -> Prop) (b : real) (x : real) : term20 s b x.
Proof. exact (fun h0 : term21 s b x => @lem5292260 s b x h0). Qed.
Lemma lem5292262 (s : real -> Prop) (b : real) (x : real) : term18 s b x.
Proof. exact (EQ_MP (@lem5291265 s b x) (@lem5292261 s b x)). Qed.
Lemma lem5292263 (s : real -> Prop) (b : real) (x : real) : term17 s b x.
Proof. exact (EQ_MP (@lem5291261 s b x) (@lem5292262 s b x)). Qed.
Lemma lem5292268 (s : real -> Prop) (b : real) : term270 s b.
Proof. exact (fun x : real => @lem5292263 s b x). Qed.
Lemma lem5292273 (s : real -> Prop) : term271 s.
Proof. exact (fun b : real => @lem5292268 s b). Qed.
Lemma lem5292278 : term272.
Proof. exact (fun s : real -> Prop => @lem5292273 s). Qed.
