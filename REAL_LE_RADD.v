Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RADD_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1500243 (z : real) (x : real) (y : real) : (term0 z x y) = (term1 z x y).
Proof. exact (@lem17646 (term2 x y z) (real_le x y)). Qed.
Lemma lem1500244 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1500245 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (@lem1500244 (term7 x y)). Qed.
Lemma lem1500246 (z : real) (x : real) (y : real) : (term8 x y z) = ((term2 x y z) = (real_le x y)).
Proof. exact (eq_refl (term8 x y z)). Qed.
Lemma lem1500247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1500248 (z : real) (x : real) (y : real) : (term9 x y z) = (term0 z x y).
Proof. exact (MK_COMB (@lem1500247) (@lem1500246 z x y)). Qed.
Lemma lem1500249 (z : real) (x : real) (y : real) : (term9 x y z) = (term1 z x y).
Proof. exact (TRANS (@lem1500248 z x y) (@lem1500243 z x y)). Qed.
Lemma lem1500250 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1500249 z x y)). Qed.
Lemma lem1500251 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500252 (x : real) (y : real) : (term6 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1500251) (@lem1500250 x y)). Qed.
Lemma lem1500253 (x : real) (y : real) : (term5 x y) = (term12 x y).
Proof. exact (TRANS (@lem1500245 x y) (@lem1500252 x y)). Qed.
Lemma lem1500254 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1500255 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1500254 (term15 x)). Qed.
Lemma lem1500256 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1500257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1500258 (x : real) (y : real) : (term18 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1500257) (@lem1500256 x y)). Qed.
Lemma lem1500259 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1500258 x y) (@lem1500253 x y)). Qed.
Lemma lem1500260 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1500259 x y)). Qed.
Lemma lem1500261 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500262 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1500261) (@lem1500260 x)). Qed.
Lemma lem1500263 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1500255 x) (@lem1500262 x)). Qed.
Lemma lem1500264 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1500265 : term22 = term23.
Proof. exact (@lem1500264 term24). Qed.
Lemma lem1500266 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1500267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1500268 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1500267) (@lem1500266 x)). Qed.
Lemma lem1500269 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1500268 x) (@lem1500263 x)). Qed.
Lemma lem1500270 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1500269 x)). Qed.
Lemma lem1500271 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500272 : term23 = term30.
Proof. exact (MK_COMB (@lem1500271) (@lem1500270)). Qed.
Lemma lem1500274 : term22 = term30.
Proof. exact (TRANS (@lem1500265) (@lem1500272)). Qed.
Lemma lem1500291 (z : real) (x : real) (y : real) : (term1 z x y) = (term1 z x y).
Proof. exact (eq_refl (term1 z x y)). Qed.
Lemma lem1500292 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1500291 z x y)). Qed.
Lemma lem1500293 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500294 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1500293) (@lem1500292 x y)). Qed.
Lemma lem1500295 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1500294 x y)). Qed.
Lemma lem1500296 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500297 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1500296) (@lem1500295 x)). Qed.
Lemma lem1500298 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1500297 x)). Qed.
Lemma lem1500299 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500300 : term30 = term30.
Proof. exact (MK_COMB (@lem1500299) (@lem1500298)). Qed.
Lemma lem1500301 : term22 = term30.
Proof. exact (TRANS (@lem1500274) (@lem1500300)). Qed.
Lemma lem1500302 (y : real) (x : real) (z : real) : (term2 x y z) = (term31 y x z).
Proof. exact (@lem1483523 (real_add y z) (real_add x z)). Qed.
Lemma lem1500320 (y : real) (x : real) (z : real) : (term32 y x z) = (term33 y x z).
Proof. exact (@lem1483519 (real_add y z) (real_add x z)). Qed.
Lemma lem1500327 (x : real) (z : real) : (term34 x z) = (term35 x z).
Proof. exact (@lem1483508 x term36 z). Qed.
Lemma lem1500328 (y : real) (z : real) : (term37 y z) = (term37 y z).
Proof. exact (eq_refl (term37 y z)). Qed.
Lemma lem1500329 (y : real) (x : real) (z : real) : (term33 y x z) = (term38 y x z).
Proof. exact (MK_COMB (@lem1500328 y z) (@lem1500327 x z)). Qed.
Lemma lem1500330 (x : real) (y : real) (z : real) : (term38 y x z) = (term39 x y z).
Proof. exact (@lem1483484 (term40 x) (real_add y z) (term40 z)). Qed.
Lemma lem1500331 (y : real) (z : real) : (term41 y z) = (term42 y z).
Proof. exact (@lem1483482 y z (term40 z)). Qed.
Lemma lem1500332 (z : real) : (term43 z) = (term44 z).
Proof. exact (@lem1483442 term36 z). Qed.
Lemma lem1500334 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500335 : term47 = term46.
Proof. exact (@lem1500334 term48). Qed.
Lemma lem1500336 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500337 : term49 = term50.
Proof. exact (MK_COMB (@lem1500336) (@lem1500335)). Qed.
Lemma lem1500338 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1500339 (z : real) : (term44 z) = (term51 z).
Proof. exact (MK_COMB (@lem1500337) (@lem1500338 z)). Qed.
Lemma lem1500340 (z : real) : (term43 z) = (term51 z).
Proof. exact (TRANS (@lem1500332 z) (@lem1500339 z)). Qed.
Lemma lem1500341 (z : real) : (term51 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1500342 (z : real) : (term43 z) = term46.
Proof. exact (TRANS (@lem1500340 z) (@lem1500341 z)). Qed.
Lemma lem1500343 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1500344 (z : real) (y : real) : (term42 y z) = (term52 y).
Proof. exact (MK_COMB (@lem1500343 y) (@lem1500342 z)). Qed.
Lemma lem1500345 (z : real) (y : real) : (term41 y z) = (term52 y).
Proof. exact (TRANS (@lem1500331 y z) (@lem1500344 z y)). Qed.
Lemma lem1500346 (y : real) : (term52 y) = y.
Proof. exact (@lem1483450 y). Qed.
Lemma lem1500347 (z : real) (y : real) : (term41 y z) = y.
Proof. exact (TRANS (@lem1500345 z y) (@lem1500346 y)). Qed.
Lemma lem1500348 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1500349 (z : real) (x : real) (y : real) : (term39 x y z) = (term54 x y).
Proof. exact (MK_COMB (@lem1500348 x) (@lem1500347 z y)). Qed.
Lemma lem1500350 (z : real) (x : real) (y : real) : (term38 y x z) = (term54 x y).
Proof. exact (TRANS (@lem1500330 x y z) (@lem1500349 z x y)). Qed.
Lemma lem1500351 (z : real) (x : real) (y : real) : (term33 y x z) = (term54 x y).
Proof. exact (TRANS (@lem1500329 y x z) (@lem1500350 z x y)). Qed.
Lemma lem1500353 (z : real) (x : real) (y : real) : (term32 y x z) = (term54 x y).
Proof. exact (TRANS (@lem1500320 y x z) (@lem1500351 z x y)). Qed.
Lemma lem1500354 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1500355 (z : real) (x : real) (y : real) : (term55 y x z) = (term56 x y).
Proof. exact (MK_COMB (@lem1500354) (@lem1500353 z x y)). Qed.
Lemma lem1500356 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1500357 (z : real) (x : real) (y : real) : (term31 y x z) = (term57 x y).
Proof. exact (MK_COMB (@lem1500355 z x y) (@lem1500356)). Qed.
Lemma lem1500358 (z : real) (x : real) (y : real) : (term2 x y z) = (term57 x y).
Proof. exact (TRANS (@lem1500302 y x z) (@lem1500357 z x y)). Qed.
Lemma lem1500359 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1483533 x y). Qed.
Lemma lem1500372 (x : real) (y : real) : (real_sub x y) = (term60 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1500373 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500374 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1500373) (@lem1500372 x y)). Qed.
Lemma lem1500375 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1500376 (x : real) (y : real) : (term59 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1500374 x y) (@lem1500375)). Qed.
Lemma lem1500377 (x : real) (y : real) : (term58 x y) = (term63 x y).
Proof. exact (TRANS (@lem1500359 x y) (@lem1500376 x y)). Qed.
Lemma lem1500378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1500379 (z : real) (x : real) (y : real) : (term64 x y z) = (term65 x y).
Proof. exact (MK_COMB (@lem1500378) (@lem1500358 z x y)). Qed.
Lemma lem1500380 (z : real) (x : real) (y : real) : (term66 z x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1500379 z x y) (@lem1500377 x y)). Qed.
Lemma lem1500381 (x : real) (y : real) (z : real) : (term68 x y z) = (term69 x y z).
Proof. exact (@lem1483533 (real_add x z) (real_add y z)). Qed.
Lemma lem1500399 (x : real) (y : real) (z : real) : (term32 x y z) = (term33 x y z).
Proof. exact (@lem1483519 (real_add x z) (real_add y z)). Qed.
Lemma lem1500406 (y : real) (z : real) : (term34 y z) = (term35 y z).
Proof. exact (@lem1483508 y term36 z). Qed.
Lemma lem1500407 (x : real) (z : real) : (term37 x z) = (term37 x z).
Proof. exact (eq_refl (term37 x z)). Qed.
Lemma lem1500408 (x : real) (y : real) (z : real) : (term33 x y z) = (term38 x y z).
Proof. exact (MK_COMB (@lem1500407 x z) (@lem1500406 y z)). Qed.
Lemma lem1500409 (x : real) (y : real) (z : real) : (term38 x y z) = (term70 x y z).
Proof. exact (@lem1483482 x z (term35 y z)). Qed.
Lemma lem1500410 (y : real) (z : real) : (term71 y z) = (term72 y z).
Proof. exact (@lem1483484 (term40 y) z (term40 z)). Qed.
Lemma lem1500411 (z : real) : (term43 z) = (term44 z).
Proof. exact (@lem1483442 term36 z). Qed.
Lemma lem1500413 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500414 : term47 = term46.
Proof. exact (@lem1500413 term48). Qed.
Lemma lem1500415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500416 : term49 = term50.
Proof. exact (MK_COMB (@lem1500415) (@lem1500414)). Qed.
Lemma lem1500417 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1500418 (z : real) : (term44 z) = (term51 z).
Proof. exact (MK_COMB (@lem1500416) (@lem1500417 z)). Qed.
Lemma lem1500419 (z : real) : (term43 z) = (term51 z).
Proof. exact (TRANS (@lem1500411 z) (@lem1500418 z)). Qed.
Lemma lem1500420 (z : real) : (term51 z) = term46.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1500421 (z : real) : (term43 z) = term46.
Proof. exact (TRANS (@lem1500419 z) (@lem1500420 z)). Qed.
Lemma lem1500422 (y : real) : (term53 y) = (term53 y).
Proof. exact (eq_refl (term53 y)). Qed.
Lemma lem1500423 (z : real) (y : real) : (term72 y z) = (term73 y).
Proof. exact (MK_COMB (@lem1500422 y) (@lem1500421 z)). Qed.
Lemma lem1500424 (z : real) (y : real) : (term71 y z) = (term73 y).
Proof. exact (TRANS (@lem1500410 y z) (@lem1500423 z y)). Qed.
Lemma lem1500425 (y : real) : (term73 y) = (term40 y).
Proof. exact (@lem1483450 (term40 y)). Qed.
Lemma lem1500426 (z : real) (y : real) : (term71 y z) = (term40 y).
Proof. exact (TRANS (@lem1500424 z y) (@lem1500425 y)). Qed.
Lemma lem1500427 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1500428 (z : real) (x : real) (y : real) : (term70 x y z) = (term60 x y).
Proof. exact (MK_COMB (@lem1500427 x) (@lem1500426 z y)). Qed.
Lemma lem1500429 (z : real) (x : real) (y : real) : (term38 x y z) = (term60 x y).
Proof. exact (TRANS (@lem1500409 x y z) (@lem1500428 z x y)). Qed.
Lemma lem1500430 (z : real) (x : real) (y : real) : (term33 x y z) = (term60 x y).
Proof. exact (TRANS (@lem1500408 x y z) (@lem1500429 z x y)). Qed.
Lemma lem1500432 (z : real) (x : real) (y : real) : (term32 x y z) = (term60 x y).
Proof. exact (TRANS (@lem1500399 x y z) (@lem1500430 z x y)). Qed.
Lemma lem1500433 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500434 (z : real) (x : real) (y : real) : (term74 x y z) = (term62 x y).
Proof. exact (MK_COMB (@lem1500433) (@lem1500432 z x y)). Qed.
Lemma lem1500435 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1500436 (z : real) (x : real) (y : real) : (term69 x y z) = (term63 x y).
Proof. exact (MK_COMB (@lem1500434 z x y) (@lem1500435)). Qed.
Lemma lem1500437 (z : real) (x : real) (y : real) : (term68 x y z) = (term63 x y).
Proof. exact (TRANS (@lem1500381 x y z) (@lem1500436 z x y)). Qed.
Lemma lem1500438 (y : real) (x : real) : (real_le x y) = (term75 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1500444 (y : real) (x : real) : (real_sub y x) = (term60 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1500449 (x : real) (y : real) : (term60 y x) = (term54 x y).
Proof. exact (@lem1483488 (term40 x) y). Qed.
Lemma lem1500451 (x : real) (y : real) : (real_sub y x) = (term54 x y).
Proof. exact (TRANS (@lem1500444 y x) (@lem1500449 x y)). Qed.
Lemma lem1500452 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1500453 (x : real) (y : real) : (term76 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1500452) (@lem1500451 x y)). Qed.
Lemma lem1500454 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1500455 (x : real) (y : real) : (term75 y x) = (term57 x y).
Proof. exact (MK_COMB (@lem1500453 x y) (@lem1500454)). Qed.
Lemma lem1500456 (x : real) (y : real) : (real_le x y) = (term57 x y).
Proof. exact (TRANS (@lem1500438 y x) (@lem1500455 x y)). Qed.
Lemma lem1500457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1500458 (z : real) (x : real) (y : real) : (term77 x y z) = (term78 x y).
Proof. exact (MK_COMB (@lem1500457) (@lem1500437 z x y)). Qed.
Lemma lem1500459 (z : real) (x : real) (y : real) : (term79 z x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1500458 z x y) (@lem1500456 x y)). Qed.
Lemma lem1500460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500461 (z : real) (x : real) (y : real) : (term81 z x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1500460) (@lem1500380 z x y)). Qed.
Lemma lem1500462 (z : real) (x : real) (y : real) : (term1 z x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1500461 z x y) (@lem1500459 z x y)). Qed.
Lemma lem1500463 (x : real) (y : real) : (term11 x y) = (term84 x y).
Proof. exact (fun_ext (fun z : real => @lem1500462 z x y)). Qed.
Lemma lem1500464 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500465 (x : real) (y : real) : (term12 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1500464) (@lem1500463 x y)). Qed.
Lemma lem1500466 (x : real) : (term20 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1500465 x y)). Qed.
Lemma lem1500467 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500468 (x : real) : (term21 x) = (term87 x).
Proof. exact (MK_COMB (@lem1500467) (@lem1500466 x)). Qed.
Lemma lem1500469 : term29 = term88.
Proof. exact (fun_ext (fun x : real => @lem1500468 x)). Qed.
Lemma lem1500470 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500471 : term30 = term89.
Proof. exact (MK_COMB (@lem1500470) (@lem1500469)). Qed.
Lemma lem1500472 : term22 = term89.
Proof. exact (TRANS (@lem1500301) (@lem1500471)). Qed.
Lemma lem1500482 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1500483 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1500482 real P Q). Qed.
Lemma lem1500484 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (@lem1500483 (term96 x y) (term97 x y)). Qed.
Lemma lem1500485 (z : real) (x : real) (y : real) : (term98 x y z) = (term67 x y).
Proof. exact (eq_refl (term98 x y z)). Qed.
Lemma lem1500486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500487 (z : real) (x : real) (y : real) : (term99 x y z) = (term82 x y).
Proof. exact (MK_COMB (@lem1500486) (@lem1500485 z x y)). Qed.
Lemma lem1500488 (z : real) (x : real) (y : real) : (term100 x y z) = (term80 x y).
Proof. exact (eq_refl (term100 x y z)). Qed.
Lemma lem1500489 (z : real) (x : real) (y : real) : (term101 x y z) = (term83 x y).
Proof. exact (MK_COMB (@lem1500487 z x y) (@lem1500488 z x y)). Qed.
Lemma lem1500490 (x : real) (y : real) : (term102 x y) = (term84 x y).
Proof. exact (fun_ext (fun z : real => @lem1500489 z x y)). Qed.
Lemma lem1500491 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500492 (x : real) (y : real) : (term94 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1500491) (@lem1500490 x y)). Qed.
Lemma lem1500493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500494 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1500493) (@lem1500492 x y)). Qed.
Lemma lem1500495 (z : real) (x : real) (y : real) : (term98 x y z) = (term67 x y).
Proof. exact (eq_refl (term98 x y z)). Qed.
Lemma lem1500496 (x : real) (y : real) : (term105 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1500495 z x y)). Qed.
Lemma lem1500497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500498 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1500497) (@lem1500496 x y)). Qed.
Lemma lem1500499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500500 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1500499) (@lem1500498 x y)). Qed.
Lemma lem1500501 (z : real) (x : real) (y : real) : (term100 x y z) = (term80 x y).
Proof. exact (eq_refl (term100 x y z)). Qed.
Lemma lem1500502 (x : real) (y : real) : (term110 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1500501 z x y)). Qed.
Lemma lem1500503 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500504 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1500503) (@lem1500502 x y)). Qed.
Lemma lem1500505 (x : real) (y : real) : (term95 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1500500 x y) (@lem1500504 x y)). Qed.
Lemma lem1500506 (x : real) (y : real) : ((term94 x y) = (term95 x y)) = ((term85 x y) = (term113 x y)).
Proof. exact (MK_COMB (@lem1500494 x y) (@lem1500505 x y)). Qed.
Lemma lem1500507 (x : real) (y : real) : (term85 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem1500506 x y) (@lem1500484 x y)). Qed.
Lemma lem1500509 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1500510 (P : Prop) (Q : real -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem1500509 real P Q). Qed.
Lemma lem1500511 (x : real) (y : real) : (term118 x y) = (term119 x y).
Proof. exact (@lem1500510 (term57 x y) (term120 x y)). Qed.
Lemma lem1500512 (z : real) (x : real) (y : real) : (term121 x y z) = (term63 x y).
Proof. exact (eq_refl (term121 x y z)). Qed.
Lemma lem1500513 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1500514 (z : real) (x : real) (y : real) : (term122 x y z) = (term67 x y).
Proof. exact (MK_COMB (@lem1500513 x y) (@lem1500512 z x y)). Qed.
Lemma lem1500515 (x : real) (y : real) : (term123 x y) = (term96 x y).
Proof. exact (fun_ext (fun z : real => @lem1500514 z x y)). Qed.
Lemma lem1500516 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500517 (x : real) (y : real) : (term118 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1500516) (@lem1500515 x y)). Qed.
Lemma lem1500518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500519 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1500518) (@lem1500517 x y)). Qed.
Lemma lem1500520 (z : real) (x : real) (y : real) : (term121 x y z) = (term63 x y).
Proof. exact (eq_refl (term121 x y z)). Qed.
Lemma lem1500521 (x : real) (y : real) : (term126 x y) = (term120 x y).
Proof. exact (fun_ext (fun z : real => @lem1500520 z x y)). Qed.
Lemma lem1500522 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500523 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1500522) (@lem1500521 x y)). Qed.
Lemma lem1500524 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1500525 (x : real) (y : real) : (term119 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1500524 x y) (@lem1500523 x y)). Qed.
Lemma lem1500526 (x : real) (y : real) : ((term118 x y) = (term119 x y)) = ((term107 x y) = (term129 x y)).
Proof. exact (MK_COMB (@lem1500519 x y) (@lem1500525 x y)). Qed.
Lemma lem1500527 (x : real) (y : real) : (term107 x y) = (term129 x y).
Proof. exact (EQ_MP (@lem1500526 x y) (@lem1500511 x y)). Qed.
Lemma lem1500529 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1500530 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1500529 real t). Qed.
Lemma lem1500531 (x : real) (y : real) : (term128 x y) = (term63 x y).
Proof. exact (@lem1500530 (term63 x y)). Qed.
Lemma lem1500532 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1500533 (x : real) (y : real) : (term129 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1500532 x y) (@lem1500531 x y)). Qed.
Lemma lem1500534 (x : real) (y : real) : (term107 x y) = (term67 x y).
Proof. exact (TRANS (@lem1500527 x y) (@lem1500533 x y)). Qed.
Lemma lem1500535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500536 (x : real) (y : real) : (term109 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1500535) (@lem1500534 x y)). Qed.
Lemma lem1500538 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1500539 (P : Prop) (Q : real -> Prop) : (term116 P Q) = (term117 P Q).
Proof. exact (@lem1500538 real P Q). Qed.
Lemma lem1500540 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (@lem1500539 (term63 x y) (term134 x y)). Qed.
Lemma lem1500541 (z : real) (x : real) (y : real) : (term135 x y z) = (term57 x y).
Proof. exact (eq_refl (term135 x y z)). Qed.
Lemma lem1500542 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1500543 (z : real) (x : real) (y : real) : (term136 x y z) = (term80 x y).
Proof. exact (MK_COMB (@lem1500542 x y) (@lem1500541 z x y)). Qed.
Lemma lem1500544 (x : real) (y : real) : (term137 x y) = (term97 x y).
Proof. exact (fun_ext (fun z : real => @lem1500543 z x y)). Qed.
Lemma lem1500545 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500546 (x : real) (y : real) : (term132 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1500545) (@lem1500544 x y)). Qed.
Lemma lem1500547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500548 (x : real) (y : real) : (term138 x y) = (term139 x y).
Proof. exact (MK_COMB (@lem1500547) (@lem1500546 x y)). Qed.
Lemma lem1500549 (z : real) (x : real) (y : real) : (term135 x y z) = (term57 x y).
Proof. exact (eq_refl (term135 x y z)). Qed.
Lemma lem1500550 (x : real) (y : real) : (term140 x y) = (term134 x y).
Proof. exact (fun_ext (fun z : real => @lem1500549 z x y)). Qed.
Lemma lem1500551 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500552 (x : real) (y : real) : (term141 x y) = (term142 x y).
Proof. exact (MK_COMB (@lem1500551) (@lem1500550 x y)). Qed.
Lemma lem1500553 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1500554 (x : real) (y : real) : (term133 x y) = (term143 x y).
Proof. exact (MK_COMB (@lem1500553 x y) (@lem1500552 x y)). Qed.
Lemma lem1500555 (x : real) (y : real) : ((term132 x y) = (term133 x y)) = ((term112 x y) = (term143 x y)).
Proof. exact (MK_COMB (@lem1500548 x y) (@lem1500554 x y)). Qed.
Lemma lem1500556 (x : real) (y : real) : (term112 x y) = (term143 x y).
Proof. exact (EQ_MP (@lem1500555 x y) (@lem1500540 x y)). Qed.
Lemma lem1500558 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1500559 (t : Prop) : (term131 t) = t.
Proof. exact (@lem1500558 real t). Qed.
Lemma lem1500560 (x : real) (y : real) : (term142 x y) = (term57 x y).
Proof. exact (@lem1500559 (term57 x y)). Qed.
Lemma lem1500561 (x : real) (y : real) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1500562 (x : real) (y : real) : (term143 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1500561 x y) (@lem1500560 x y)). Qed.
Lemma lem1500563 (x : real) (y : real) : (term112 x y) = (term80 x y).
Proof. exact (TRANS (@lem1500556 x y) (@lem1500562 x y)). Qed.
Lemma lem1500564 (x : real) (y : real) : (term113 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1500536 x y) (@lem1500563 x y)). Qed.
Lemma lem1500565 (x : real) (y : real) : (term85 x y) = (term83 x y).
Proof. exact (TRANS (@lem1500507 x y) (@lem1500564 x y)). Qed.
Lemma lem1500566 (x : real) : (term86 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1500565 x y)). Qed.
Lemma lem1500567 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500568 (x : real) : (term87 x) = (term145 x).
Proof. exact (MK_COMB (@lem1500567) (@lem1500566 x)). Qed.
Lemma lem1500570 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1500571 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1500570 real P Q). Qed.
Lemma lem1500572 (x : real) : (term146 x) = (term147 x).
Proof. exact (@lem1500571 (term148 x) (term149 x)). Qed.
Lemma lem1500573 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1500574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500575 (x : real) (y : real) : (term151 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1500574) (@lem1500573 x y)). Qed.
Lemma lem1500576 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1500577 (x : real) (y : real) : (term153 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1500575 x y) (@lem1500576 x y)). Qed.
Lemma lem1500578 (x : real) : (term154 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1500577 x y)). Qed.
Lemma lem1500579 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500580 (x : real) : (term146 x) = (term145 x).
Proof. exact (MK_COMB (@lem1500579) (@lem1500578 x)). Qed.
Lemma lem1500581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500582 (x : real) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem1500581) (@lem1500580 x)). Qed.
Lemma lem1500583 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1500584 (x : real) : (term157 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1500583 x y)). Qed.
Lemma lem1500585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500586 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1500585) (@lem1500584 x)). Qed.
Lemma lem1500587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500588 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1500587) (@lem1500586 x)). Qed.
Lemma lem1500589 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1500590 (x : real) : (term162 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem1500589 x y)). Qed.
Lemma lem1500591 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500592 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1500591) (@lem1500590 x)). Qed.
Lemma lem1500593 (x : real) : (term147 x) = (term165 x).
Proof. exact (MK_COMB (@lem1500588 x) (@lem1500592 x)). Qed.
Lemma lem1500594 (x : real) : ((term146 x) = (term147 x)) = ((term145 x) = (term165 x)).
Proof. exact (MK_COMB (@lem1500582 x) (@lem1500593 x)). Qed.
Lemma lem1500595 (x : real) : (term145 x) = (term165 x).
Proof. exact (EQ_MP (@lem1500594 x) (@lem1500572 x)). Qed.
Lemma lem1500692 (x : real) : (term87 x) = (term165 x).
Proof. exact (TRANS (@lem1500568 x) (@lem1500595 x)). Qed.
Lemma lem1500693 : term88 = term166.
Proof. exact (fun_ext (fun x : real => @lem1500692 x)). Qed.
Lemma lem1500694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500695 : term89 = term167.
Proof. exact (MK_COMB (@lem1500694) (@lem1500693)). Qed.
Lemma lem1500697 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1500698 (P : real -> Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem1500697 real P Q). Qed.
Lemma lem1500699 : term168 = term169.
Proof. exact (@lem1500698 term170 term171). Qed.
Lemma lem1500700 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1500701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500702 (x : real) : (term173 x) = (term161 x).
Proof. exact (MK_COMB (@lem1500701) (@lem1500700 x)). Qed.
Lemma lem1500703 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1500704 (x : real) : (term175 x) = (term165 x).
Proof. exact (MK_COMB (@lem1500702 x) (@lem1500703 x)). Qed.
Lemma lem1500705 : term176 = term166.
Proof. exact (fun_ext (fun x : real => @lem1500704 x)). Qed.
Lemma lem1500706 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500707 : term168 = term167.
Proof. exact (MK_COMB (@lem1500706) (@lem1500705)). Qed.
Lemma lem1500708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500709 : term177 = term178.
Proof. exact (MK_COMB (@lem1500708) (@lem1500707)). Qed.
Lemma lem1500710 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1500711 : term179 = term170.
Proof. exact (fun_ext (fun x : real => @lem1500710 x)). Qed.
Lemma lem1500712 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500713 : term180 = term181.
Proof. exact (MK_COMB (@lem1500712) (@lem1500711)). Qed.
Lemma lem1500714 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500715 : term182 = term183.
Proof. exact (MK_COMB (@lem1500714) (@lem1500713)). Qed.
Lemma lem1500716 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1500717 : term184 = term171.
Proof. exact (fun_ext (fun x : real => @lem1500716 x)). Qed.
Lemma lem1500718 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500719 : term185 = term186.
Proof. exact (MK_COMB (@lem1500718) (@lem1500717)). Qed.
Lemma lem1500720 : term169 = term187.
Proof. exact (MK_COMB (@lem1500715) (@lem1500719)). Qed.
Lemma lem1500721 : (term168 = term169) = (term167 = term187).
Proof. exact (MK_COMB (@lem1500709) (@lem1500720)). Qed.
Lemma lem1500722 : term167 = term187.
Proof. exact (EQ_MP (@lem1500721) (@lem1500699)). Qed.
Lemma lem1500827 : term89 = term187.
Proof. exact (TRANS (@lem1500695) (@lem1500722)). Qed.
Lemma lem1500829 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1500830 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1500829 real P Q). Qed.
Lemma lem1500831 : term169 = term168.
Proof. exact (@lem1500830 term170 term171). Qed.
Lemma lem1500832 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1500833 : term179 = term170.
Proof. exact (fun_ext (fun x : real => @lem1500832 x)). Qed.
Lemma lem1500834 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500835 : term180 = term181.
Proof. exact (MK_COMB (@lem1500834) (@lem1500833)). Qed.
Lemma lem1500836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500837 : term182 = term183.
Proof. exact (MK_COMB (@lem1500836) (@lem1500835)). Qed.
Lemma lem1500838 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1500839 : term184 = term171.
Proof. exact (fun_ext (fun x : real => @lem1500838 x)). Qed.
Lemma lem1500840 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500841 : term185 = term186.
Proof. exact (MK_COMB (@lem1500840) (@lem1500839)). Qed.
Lemma lem1500842 : term169 = term187.
Proof. exact (MK_COMB (@lem1500837) (@lem1500841)). Qed.
Lemma lem1500843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500844 : term188 = term189.
Proof. exact (MK_COMB (@lem1500843) (@lem1500842)). Qed.
Lemma lem1500845 (x : real) : (term172 x) = (term159 x).
Proof. exact (eq_refl (term172 x)). Qed.
Lemma lem1500846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500847 (x : real) : (term173 x) = (term161 x).
Proof. exact (MK_COMB (@lem1500846) (@lem1500845 x)). Qed.
Lemma lem1500848 (x : real) : (term174 x) = (term164 x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1500849 (x : real) : (term175 x) = (term165 x).
Proof. exact (MK_COMB (@lem1500847 x) (@lem1500848 x)). Qed.
Lemma lem1500850 : term176 = term166.
Proof. exact (fun_ext (fun x : real => @lem1500849 x)). Qed.
Lemma lem1500851 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500852 : term168 = term167.
Proof. exact (MK_COMB (@lem1500851) (@lem1500850)). Qed.
Lemma lem1500853 : (term169 = term168) = (term187 = term167).
Proof. exact (MK_COMB (@lem1500844) (@lem1500852)). Qed.
Lemma lem1500854 : term187 = term167.
Proof. exact (EQ_MP (@lem1500853) (@lem1500831)). Qed.
Lemma lem1500856 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1500857 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem1500856 real P Q). Qed.
Lemma lem1500858 (x : real) : (term147 x) = (term146 x).
Proof. exact (@lem1500857 (term148 x) (term149 x)). Qed.
Lemma lem1500859 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1500860 (x : real) : (term157 x) = (term148 x).
Proof. exact (fun_ext (fun y : real => @lem1500859 x y)). Qed.
Lemma lem1500861 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500862 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1500861) (@lem1500860 x)). Qed.
Lemma lem1500863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500864 (x : real) : (term160 x) = (term161 x).
Proof. exact (MK_COMB (@lem1500863) (@lem1500862 x)). Qed.
Lemma lem1500865 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1500866 (x : real) : (term162 x) = (term149 x).
Proof. exact (fun_ext (fun y : real => @lem1500865 x y)). Qed.
Lemma lem1500867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500868 (x : real) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1500867) (@lem1500866 x)). Qed.
Lemma lem1500869 (x : real) : (term147 x) = (term165 x).
Proof. exact (MK_COMB (@lem1500864 x) (@lem1500868 x)). Qed.
Lemma lem1500870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1500871 (x : real) : (term190 x) = (term191 x).
Proof. exact (MK_COMB (@lem1500870) (@lem1500869 x)). Qed.
Lemma lem1500872 (x : real) (y : real) : (term150 x y) = (term67 x y).
Proof. exact (eq_refl (term150 x y)). Qed.
Lemma lem1500873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1500874 (x : real) (y : real) : (term151 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1500873) (@lem1500872 x y)). Qed.
Lemma lem1500875 (x : real) (y : real) : (term152 x y) = (term80 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem1500876 (x : real) (y : real) : (term153 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1500874 x y) (@lem1500875 x y)). Qed.
Lemma lem1500877 (x : real) : (term154 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1500876 x y)). Qed.
Lemma lem1500878 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500879 (x : real) : (term146 x) = (term145 x).
Proof. exact (MK_COMB (@lem1500878) (@lem1500877 x)). Qed.
Lemma lem1500880 (x : real) : ((term147 x) = (term146 x)) = ((term165 x) = (term145 x)).
Proof. exact (MK_COMB (@lem1500871 x) (@lem1500879 x)). Qed.
Lemma lem1500881 (x : real) : (term165 x) = (term145 x).
Proof. exact (EQ_MP (@lem1500880 x) (@lem1500858 x)). Qed.
Lemma lem1500882 : term166 = term192.
Proof. exact (fun_ext (fun x : real => @lem1500881 x)). Qed.
Lemma lem1500883 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500884 : term167 = term193.
Proof. exact (MK_COMB (@lem1500883) (@lem1500882)). Qed.
Lemma lem1500885 : term187 = term193.
Proof. exact (TRANS (@lem1500854) (@lem1500884)). Qed.
Lemma lem1500886 : term89 = term193.
Proof. exact (TRANS (@lem1500827) (@lem1500885)). Qed.
Lemma lem1500889 : term22 = term193.
Proof. exact (TRANS (@lem1500472) (@lem1500886)). Qed.
Lemma lem1500906 (x : real) (y : real) : (term83 x y) = (term83 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1500907 (x : real) : (term144 x) = (term144 x).
Proof. exact (fun_ext (fun y : real => @lem1500906 x y)). Qed.
Lemma lem1500908 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500909 (x : real) : (term145 x) = (term145 x).
Proof. exact (MK_COMB (@lem1500908) (@lem1500907 x)). Qed.
Lemma lem1500910 : term192 = term192.
Proof. exact (fun_ext (fun x : real => @lem1500909 x)). Qed.
Lemma lem1500911 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1500912 : term193 = term193.
Proof. exact (MK_COMB (@lem1500911) (@lem1500910)). Qed.
Lemma lem1500913 : term22 = term193.
Proof. exact (TRANS (@lem1500889) (@lem1500912)). Qed.
Lemma lem1500923 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1500924 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (h1). Qed.
Lemma lem1500925 (x : real) (y : real) (h1 : term67 x y) : term63 x y.
Proof. exact (proj2 (@lem1500924 x y h1)). Qed.
Lemma lem1500926 (x : real) (y : real) (h1 : term67 x y) : term57 x y.
Proof. exact (proj1 (@lem1500924 x y h1)). Qed.
Lemma lem1500928 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500929 : term195 = term196.
Proof. exact (@lem1500928 (NUMERAL 0) term48). Qed.
Lemma lem1500930 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1500931 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1500932 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1500931 h1) (fun h1 : term196 = True => @lem1500930)). Qed.
Lemma lem1500933 : term196 = True.
Proof. exact (EQ_MP (@lem1500932) (@lem1500930)). Qed.
Lemma lem1500934 : term195 = True.
Proof. exact (TRANS (@lem1500929) (@lem1500933)). Qed.
Lemma lem1500935 : True = term195.
Proof. exact (SYM (@lem1500934)). Qed.
Lemma lem1500936 : term195.
Proof. exact (EQ_MP (@lem1500935) (@lem0)). Qed.
Lemma lem1500937 (x : real) (y : real) (h1 : term67 x y) : term198 x y.
Proof. exact (conj (@lem1500936) (@lem1500926 x y h1)). Qed.
Lemma lem1500939 (x : real) (y : real) : term199 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1500940 (x : real) (y : real) : term200 x y.
Proof. exact (@lem1500939 term201 (term54 x y)). Qed.
Lemma lem1500941 (x : real) (y : real) (h1 : term67 x y) : term202 x y.
Proof. exact (@lem1500940 x y (@lem1500937 x y h1)). Qed.
Lemma lem1500942 (x : real) (y : real) : (term203 x y) = (term54 x y).
Proof. exact (@lem1483460 (term54 x y)). Qed.
Lemma lem1500943 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1500944 (x : real) (y : real) : (term204 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1500943) (@lem1500942 x y)). Qed.
Lemma lem1500945 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1500946 (x : real) (y : real) : (term202 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1500944 x y) (@lem1500945)). Qed.
Lemma lem1500947 (x : real) (y : real) (h1 : term67 x y) : term57 x y.
Proof. exact (EQ_MP (@lem1500946 x y) (@lem1500941 x y h1)). Qed.
Lemma lem1500949 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1500950 : term195 = term196.
Proof. exact (@lem1500949 (NUMERAL 0) term48). Qed.
Lemma lem1500951 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1500952 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1500953 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1500952 h1) (fun h1 : term196 = True => @lem1500951)). Qed.
Lemma lem1500954 : term196 = True.
Proof. exact (EQ_MP (@lem1500953) (@lem1500951)). Qed.
Lemma lem1500955 : term195 = True.
Proof. exact (TRANS (@lem1500950) (@lem1500954)). Qed.
Lemma lem1500956 : True = term195.
Proof. exact (SYM (@lem1500955)). Qed.
Lemma lem1500957 : term195.
Proof. exact (EQ_MP (@lem1500956) (@lem0)). Qed.
Lemma lem1500958 (x : real) (y : real) (h1 : term67 x y) : term205 x y.
Proof. exact (conj (@lem1500957) (@lem1500925 x y h1)). Qed.
Lemma lem1500960 (x : real) (y : real) : term206 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1500961 (x : real) (y : real) : term207 x y.
Proof. exact (@lem1500960 term201 (term60 x y)). Qed.
Lemma lem1500962 (x : real) (y : real) (h1 : term67 x y) : term208 x y.
Proof. exact (@lem1500961 x y (@lem1500958 x y h1)). Qed.
Lemma lem1500963 (x : real) (y : real) : (term209 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1500964 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1500965 (x : real) (y : real) : (term210 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1500964) (@lem1500963 x y)). Qed.
Lemma lem1500966 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1500967 (x : real) (y : real) : (term208 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1500965 x y) (@lem1500966)). Qed.
Lemma lem1500968 (x : real) (y : real) (h1 : term67 x y) : term63 x y.
Proof. exact (EQ_MP (@lem1500967 x y) (@lem1500962 x y h1)). Qed.
Lemma lem1500969 (x : real) (y : real) (h1 : term67 x y) : term80 x y.
Proof. exact (conj (@lem1500968 x y h1) (@lem1500947 x y h1)). Qed.
Lemma lem1500971 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1500972 (x : real) (y : real) : term212 x y.
Proof. exact (@lem1500971 (term60 x y) (term54 x y)). Qed.
Lemma lem1500973 (x : real) (y : real) (h1 : term67 x y) : term213 x y.
Proof. exact (@lem1500972 x y (@lem1500969 x y h1)). Qed.
Lemma lem1500974 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483480 x (term40 x) (term40 y) y). Qed.
Lemma lem1500975 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483442 term36 x). Qed.
Lemma lem1500977 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500978 : term47 = term46.
Proof. exact (@lem1500977 term48). Qed.
Lemma lem1500979 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500980 : term49 = term50.
Proof. exact (MK_COMB (@lem1500979) (@lem1500978)). Qed.
Lemma lem1500981 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1500982 (x : real) : (term44 x) = (term51 x).
Proof. exact (MK_COMB (@lem1500980) (@lem1500981 x)). Qed.
Lemma lem1500983 (x : real) : (term43 x) = (term51 x).
Proof. exact (TRANS (@lem1500975 x) (@lem1500982 x)). Qed.
Lemma lem1500984 (x : real) : (term51 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1500985 (x : real) : (term43 x) = term46.
Proof. exact (TRANS (@lem1500983 x) (@lem1500984 x)). Qed.
Lemma lem1500986 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1500987 (x : real) : (term216 x) = term217.
Proof. exact (MK_COMB (@lem1500986) (@lem1500985 x)). Qed.
Lemma lem1500988 (y : real) : (term218 y) = (term44 y).
Proof. exact (@lem1483440 term36 y). Qed.
Lemma lem1500990 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1500991 : term47 = term46.
Proof. exact (@lem1500990 term48). Qed.
Lemma lem1500992 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1500993 : term49 = term50.
Proof. exact (MK_COMB (@lem1500992) (@lem1500991)). Qed.
Lemma lem1500994 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1500995 (y : real) : (term44 y) = (term51 y).
Proof. exact (MK_COMB (@lem1500993) (@lem1500994 y)). Qed.
Lemma lem1500996 (y : real) : (term218 y) = (term51 y).
Proof. exact (TRANS (@lem1500988 y) (@lem1500995 y)). Qed.
Lemma lem1500997 (y : real) : (term51 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1500998 (y : real) : (term218 y) = term46.
Proof. exact (TRANS (@lem1500996 y) (@lem1500997 y)). Qed.
Lemma lem1500999 (x : real) (y : real) : (term215 x y) = term219.
Proof. exact (MK_COMB (@lem1500987 x) (@lem1500998 y)). Qed.
Lemma lem1501000 (x : real) (y : real) : (term214 x y) = term219.
Proof. exact (TRANS (@lem1500974 x y) (@lem1500999 x y)). Qed.
Lemma lem1501001 : term219 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1501002 (x : real) (y : real) : (term214 x y) = term46.
Proof. exact (TRANS (@lem1501000 x y) (@lem1501001)). Qed.
Lemma lem1501003 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501004 (x : real) (y : real) : (term220 x y) = term221.
Proof. exact (MK_COMB (@lem1501003) (@lem1501002 x y)). Qed.
Lemma lem1501005 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1501006 (x : real) (y : real) : (term213 x y) = term222.
Proof. exact (MK_COMB (@lem1501004 x y) (@lem1501005)). Qed.
Lemma lem1501007 (x : real) (y : real) (h1 : term67 x y) : term222.
Proof. exact (EQ_MP (@lem1501006 x y) (@lem1500973 x y h1)). Qed.
Lemma lem1501009 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501010 : term222 = term223.
Proof. exact (@lem1501009 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1501011 : term223 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1501012 : term222 = False.
Proof. exact (TRANS (@lem1501010) (@lem1501011)). Qed.
Lemma lem1501013 (x : real) (y : real) (h1 : term67 x y) : False.
Proof. exact (EQ_MP (@lem1501012) (@lem1501007 x y h1)). Qed.
Lemma lem1501014 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (h1). Qed.
Lemma lem1501015 (x : real) (y : real) (h1 : term80 x y) : term57 x y.
Proof. exact (proj2 (@lem1501014 x y h1)). Qed.
Lemma lem1501016 (x : real) (y : real) (h1 : term80 x y) : term63 x y.
Proof. exact (proj1 (@lem1501014 x y h1)). Qed.
Lemma lem1501018 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501019 : term195 = term196.
Proof. exact (@lem1501018 (NUMERAL 0) term48). Qed.
Lemma lem1501020 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501021 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501022 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1501021 h1) (fun h1 : term196 = True => @lem1501020)). Qed.
Lemma lem1501023 : term196 = True.
Proof. exact (EQ_MP (@lem1501022) (@lem1501020)). Qed.
Lemma lem1501024 : term195 = True.
Proof. exact (TRANS (@lem1501019) (@lem1501023)). Qed.
Lemma lem1501025 : True = term195.
Proof. exact (SYM (@lem1501024)). Qed.
Lemma lem1501026 : term195.
Proof. exact (EQ_MP (@lem1501025) (@lem0)). Qed.
Lemma lem1501027 (x : real) (y : real) (h1 : term80 x y) : term198 x y.
Proof. exact (conj (@lem1501026) (@lem1501015 x y h1)). Qed.
Lemma lem1501029 (x : real) (y : real) : term199 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1501030 (x : real) (y : real) : term200 x y.
Proof. exact (@lem1501029 term201 (term54 x y)). Qed.
Lemma lem1501031 (x : real) (y : real) (h1 : term80 x y) : term202 x y.
Proof. exact (@lem1501030 x y (@lem1501027 x y h1)). Qed.
Lemma lem1501032 (x : real) (y : real) : (term203 x y) = (term54 x y).
Proof. exact (@lem1483460 (term54 x y)). Qed.
Lemma lem1501033 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1501034 (x : real) (y : real) : (term204 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1501033) (@lem1501032 x y)). Qed.
Lemma lem1501035 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1501036 (x : real) (y : real) : (term202 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1501034 x y) (@lem1501035)). Qed.
Lemma lem1501037 (x : real) (y : real) (h1 : term80 x y) : term57 x y.
Proof. exact (EQ_MP (@lem1501036 x y) (@lem1501031 x y h1)). Qed.
Lemma lem1501039 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501040 : term195 = term196.
Proof. exact (@lem1501039 (NUMERAL 0) term48). Qed.
Lemma lem1501041 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1501042 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1501043 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem1501042 h1) (fun h1 : term196 = True => @lem1501041)). Qed.
Lemma lem1501044 : term196 = True.
Proof. exact (EQ_MP (@lem1501043) (@lem1501041)). Qed.
Lemma lem1501045 : term195 = True.
Proof. exact (TRANS (@lem1501040) (@lem1501044)). Qed.
Lemma lem1501046 : True = term195.
Proof. exact (SYM (@lem1501045)). Qed.
Lemma lem1501047 : term195.
Proof. exact (EQ_MP (@lem1501046) (@lem0)). Qed.
Lemma lem1501048 (x : real) (y : real) (h1 : term80 x y) : term205 x y.
Proof. exact (conj (@lem1501047) (@lem1501016 x y h1)). Qed.
Lemma lem1501050 (x : real) (y : real) : term206 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1501051 (x : real) (y : real) : term207 x y.
Proof. exact (@lem1501050 term201 (term60 x y)). Qed.
Lemma lem1501052 (x : real) (y : real) (h1 : term80 x y) : term208 x y.
Proof. exact (@lem1501051 x y (@lem1501048 x y h1)). Qed.
Lemma lem1501053 (x : real) (y : real) : (term209 x y) = (term60 x y).
Proof. exact (@lem1483460 (term60 x y)). Qed.
Lemma lem1501054 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501055 (x : real) (y : real) : (term210 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1501054) (@lem1501053 x y)). Qed.
Lemma lem1501056 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1501057 (x : real) (y : real) : (term208 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1501055 x y) (@lem1501056)). Qed.
Lemma lem1501058 (x : real) (y : real) (h1 : term80 x y) : term63 x y.
Proof. exact (EQ_MP (@lem1501057 x y) (@lem1501052 x y h1)). Qed.
Lemma lem1501059 (x : real) (y : real) (h1 : term80 x y) : term80 x y.
Proof. exact (conj (@lem1501058 x y h1) (@lem1501037 x y h1)). Qed.
Lemma lem1501061 (x : real) (y : real) : term211 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1501062 (x : real) (y : real) : term212 x y.
Proof. exact (@lem1501061 (term60 x y) (term54 x y)). Qed.
Lemma lem1501063 (x : real) (y : real) (h1 : term80 x y) : term213 x y.
Proof. exact (@lem1501062 x y (@lem1501059 x y h1)). Qed.
Lemma lem1501064 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483480 x (term40 x) (term40 y) y). Qed.
Lemma lem1501065 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483442 term36 x). Qed.
Lemma lem1501067 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501068 : term47 = term46.
Proof. exact (@lem1501067 term48). Qed.
Lemma lem1501069 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501070 : term49 = term50.
Proof. exact (MK_COMB (@lem1501069) (@lem1501068)). Qed.
Lemma lem1501071 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1501072 (x : real) : (term44 x) = (term51 x).
Proof. exact (MK_COMB (@lem1501070) (@lem1501071 x)). Qed.
Lemma lem1501073 (x : real) : (term43 x) = (term51 x).
Proof. exact (TRANS (@lem1501065 x) (@lem1501072 x)). Qed.
Lemma lem1501074 (x : real) : (term51 x) = term46.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1501075 (x : real) : (term43 x) = term46.
Proof. exact (TRANS (@lem1501073 x) (@lem1501074 x)). Qed.
Lemma lem1501076 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1501077 (x : real) : (term216 x) = term217.
Proof. exact (MK_COMB (@lem1501076) (@lem1501075 x)). Qed.
Lemma lem1501078 (y : real) : (term218 y) = (term44 y).
Proof. exact (@lem1483440 term36 y). Qed.
Lemma lem1501080 (m : nat) : (term45 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1501081 : term47 = term46.
Proof. exact (@lem1501080 term48). Qed.
Lemma lem1501082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1501083 : term49 = term50.
Proof. exact (MK_COMB (@lem1501082) (@lem1501081)). Qed.
Lemma lem1501084 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1501085 (y : real) : (term44 y) = (term51 y).
Proof. exact (MK_COMB (@lem1501083) (@lem1501084 y)). Qed.
Lemma lem1501086 (y : real) : (term218 y) = (term51 y).
Proof. exact (TRANS (@lem1501078 y) (@lem1501085 y)). Qed.
Lemma lem1501087 (y : real) : (term51 y) = term46.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1501088 (y : real) : (term218 y) = term46.
Proof. exact (TRANS (@lem1501086 y) (@lem1501087 y)). Qed.
Lemma lem1501089 (x : real) (y : real) : (term215 x y) = term219.
Proof. exact (MK_COMB (@lem1501077 x) (@lem1501088 y)). Qed.
Lemma lem1501090 (x : real) (y : real) : (term214 x y) = term219.
Proof. exact (TRANS (@lem1501064 x y) (@lem1501089 x y)). Qed.
Lemma lem1501091 : term219 = term46.
Proof. exact (@lem1483448 term46). Qed.
Lemma lem1501092 (x : real) (y : real) : (term214 x y) = term46.
Proof. exact (TRANS (@lem1501090 x y) (@lem1501091)). Qed.
Lemma lem1501093 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1501094 (x : real) (y : real) : (term220 x y) = term221.
Proof. exact (MK_COMB (@lem1501093) (@lem1501092 x y)). Qed.
Lemma lem1501095 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1501096 (x : real) (y : real) : (term213 x y) = term222.
Proof. exact (MK_COMB (@lem1501094 x y) (@lem1501095)). Qed.
Lemma lem1501097 (x : real) (y : real) (h1 : term80 x y) : term222.
Proof. exact (EQ_MP (@lem1501096 x y) (@lem1501063 x y h1)). Qed.
Lemma lem1501099 (n : nat) (m : nat) : (term194 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1501100 : term222 = term223.
Proof. exact (@lem1501099 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1501101 : term223 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1501102 : term222 = False.
Proof. exact (TRANS (@lem1501100) (@lem1501101)). Qed.
Lemma lem1501103 (x : real) (y : real) (h1 : term80 x y) : False.
Proof. exact (EQ_MP (@lem1501102) (@lem1501097 x y h1)). Qed.
Lemma lem1501104 (x : real) (y : real) (h1 : term83 x y) : False.
Proof. exact (or_elim (@lem1500923 x y h1) (fun h0 : term67 x y => @lem1501013 x y h0) (fun h0 : term80 x y => @lem1501103 x y h0)). Qed.
Lemma lem1501106 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1501107 (x : real) (y : real) (h1 : term83 x y) : (term83 x y) = False.
Proof. exact (prop_ext (fun h2 : term83 x y => @lem1501104 x y h1) (fun h2 : False => @lem1501106 x y h1)). Qed.
Lemma lem1501108 (x : real) (y : real) (h1 : term83 x y) : False.
Proof. exact (EQ_MP (@lem1501107 x y h1) (@lem1501106 x y h1)). Qed.
Lemma lem1501109 (x : real) (h1 : term145 x) : term145 x.
Proof. exact (h1). Qed.
Lemma lem1501110 (x : real) (h1 : term145 x) : False.
Proof. exact (ex_elim (@lem1501109 x h1) (fun y : real => fun h0 : term144 x y => @lem1501108 x y h0)). Qed.
Lemma lem1501111 (h1 : term193) : term193.
Proof. exact (h1). Qed.
Lemma lem1501112 (h1 : term193) : False.
Proof. exact (ex_elim (@lem1501111 h1) (fun x : real => fun h0 : term192 x => @lem1501110 x h0)). Qed.
Lemma lem1501113 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1501114 (h1 : term22) : term193.
Proof. exact (EQ_MP (@lem1500913) (@lem1501113 h1)). Qed.
Lemma lem1501115 (h1 : term22) : term193 = False.
Proof. exact (prop_ext (fun h2 : term193 => @lem1501112 h2) (fun h2 : False => @lem1501114 h1)). Qed.
Lemma lem1501116 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1501115 h1) (@lem1501114 h1)). Qed.
Lemma lem1501117 : term224.
Proof. exact (fun h0 : term22 => @lem1501116 h0). Qed.
Lemma lem1501118 : term225.
Proof. exact (@lem1386578 term226). Qed.
Lemma lem1501119 : term226.
Proof. exact (@lem1501118 (@lem1501117)). Qed.
