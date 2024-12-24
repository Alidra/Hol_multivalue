Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_ADDL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
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
Lemma lem1511214 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17646 (term2 x y) (term3 x)). Qed.
Lemma lem1511215 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1511216 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1511215 (term8 x)). Qed.
Lemma lem1511217 (y : real) (x : real) : (term9 x y) = ((term2 x y) = (term3 x)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1511218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1511219 (y : real) (x : real) : (term10 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1511218) (@lem1511217 y x)). Qed.
Lemma lem1511220 (y : real) (x : real) : (term10 x y) = (term1 y x).
Proof. exact (TRANS (@lem1511219 y x) (@lem1511214 y x)). Qed.
Lemma lem1511221 (x : real) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1511220 y x)). Qed.
Lemma lem1511222 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511223 (x : real) : (term7 x) = (term13 x).
Proof. exact (MK_COMB (@lem1511222) (@lem1511221 x)). Qed.
Lemma lem1511224 (x : real) : (term6 x) = (term13 x).
Proof. exact (TRANS (@lem1511216 x) (@lem1511223 x)). Qed.
Lemma lem1511225 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1511226 : term14 = term15.
Proof. exact (@lem1511225 term16). Qed.
Lemma lem1511227 (x : real) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem1511228 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1511229 (x : real) : (term19 x) = (term6 x).
Proof. exact (MK_COMB (@lem1511228) (@lem1511227 x)). Qed.
Lemma lem1511230 (x : real) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem1511229 x) (@lem1511224 x)). Qed.
Lemma lem1511231 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1511230 x)). Qed.
Lemma lem1511232 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511233 : term15 = term22.
Proof. exact (MK_COMB (@lem1511232) (@lem1511231)). Qed.
Lemma lem1511235 : term14 = term22.
Proof. exact (TRANS (@lem1511226) (@lem1511233)). Qed.
Lemma lem1511252 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1511253 (x : real) : (term12 x) = (term12 x).
Proof. exact (fun_ext (fun y : real => @lem1511252 y x)). Qed.
Lemma lem1511254 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511255 (x : real) : (term13 x) = (term13 x).
Proof. exact (MK_COMB (@lem1511254) (@lem1511253 x)). Qed.
Lemma lem1511256 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1511255 x)). Qed.
Lemma lem1511257 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511258 : term22 = term22.
Proof. exact (MK_COMB (@lem1511257) (@lem1511256)). Qed.
Lemma lem1511259 : term14 = term22.
Proof. exact (TRANS (@lem1511235) (@lem1511258)). Qed.
Lemma lem1511260 (x : real) (y : real) : (term2 x y) = (term23 x y).
Proof. exact (@lem1483521 (real_add x y) y). Qed.
Lemma lem1511272 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1483519 (real_add x y) y). Qed.
Lemma lem1511276 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (@lem1483482 x y (term27 y)). Qed.
Lemma lem1511277 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1511279 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511280 : term33 = term32.
Proof. exact (@lem1511279 term34). Qed.
Lemma lem1511281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511282 : term35 = term36.
Proof. exact (MK_COMB (@lem1511281) (@lem1511280)). Qed.
Lemma lem1511283 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1511284 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1511282) (@lem1511283 y)). Qed.
Lemma lem1511285 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1511277 y) (@lem1511284 y)). Qed.
Lemma lem1511286 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1511287 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1511285 y) (@lem1511286 y)). Qed.
Lemma lem1511288 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1511289 (y : real) (x : real) : (term26 x y) = (term38 x).
Proof. exact (MK_COMB (@lem1511288 x) (@lem1511287 y)). Qed.
Lemma lem1511290 (y : real) (x : real) : (term25 x y) = (term38 x).
Proof. exact (TRANS (@lem1511276 x y) (@lem1511289 y x)). Qed.
Lemma lem1511291 (x : real) : (term38 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1511293 (y : real) (x : real) : (term25 x y) = x.
Proof. exact (TRANS (@lem1511290 y x) (@lem1511291 x)). Qed.
Lemma lem1511295 (y : real) (x : real) : (term24 x y) = x.
Proof. exact (TRANS (@lem1511272 x y) (@lem1511293 y x)). Qed.
Lemma lem1511296 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511297 (y : real) (x : real) : (term39 x y) = (real_gt x).
Proof. exact (MK_COMB (@lem1511296) (@lem1511295 y x)). Qed.
Lemma lem1511298 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511299 (y : real) (x : real) : (term23 x y) = (term40 x).
Proof. exact (MK_COMB (@lem1511297 y x) (@lem1511298)). Qed.
Lemma lem1511300 (y : real) (x : real) : (term2 x y) = (term40 x).
Proof. exact (TRANS (@lem1511260 x y) (@lem1511299 y x)). Qed.
Lemma lem1511301 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483531 term32 x). Qed.
Lemma lem1511307 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483519 term32 x). Qed.
Lemma lem1511312 (x : real) : (term44 x) = (term27 x).
Proof. exact (@lem1483448 (term27 x)). Qed.
Lemma lem1511314 (x : real) : (term43 x) = (term27 x).
Proof. exact (TRANS (@lem1511307 x) (@lem1511312 x)). Qed.
Lemma lem1511315 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1511316 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1511315) (@lem1511314 x)). Qed.
Lemma lem1511317 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511318 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1511316 x) (@lem1511317)). Qed.
Lemma lem1511319 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1511301 x) (@lem1511318 x)). Qed.
Lemma lem1511320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1511321 (y : real) (x : real) : (term48 x y) = (term49 x).
Proof. exact (MK_COMB (@lem1511320) (@lem1511300 y x)). Qed.
Lemma lem1511322 (y : real) (x : real) : (term50 y x) = (term51 x).
Proof. exact (MK_COMB (@lem1511321 y x) (@lem1511319 x)). Qed.
Lemma lem1511323 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem1483531 y (real_add x y)). Qed.
Lemma lem1511335 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (@lem1483519 y (real_add x y)). Qed.
Lemma lem1511342 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (@lem1483508 x term30 y). Qed.
Lemma lem1511343 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1511344 (x : real) (y : real) : (term55 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1511343 y) (@lem1511342 x y)). Qed.
Lemma lem1511345 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1483484 (term27 x) y (term27 y)). Qed.
Lemma lem1511346 (y : real) : (term28 y) = (term29 y).
Proof. exact (@lem1483442 term30 y). Qed.
Lemma lem1511348 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511349 : term33 = term32.
Proof. exact (@lem1511348 term34). Qed.
Lemma lem1511350 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511351 : term35 = term36.
Proof. exact (MK_COMB (@lem1511350) (@lem1511349)). Qed.
Lemma lem1511352 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1511353 (y : real) : (term29 y) = (term37 y).
Proof. exact (MK_COMB (@lem1511351) (@lem1511352 y)). Qed.
Lemma lem1511354 (y : real) : (term28 y) = (term37 y).
Proof. exact (TRANS (@lem1511346 y) (@lem1511353 y)). Qed.
Lemma lem1511355 (y : real) : (term37 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1511356 (y : real) : (term28 y) = term32.
Proof. exact (TRANS (@lem1511354 y) (@lem1511355 y)). Qed.
Lemma lem1511357 (x : real) : (term60 x) = (term60 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1511358 (y : real) (x : real) : (term59 x y) = (term61 x).
Proof. exact (MK_COMB (@lem1511357 x) (@lem1511356 y)). Qed.
Lemma lem1511359 (y : real) (x : real) : (term58 x y) = (term61 x).
Proof. exact (TRANS (@lem1511345 x y) (@lem1511358 y x)). Qed.
Lemma lem1511360 (x : real) : (term61 x) = (term27 x).
Proof. exact (@lem1483450 (term27 x)). Qed.
Lemma lem1511361 (y : real) (x : real) : (term58 x y) = (term27 x).
Proof. exact (TRANS (@lem1511359 y x) (@lem1511360 x)). Qed.
Lemma lem1511362 (y : real) (x : real) : (term55 x y) = (term27 x).
Proof. exact (TRANS (@lem1511344 x y) (@lem1511361 y x)). Qed.
Lemma lem1511364 (y : real) (x : real) : (term54 x y) = (term27 x).
Proof. exact (TRANS (@lem1511335 x y) (@lem1511362 y x)). Qed.
Lemma lem1511365 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1511366 (y : real) (x : real) : (term62 x y) = (term46 x).
Proof. exact (MK_COMB (@lem1511365) (@lem1511364 y x)). Qed.
Lemma lem1511367 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511368 (y : real) (x : real) : (term53 x y) = (term47 x).
Proof. exact (MK_COMB (@lem1511366 y x) (@lem1511367)). Qed.
Lemma lem1511369 (y : real) (x : real) : (term52 x y) = (term47 x).
Proof. exact (TRANS (@lem1511323 x y) (@lem1511368 y x)). Qed.
Lemma lem1511370 (x : real) : (term3 x) = (term63 x).
Proof. exact (@lem1483521 x term32). Qed.
Lemma lem1511376 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1483519 x term32). Qed.
Lemma lem1511378 (x : nat) : (term66 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1511379 : term67 = term32.
Proof. exact (@lem1511378 term34). Qed.
Lemma lem1511380 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1511381 (x : real) : (term65 x) = (term38 x).
Proof. exact (MK_COMB (@lem1511380 x) (@lem1511379)). Qed.
Lemma lem1511382 (x : real) : (term38 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1511383 (x : real) : (term65 x) = x.
Proof. exact (TRANS (@lem1511381 x) (@lem1511382 x)). Qed.
Lemma lem1511385 (x : real) : (term64 x) = x.
Proof. exact (TRANS (@lem1511376 x) (@lem1511383 x)). Qed.
Lemma lem1511386 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511387 (x : real) : (term68 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1511386) (@lem1511385 x)). Qed.
Lemma lem1511388 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511389 (x : real) : (term63 x) = (term40 x).
Proof. exact (MK_COMB (@lem1511387 x) (@lem1511388)). Qed.
Lemma lem1511390 (x : real) : (term3 x) = (term40 x).
Proof. exact (TRANS (@lem1511370 x) (@lem1511389 x)). Qed.
Lemma lem1511391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1511392 (y : real) (x : real) : (term69 x y) = (term70 x).
Proof. exact (MK_COMB (@lem1511391) (@lem1511369 y x)). Qed.
Lemma lem1511393 (y : real) (x : real) : (term71 y x) = (term72 x).
Proof. exact (MK_COMB (@lem1511392 y x) (@lem1511390 x)). Qed.
Lemma lem1511394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511395 (y : real) (x : real) : (term73 y x) = (term74 x).
Proof. exact (MK_COMB (@lem1511394) (@lem1511322 y x)). Qed.
Lemma lem1511396 (y : real) (x : real) : (term1 y x) = (term75 x).
Proof. exact (MK_COMB (@lem1511395 y x) (@lem1511393 y x)). Qed.
Lemma lem1511397 (x : real) : (term12 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1511396 y x)). Qed.
Lemma lem1511398 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511399 (x : real) : (term13 x) = (term77 x).
Proof. exact (MK_COMB (@lem1511398) (@lem1511397 x)). Qed.
Lemma lem1511400 : term21 = term78.
Proof. exact (fun_ext (fun x : real => @lem1511399 x)). Qed.
Lemma lem1511401 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511402 : term22 = term79.
Proof. exact (MK_COMB (@lem1511401) (@lem1511400)). Qed.
Lemma lem1511403 : term14 = term79.
Proof. exact (TRANS (@lem1511259) (@lem1511402)). Qed.
Lemma lem1511409 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1511410 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1511409 real P Q). Qed.
Lemma lem1511411 (x : real) : (term84 x) = (term85 x).
Proof. exact (@lem1511410 (term86 x) (term87 x)). Qed.
Lemma lem1511412 (y : real) (x : real) : (term88 x y) = (term51 x).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1511413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511414 (y : real) (x : real) : (term89 x y) = (term74 x).
Proof. exact (MK_COMB (@lem1511413) (@lem1511412 y x)). Qed.
Lemma lem1511415 (y : real) (x : real) : (term90 x y) = (term72 x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1511416 (y : real) (x : real) : (term91 x y) = (term75 x).
Proof. exact (MK_COMB (@lem1511414 y x) (@lem1511415 y x)). Qed.
Lemma lem1511417 (x : real) : (term92 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1511416 y x)). Qed.
Lemma lem1511418 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511419 (x : real) : (term84 x) = (term77 x).
Proof. exact (MK_COMB (@lem1511418) (@lem1511417 x)). Qed.
Lemma lem1511420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1511421 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1511420) (@lem1511419 x)). Qed.
Lemma lem1511422 (y : real) (x : real) : (term88 x y) = (term51 x).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1511423 (x : real) : (term95 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1511422 y x)). Qed.
Lemma lem1511424 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511425 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1511424) (@lem1511423 x)). Qed.
Lemma lem1511426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511427 (x : real) : (term98 x) = (term99 x).
Proof. exact (MK_COMB (@lem1511426) (@lem1511425 x)). Qed.
Lemma lem1511428 (y : real) (x : real) : (term90 x y) = (term72 x).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1511429 (x : real) : (term100 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1511428 y x)). Qed.
Lemma lem1511430 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511431 (x : real) : (term101 x) = (term102 x).
Proof. exact (MK_COMB (@lem1511430) (@lem1511429 x)). Qed.
Lemma lem1511432 (x : real) : (term85 x) = (term103 x).
Proof. exact (MK_COMB (@lem1511427 x) (@lem1511431 x)). Qed.
Lemma lem1511433 (x : real) : ((term84 x) = (term85 x)) = ((term77 x) = (term103 x)).
Proof. exact (MK_COMB (@lem1511421 x) (@lem1511432 x)). Qed.
Lemma lem1511434 (x : real) : (term77 x) = (term103 x).
Proof. exact (EQ_MP (@lem1511433 x) (@lem1511411 x)). Qed.
Lemma lem1511436 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1511437 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1511436 real P Q). Qed.
Lemma lem1511438 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1511437 (term40 x) (term110 x)). Qed.
Lemma lem1511439 (y : real) (x : real) : (term111 x y) = (term47 x).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1511440 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1511441 (y : real) (x : real) : (term112 x y) = (term51 x).
Proof. exact (MK_COMB (@lem1511440 x) (@lem1511439 y x)). Qed.
Lemma lem1511442 (x : real) : (term113 x) = (term86 x).
Proof. exact (fun_ext (fun y : real => @lem1511441 y x)). Qed.
Lemma lem1511443 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511444 (x : real) : (term108 x) = (term97 x).
Proof. exact (MK_COMB (@lem1511443) (@lem1511442 x)). Qed.
Lemma lem1511445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1511446 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1511445) (@lem1511444 x)). Qed.
Lemma lem1511447 (y : real) (x : real) : (term111 x y) = (term47 x).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1511448 (x : real) : (term116 x) = (term110 x).
Proof. exact (fun_ext (fun y : real => @lem1511447 y x)). Qed.
Lemma lem1511449 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511450 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1511449) (@lem1511448 x)). Qed.
Lemma lem1511451 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1511452 (x : real) : (term109 x) = (term119 x).
Proof. exact (MK_COMB (@lem1511451 x) (@lem1511450 x)). Qed.
Lemma lem1511453 (x : real) : ((term108 x) = (term109 x)) = ((term97 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1511446 x) (@lem1511452 x)). Qed.
Lemma lem1511454 (x : real) : (term97 x) = (term119 x).
Proof. exact (EQ_MP (@lem1511453 x) (@lem1511438 x)). Qed.
Lemma lem1511456 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1511457 (t : Prop) : (term121 t) = t.
Proof. exact (@lem1511456 real t). Qed.
Lemma lem1511458 (x : real) : (term118 x) = (term47 x).
Proof. exact (@lem1511457 (term47 x)). Qed.
Lemma lem1511459 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1511460 (x : real) : (term119 x) = (term51 x).
Proof. exact (MK_COMB (@lem1511459 x) (@lem1511458 x)). Qed.
Lemma lem1511461 (x : real) : (term97 x) = (term51 x).
Proof. exact (TRANS (@lem1511454 x) (@lem1511460 x)). Qed.
Lemma lem1511462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511463 (x : real) : (term99 x) = (term74 x).
Proof. exact (MK_COMB (@lem1511462) (@lem1511461 x)). Qed.
Lemma lem1511465 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1511466 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term107 P Q).
Proof. exact (@lem1511465 real P Q). Qed.
Lemma lem1511467 (x : real) : (term122 x) = (term123 x).
Proof. exact (@lem1511466 (term47 x) (term124 x)). Qed.
Lemma lem1511468 (y : real) (x : real) : (term125 x y) = (term40 x).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1511469 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1511470 (y : real) (x : real) : (term126 x y) = (term72 x).
Proof. exact (MK_COMB (@lem1511469 x) (@lem1511468 y x)). Qed.
Lemma lem1511471 (x : real) : (term127 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem1511470 y x)). Qed.
Lemma lem1511472 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511473 (x : real) : (term122 x) = (term102 x).
Proof. exact (MK_COMB (@lem1511472) (@lem1511471 x)). Qed.
Lemma lem1511474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1511475 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1511474) (@lem1511473 x)). Qed.
Lemma lem1511476 (y : real) (x : real) : (term125 x y) = (term40 x).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1511477 (x : real) : (term130 x) = (term124 x).
Proof. exact (fun_ext (fun y : real => @lem1511476 y x)). Qed.
Lemma lem1511478 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511479 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem1511478) (@lem1511477 x)). Qed.
Lemma lem1511480 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1511481 (x : real) : (term123 x) = (term133 x).
Proof. exact (MK_COMB (@lem1511480 x) (@lem1511479 x)). Qed.
Lemma lem1511482 (x : real) : ((term122 x) = (term123 x)) = ((term102 x) = (term133 x)).
Proof. exact (MK_COMB (@lem1511475 x) (@lem1511481 x)). Qed.
Lemma lem1511483 (x : real) : (term102 x) = (term133 x).
Proof. exact (EQ_MP (@lem1511482 x) (@lem1511467 x)). Qed.
Lemma lem1511485 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1511486 (t : Prop) : (term121 t) = t.
Proof. exact (@lem1511485 real t). Qed.
Lemma lem1511487 (x : real) : (term132 x) = (term40 x).
Proof. exact (@lem1511486 (term40 x)). Qed.
Lemma lem1511488 (x : real) : (term70 x) = (term70 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1511489 (x : real) : (term133 x) = (term72 x).
Proof. exact (MK_COMB (@lem1511488 x) (@lem1511487 x)). Qed.
Lemma lem1511490 (x : real) : (term102 x) = (term72 x).
Proof. exact (TRANS (@lem1511483 x) (@lem1511489 x)). Qed.
Lemma lem1511491 (x : real) : (term103 x) = (term75 x).
Proof. exact (MK_COMB (@lem1511463 x) (@lem1511490 x)). Qed.
Lemma lem1511492 (x : real) : (term77 x) = (term75 x).
Proof. exact (TRANS (@lem1511434 x) (@lem1511491 x)). Qed.
Lemma lem1511493 : term78 = term134.
Proof. exact (fun_ext (fun x : real => @lem1511492 x)). Qed.
Lemma lem1511494 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511495 : term79 = term135.
Proof. exact (MK_COMB (@lem1511494) (@lem1511493)). Qed.
Lemma lem1511497 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1511498 (P : real -> Prop) (Q : real -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem1511497 real P Q). Qed.
Lemma lem1511499 : term136 = term137.
Proof. exact (@lem1511498 term138 term139). Qed.
Lemma lem1511500 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1511501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511502 (x : real) : (term141 x) = (term74 x).
Proof. exact (MK_COMB (@lem1511501) (@lem1511500 x)). Qed.
Lemma lem1511503 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1511504 (x : real) : (term143 x) = (term75 x).
Proof. exact (MK_COMB (@lem1511502 x) (@lem1511503 x)). Qed.
Lemma lem1511505 : term144 = term134.
Proof. exact (fun_ext (fun x : real => @lem1511504 x)). Qed.
Lemma lem1511506 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511507 : term136 = term135.
Proof. exact (MK_COMB (@lem1511506) (@lem1511505)). Qed.
Lemma lem1511508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1511509 : term145 = term146.
Proof. exact (MK_COMB (@lem1511508) (@lem1511507)). Qed.
Lemma lem1511510 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1511511 : term147 = term138.
Proof. exact (fun_ext (fun x : real => @lem1511510 x)). Qed.
Lemma lem1511512 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511513 : term148 = term149.
Proof. exact (MK_COMB (@lem1511512) (@lem1511511)). Qed.
Lemma lem1511514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511515 : term150 = term151.
Proof. exact (MK_COMB (@lem1511514) (@lem1511513)). Qed.
Lemma lem1511516 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1511517 : term152 = term139.
Proof. exact (fun_ext (fun x : real => @lem1511516 x)). Qed.
Lemma lem1511518 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511519 : term153 = term154.
Proof. exact (MK_COMB (@lem1511518) (@lem1511517)). Qed.
Lemma lem1511520 : term137 = term155.
Proof. exact (MK_COMB (@lem1511515) (@lem1511519)). Qed.
Lemma lem1511521 : (term136 = term137) = (term135 = term155).
Proof. exact (MK_COMB (@lem1511509) (@lem1511520)). Qed.
Lemma lem1511522 : term135 = term155.
Proof. exact (EQ_MP (@lem1511521) (@lem1511499)). Qed.
Lemma lem1511619 : term79 = term155.
Proof. exact (TRANS (@lem1511495) (@lem1511522)). Qed.
Lemma lem1511621 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1511622 (P : real -> Prop) (Q : real -> Prop) : (term83 P Q) = (term82 P Q).
Proof. exact (@lem1511621 real P Q). Qed.
Lemma lem1511623 : term137 = term136.
Proof. exact (@lem1511622 term138 term139). Qed.
Lemma lem1511624 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1511625 : term147 = term138.
Proof. exact (fun_ext (fun x : real => @lem1511624 x)). Qed.
Lemma lem1511626 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511627 : term148 = term149.
Proof. exact (MK_COMB (@lem1511626) (@lem1511625)). Qed.
Lemma lem1511628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511629 : term150 = term151.
Proof. exact (MK_COMB (@lem1511628) (@lem1511627)). Qed.
Lemma lem1511630 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1511631 : term152 = term139.
Proof. exact (fun_ext (fun x : real => @lem1511630 x)). Qed.
Lemma lem1511632 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511633 : term153 = term154.
Proof. exact (MK_COMB (@lem1511632) (@lem1511631)). Qed.
Lemma lem1511634 : term137 = term155.
Proof. exact (MK_COMB (@lem1511629) (@lem1511633)). Qed.
Lemma lem1511635 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1511636 : term156 = term157.
Proof. exact (MK_COMB (@lem1511635) (@lem1511634)). Qed.
Lemma lem1511637 (x : real) : (term140 x) = (term51 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1511638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1511639 (x : real) : (term141 x) = (term74 x).
Proof. exact (MK_COMB (@lem1511638) (@lem1511637 x)). Qed.
Lemma lem1511640 (x : real) : (term142 x) = (term72 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1511641 (x : real) : (term143 x) = (term75 x).
Proof. exact (MK_COMB (@lem1511639 x) (@lem1511640 x)). Qed.
Lemma lem1511642 : term144 = term134.
Proof. exact (fun_ext (fun x : real => @lem1511641 x)). Qed.
Lemma lem1511643 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511644 : term136 = term135.
Proof. exact (MK_COMB (@lem1511643) (@lem1511642)). Qed.
Lemma lem1511645 : (term137 = term136) = (term155 = term135).
Proof. exact (MK_COMB (@lem1511636) (@lem1511644)). Qed.
Lemma lem1511646 : term155 = term135.
Proof. exact (EQ_MP (@lem1511645) (@lem1511623)). Qed.
Lemma lem1511647 : term79 = term135.
Proof. exact (TRANS (@lem1511619) (@lem1511646)). Qed.
Lemma lem1511650 : term14 = term135.
Proof. exact (TRANS (@lem1511403) (@lem1511647)). Qed.
Lemma lem1511667 (x : real) : (term75 x) = (term75 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1511668 : term134 = term134.
Proof. exact (fun_ext (fun x : real => @lem1511667 x)). Qed.
Lemma lem1511669 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1511670 : term135 = term135.
Proof. exact (MK_COMB (@lem1511669) (@lem1511668)). Qed.
Lemma lem1511671 : term14 = term135.
Proof. exact (TRANS (@lem1511650) (@lem1511670)). Qed.
Lemma lem1511681 (x : real) (h1 : term75 x) : term75 x.
Proof. exact (h1). Qed.
Lemma lem1511682 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1511683 (x : real) (h1 : term51 x) : term47 x.
Proof. exact (proj2 (@lem1511682 x h1)). Qed.
Lemma lem1511684 (x : real) (h1 : term51 x) : term40 x.
Proof. exact (proj1 (@lem1511682 x h1)). Qed.
Lemma lem1511686 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511687 : term159 = term160.
Proof. exact (@lem1511686 (NUMERAL 0) term34). Qed.
Lemma lem1511688 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511689 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511690 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1511689 h1) (fun h1 : term160 = True => @lem1511688)). Qed.
Lemma lem1511691 : term160 = True.
Proof. exact (EQ_MP (@lem1511690) (@lem1511688)). Qed.
Lemma lem1511692 : term159 = True.
Proof. exact (TRANS (@lem1511687) (@lem1511691)). Qed.
Lemma lem1511693 : True = term159.
Proof. exact (SYM (@lem1511692)). Qed.
Lemma lem1511694 : term159.
Proof. exact (EQ_MP (@lem1511693) (@lem0)). Qed.
Lemma lem1511695 (x : real) (h1 : term51 x) : term162 x.
Proof. exact (conj (@lem1511694) (@lem1511683 x h1)). Qed.
Lemma lem1511697 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1511698 (x : real) : term164 x.
Proof. exact (@lem1511697 term165 (term27 x)). Qed.
Lemma lem1511699 (x : real) (h1 : term51 x) : term166 x.
Proof. exact (@lem1511698 x (@lem1511695 x h1)). Qed.
Lemma lem1511700 (x : real) : (term167 x) = (term27 x).
Proof. exact (@lem1483460 (term27 x)). Qed.
Lemma lem1511701 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1511702 (x : real) : (term168 x) = (term46 x).
Proof. exact (MK_COMB (@lem1511701) (@lem1511700 x)). Qed.
Lemma lem1511703 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511704 (x : real) : (term166 x) = (term47 x).
Proof. exact (MK_COMB (@lem1511702 x) (@lem1511703)). Qed.
Lemma lem1511705 (x : real) (h1 : term51 x) : term47 x.
Proof. exact (EQ_MP (@lem1511704 x) (@lem1511699 x h1)). Qed.
Lemma lem1511707 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511708 : term159 = term160.
Proof. exact (@lem1511707 (NUMERAL 0) term34). Qed.
Lemma lem1511709 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511710 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511711 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1511710 h1) (fun h1 : term160 = True => @lem1511709)). Qed.
Lemma lem1511712 : term160 = True.
Proof. exact (EQ_MP (@lem1511711) (@lem1511709)). Qed.
Lemma lem1511713 : term159 = True.
Proof. exact (TRANS (@lem1511708) (@lem1511712)). Qed.
Lemma lem1511714 : True = term159.
Proof. exact (SYM (@lem1511713)). Qed.
Lemma lem1511715 : term159.
Proof. exact (EQ_MP (@lem1511714) (@lem0)). Qed.
Lemma lem1511716 (x : real) (h1 : term51 x) : term169 x.
Proof. exact (conj (@lem1511715) (@lem1511684 x h1)). Qed.
Lemma lem1511718 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1511719 (x : real) : term171 x.
Proof. exact (@lem1511718 term165 x). Qed.
Lemma lem1511720 (x : real) (h1 : term51 x) : term172 x.
Proof. exact (@lem1511719 x (@lem1511716 x h1)). Qed.
Lemma lem1511721 (x : real) : (term173 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1511722 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511723 (x : real) : (term174 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1511722) (@lem1511721 x)). Qed.
Lemma lem1511724 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511725 (x : real) : (term172 x) = (term40 x).
Proof. exact (MK_COMB (@lem1511723 x) (@lem1511724)). Qed.
Lemma lem1511726 (x : real) (h1 : term51 x) : term40 x.
Proof. exact (EQ_MP (@lem1511725 x) (@lem1511720 x h1)). Qed.
Lemma lem1511727 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (conj (@lem1511726 x h1) (@lem1511705 x h1)). Qed.
Lemma lem1511729 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1511730 (x : real) : term176 x.
Proof. exact (@lem1511729 x (term27 x)). Qed.
Lemma lem1511731 (x : real) (h1 : term51 x) : term177 x.
Proof. exact (@lem1511730 x (@lem1511727 x h1)). Qed.
Lemma lem1511732 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1511734 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511735 : term33 = term32.
Proof. exact (@lem1511734 term34). Qed.
Lemma lem1511736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511737 : term35 = term36.
Proof. exact (MK_COMB (@lem1511736) (@lem1511735)). Qed.
Lemma lem1511738 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1511739 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1511737) (@lem1511738 x)). Qed.
Lemma lem1511740 (x : real) : (term28 x) = (term37 x).
Proof. exact (TRANS (@lem1511732 x) (@lem1511739 x)). Qed.
Lemma lem1511741 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1511742 (x : real) : (term28 x) = term32.
Proof. exact (TRANS (@lem1511740 x) (@lem1511741 x)). Qed.
Lemma lem1511743 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511744 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1511743) (@lem1511742 x)). Qed.
Lemma lem1511745 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511746 (x : real) : (term177 x) = term180.
Proof. exact (MK_COMB (@lem1511744 x) (@lem1511745)). Qed.
Lemma lem1511747 (x : real) (h1 : term51 x) : term180.
Proof. exact (EQ_MP (@lem1511746 x) (@lem1511731 x h1)). Qed.
Lemma lem1511749 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511750 : term180 = term181.
Proof. exact (@lem1511749 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1511751 : term181 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1511752 : term180 = False.
Proof. exact (TRANS (@lem1511750) (@lem1511751)). Qed.
Lemma lem1511753 (x : real) (h1 : term51 x) : False.
Proof. exact (EQ_MP (@lem1511752) (@lem1511747 x h1)). Qed.
Lemma lem1511754 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1511755 (x : real) (h1 : term72 x) : term40 x.
Proof. exact (proj2 (@lem1511754 x h1)). Qed.
Lemma lem1511756 (x : real) (h1 : term72 x) : term47 x.
Proof. exact (proj1 (@lem1511754 x h1)). Qed.
Lemma lem1511758 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511759 : term159 = term160.
Proof. exact (@lem1511758 (NUMERAL 0) term34). Qed.
Lemma lem1511760 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511761 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511762 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1511761 h1) (fun h1 : term160 = True => @lem1511760)). Qed.
Lemma lem1511763 : term160 = True.
Proof. exact (EQ_MP (@lem1511762) (@lem1511760)). Qed.
Lemma lem1511764 : term159 = True.
Proof. exact (TRANS (@lem1511759) (@lem1511763)). Qed.
Lemma lem1511765 : True = term159.
Proof. exact (SYM (@lem1511764)). Qed.
Lemma lem1511766 : term159.
Proof. exact (EQ_MP (@lem1511765) (@lem0)). Qed.
Lemma lem1511767 (x : real) (h1 : term72 x) : term162 x.
Proof. exact (conj (@lem1511766) (@lem1511756 x h1)). Qed.
Lemma lem1511769 (x : real) (y : real) : term163 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1511770 (x : real) : term164 x.
Proof. exact (@lem1511769 term165 (term27 x)). Qed.
Lemma lem1511771 (x : real) (h1 : term72 x) : term166 x.
Proof. exact (@lem1511770 x (@lem1511767 x h1)). Qed.
Lemma lem1511772 (x : real) : (term167 x) = (term27 x).
Proof. exact (@lem1483460 (term27 x)). Qed.
Lemma lem1511773 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1511774 (x : real) : (term168 x) = (term46 x).
Proof. exact (MK_COMB (@lem1511773) (@lem1511772 x)). Qed.
Lemma lem1511775 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511776 (x : real) : (term166 x) = (term47 x).
Proof. exact (MK_COMB (@lem1511774 x) (@lem1511775)). Qed.
Lemma lem1511777 (x : real) (h1 : term72 x) : term47 x.
Proof. exact (EQ_MP (@lem1511776 x) (@lem1511771 x h1)). Qed.
Lemma lem1511779 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511780 : term159 = term160.
Proof. exact (@lem1511779 (NUMERAL 0) term34). Qed.
Lemma lem1511781 : term161 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1511782 (h1 : term161 = (BIT1 0)) : term160 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1511783 : (term161 = (BIT1 0)) = (term160 = True).
Proof. exact (prop_ext (fun h1 : term161 = (BIT1 0) => @lem1511782 h1) (fun h1 : term160 = True => @lem1511781)). Qed.
Lemma lem1511784 : term160 = True.
Proof. exact (EQ_MP (@lem1511783) (@lem1511781)). Qed.
Lemma lem1511785 : term159 = True.
Proof. exact (TRANS (@lem1511780) (@lem1511784)). Qed.
Lemma lem1511786 : True = term159.
Proof. exact (SYM (@lem1511785)). Qed.
Lemma lem1511787 : term159.
Proof. exact (EQ_MP (@lem1511786) (@lem0)). Qed.
Lemma lem1511788 (x : real) (h1 : term72 x) : term169 x.
Proof. exact (conj (@lem1511787) (@lem1511755 x h1)). Qed.
Lemma lem1511790 (x : real) (y : real) : term170 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1511791 (x : real) : term171 x.
Proof. exact (@lem1511790 term165 x). Qed.
Lemma lem1511792 (x : real) (h1 : term72 x) : term172 x.
Proof. exact (@lem1511791 x (@lem1511788 x h1)). Qed.
Lemma lem1511793 (x : real) : (term173 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1511794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511795 (x : real) : (term174 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1511794) (@lem1511793 x)). Qed.
Lemma lem1511796 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511797 (x : real) : (term172 x) = (term40 x).
Proof. exact (MK_COMB (@lem1511795 x) (@lem1511796)). Qed.
Lemma lem1511798 (x : real) (h1 : term72 x) : term40 x.
Proof. exact (EQ_MP (@lem1511797 x) (@lem1511792 x h1)). Qed.
Lemma lem1511799 (x : real) (h1 : term72 x) : term51 x.
Proof. exact (conj (@lem1511798 x h1) (@lem1511777 x h1)). Qed.
Lemma lem1511801 (x : real) (y : real) : term175 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1511802 (x : real) : term176 x.
Proof. exact (@lem1511801 x (term27 x)). Qed.
Lemma lem1511803 (x : real) (h1 : term72 x) : term177 x.
Proof. exact (@lem1511802 x (@lem1511799 x h1)). Qed.
Lemma lem1511804 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem1483442 term30 x). Qed.
Lemma lem1511806 (m : nat) : (term31 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1511807 : term33 = term32.
Proof. exact (@lem1511806 term34). Qed.
Lemma lem1511808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1511809 : term35 = term36.
Proof. exact (MK_COMB (@lem1511808) (@lem1511807)). Qed.
Lemma lem1511810 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1511811 (x : real) : (term29 x) = (term37 x).
Proof. exact (MK_COMB (@lem1511809) (@lem1511810 x)). Qed.
Lemma lem1511812 (x : real) : (term28 x) = (term37 x).
Proof. exact (TRANS (@lem1511804 x) (@lem1511811 x)). Qed.
Lemma lem1511813 (x : real) : (term37 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1511814 (x : real) : (term28 x) = term32.
Proof. exact (TRANS (@lem1511812 x) (@lem1511813 x)). Qed.
Lemma lem1511815 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1511816 (x : real) : (term178 x) = term179.
Proof. exact (MK_COMB (@lem1511815) (@lem1511814 x)). Qed.
Lemma lem1511817 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1511818 (x : real) : (term177 x) = term180.
Proof. exact (MK_COMB (@lem1511816 x) (@lem1511817)). Qed.
Lemma lem1511819 (x : real) (h1 : term72 x) : term180.
Proof. exact (EQ_MP (@lem1511818 x) (@lem1511803 x h1)). Qed.
Lemma lem1511821 (n : nat) (m : nat) : (term158 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1511822 : term180 = term181.
Proof. exact (@lem1511821 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1511823 : term181 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1511824 : term180 = False.
Proof. exact (TRANS (@lem1511822) (@lem1511823)). Qed.
Lemma lem1511825 (x : real) (h1 : term72 x) : False.
Proof. exact (EQ_MP (@lem1511824) (@lem1511819 x h1)). Qed.
Lemma lem1511826 (x : real) (h1 : term75 x) : False.
Proof. exact (or_elim (@lem1511681 x h1) (fun h0 : term51 x => @lem1511753 x h0) (fun h0 : term72 x => @lem1511825 x h0)). Qed.
Lemma lem1511828 (x : real) (h1 : term75 x) : term75 x.
Proof. exact (h1). Qed.
Lemma lem1511829 (x : real) (h1 : term75 x) : (term75 x) = False.
Proof. exact (prop_ext (fun h2 : term75 x => @lem1511826 x h1) (fun h2 : False => @lem1511828 x h1)). Qed.
Lemma lem1511830 (x : real) (h1 : term75 x) : False.
Proof. exact (EQ_MP (@lem1511829 x h1) (@lem1511828 x h1)). Qed.
Lemma lem1511831 (h1 : term135) : term135.
Proof. exact (h1). Qed.
Lemma lem1511832 (h1 : term135) : False.
Proof. exact (ex_elim (@lem1511831 h1) (fun x : real => fun h0 : term134 x => @lem1511830 x h0)). Qed.
Lemma lem1511833 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1511834 (h1 : term14) : term135.
Proof. exact (EQ_MP (@lem1511671) (@lem1511833 h1)). Qed.
Lemma lem1511835 (h1 : term14) : term135 = False.
Proof. exact (prop_ext (fun h2 : term135 => @lem1511832 h2) (fun h2 : False => @lem1511834 h1)). Qed.
Lemma lem1511836 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1511835 h1) (@lem1511834 h1)). Qed.
Lemma lem1511837 : term182.
Proof. exact (fun h0 : term14 => @lem1511836 h0). Qed.
Lemma lem1511838 : term183.
Proof. exact (@lem1386578 term184). Qed.
Lemma lem1511839 : term184.
Proof. exact (@lem1511838 (@lem1511837)). Qed.
