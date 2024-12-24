Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_LT0_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1496236 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1496237 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1496238 : term6 = term7.
Proof. exact (@lem1496237 term8). Qed.
Lemma lem1496239 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1496240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1496241 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1496240) (@lem1496239 x)). Qed.
Lemma lem1496242 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1496241 x) (@lem1496236 x)). Qed.
Lemma lem1496243 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1496242 x)). Qed.
Lemma lem1496244 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496245 : term7 = term13.
Proof. exact (MK_COMB (@lem1496244) (@lem1496243)). Qed.
Lemma lem1496247 : term6 = term13.
Proof. exact (TRANS (@lem1496238) (@lem1496245)). Qed.
Lemma lem1496264 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1496265 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1496264 x)). Qed.
Lemma lem1496266 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496267 : term13 = term13.
Proof. exact (MK_COMB (@lem1496266) (@lem1496265)). Qed.
Lemma lem1496268 : term6 = term13.
Proof. exact (TRANS (@lem1496247) (@lem1496267)). Qed.
Lemma lem1496269 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483521 term15 (real_neg x)). Qed.
Lemma lem1496276 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1496279 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1496280 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1496279) (@lem1496276 x)). Qed.
Lemma lem1496281 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 term15 (term16 x)). Qed.
Lemma lem1496282 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1483476 term23 term23 x). Qed.
Lemma lem1496284 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1496285 : term26 = term27.
Proof. exact (@lem1496284 term28 term28). Qed.
Lemma lem1496286 : (term29 = (BIT1 0)) = (term30 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1496287 : term30 = term28.
Proof. exact (EQ_MP (@lem1496286) (@lem940073)). Qed.
Lemma lem1496288 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1496289 : term27 = term31.
Proof. exact (MK_COMB (@lem1496288) (@lem1496287)). Qed.
Lemma lem1496290 : term26 = term31.
Proof. exact (TRANS (@lem1496285) (@lem1496289)). Qed.
Lemma lem1496291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1496292 : term32 = term33.
Proof. exact (MK_COMB (@lem1496291) (@lem1496290)). Qed.
Lemma lem1496293 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1496294 (x : real) : (term22 x) = (term34 x).
Proof. exact (MK_COMB (@lem1496292) (@lem1496293 x)). Qed.
Lemma lem1496295 (x : real) : (term21 x) = (term34 x).
Proof. exact (TRANS (@lem1496282 x) (@lem1496294 x)). Qed.
Lemma lem1496296 (x : real) : (term34 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1496297 (x : real) : (term21 x) = x.
Proof. exact (TRANS (@lem1496295 x) (@lem1496296 x)). Qed.
Lemma lem1496298 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1496299 (x : real) : (term20 x) = (term36 x).
Proof. exact (MK_COMB (@lem1496298) (@lem1496297 x)). Qed.
Lemma lem1496300 (x : real) : (term36 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1496301 (x : real) : (term20 x) = x.
Proof. exact (TRANS (@lem1496299 x) (@lem1496300 x)). Qed.
Lemma lem1496302 (x : real) : (term19 x) = x.
Proof. exact (TRANS (@lem1496281 x) (@lem1496301 x)). Qed.
Lemma lem1496303 (x : real) : (term18 x) = x.
Proof. exact (TRANS (@lem1496280 x) (@lem1496302 x)). Qed.
Lemma lem1496304 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496305 (x : real) : (term37 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1496304) (@lem1496303 x)). Qed.
Lemma lem1496306 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496307 (x : real) : (term14 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496305 x) (@lem1496306)). Qed.
Lemma lem1496308 (x : real) : (term2 x) = (term38 x).
Proof. exact (TRANS (@lem1496269 x) (@lem1496307 x)). Qed.
Lemma lem1496309 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483531 term15 x). Qed.
Lemma lem1496315 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1496320 (x : real) : (term42 x) = (term16 x).
Proof. exact (@lem1483448 (term16 x)). Qed.
Lemma lem1496322 (x : real) : (term41 x) = (term16 x).
Proof. exact (TRANS (@lem1496315 x) (@lem1496320 x)). Qed.
Lemma lem1496323 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496324 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem1496323) (@lem1496322 x)). Qed.
Lemma lem1496325 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496326 (x : real) : (term40 x) = (term45 x).
Proof. exact (MK_COMB (@lem1496324 x) (@lem1496325)). Qed.
Lemma lem1496327 (x : real) : (term39 x) = (term45 x).
Proof. exact (TRANS (@lem1496309 x) (@lem1496326 x)). Qed.
Lemma lem1496328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1496329 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1496328) (@lem1496308 x)). Qed.
Lemma lem1496330 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem1496329 x) (@lem1496327 x)). Qed.
Lemma lem1496331 (x : real) : (term50 x) = (term51 x).
Proof. exact (@lem1483531 (real_neg x) term15). Qed.
Lemma lem1496332 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496339 (x : real) : (real_neg x) = (term16 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1496340 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1496341 (x : real) : (term52 x) = (term53 x).
Proof. exact (MK_COMB (@lem1496340) (@lem1496339 x)). Qed.
Lemma lem1496342 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem1496341 x) (@lem1496332)). Qed.
Lemma lem1496343 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem1483519 (term16 x) term15). Qed.
Lemma lem1496345 (x : nat) : (term57 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1496346 : term58 = term15.
Proof. exact (@lem1496345 term28). Qed.
Lemma lem1496347 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1496348 (x : real) : (term56 x) = (term60 x).
Proof. exact (MK_COMB (@lem1496347 x) (@lem1496346)). Qed.
Lemma lem1496349 (x : real) : (term60 x) = (term16 x).
Proof. exact (@lem1483450 (term16 x)). Qed.
Lemma lem1496350 (x : real) : (term56 x) = (term16 x).
Proof. exact (TRANS (@lem1496348 x) (@lem1496349 x)). Qed.
Lemma lem1496351 (x : real) : (term55 x) = (term16 x).
Proof. exact (TRANS (@lem1496343 x) (@lem1496350 x)). Qed.
Lemma lem1496352 (x : real) : (term54 x) = (term16 x).
Proof. exact (TRANS (@lem1496342 x) (@lem1496351 x)). Qed.
Lemma lem1496353 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496354 (x : real) : (term61 x) = (term44 x).
Proof. exact (MK_COMB (@lem1496353) (@lem1496352 x)). Qed.
Lemma lem1496355 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496356 (x : real) : (term51 x) = (term45 x).
Proof. exact (MK_COMB (@lem1496354 x) (@lem1496355)). Qed.
Lemma lem1496357 (x : real) : (term50 x) = (term45 x).
Proof. exact (TRANS (@lem1496331 x) (@lem1496356 x)). Qed.
Lemma lem1496358 (x : real) : (term3 x) = (term62 x).
Proof. exact (@lem1483521 x term15). Qed.
Lemma lem1496364 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1483519 x term15). Qed.
Lemma lem1496366 (x : nat) : (term57 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1496367 : term58 = term15.
Proof. exact (@lem1496366 term28). Qed.
Lemma lem1496368 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1496369 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1496368 x) (@lem1496367)). Qed.
Lemma lem1496370 (x : real) : (term65 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1496371 (x : real) : (term64 x) = x.
Proof. exact (TRANS (@lem1496369 x) (@lem1496370 x)). Qed.
Lemma lem1496373 (x : real) : (term63 x) = x.
Proof. exact (TRANS (@lem1496364 x) (@lem1496371 x)). Qed.
Lemma lem1496374 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496375 (x : real) : (term66 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1496374) (@lem1496373 x)). Qed.
Lemma lem1496376 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496377 (x : real) : (term62 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496375 x) (@lem1496376)). Qed.
Lemma lem1496378 (x : real) : (term3 x) = (term38 x).
Proof. exact (TRANS (@lem1496358 x) (@lem1496377 x)). Qed.
Lemma lem1496379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1496380 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1496379) (@lem1496357 x)). Qed.
Lemma lem1496381 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem1496380 x) (@lem1496378 x)). Qed.
Lemma lem1496382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496383 (x : real) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem1496382) (@lem1496330 x)). Qed.
Lemma lem1496384 (x : real) : (term1 x) = (term73 x).
Proof. exact (MK_COMB (@lem1496383 x) (@lem1496381 x)). Qed.
Lemma lem1496385 : term12 = term74.
Proof. exact (fun_ext (fun x : real => @lem1496384 x)). Qed.
Lemma lem1496386 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496387 : term13 = term75.
Proof. exact (MK_COMB (@lem1496386) (@lem1496385)). Qed.
Lemma lem1496388 : term6 = term75.
Proof. exact (TRANS (@lem1496268) (@lem1496387)). Qed.
Lemma lem1496390 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1496391 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1496390 real P Q). Qed.
Lemma lem1496392 : term80 = term81.
Proof. exact (@lem1496391 term82 term83). Qed.
Lemma lem1496393 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1496394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496395 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1496394) (@lem1496393 x)). Qed.
Lemma lem1496396 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1496397 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1496395 x) (@lem1496396 x)). Qed.
Lemma lem1496398 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1496397 x)). Qed.
Lemma lem1496399 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496400 : term80 = term75.
Proof. exact (MK_COMB (@lem1496399) (@lem1496398)). Qed.
Lemma lem1496401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1496402 : term89 = term90.
Proof. exact (MK_COMB (@lem1496401) (@lem1496400)). Qed.
Lemma lem1496403 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1496404 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1496403 x)). Qed.
Lemma lem1496405 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496406 : term92 = term93.
Proof. exact (MK_COMB (@lem1496405) (@lem1496404)). Qed.
Lemma lem1496407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496408 : term94 = term95.
Proof. exact (MK_COMB (@lem1496407) (@lem1496406)). Qed.
Lemma lem1496409 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1496410 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1496409 x)). Qed.
Lemma lem1496411 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496412 : term97 = term98.
Proof. exact (MK_COMB (@lem1496411) (@lem1496410)). Qed.
Lemma lem1496413 : term81 = term99.
Proof. exact (MK_COMB (@lem1496408) (@lem1496412)). Qed.
Lemma lem1496414 : (term80 = term81) = (term75 = term99).
Proof. exact (MK_COMB (@lem1496402) (@lem1496413)). Qed.
Lemma lem1496415 : term75 = term99.
Proof. exact (EQ_MP (@lem1496414) (@lem1496392)). Qed.
Lemma lem1496513 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1496514 (P : real -> Prop) (Q : real -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1496513 real P Q). Qed.
Lemma lem1496515 : term81 = term80.
Proof. exact (@lem1496514 term82 term83). Qed.
Lemma lem1496516 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1496517 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1496516 x)). Qed.
Lemma lem1496518 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496519 : term92 = term93.
Proof. exact (MK_COMB (@lem1496518) (@lem1496517)). Qed.
Lemma lem1496520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496521 : term94 = term95.
Proof. exact (MK_COMB (@lem1496520) (@lem1496519)). Qed.
Lemma lem1496522 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1496523 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1496522 x)). Qed.
Lemma lem1496524 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496525 : term97 = term98.
Proof. exact (MK_COMB (@lem1496524) (@lem1496523)). Qed.
Lemma lem1496526 : term81 = term99.
Proof. exact (MK_COMB (@lem1496521) (@lem1496525)). Qed.
Lemma lem1496527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1496528 : term100 = term101.
Proof. exact (MK_COMB (@lem1496527) (@lem1496526)). Qed.
Lemma lem1496529 (x : real) : (term84 x) = (term49 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1496530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1496531 (x : real) : (term85 x) = (term72 x).
Proof. exact (MK_COMB (@lem1496530) (@lem1496529 x)). Qed.
Lemma lem1496532 (x : real) : (term86 x) = (term70 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1496533 (x : real) : (term87 x) = (term73 x).
Proof. exact (MK_COMB (@lem1496531 x) (@lem1496532 x)). Qed.
Lemma lem1496534 : term88 = term74.
Proof. exact (fun_ext (fun x : real => @lem1496533 x)). Qed.
Lemma lem1496535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496536 : term80 = term75.
Proof. exact (MK_COMB (@lem1496535) (@lem1496534)). Qed.
Lemma lem1496537 : (term81 = term80) = (term99 = term75).
Proof. exact (MK_COMB (@lem1496528) (@lem1496536)). Qed.
Lemma lem1496538 : term99 = term75.
Proof. exact (EQ_MP (@lem1496537) (@lem1496515)). Qed.
Lemma lem1496539 : term75 = term75.
Proof. exact (TRANS (@lem1496415) (@lem1496538)). Qed.
Lemma lem1496542 : term6 = term75.
Proof. exact (TRANS (@lem1496388) (@lem1496539)). Qed.
Lemma lem1496559 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1496560 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem1496559 x)). Qed.
Lemma lem1496561 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1496562 : term75 = term75.
Proof. exact (MK_COMB (@lem1496561) (@lem1496560)). Qed.
Lemma lem1496563 : term6 = term75.
Proof. exact (TRANS (@lem1496542) (@lem1496562)). Qed.
Lemma lem1496573 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1496574 (x : real) (h1 : term49 x) : term49 x.
Proof. exact (h1). Qed.
Lemma lem1496575 (x : real) (h1 : term49 x) : term45 x.
Proof. exact (proj2 (@lem1496574 x h1)). Qed.
Lemma lem1496576 (x : real) (h1 : term49 x) : term38 x.
Proof. exact (proj1 (@lem1496574 x h1)). Qed.
Lemma lem1496578 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496579 : term103 = term104.
Proof. exact (@lem1496578 (NUMERAL 0) term28). Qed.
Lemma lem1496580 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1496581 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1496582 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1496581 h1) (fun h1 : term104 = True => @lem1496580)). Qed.
Lemma lem1496583 : term104 = True.
Proof. exact (EQ_MP (@lem1496582) (@lem1496580)). Qed.
Lemma lem1496584 : term103 = True.
Proof. exact (TRANS (@lem1496579) (@lem1496583)). Qed.
Lemma lem1496585 : True = term103.
Proof. exact (SYM (@lem1496584)). Qed.
Lemma lem1496586 : term103.
Proof. exact (EQ_MP (@lem1496585) (@lem0)). Qed.
Lemma lem1496587 (x : real) (h1 : term49 x) : term106 x.
Proof. exact (conj (@lem1496586) (@lem1496575 x h1)). Qed.
Lemma lem1496589 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1496590 (x : real) : term108 x.
Proof. exact (@lem1496589 term31 (term16 x)). Qed.
Lemma lem1496591 (x : real) (h1 : term49 x) : term109 x.
Proof. exact (@lem1496590 x (@lem1496587 x h1)). Qed.
Lemma lem1496592 (x : real) : (term110 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1496593 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496594 (x : real) : (term111 x) = (term44 x).
Proof. exact (MK_COMB (@lem1496593) (@lem1496592 x)). Qed.
Lemma lem1496595 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496596 (x : real) : (term109 x) = (term45 x).
Proof. exact (MK_COMB (@lem1496594 x) (@lem1496595)). Qed.
Lemma lem1496597 (x : real) (h1 : term49 x) : term45 x.
Proof. exact (EQ_MP (@lem1496596 x) (@lem1496591 x h1)). Qed.
Lemma lem1496599 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496600 : term103 = term104.
Proof. exact (@lem1496599 (NUMERAL 0) term28). Qed.
Lemma lem1496601 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1496602 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1496603 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1496602 h1) (fun h1 : term104 = True => @lem1496601)). Qed.
Lemma lem1496604 : term104 = True.
Proof. exact (EQ_MP (@lem1496603) (@lem1496601)). Qed.
Lemma lem1496605 : term103 = True.
Proof. exact (TRANS (@lem1496600) (@lem1496604)). Qed.
Lemma lem1496606 : True = term103.
Proof. exact (SYM (@lem1496605)). Qed.
Lemma lem1496607 : term103.
Proof. exact (EQ_MP (@lem1496606) (@lem0)). Qed.
Lemma lem1496608 (x : real) (h1 : term49 x) : term112 x.
Proof. exact (conj (@lem1496607) (@lem1496576 x h1)). Qed.
Lemma lem1496610 (x : real) (y : real) : term113 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1496611 (x : real) : term114 x.
Proof. exact (@lem1496610 term31 x). Qed.
Lemma lem1496612 (x : real) (h1 : term49 x) : term115 x.
Proof. exact (@lem1496611 x (@lem1496608 x h1)). Qed.
Lemma lem1496613 (x : real) : (term34 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1496614 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496615 (x : real) : (term116 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1496614) (@lem1496613 x)). Qed.
Lemma lem1496616 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496617 (x : real) : (term115 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496615 x) (@lem1496616)). Qed.
Lemma lem1496618 (x : real) (h1 : term49 x) : term38 x.
Proof. exact (EQ_MP (@lem1496617 x) (@lem1496612 x h1)). Qed.
Lemma lem1496619 (x : real) (h1 : term49 x) : term49 x.
Proof. exact (conj (@lem1496618 x h1) (@lem1496597 x h1)). Qed.
Lemma lem1496621 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1496622 (x : real) : term118 x.
Proof. exact (@lem1496621 x (term16 x)). Qed.
Lemma lem1496623 (x : real) (h1 : term49 x) : term119 x.
Proof. exact (@lem1496622 x (@lem1496619 x h1)). Qed.
Lemma lem1496624 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1496626 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1496627 : term123 = term15.
Proof. exact (@lem1496626 term28). Qed.
Lemma lem1496628 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1496629 : term124 = term125.
Proof. exact (MK_COMB (@lem1496628) (@lem1496627)). Qed.
Lemma lem1496630 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1496631 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1496629) (@lem1496630 x)). Qed.
Lemma lem1496632 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1496624 x) (@lem1496631 x)). Qed.
Lemma lem1496633 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1496634 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1496632 x) (@lem1496633 x)). Qed.
Lemma lem1496635 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496636 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1496635) (@lem1496634 x)). Qed.
Lemma lem1496637 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496638 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1496636 x) (@lem1496637)). Qed.
Lemma lem1496639 (x : real) (h1 : term49 x) : term129.
Proof. exact (EQ_MP (@lem1496638 x) (@lem1496623 x h1)). Qed.
Lemma lem1496641 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496642 : term129 = term130.
Proof. exact (@lem1496641 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1496643 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1496644 : term129 = False.
Proof. exact (TRANS (@lem1496642) (@lem1496643)). Qed.
Lemma lem1496645 (x : real) (h1 : term49 x) : False.
Proof. exact (EQ_MP (@lem1496644) (@lem1496639 x h1)). Qed.
Lemma lem1496646 (x : real) (h1 : term70 x) : term70 x.
Proof. exact (h1). Qed.
Lemma lem1496647 (x : real) (h1 : term70 x) : term38 x.
Proof. exact (proj2 (@lem1496646 x h1)). Qed.
Lemma lem1496648 (x : real) (h1 : term70 x) : term45 x.
Proof. exact (proj1 (@lem1496646 x h1)). Qed.
Lemma lem1496650 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496651 : term103 = term104.
Proof. exact (@lem1496650 (NUMERAL 0) term28). Qed.
Lemma lem1496652 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1496653 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1496654 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1496653 h1) (fun h1 : term104 = True => @lem1496652)). Qed.
Lemma lem1496655 : term104 = True.
Proof. exact (EQ_MP (@lem1496654) (@lem1496652)). Qed.
Lemma lem1496656 : term103 = True.
Proof. exact (TRANS (@lem1496651) (@lem1496655)). Qed.
Lemma lem1496657 : True = term103.
Proof. exact (SYM (@lem1496656)). Qed.
Lemma lem1496658 : term103.
Proof. exact (EQ_MP (@lem1496657) (@lem0)). Qed.
Lemma lem1496659 (x : real) (h1 : term70 x) : term106 x.
Proof. exact (conj (@lem1496658) (@lem1496648 x h1)). Qed.
Lemma lem1496661 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1496662 (x : real) : term108 x.
Proof. exact (@lem1496661 term31 (term16 x)). Qed.
Lemma lem1496663 (x : real) (h1 : term70 x) : term109 x.
Proof. exact (@lem1496662 x (@lem1496659 x h1)). Qed.
Lemma lem1496664 (x : real) : (term110 x) = (term16 x).
Proof. exact (@lem1483460 (term16 x)). Qed.
Lemma lem1496665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1496666 (x : real) : (term111 x) = (term44 x).
Proof. exact (MK_COMB (@lem1496665) (@lem1496664 x)). Qed.
Lemma lem1496667 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496668 (x : real) : (term109 x) = (term45 x).
Proof. exact (MK_COMB (@lem1496666 x) (@lem1496667)). Qed.
Lemma lem1496669 (x : real) (h1 : term70 x) : term45 x.
Proof. exact (EQ_MP (@lem1496668 x) (@lem1496663 x h1)). Qed.
Lemma lem1496671 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496672 : term103 = term104.
Proof. exact (@lem1496671 (NUMERAL 0) term28). Qed.
Lemma lem1496673 : term105 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1496674 (h1 : term105 = (BIT1 0)) : term104 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1496675 : (term105 = (BIT1 0)) = (term104 = True).
Proof. exact (prop_ext (fun h1 : term105 = (BIT1 0) => @lem1496674 h1) (fun h1 : term104 = True => @lem1496673)). Qed.
Lemma lem1496676 : term104 = True.
Proof. exact (EQ_MP (@lem1496675) (@lem1496673)). Qed.
Lemma lem1496677 : term103 = True.
Proof. exact (TRANS (@lem1496672) (@lem1496676)). Qed.
Lemma lem1496678 : True = term103.
Proof. exact (SYM (@lem1496677)). Qed.
Lemma lem1496679 : term103.
Proof. exact (EQ_MP (@lem1496678) (@lem0)). Qed.
Lemma lem1496680 (x : real) (h1 : term70 x) : term112 x.
Proof. exact (conj (@lem1496679) (@lem1496647 x h1)). Qed.
Lemma lem1496682 (x : real) (y : real) : term113 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1496683 (x : real) : term114 x.
Proof. exact (@lem1496682 term31 x). Qed.
Lemma lem1496684 (x : real) (h1 : term70 x) : term115 x.
Proof. exact (@lem1496683 x (@lem1496680 x h1)). Qed.
Lemma lem1496685 (x : real) : (term34 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1496686 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496687 (x : real) : (term116 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1496686) (@lem1496685 x)). Qed.
Lemma lem1496688 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496689 (x : real) : (term115 x) = (term38 x).
Proof. exact (MK_COMB (@lem1496687 x) (@lem1496688)). Qed.
Lemma lem1496690 (x : real) (h1 : term70 x) : term38 x.
Proof. exact (EQ_MP (@lem1496689 x) (@lem1496684 x h1)). Qed.
Lemma lem1496691 (x : real) (h1 : term70 x) : term49 x.
Proof. exact (conj (@lem1496690 x h1) (@lem1496669 x h1)). Qed.
Lemma lem1496693 (x : real) (y : real) : term117 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1496694 (x : real) : term118 x.
Proof. exact (@lem1496693 x (term16 x)). Qed.
Lemma lem1496695 (x : real) (h1 : term70 x) : term119 x.
Proof. exact (@lem1496694 x (@lem1496691 x h1)). Qed.
Lemma lem1496696 (x : real) : (term120 x) = (term121 x).
Proof. exact (@lem1483442 term23 x). Qed.
Lemma lem1496698 (m : nat) : (term122 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1496699 : term123 = term15.
Proof. exact (@lem1496698 term28). Qed.
Lemma lem1496700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1496701 : term124 = term125.
Proof. exact (MK_COMB (@lem1496700) (@lem1496699)). Qed.
Lemma lem1496702 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1496703 (x : real) : (term121 x) = (term126 x).
Proof. exact (MK_COMB (@lem1496701) (@lem1496702 x)). Qed.
Lemma lem1496704 (x : real) : (term120 x) = (term126 x).
Proof. exact (TRANS (@lem1496696 x) (@lem1496703 x)). Qed.
Lemma lem1496705 (x : real) : (term126 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1496706 (x : real) : (term120 x) = term15.
Proof. exact (TRANS (@lem1496704 x) (@lem1496705 x)). Qed.
Lemma lem1496707 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1496708 (x : real) : (term127 x) = term128.
Proof. exact (MK_COMB (@lem1496707) (@lem1496706 x)). Qed.
Lemma lem1496709 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1496710 (x : real) : (term119 x) = term129.
Proof. exact (MK_COMB (@lem1496708 x) (@lem1496709)). Qed.
Lemma lem1496711 (x : real) (h1 : term70 x) : term129.
Proof. exact (EQ_MP (@lem1496710 x) (@lem1496695 x h1)). Qed.
Lemma lem1496713 (n : nat) (m : nat) : (term102 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1496714 : term129 = term130.
Proof. exact (@lem1496713 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1496715 : term130 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1496716 : term129 = False.
Proof. exact (TRANS (@lem1496714) (@lem1496715)). Qed.
Lemma lem1496717 (x : real) (h1 : term70 x) : False.
Proof. exact (EQ_MP (@lem1496716) (@lem1496711 x h1)). Qed.
Lemma lem1496718 (x : real) (h1 : term73 x) : False.
Proof. exact (or_elim (@lem1496573 x h1) (fun h0 : term49 x => @lem1496645 x h0) (fun h0 : term70 x => @lem1496717 x h0)). Qed.
Lemma lem1496720 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1496721 (x : real) (h1 : term73 x) : (term73 x) = False.
Proof. exact (prop_ext (fun h2 : term73 x => @lem1496718 x h1) (fun h2 : False => @lem1496720 x h1)). Qed.
Lemma lem1496722 (x : real) (h1 : term73 x) : False.
Proof. exact (EQ_MP (@lem1496721 x h1) (@lem1496720 x h1)). Qed.
Lemma lem1496723 (h1 : term75) : term75.
Proof. exact (h1). Qed.
Lemma lem1496724 (h1 : term75) : False.
Proof. exact (ex_elim (@lem1496723 h1) (fun x : real => fun h0 : term74 x => @lem1496722 x h0)). Qed.
Lemma lem1496725 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1496726 (h1 : term6) : term75.
Proof. exact (EQ_MP (@lem1496563) (@lem1496725 h1)). Qed.
Lemma lem1496727 (h1 : term6) : term75 = False.
Proof. exact (prop_ext (fun h2 : term75 => @lem1496724 h2) (fun h2 : False => @lem1496726 h1)). Qed.
Lemma lem1496728 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1496727 h1) (@lem1496726 h1)). Qed.
Lemma lem1496729 : term131.
Proof. exact (fun h0 : term6 => @lem1496728 h0). Qed.
Lemma lem1496730 : term132.
Proof. exact (@lem1386578 term133). Qed.
Lemma lem1496731 : term133.
Proof. exact (@lem1496730 (@lem1496729)). Qed.
