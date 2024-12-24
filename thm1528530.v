Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1528530_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1482703_spec.
Require Import thm1482981_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483462_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm706885_spec.
Require Import thm940073_spec.
Lemma lem1528219 : term0 = term1.
Proof. exact (@lem1483554 term2 term3). Qed.
Lemma lem1528225 : term4 = term5.
Proof. exact (@lem1483519 term2 term3). Qed.
Lemma lem1528227 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1528228 : term8 = term9.
Proof. exact (@lem1528227 term10 term10). Qed.
Lemma lem1528229 : (term11 = (BIT1 0)) = (term12 = term10).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1528230 : term12 = term10.
Proof. exact (EQ_MP (@lem1528229) (@lem940073)). Qed.
Lemma lem1528231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1528232 : term13 = term3.
Proof. exact (MK_COMB (@lem1528231) (@lem1528230)). Qed.
Lemma lem1528233 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1528234 : term9 = term14.
Proof. exact (MK_COMB (@lem1528233) (@lem1528232)). Qed.
Lemma lem1528235 : term8 = term14.
Proof. exact (TRANS (@lem1528228) (@lem1528234)). Qed.
Lemma lem1528236 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1528239 : term5 = term16.
Proof. exact (MK_COMB (@lem1528236) (@lem1528235)). Qed.
Lemma lem1528241 : term4 = term16.
Proof. exact (TRANS (@lem1528225) (@lem1528239)). Qed.
Lemma lem1528242 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1528243 : term17 = term18.
Proof. exact (MK_COMB (@lem1528242) (@lem1528241)). Qed.
Lemma lem1528244 : term18 = term19.
Proof. exact (@lem1483512 term16). Qed.
Lemma lem1528245 : term19 = term20.
Proof. exact (@lem1483508 term2 term14 term14). Qed.
Lemma lem1528247 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1528248 : term23 = term13.
Proof. exact (@lem1528247 term10 term10). Qed.
Lemma lem1528249 : (term11 = (BIT1 0)) = (term12 = term10).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1528250 : term12 = term10.
Proof. exact (EQ_MP (@lem1528249) (@lem940073)). Qed.
Lemma lem1528251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1528252 : term13 = term3.
Proof. exact (MK_COMB (@lem1528251) (@lem1528250)). Qed.
Lemma lem1528253 : term23 = term3.
Proof. exact (TRANS (@lem1528248) (@lem1528252)). Qed.
Lemma lem1528256 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1528257 : term20 = term25.
Proof. exact (MK_COMB (@lem1528256) (@lem1528253)). Qed.
Lemma lem1528258 : term19 = term25.
Proof. exact (TRANS (@lem1528245) (@lem1528257)). Qed.
Lemma lem1528259 : term18 = term25.
Proof. exact (TRANS (@lem1528244) (@lem1528258)). Qed.
Lemma lem1528260 : term26 = term26.
Proof. exact (eq_refl term26). Qed.
Lemma lem1528261 : (term17 = term18) = (term17 = term25).
Proof. exact (MK_COMB (@lem1528260) (@lem1528259)). Qed.
Lemma lem1528262 : term17 = term25.
Proof. exact (EQ_MP (@lem1528261) (@lem1528243)). Qed.
Lemma lem1528263 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528264 : term27 = term28.
Proof. exact (MK_COMB (@lem1528263) (@lem1528262)). Qed.
Lemma lem1528265 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528266 : term30 = term31.
Proof. exact (MK_COMB (@lem1528264) (@lem1528265)). Qed.
Lemma lem1528267 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528268 : term32 = term33.
Proof. exact (MK_COMB (@lem1528267) (@lem1528241)). Qed.
Lemma lem1528269 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528270 : term34 = term35.
Proof. exact (MK_COMB (@lem1528268) (@lem1528269)). Qed.
Lemma lem1528271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528272 : term36 = term37.
Proof. exact (MK_COMB (@lem1528271) (@lem1528270)). Qed.
Lemma lem1528273 : term1 = term38.
Proof. exact (MK_COMB (@lem1528272) (@lem1528266)). Qed.
Lemma lem1528287 : term0 = term38.
Proof. exact (TRANS (@lem1528219) (@lem1528273)). Qed.
Lemma lem1528289 : term39 = term35.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528290 : term35 = term39.
Proof. exact (SYM (@lem1528289)). Qed.
Lemma lem1528291 : term39 = term40.
Proof. exact (@lem1482981 term41 term3). Qed.
Lemma lem1528292 : term35 = term40.
Proof. exact (TRANS (@lem1528290) (@lem1528291)). Qed.
Lemma lem1528293 : term42 = term43.
Proof. exact (eq_refl term42). Qed.
Lemma lem1528294 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem1528295 : term45 = term46.
Proof. exact (MK_COMB (@lem1528294) (@lem1528293)). Qed.
Lemma lem1528296 : term47 = term48.
Proof. exact (eq_refl term47). Qed.
Lemma lem1528297 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1528298 : term50 = term51.
Proof. exact (MK_COMB (@lem1528297) (@lem1528296)). Qed.
Lemma lem1528299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528300 : term52 = term53.
Proof. exact (MK_COMB (@lem1528299) (@lem1528298)). Qed.
Lemma lem1528301 : term40 = term54.
Proof. exact (MK_COMB (@lem1528300) (@lem1528295)). Qed.
Lemma lem1528302 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem1528303 : (term35 = term40) = (term35 = term54).
Proof. exact (MK_COMB (@lem1528302) (@lem1528301)). Qed.
Lemma lem1528304 : term35 = term54.
Proof. exact (EQ_MP (@lem1528303) (@lem1528292)). Qed.
Lemma lem1528305 : term56 = term57.
Proof. exact (@lem1483527 term3 term29). Qed.
Lemma lem1528311 : term58 = term59.
Proof. exact (@lem1483519 term3 term29). Qed.
Lemma lem1528313 (x : nat) : (term60 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528314 : term61 = term29.
Proof. exact (@lem1528313 term10). Qed.
Lemma lem1528315 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1528316 : term59 = term63.
Proof. exact (MK_COMB (@lem1528315) (@lem1528314)). Qed.
Lemma lem1528317 : term63 = term3.
Proof. exact (@lem1483450 term3). Qed.
Lemma lem1528318 : term59 = term3.
Proof. exact (TRANS (@lem1528316) (@lem1528317)). Qed.
Lemma lem1528320 : term58 = term3.
Proof. exact (TRANS (@lem1528311) (@lem1528318)). Qed.
Lemma lem1528321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1528322 : term64 = term65.
Proof. exact (MK_COMB (@lem1528321) (@lem1528320)). Qed.
Lemma lem1528323 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528324 : term57 = term56.
Proof. exact (MK_COMB (@lem1528322) (@lem1528323)). Qed.
Lemma lem1528325 : term56 = term56.
Proof. exact (TRANS (@lem1528305) (@lem1528324)). Qed.
Lemma lem1528326 : term48 = term66.
Proof. exact (@lem1483525 term67 term29). Qed.
Lemma lem1528327 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528334 (m : nat) : (term68 m) = term29.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1528336 : term67 = term29.
Proof. exact (@lem1528334 term10). Qed.
Lemma lem1528337 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1528338 : term69 = term70.
Proof. exact (MK_COMB (@lem1528337) (@lem1528336)). Qed.
Lemma lem1528339 : term71 = term72.
Proof. exact (MK_COMB (@lem1528338) (@lem1528327)). Qed.
Lemma lem1528340 : term72 = term73.
Proof. exact (@lem1483519 term29 term29). Qed.
Lemma lem1528342 (x : nat) : (term60 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528343 : term61 = term29.
Proof. exact (@lem1528342 term10). Qed.
Lemma lem1528344 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1528345 : term73 = term75.
Proof. exact (MK_COMB (@lem1528344) (@lem1528343)). Qed.
Lemma lem1528346 : term75 = term29.
Proof. exact (@lem1483448 term29). Qed.
Lemma lem1528347 : term73 = term29.
Proof. exact (TRANS (@lem1528345) (@lem1528346)). Qed.
Lemma lem1528348 : term72 = term29.
Proof. exact (TRANS (@lem1528340) (@lem1528347)). Qed.
Lemma lem1528349 : term71 = term29.
Proof. exact (TRANS (@lem1528339) (@lem1528348)). Qed.
Lemma lem1528350 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528351 : term76 = term77.
Proof. exact (MK_COMB (@lem1528350) (@lem1528349)). Qed.
Lemma lem1528352 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528353 : term66 = term78.
Proof. exact (MK_COMB (@lem1528351) (@lem1528352)). Qed.
Lemma lem1528354 : term48 = term78.
Proof. exact (TRANS (@lem1528326) (@lem1528353)). Qed.
Lemma lem1528355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528356 : term49 = term49.
Proof. exact (MK_COMB (@lem1528355) (@lem1528325)). Qed.
Lemma lem1528357 : term51 = term79.
Proof. exact (MK_COMB (@lem1528356) (@lem1528354)). Qed.
Lemma lem1528358 : term80 = term81.
Proof. exact (@lem1483525 term29 term3). Qed.
Lemma lem1528364 : term82 = term83.
Proof. exact (@lem1483519 term29 term3). Qed.
Lemma lem1528366 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1528367 : term8 = term9.
Proof. exact (@lem1528366 term10 term10). Qed.
Lemma lem1528368 : (term11 = (BIT1 0)) = (term12 = term10).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1528369 : term12 = term10.
Proof. exact (EQ_MP (@lem1528368) (@lem940073)). Qed.
Lemma lem1528370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1528371 : term13 = term3.
Proof. exact (MK_COMB (@lem1528370) (@lem1528369)). Qed.
Lemma lem1528372 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1528373 : term9 = term14.
Proof. exact (MK_COMB (@lem1528372) (@lem1528371)). Qed.
Lemma lem1528374 : term8 = term14.
Proof. exact (TRANS (@lem1528367) (@lem1528373)). Qed.
Lemma lem1528375 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1528376 : term83 = term84.
Proof. exact (MK_COMB (@lem1528375) (@lem1528374)). Qed.
Lemma lem1528377 : term84 = term14.
Proof. exact (@lem1483448 term14). Qed.
Lemma lem1528378 : term83 = term14.
Proof. exact (TRANS (@lem1528376) (@lem1528377)). Qed.
Lemma lem1528380 : term82 = term14.
Proof. exact (TRANS (@lem1528364) (@lem1528378)). Qed.
Lemma lem1528381 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528382 : term85 = term86.
Proof. exact (MK_COMB (@lem1528381) (@lem1528380)). Qed.
Lemma lem1528383 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528384 : term81 = term87.
Proof. exact (MK_COMB (@lem1528382) (@lem1528383)). Qed.
Lemma lem1528385 : term80 = term87.
Proof. exact (TRANS (@lem1528358) (@lem1528384)). Qed.
Lemma lem1528386 : term43 = term88.
Proof. exact (@lem1483525 term89 term29). Qed.
Lemma lem1528387 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528393 : term89 = term90.
Proof. exact (@lem1367763 term10 term10). Qed.
Lemma lem1528394 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1528395 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1528396 : term93 = term94.
Proof. exact (EQ_MP (@lem1528395) (@lem1528394)). Qed.
Lemma lem1528397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1528398 : term95 = term96.
Proof. exact (MK_COMB (@lem1528397) (@lem1528396)). Qed.
Lemma lem1528399 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1528400 : term90 = term97.
Proof. exact (MK_COMB (@lem1528399) (@lem1528398)). Qed.
Lemma lem1528402 : term89 = term97.
Proof. exact (TRANS (@lem1528393) (@lem1528400)). Qed.
Lemma lem1528403 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1528404 : term98 = term99.
Proof. exact (MK_COMB (@lem1528403) (@lem1528402)). Qed.
Lemma lem1528405 : term100 = term101.
Proof. exact (MK_COMB (@lem1528404) (@lem1528387)). Qed.
Lemma lem1528406 : term101 = term102.
Proof. exact (@lem1483519 term97 term29). Qed.
Lemma lem1528408 (x : nat) : (term60 x) = term29.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528409 : term61 = term29.
Proof. exact (@lem1528408 term10). Qed.
Lemma lem1528410 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem1528411 : term102 = term104.
Proof. exact (MK_COMB (@lem1528410) (@lem1528409)). Qed.
Lemma lem1528412 : term104 = term97.
Proof. exact (@lem1483450 term97). Qed.
Lemma lem1528413 : term102 = term97.
Proof. exact (TRANS (@lem1528411) (@lem1528412)). Qed.
Lemma lem1528414 : term101 = term97.
Proof. exact (TRANS (@lem1528406) (@lem1528413)). Qed.
Lemma lem1528415 : term100 = term97.
Proof. exact (TRANS (@lem1528405) (@lem1528414)). Qed.
Lemma lem1528416 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528417 : term105 = term106.
Proof. exact (MK_COMB (@lem1528416) (@lem1528415)). Qed.
Lemma lem1528418 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528419 : term88 = term107.
Proof. exact (MK_COMB (@lem1528417) (@lem1528418)). Qed.
Lemma lem1528420 : term43 = term107.
Proof. exact (TRANS (@lem1528386) (@lem1528419)). Qed.
Lemma lem1528421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528422 : term44 = term108.
Proof. exact (MK_COMB (@lem1528421) (@lem1528385)). Qed.
Lemma lem1528423 : term46 = term109.
Proof. exact (MK_COMB (@lem1528422) (@lem1528420)). Qed.
Lemma lem1528424 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528425 : term53 = term110.
Proof. exact (MK_COMB (@lem1528424) (@lem1528357)). Qed.
Lemma lem1528426 : term54 = term111.
Proof. exact (MK_COMB (@lem1528425) (@lem1528423)). Qed.
Lemma lem1528438 : term35 = term111.
Proof. exact (TRANS (@lem1528304) (@lem1528426)). Qed.
Lemma lem1528440 (a : real) (x : real) (r : real) : (term112 x a r) = (term113 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1528441 : term31 = term114.
Proof. exact (@lem1528440 term3 term3 term29). Qed.
Lemma lem1528448 : term115 = term3.
Proof. exact (@lem1483460 term3). Qed.
Lemma lem1528451 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1528452 : term116 = term117.
Proof. exact (MK_COMB (@lem1528451) (@lem1528448)). Qed.
Lemma lem1528453 : term117 = term95.
Proof. exact (@lem1367770 term10 term10). Qed.
Lemma lem1528454 : term91 = term92.
Proof. exact (@lem706885). Qed.
Lemma lem1528455 : (term91 = term92) = (term93 = term94).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term92). Qed.
Lemma lem1528456 : term93 = term94.
Proof. exact (EQ_MP (@lem1528455) (@lem1528454)). Qed.
Lemma lem1528457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1528458 : term95 = term96.
Proof. exact (MK_COMB (@lem1528457) (@lem1528456)). Qed.
Lemma lem1528459 : term117 = term96.
Proof. exact (TRANS (@lem1528453) (@lem1528458)). Qed.
Lemma lem1528460 : term116 = term96.
Proof. exact (TRANS (@lem1528452) (@lem1528459)). Qed.
Lemma lem1528461 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528462 : term118 = term119.
Proof. exact (MK_COMB (@lem1528461) (@lem1528460)). Qed.
Lemma lem1528463 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528464 : term120 = term121.
Proof. exact (MK_COMB (@lem1528462) (@lem1528463)). Qed.
Lemma lem1528471 : term8 = term14.
Proof. exact (@lem1483462 term14). Qed.
Lemma lem1528474 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem1528475 : term122 = term67.
Proof. exact (MK_COMB (@lem1528474) (@lem1528471)). Qed.
Lemma lem1528477 (m : nat) : (term68 m) = term29.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1528478 : term67 = term29.
Proof. exact (@lem1528477 term10). Qed.
Lemma lem1528479 : term122 = term29.
Proof. exact (TRANS (@lem1528475) (@lem1528478)). Qed.
Lemma lem1528480 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528481 : term123 = term77.
Proof. exact (MK_COMB (@lem1528480) (@lem1528479)). Qed.
Lemma lem1528482 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1528483 : term124 = term78.
Proof. exact (MK_COMB (@lem1528481) (@lem1528482)). Qed.
Lemma lem1528484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528485 : term125 = term126.
Proof. exact (MK_COMB (@lem1528484) (@lem1528483)). Qed.
Lemma lem1528486 : term114 = term127.
Proof. exact (MK_COMB (@lem1528485) (@lem1528464)). Qed.
Lemma lem1528489 : term31 = term127.
Proof. exact (TRANS (@lem1528441) (@lem1528486)). Qed.
Lemma lem1528490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528491 : term37 = term128.
Proof. exact (MK_COMB (@lem1528490) (@lem1528438)). Qed.
Lemma lem1528492 : term38 = term129.
Proof. exact (MK_COMB (@lem1528491) (@lem1528489)). Qed.
Lemma lem1528493 (h1 : term129) : term129.
Proof. exact (h1). Qed.
Lemma lem1528494 (h1 : term111) : term111.
Proof. exact (h1). Qed.
Lemma lem1528495 (h1 : term79) : term79.
Proof. exact (h1). Qed.
Lemma lem1528496 (h1 : term79) : term78.
Proof. exact (proj2 (@lem1528495 h1)). Qed.
Lemma lem1528499 (n : nat) (m : nat) : (term130 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1528500 : term78 = term131.
Proof. exact (@lem1528499 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1528501 : term131 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1528502 : term78 = False.
Proof. exact (TRANS (@lem1528500) (@lem1528501)). Qed.
Lemma lem1528503 (h1 : term79) : False.
Proof. exact (EQ_MP (@lem1528502) (@lem1528496 h1)). Qed.
Lemma lem1528504 (h1 : term109) : term109.
Proof. exact (h1). Qed.
Lemma lem1528505 (h1 : term109) : term107.
Proof. exact (proj2 (@lem1528504 h1)). Qed.
Lemma lem1528508 (m : nat) (n : nat) : (term132 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1528509 : term107 = False.
Proof. exact (@lem1528508 term94 (NUMERAL 0)). Qed.
Lemma lem1528510 (h1 : term109) : False.
Proof. exact (EQ_MP (@lem1528509) (@lem1528505 h1)). Qed.
Lemma lem1528511 (h1 : term111) : False.
Proof. exact (or_elim (@lem1528494 h1) (fun h0 : term79 => @lem1528503 h0) (fun h0 : term109 => @lem1528510 h0)). Qed.
Lemma lem1528512 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1528514 (h1 : term127) : term78.
Proof. exact (proj1 (@lem1528512 h1)). Qed.
Lemma lem1528516 (n : nat) (m : nat) : (term130 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1528517 : term78 = term131.
Proof. exact (@lem1528516 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1528518 : term131 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1528519 : term78 = False.
Proof. exact (TRANS (@lem1528517) (@lem1528518)). Qed.
Lemma lem1528520 (h1 : term127) : False.
Proof. exact (EQ_MP (@lem1528519) (@lem1528514 h1)). Qed.
Lemma lem1528521 (h1 : term129) : False.
Proof. exact (or_elim (@lem1528493 h1) (fun h0 : term111 => @lem1528511 h0) (fun h0 : term127 => @lem1528520 h0)). Qed.
Lemma lem1528522 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1528523 (h1 : term38) : term129.
Proof. exact (EQ_MP (@lem1528492) (@lem1528522 h1)). Qed.
Lemma lem1528524 (h1 : term38) : term129 = False.
Proof. exact (prop_ext (fun h2 : term129 => @lem1528521 h2) (fun h2 : False => @lem1528523 h1)). Qed.
Lemma lem1528525 (h1 : term38) : False.
Proof. exact (EQ_MP (@lem1528524 h1) (@lem1528523 h1)). Qed.
Lemma lem1528526 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1528527 (h1 : term0) : term38.
Proof. exact (EQ_MP (@lem1528287) (@lem1528526 h1)). Qed.
Lemma lem1528528 (h1 : term0) : term38 = False.
Proof. exact (prop_ext (fun h2 : term38 => @lem1528525 h2) (fun h2 : False => @lem1528527 h1)). Qed.
Lemma lem1528529 (h1 : term0) : False.
Proof. exact (EQ_MP (@lem1528528 h1) (@lem1528527 h1)). Qed.
Lemma lem1528530 : term133.
Proof. exact (fun h0 : term0 => @lem1528529 h0). Qed.
