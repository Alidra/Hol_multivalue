Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_2_CASES_term_abbrevs.
Require Import INT_DIVISION_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365720_spec.
Require Import thm1365721_spec.
Require Import thm1366971_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367767_spec.
Require Import thm1367769_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1482981_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1980277_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982747_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm706949_spec.
Require Import thm706951_spec.
Require Import thm707079_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm913059_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem2708270 (n : int) : term0 n.
Proof. exact (@lem2389435 n). Qed.
Lemma lem2708271 (n : int) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2708272 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem2708271 n) (@lem2708270 n)). Qed.
Lemma lem2708273 (n : int) : term2 n.
Proof. exact (@lem2708272 n term3). Qed.
Lemma lem2708274 (n : int) : (term2 n) = (term4 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem2708275 (n : int) : term4 n.
Proof. exact (EQ_MP (@lem2708274 n) (@lem2708273 n)). Qed.
Lemma lem2708276 (n : int) : (term5 n) = (term6 n).
Proof. exact (@lem2318604 (term6 n)). Qed.
Lemma lem2708294 : term7 = (term3 = term8).
Proof. exact (@lem16933 (term3 = term8)). Qed.
Lemma lem2708303 (n : int) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem2708304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2708305 : term10 = term11.
Proof. exact (MK_COMB (@lem2708304) (@lem2708294)). Qed.
Lemma lem2708306 (n : int) : (term12 n) = (term13 n).
Proof. exact (MK_COMB (@lem2708305) (@lem2708303 n)). Qed.
Lemma lem2708307 (n : int) : (term4 n) = (term12 n).
Proof. exact (@lem17265 term14 (term9 n)). Qed.
Lemma lem2708308 (n : int) : (term4 n) = (term13 n).
Proof. exact (TRANS (@lem2708307 n) (@lem2708306 n)). Qed.
Lemma lem2708315 (n : int) : (term15 n) = (term16 n).
Proof. exact (@lem17160 ((term17 n) = term8) ((term17 n) = term18)). Qed.
Lemma lem2708316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708317 (n : int) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem2708316) (@lem2708308 n)). Qed.
Lemma lem2708318 (n : int) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem2708317 n) (@lem2708315 n)). Qed.
Lemma lem2708319 (n : int) : (term23 n) = (term21 n).
Proof. exact (@lem17362 (term4 n) (term24 n)). Qed.
Lemma lem2708347 (n : int) : (term23 n) = (term22 n).
Proof. exact (TRANS (@lem2708319 n) (@lem2708318 n)). Qed.
Lemma lem2708350 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2708351 : (term3 = term8) = (term25 = term26).
Proof. exact (@lem2708350 term3 term8). Qed.
Lemma lem2708355 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708356 : term25 = term28.
Proof. exact (@lem2708355 term29). Qed.
Lemma lem2708357 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2708358 : term30 = term31.
Proof. exact (MK_COMB (@lem2708357) (@lem2708356)). Qed.
Lemma lem2708360 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708361 : term26 = term32.
Proof. exact (@lem2708360 (NUMERAL 0)). Qed.
Lemma lem2708362 : (term25 = term26) = (term28 = term32).
Proof. exact (MK_COMB (@lem2708358) (@lem2708361)). Qed.
Lemma lem2708364 : (term3 = term8) = (term28 = term32).
Proof. exact (TRANS (@lem2708351) (@lem2708362)). Qed.
Lemma lem2708367 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2708368 (n : int) : (n = (term33 n)) = ((real_of_int n) = (term34 n)).
Proof. exact (@lem2708367 n (term33 n)). Qed.
Lemma lem2708372 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2708373 (n : int) : (term34 n) = (term37 n).
Proof. exact (@lem2708372 (term38 n) (term17 n)). Qed.
Lemma lem2708375 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2708376 (n : int) : (term41 n) = (term42 n).
Proof. exact (@lem2708375 (term43 n) term3). Qed.
Lemma lem2708378 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708379 : term25 = term28.
Proof. exact (@lem2708378 term29). Qed.
Lemma lem2708380 (n : int) : (term44 n) = (term44 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem2708381 (n : int) : (term42 n) = (term45 n).
Proof. exact (MK_COMB (@lem2708380 n) (@lem2708379)). Qed.
Lemma lem2708382 (n : int) : (term41 n) = (term45 n).
Proof. exact (TRANS (@lem2708376 n) (@lem2708381 n)). Qed.
Lemma lem2708383 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2708384 (n : int) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem2708383) (@lem2708382 n)). Qed.
Lemma lem2708385 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2708386 (n : int) : (term37 n) = (term49 n).
Proof. exact (MK_COMB (@lem2708384 n) (@lem2708385 n)). Qed.
Lemma lem2708387 (n : int) : (term34 n) = (term49 n).
Proof. exact (TRANS (@lem2708373 n) (@lem2708386 n)). Qed.
Lemma lem2708388 (n : int) : (term50 n) = (term50 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem2708389 (n : int) : ((real_of_int n) = (term34 n)) = ((real_of_int n) = (term49 n)).
Proof. exact (MK_COMB (@lem2708388 n) (@lem2708387 n)). Qed.
Lemma lem2708391 (n : int) : (n = (term33 n)) = ((real_of_int n) = (term49 n)).
Proof. exact (TRANS (@lem2708368 n) (@lem2708389 n)). Qed.
Lemma lem2708394 (x : int) (y : int) : (int_le x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2708395 (n : int) : (term52 n) = (term53 n).
Proof. exact (@lem2708394 term8 (term17 n)). Qed.
Lemma lem2708397 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708398 : term26 = term32.
Proof. exact (@lem2708397 (NUMERAL 0)). Qed.
Lemma lem2708399 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2708400 : term54 = term55.
Proof. exact (MK_COMB (@lem2708399) (@lem2708398)). Qed.
Lemma lem2708401 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2708402 (n : int) : (term53 n) = (term56 n).
Proof. exact (MK_COMB (@lem2708400) (@lem2708401 n)). Qed.
Lemma lem2708404 (n : int) : (term52 n) = (term56 n).
Proof. exact (TRANS (@lem2708395 n) (@lem2708402 n)). Qed.
Lemma lem2708406 (x : int) (y : int) : (int_lt x y) = (term57 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2708407 (n : int) : (term58 n) = (term59 n).
Proof. exact (@lem2708406 (term17 n) term60). Qed.
Lemma lem2708409 (x : int) (y : int) : (int_le x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2708410 (n : int) : (term59 n) = (term61 n).
Proof. exact (@lem2708409 (term62 n) term60). Qed.
Lemma lem2708412 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2708413 (n : int) : (term63 n) = (term64 n).
Proof. exact (@lem2708412 (term17 n) term18). Qed.
Lemma lem2708415 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708416 : term65 = term66.
Proof. exact (@lem2708415 term67). Qed.
Lemma lem2708417 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2708418 (n : int) : (term64 n) = (term69 n).
Proof. exact (MK_COMB (@lem2708417 n) (@lem2708416)). Qed.
Lemma lem2708419 (n : int) : (term63 n) = (term69 n).
Proof. exact (TRANS (@lem2708413 n) (@lem2708418 n)). Qed.
Lemma lem2708420 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2708421 (n : int) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem2708420) (@lem2708419 n)). Qed.
Lemma lem2708423 (x : int) : (term72 x) = (term73 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2708424 : term74 = term75.
Proof. exact (@lem2708423 term3). Qed.
Lemma lem2708426 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708427 : term25 = term28.
Proof. exact (@lem2708426 term29). Qed.
Lemma lem2708428 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2708429 : term75 = term76.
Proof. exact (MK_COMB (@lem2708428) (@lem2708427)). Qed.
Lemma lem2708430 : term74 = term76.
Proof. exact (TRANS (@lem2708424) (@lem2708429)). Qed.
Lemma lem2708431 (n : int) : (term61 n) = (term77 n).
Proof. exact (MK_COMB (@lem2708421 n) (@lem2708430)). Qed.
Lemma lem2708432 (n : int) : (term59 n) = (term77 n).
Proof. exact (TRANS (@lem2708410 n) (@lem2708431 n)). Qed.
Lemma lem2708433 (n : int) : (term58 n) = (term77 n).
Proof. exact (TRANS (@lem2708407 n) (@lem2708432 n)). Qed.
Lemma lem2708434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708435 (n : int) : (term78 n) = (term79 n).
Proof. exact (MK_COMB (@lem2708434) (@lem2708404 n)). Qed.
Lemma lem2708436 (n : int) : (term80 n) = (term81 n).
Proof. exact (MK_COMB (@lem2708435 n) (@lem2708433 n)). Qed.
Lemma lem2708437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708438 (n : int) : (term82 n) = (term83 n).
Proof. exact (MK_COMB (@lem2708437) (@lem2708391 n)). Qed.
Lemma lem2708439 (n : int) : (term9 n) = (term84 n).
Proof. exact (MK_COMB (@lem2708438 n) (@lem2708436 n)). Qed.
Lemma lem2708440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2708441 : term11 = term85.
Proof. exact (MK_COMB (@lem2708440) (@lem2708364)). Qed.
Lemma lem2708442 (n : int) : (term13 n) = (term86 n).
Proof. exact (MK_COMB (@lem2708441) (@lem2708439 n)). Qed.
Lemma lem2708444 (y : int) (x : int) : (term87 x y) = (term88 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2708445 (n : int) : (term89 n) = (term90 n).
Proof. exact (@lem2708444 term8 (term17 n)). Qed.
Lemma lem2708447 (x : int) (y : int) : (int_le x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2708448 (n : int) : (term91 n) = (term92 n).
Proof. exact (@lem2708447 (term62 n) term8). Qed.
Lemma lem2708450 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2708451 (n : int) : (term63 n) = (term64 n).
Proof. exact (@lem2708450 (term17 n) term18). Qed.
Lemma lem2708453 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708454 : term65 = term66.
Proof. exact (@lem2708453 term67). Qed.
Lemma lem2708455 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2708456 (n : int) : (term64 n) = (term69 n).
Proof. exact (MK_COMB (@lem2708455 n) (@lem2708454)). Qed.
Lemma lem2708457 (n : int) : (term63 n) = (term69 n).
Proof. exact (TRANS (@lem2708451 n) (@lem2708456 n)). Qed.
Lemma lem2708458 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2708459 (n : int) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem2708458) (@lem2708457 n)). Qed.
Lemma lem2708461 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708462 : term26 = term32.
Proof. exact (@lem2708461 (NUMERAL 0)). Qed.
Lemma lem2708463 (n : int) : (term92 n) = (term93 n).
Proof. exact (MK_COMB (@lem2708459 n) (@lem2708462)). Qed.
Lemma lem2708464 (n : int) : (term91 n) = (term93 n).
Proof. exact (TRANS (@lem2708448 n) (@lem2708463 n)). Qed.
Lemma lem2708465 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2708466 (n : int) : (term94 n) = (term95 n).
Proof. exact (MK_COMB (@lem2708465) (@lem2708464 n)). Qed.
Lemma lem2708468 (x : int) (y : int) : (int_le x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2708469 (n : int) : (term96 n) = (term97 n).
Proof. exact (@lem2708468 term98 (term17 n)). Qed.
Lemma lem2708471 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2708472 : term99 = term100.
Proof. exact (@lem2708471 term8 term18). Qed.
Lemma lem2708474 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708475 : term26 = term32.
Proof. exact (@lem2708474 (NUMERAL 0)). Qed.
Lemma lem2708476 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2708477 : term101 = term102.
Proof. exact (MK_COMB (@lem2708476) (@lem2708475)). Qed.
Lemma lem2708479 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708480 : term65 = term66.
Proof. exact (@lem2708479 term67). Qed.
Lemma lem2708481 : term100 = term103.
Proof. exact (MK_COMB (@lem2708477) (@lem2708480)). Qed.
Lemma lem2708482 : term99 = term103.
Proof. exact (TRANS (@lem2708472) (@lem2708481)). Qed.
Lemma lem2708483 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2708484 : term104 = term105.
Proof. exact (MK_COMB (@lem2708483) (@lem2708482)). Qed.
Lemma lem2708485 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2708486 (n : int) : (term97 n) = (term106 n).
Proof. exact (MK_COMB (@lem2708484) (@lem2708485 n)). Qed.
Lemma lem2708487 (n : int) : (term96 n) = (term106 n).
Proof. exact (TRANS (@lem2708469 n) (@lem2708486 n)). Qed.
Lemma lem2708488 (n : int) : (term90 n) = (term107 n).
Proof. exact (MK_COMB (@lem2708466 n) (@lem2708487 n)). Qed.
Lemma lem2708489 (n : int) : (term89 n) = (term107 n).
Proof. exact (TRANS (@lem2708445 n) (@lem2708488 n)). Qed.
Lemma lem2708491 (y : int) (x : int) : (term87 x y) = (term88 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2708492 (n : int) : (term108 n) = (term109 n).
Proof. exact (@lem2708491 term18 (term17 n)). Qed.
Lemma lem2708494 (x : int) (y : int) : (int_le x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2708495 (n : int) : (term110 n) = (term111 n).
Proof. exact (@lem2708494 (term62 n) term18). Qed.
Lemma lem2708497 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2708498 (n : int) : (term63 n) = (term64 n).
Proof. exact (@lem2708497 (term17 n) term18). Qed.
Lemma lem2708500 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708501 : term65 = term66.
Proof. exact (@lem2708500 term67). Qed.
Lemma lem2708502 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2708503 (n : int) : (term64 n) = (term69 n).
Proof. exact (MK_COMB (@lem2708502 n) (@lem2708501)). Qed.
Lemma lem2708504 (n : int) : (term63 n) = (term69 n).
Proof. exact (TRANS (@lem2708498 n) (@lem2708503 n)). Qed.
Lemma lem2708505 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2708506 (n : int) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem2708505) (@lem2708504 n)). Qed.
Lemma lem2708508 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708509 : term65 = term66.
Proof. exact (@lem2708508 term67). Qed.
Lemma lem2708510 (n : int) : (term111 n) = (term112 n).
Proof. exact (MK_COMB (@lem2708506 n) (@lem2708509)). Qed.
Lemma lem2708511 (n : int) : (term110 n) = (term112 n).
Proof. exact (TRANS (@lem2708495 n) (@lem2708510 n)). Qed.
Lemma lem2708512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2708513 (n : int) : (term113 n) = (term114 n).
Proof. exact (MK_COMB (@lem2708512) (@lem2708511 n)). Qed.
Lemma lem2708515 (x : int) (y : int) : (int_le x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2708516 (n : int) : (term115 n) = (term116 n).
Proof. exact (@lem2708515 term117 (term17 n)). Qed.
Lemma lem2708518 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2708519 : term118 = term119.
Proof. exact (@lem2708518 term18 term18). Qed.
Lemma lem2708521 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708522 : term65 = term66.
Proof. exact (@lem2708521 term67). Qed.
Lemma lem2708523 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2708524 : term120 = term121.
Proof. exact (MK_COMB (@lem2708523) (@lem2708522)). Qed.
Lemma lem2708526 (n : nat) : (term27 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2708527 : term65 = term66.
Proof. exact (@lem2708526 term67). Qed.
Lemma lem2708528 : term119 = term122.
Proof. exact (MK_COMB (@lem2708524) (@lem2708527)). Qed.
Lemma lem2708529 : term118 = term122.
Proof. exact (TRANS (@lem2708519) (@lem2708528)). Qed.
Lemma lem2708530 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2708531 : term123 = term124.
Proof. exact (MK_COMB (@lem2708530) (@lem2708529)). Qed.
Lemma lem2708532 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2708533 (n : int) : (term116 n) = (term125 n).
Proof. exact (MK_COMB (@lem2708531) (@lem2708532 n)). Qed.
Lemma lem2708534 (n : int) : (term115 n) = (term125 n).
Proof. exact (TRANS (@lem2708516 n) (@lem2708533 n)). Qed.
Lemma lem2708535 (n : int) : (term109 n) = (term126 n).
Proof. exact (MK_COMB (@lem2708513 n) (@lem2708534 n)). Qed.
Lemma lem2708536 (n : int) : (term108 n) = (term126 n).
Proof. exact (TRANS (@lem2708492 n) (@lem2708535 n)). Qed.
Lemma lem2708537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708538 (n : int) : (term127 n) = (term128 n).
Proof. exact (MK_COMB (@lem2708537) (@lem2708489 n)). Qed.
Lemma lem2708539 (n : int) : (term16 n) = (term129 n).
Proof. exact (MK_COMB (@lem2708538 n) (@lem2708536 n)). Qed.
Lemma lem2708540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708541 (n : int) : (term20 n) = (term130 n).
Proof. exact (MK_COMB (@lem2708540) (@lem2708442 n)). Qed.
Lemma lem2708542 (n : int) : (term22 n) = (term131 n).
Proof. exact (MK_COMB (@lem2708541 n) (@lem2708539 n)). Qed.
Lemma lem2708543 (n : int) : (term23 n) = (term131 n).
Proof. exact (TRANS (@lem2708347 n) (@lem2708542 n)). Qed.
Lemma lem2708547 (t : Prop) : (term132 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2708623 (n : int) : (term133 n) = (term131 n).
Proof. exact (@lem2708547 (term131 n)). Qed.
Lemma lem2708624 : (term28 = term32) = (term134 = term32).
Proof. exact (@lem1988293 term28 term32). Qed.
Lemma lem2708630 : term134 = term135.
Proof. exact (@lem1982792 term28 term32). Qed.
Lemma lem2708632 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2708633 : term32 = term137.
Proof. exact (@lem2708632 (NUMERAL 0)). Qed.
Lemma lem2708635 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2708636 : term140 = term141.
Proof. exact (@lem2708635 term67). Qed.
Lemma lem2708637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708638 : term142 = term143.
Proof. exact (MK_COMB (@lem2708637) (@lem2708636)). Qed.
Lemma lem2708639 : term144 = term145.
Proof. exact (MK_COMB (@lem2708638) (@lem2708633)). Qed.
Lemma lem2708640 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2708642 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2708643 : term149 = term150.
Proof. exact (@lem2708642 term67 term67). Qed.
Lemma lem2708644 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708645 : term152 = term67.
Proof. exact (EQ_MP (@lem2708644) (@lem940073)). Qed.
Lemma lem2708646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708647 : term150 = term66.
Proof. exact (MK_COMB (@lem2708646) (@lem2708645)). Qed.
Lemma lem2708648 : term149 = term66.
Proof. exact (TRANS (@lem2708643) (@lem2708647)). Qed.
Lemma lem2708650 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2708651 : term144 = term32.
Proof. exact (@lem2708650 term67). Qed.
Lemma lem2708652 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2708653 : term154 = term155.
Proof. exact (MK_COMB (@lem2708652) (@lem2708651)). Qed.
Lemma lem2708654 : term146 = term137.
Proof. exact (MK_COMB (@lem2708653) (@lem2708648)). Qed.
Lemma lem2708655 : term145 = term137.
Proof. exact (TRANS (@lem2708640) (@lem2708654)). Qed.
Lemma lem2708656 : term144 = term137.
Proof. exact (TRANS (@lem2708639) (@lem2708655)). Qed.
Lemma lem2708658 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2708659 : term137 = term32.
Proof. exact (@lem2708658 term32). Qed.
Lemma lem2708660 : term144 = term32.
Proof. exact (TRANS (@lem2708656) (@lem2708659)). Qed.
Lemma lem2708661 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2708662 : term135 = term158.
Proof. exact (MK_COMB (@lem2708661) (@lem2708660)). Qed.
Lemma lem2708663 : term158 = term28.
Proof. exact (@lem1982723 term28). Qed.
Lemma lem2708664 : term135 = term28.
Proof. exact (TRANS (@lem2708662) (@lem2708663)). Qed.
Lemma lem2708666 : term134 = term28.
Proof. exact (TRANS (@lem2708630) (@lem2708664)). Qed.
Lemma lem2708667 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2708668 : term159 = term31.
Proof. exact (MK_COMB (@lem2708667) (@lem2708666)). Qed.
Lemma lem2708669 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2708670 : (term134 = term32) = (term28 = term32).
Proof. exact (MK_COMB (@lem2708668) (@lem2708669)). Qed.
Lemma lem2708671 : (term28 = term32) = (term28 = term32).
Proof. exact (TRANS (@lem2708624) (@lem2708670)). Qed.
Lemma lem2708672 (n : int) : ((real_of_int n) = (term49 n)) = ((term160 n) = term32).
Proof. exact (@lem1988293 (real_of_int n) (term49 n)). Qed.
Lemma lem2708673 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2708680 (n : int) : (term45 n) = (term161 n).
Proof. exact (@lem1982747 term28 (term162 n)). Qed.
Lemma lem2708681 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2708682 (n : int) : (term47 n) = (term163 n).
Proof. exact (MK_COMB (@lem2708681) (@lem2708680 n)). Qed.
Lemma lem2708685 (n : int) : (term49 n) = (term164 n).
Proof. exact (MK_COMB (@lem2708682 n) (@lem2708673 n)). Qed.
Lemma lem2708688 (n : int) : (term165 n) = (term165 n).
Proof. exact (eq_refl (term165 n)). Qed.
Lemma lem2708689 (n : int) : (term160 n) = (term166 n).
Proof. exact (MK_COMB (@lem2708688 n) (@lem2708685 n)). Qed.
Lemma lem2708690 (n : int) : (term166 n) = (term167 n).
Proof. exact (@lem1982792 (real_of_int n) (term164 n)). Qed.
Lemma lem2708691 (n : int) : (term168 n) = (term169 n).
Proof. exact (@lem1982781 (term161 n) term140 (term48 n)). Qed.
Lemma lem2708692 (n : int) : (term170 n) = (term170 n).
Proof. exact (eq_refl (term170 n)). Qed.
Lemma lem2708693 (n : int) : (term171 n) = (term172 n).
Proof. exact (@lem1982749 term140 term28 (term162 n)). Qed.
Lemma lem2708695 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2708696 : term28 = term173.
Proof. exact (@lem2708695 term29). Qed.
Lemma lem2708698 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2708699 : term140 = term141.
Proof. exact (@lem2708698 term67). Qed.
Lemma lem2708700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708701 : term142 = term143.
Proof. exact (MK_COMB (@lem2708700) (@lem2708699)). Qed.
Lemma lem2708702 : term174 = term175.
Proof. exact (MK_COMB (@lem2708701) (@lem2708696)). Qed.
Lemma lem2708703 : term175 = term176.
Proof. exact (@lem1981613 term140 term28 term66 term66). Qed.
Lemma lem2708705 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2708706 : term149 = term150.
Proof. exact (@lem2708705 term67 term67). Qed.
Lemma lem2708707 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708708 : term152 = term67.
Proof. exact (EQ_MP (@lem2708707) (@lem940073)). Qed.
Lemma lem2708709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708710 : term150 = term66.
Proof. exact (MK_COMB (@lem2708709) (@lem2708708)). Qed.
Lemma lem2708711 : term149 = term66.
Proof. exact (TRANS (@lem2708706) (@lem2708710)). Qed.
Lemma lem2708713 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2708714 : term174 = term179.
Proof. exact (@lem2708713 term67 term29). Qed.
Lemma lem2708715 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2708716 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2708717 : term182 = term29.
Proof. exact (EQ_MP (@lem2708716) (@lem2708715)). Qed.
Lemma lem2708718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708719 : term183 = term28.
Proof. exact (MK_COMB (@lem2708718) (@lem2708717)). Qed.
Lemma lem2708720 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2708721 : term179 = term184.
Proof. exact (MK_COMB (@lem2708720) (@lem2708719)). Qed.
Lemma lem2708722 : term174 = term184.
Proof. exact (TRANS (@lem2708714) (@lem2708721)). Qed.
Lemma lem2708723 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2708724 : term185 = term186.
Proof. exact (MK_COMB (@lem2708723) (@lem2708722)). Qed.
Lemma lem2708725 : term176 = term187.
Proof. exact (MK_COMB (@lem2708724) (@lem2708711)). Qed.
Lemma lem2708726 : term175 = term187.
Proof. exact (TRANS (@lem2708703) (@lem2708725)). Qed.
Lemma lem2708727 : term174 = term187.
Proof. exact (TRANS (@lem2708702) (@lem2708726)). Qed.
Lemma lem2708729 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2708730 : term187 = term184.
Proof. exact (@lem2708729 term184). Qed.
Lemma lem2708731 : term174 = term184.
Proof. exact (TRANS (@lem2708727) (@lem2708730)). Qed.
Lemma lem2708732 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708733 : term188 = term189.
Proof. exact (MK_COMB (@lem2708732) (@lem2708731)). Qed.
Lemma lem2708734 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2708735 (n : int) : (term172 n) = (term190 n).
Proof. exact (MK_COMB (@lem2708733) (@lem2708734 n)). Qed.
Lemma lem2708736 (n : int) : (term171 n) = (term190 n).
Proof. exact (TRANS (@lem2708693 n) (@lem2708735 n)). Qed.
Lemma lem2708737 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2708738 (n : int) : (term191 n) = (term192 n).
Proof. exact (MK_COMB (@lem2708737) (@lem2708736 n)). Qed.
Lemma lem2708739 (n : int) : (term169 n) = (term193 n).
Proof. exact (MK_COMB (@lem2708738 n) (@lem2708692 n)). Qed.
Lemma lem2708740 (n : int) : (term168 n) = (term193 n).
Proof. exact (TRANS (@lem2708691 n) (@lem2708739 n)). Qed.
Lemma lem2708741 (n : int) : (term194 n) = (term194 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem2708744 (n : int) : (term167 n) = (term195 n).
Proof. exact (MK_COMB (@lem2708741 n) (@lem2708740 n)). Qed.
Lemma lem2708745 (n : int) : (term166 n) = (term195 n).
Proof. exact (TRANS (@lem2708690 n) (@lem2708744 n)). Qed.
Lemma lem2708746 (n : int) : (term160 n) = (term195 n).
Proof. exact (TRANS (@lem2708689 n) (@lem2708745 n)). Qed.
Lemma lem2708747 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2708748 (n : int) : (term196 n) = (term197 n).
Proof. exact (MK_COMB (@lem2708747) (@lem2708746 n)). Qed.
Lemma lem2708749 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2708750 (n : int) : ((term160 n) = term32) = ((term195 n) = term32).
Proof. exact (MK_COMB (@lem2708748 n) (@lem2708749)). Qed.
Lemma lem2708751 (n : int) : ((real_of_int n) = (term49 n)) = ((term195 n) = term32).
Proof. exact (TRANS (@lem2708672 n) (@lem2708750 n)). Qed.
Lemma lem2708752 (n : int) : (term56 n) = (term198 n).
Proof. exact (@lem1988287 (term48 n) term32). Qed.
Lemma lem2708758 (n : int) : (term199 n) = (term200 n).
Proof. exact (@lem1982792 (term48 n) term32). Qed.
Lemma lem2708760 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2708761 : term32 = term137.
Proof. exact (@lem2708760 (NUMERAL 0)). Qed.
Lemma lem2708763 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2708764 : term140 = term141.
Proof. exact (@lem2708763 term67). Qed.
Lemma lem2708765 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708766 : term142 = term143.
Proof. exact (MK_COMB (@lem2708765) (@lem2708764)). Qed.
Lemma lem2708767 : term144 = term145.
Proof. exact (MK_COMB (@lem2708766) (@lem2708761)). Qed.
Lemma lem2708768 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2708770 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2708771 : term149 = term150.
Proof. exact (@lem2708770 term67 term67). Qed.
Lemma lem2708772 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708773 : term152 = term67.
Proof. exact (EQ_MP (@lem2708772) (@lem940073)). Qed.
Lemma lem2708774 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708775 : term150 = term66.
Proof. exact (MK_COMB (@lem2708774) (@lem2708773)). Qed.
Lemma lem2708776 : term149 = term66.
Proof. exact (TRANS (@lem2708771) (@lem2708775)). Qed.
Lemma lem2708778 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2708779 : term144 = term32.
Proof. exact (@lem2708778 term67). Qed.
Lemma lem2708780 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2708781 : term154 = term155.
Proof. exact (MK_COMB (@lem2708780) (@lem2708779)). Qed.
Lemma lem2708782 : term146 = term137.
Proof. exact (MK_COMB (@lem2708781) (@lem2708776)). Qed.
Lemma lem2708783 : term145 = term137.
Proof. exact (TRANS (@lem2708768) (@lem2708782)). Qed.
Lemma lem2708784 : term144 = term137.
Proof. exact (TRANS (@lem2708767) (@lem2708783)). Qed.
Lemma lem2708786 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2708787 : term137 = term32.
Proof. exact (@lem2708786 term32). Qed.
Lemma lem2708788 : term144 = term32.
Proof. exact (TRANS (@lem2708784) (@lem2708787)). Qed.
Lemma lem2708789 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2708790 (n : int) : (term200 n) = (term201 n).
Proof. exact (MK_COMB (@lem2708789 n) (@lem2708788)). Qed.
Lemma lem2708791 (n : int) : (term201 n) = (term48 n).
Proof. exact (@lem1982723 (term48 n)). Qed.
Lemma lem2708792 (n : int) : (term200 n) = (term48 n).
Proof. exact (TRANS (@lem2708790 n) (@lem2708791 n)). Qed.
Lemma lem2708794 (n : int) : (term199 n) = (term48 n).
Proof. exact (TRANS (@lem2708758 n) (@lem2708792 n)). Qed.
Lemma lem2708795 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2708796 (n : int) : (term202 n) = (term203 n).
Proof. exact (MK_COMB (@lem2708795) (@lem2708794 n)). Qed.
Lemma lem2708797 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2708798 (n : int) : (term198 n) = (term204 n).
Proof. exact (MK_COMB (@lem2708796 n) (@lem2708797)). Qed.
Lemma lem2708799 (n : int) : (term56 n) = (term204 n).
Proof. exact (TRANS (@lem2708752 n) (@lem2708798 n)). Qed.
Lemma lem2708800 (n : int) : (term77 n) = (term205 n).
Proof. exact (@lem1988287 term76 (term69 n)). Qed.
Lemma lem2708814 (n : int) : (term206 n) = (term207 n).
Proof. exact (@lem1982792 term76 (term69 n)). Qed.
Lemma lem2708815 (n : int) : (term208 n) = (term209 n).
Proof. exact (@lem1982781 (term48 n) term140 term66). Qed.
Lemma lem2708817 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2708818 : term66 = term210.
Proof. exact (@lem2708817 term67). Qed.
Lemma lem2708820 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2708821 : term140 = term141.
Proof. exact (@lem2708820 term67). Qed.
Lemma lem2708822 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708823 : term142 = term143.
Proof. exact (MK_COMB (@lem2708822) (@lem2708821)). Qed.
Lemma lem2708824 : term211 = term212.
Proof. exact (MK_COMB (@lem2708823) (@lem2708818)). Qed.
Lemma lem2708825 : term212 = term213.
Proof. exact (@lem1981613 term140 term66 term66 term66). Qed.
Lemma lem2708827 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2708828 : term149 = term150.
Proof. exact (@lem2708827 term67 term67). Qed.
Lemma lem2708829 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708830 : term152 = term67.
Proof. exact (EQ_MP (@lem2708829) (@lem940073)). Qed.
Lemma lem2708831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708832 : term150 = term66.
Proof. exact (MK_COMB (@lem2708831) (@lem2708830)). Qed.
Lemma lem2708833 : term149 = term66.
Proof. exact (TRANS (@lem2708828) (@lem2708832)). Qed.
Lemma lem2708835 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2708836 : term211 = term214.
Proof. exact (@lem2708835 term67 term67). Qed.
Lemma lem2708837 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708838 : term152 = term67.
Proof. exact (EQ_MP (@lem2708837) (@lem940073)). Qed.
Lemma lem2708839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708840 : term150 = term66.
Proof. exact (MK_COMB (@lem2708839) (@lem2708838)). Qed.
Lemma lem2708841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2708842 : term214 = term140.
Proof. exact (MK_COMB (@lem2708841) (@lem2708840)). Qed.
Lemma lem2708843 : term211 = term140.
Proof. exact (TRANS (@lem2708836) (@lem2708842)). Qed.
Lemma lem2708844 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2708845 : term215 = term216.
Proof. exact (MK_COMB (@lem2708844) (@lem2708843)). Qed.
Lemma lem2708846 : term213 = term141.
Proof. exact (MK_COMB (@lem2708845) (@lem2708833)). Qed.
Lemma lem2708847 : term212 = term141.
Proof. exact (TRANS (@lem2708825) (@lem2708846)). Qed.
Lemma lem2708848 : term211 = term141.
Proof. exact (TRANS (@lem2708824) (@lem2708847)). Qed.
Lemma lem2708850 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2708851 : term141 = term140.
Proof. exact (@lem2708850 term140). Qed.
Lemma lem2708852 : term211 = term140.
Proof. exact (TRANS (@lem2708848) (@lem2708851)). Qed.
Lemma lem2708855 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2708856 (n : int) : (term209 n) = (term218 n).
Proof. exact (MK_COMB (@lem2708855 n) (@lem2708852)). Qed.
Lemma lem2708857 (n : int) : (term208 n) = (term218 n).
Proof. exact (TRANS (@lem2708815 n) (@lem2708856 n)). Qed.
Lemma lem2708858 : term219 = term219.
Proof. exact (eq_refl term219). Qed.
Lemma lem2708861 (n : int) : (term207 n) = (term220 n).
Proof. exact (MK_COMB (@lem2708858) (@lem2708857 n)). Qed.
Lemma lem2708863 (n : int) : (term206 n) = (term220 n).
Proof. exact (TRANS (@lem2708814 n) (@lem2708861 n)). Qed.
Lemma lem2708864 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2708865 (n : int) : (term221 n) = (term222 n).
Proof. exact (MK_COMB (@lem2708864) (@lem2708863 n)). Qed.
Lemma lem2708866 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2708867 (n : int) : (term205 n) = (term223 n).
Proof. exact (MK_COMB (@lem2708865 n) (@lem2708866)). Qed.
Lemma lem2708868 (n : int) : (term77 n) = (term223 n).
Proof. exact (TRANS (@lem2708800 n) (@lem2708867 n)). Qed.
Lemma lem2708869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708870 (n : int) : (term79 n) = (term224 n).
Proof. exact (MK_COMB (@lem2708869) (@lem2708799 n)). Qed.
Lemma lem2708871 (n : int) : (term81 n) = (term225 n).
Proof. exact (MK_COMB (@lem2708870 n) (@lem2708868 n)). Qed.
Lemma lem2708872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2708873 (n : int) : (term83 n) = (term226 n).
Proof. exact (MK_COMB (@lem2708872) (@lem2708751 n)). Qed.
Lemma lem2708874 (n : int) : (term84 n) = (term227 n).
Proof. exact (MK_COMB (@lem2708873 n) (@lem2708871 n)). Qed.
Lemma lem2708875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2708876 : term85 = term85.
Proof. exact (MK_COMB (@lem2708875) (@lem2708671)). Qed.
Lemma lem2708877 (n : int) : (term86 n) = (term228 n).
Proof. exact (MK_COMB (@lem2708876) (@lem2708874 n)). Qed.
Lemma lem2708878 (n : int) : (term93 n) = (term229 n).
Proof. exact (@lem1988287 term32 (term69 n)). Qed.
Lemma lem2708890 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982792 term32 (term69 n)). Qed.
Lemma lem2708891 (n : int) : (term208 n) = (term209 n).
Proof. exact (@lem1982781 (term48 n) term140 term66). Qed.
Lemma lem2708893 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2708894 : term66 = term210.
Proof. exact (@lem2708893 term67). Qed.
Lemma lem2708896 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2708897 : term140 = term141.
Proof. exact (@lem2708896 term67). Qed.
Lemma lem2708898 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708899 : term142 = term143.
Proof. exact (MK_COMB (@lem2708898) (@lem2708897)). Qed.
Lemma lem2708900 : term211 = term212.
Proof. exact (MK_COMB (@lem2708899) (@lem2708894)). Qed.
Lemma lem2708901 : term212 = term213.
Proof. exact (@lem1981613 term140 term66 term66 term66). Qed.
Lemma lem2708903 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2708904 : term149 = term150.
Proof. exact (@lem2708903 term67 term67). Qed.
Lemma lem2708905 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708906 : term152 = term67.
Proof. exact (EQ_MP (@lem2708905) (@lem940073)). Qed.
Lemma lem2708907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708908 : term150 = term66.
Proof. exact (MK_COMB (@lem2708907) (@lem2708906)). Qed.
Lemma lem2708909 : term149 = term66.
Proof. exact (TRANS (@lem2708904) (@lem2708908)). Qed.
Lemma lem2708911 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2708912 : term211 = term214.
Proof. exact (@lem2708911 term67 term67). Qed.
Lemma lem2708913 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708914 : term152 = term67.
Proof. exact (EQ_MP (@lem2708913) (@lem940073)). Qed.
Lemma lem2708915 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708916 : term150 = term66.
Proof. exact (MK_COMB (@lem2708915) (@lem2708914)). Qed.
Lemma lem2708917 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2708918 : term214 = term140.
Proof. exact (MK_COMB (@lem2708917) (@lem2708916)). Qed.
Lemma lem2708919 : term211 = term140.
Proof. exact (TRANS (@lem2708912) (@lem2708918)). Qed.
Lemma lem2708920 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2708921 : term215 = term216.
Proof. exact (MK_COMB (@lem2708920) (@lem2708919)). Qed.
Lemma lem2708922 : term213 = term141.
Proof. exact (MK_COMB (@lem2708921) (@lem2708909)). Qed.
Lemma lem2708923 : term212 = term141.
Proof. exact (TRANS (@lem2708901) (@lem2708922)). Qed.
Lemma lem2708924 : term211 = term141.
Proof. exact (TRANS (@lem2708900) (@lem2708923)). Qed.
Lemma lem2708926 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2708927 : term141 = term140.
Proof. exact (@lem2708926 term140). Qed.
Lemma lem2708928 : term211 = term140.
Proof. exact (TRANS (@lem2708924) (@lem2708927)). Qed.
Lemma lem2708931 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2708932 (n : int) : (term209 n) = (term218 n).
Proof. exact (MK_COMB (@lem2708931 n) (@lem2708928)). Qed.
Lemma lem2708933 (n : int) : (term208 n) = (term218 n).
Proof. exact (TRANS (@lem2708891 n) (@lem2708932 n)). Qed.
Lemma lem2708934 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem2708935 (n : int) : (term231 n) = (term232 n).
Proof. exact (MK_COMB (@lem2708934) (@lem2708933 n)). Qed.
Lemma lem2708936 (n : int) : (term232 n) = (term218 n).
Proof. exact (@lem1982721 (term218 n)). Qed.
Lemma lem2708937 (n : int) : (term231 n) = (term218 n).
Proof. exact (TRANS (@lem2708935 n) (@lem2708936 n)). Qed.
Lemma lem2708939 (n : int) : (term230 n) = (term218 n).
Proof. exact (TRANS (@lem2708890 n) (@lem2708937 n)). Qed.
Lemma lem2708940 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2708941 (n : int) : (term233 n) = (term234 n).
Proof. exact (MK_COMB (@lem2708940) (@lem2708939 n)). Qed.
Lemma lem2708942 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2708943 (n : int) : (term229 n) = (term235 n).
Proof. exact (MK_COMB (@lem2708941 n) (@lem2708942)). Qed.
Lemma lem2708944 (n : int) : (term93 n) = (term235 n).
Proof. exact (TRANS (@lem2708878 n) (@lem2708943 n)). Qed.
Lemma lem2708945 (n : int) : (term106 n) = (term236 n).
Proof. exact (@lem1988287 (term48 n) term103). Qed.
Lemma lem2708952 : term103 = term66.
Proof. exact (@lem1982721 term66). Qed.
Lemma lem2708955 (n : int) : (term237 n) = (term237 n).
Proof. exact (eq_refl (term237 n)). Qed.
Lemma lem2708956 (n : int) : (term238 n) = (term239 n).
Proof. exact (MK_COMB (@lem2708955 n) (@lem2708952)). Qed.
Lemma lem2708957 (n : int) : (term239 n) = (term240 n).
Proof. exact (@lem1982792 (term48 n) term66). Qed.
Lemma lem2708959 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2708960 : term66 = term210.
Proof. exact (@lem2708959 term67). Qed.
Lemma lem2708962 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2708963 : term140 = term141.
Proof. exact (@lem2708962 term67). Qed.
Lemma lem2708964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2708965 : term142 = term143.
Proof. exact (MK_COMB (@lem2708964) (@lem2708963)). Qed.
Lemma lem2708966 : term211 = term212.
Proof. exact (MK_COMB (@lem2708965) (@lem2708960)). Qed.
Lemma lem2708967 : term212 = term213.
Proof. exact (@lem1981613 term140 term66 term66 term66). Qed.
Lemma lem2708969 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2708970 : term149 = term150.
Proof. exact (@lem2708969 term67 term67). Qed.
Lemma lem2708971 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708972 : term152 = term67.
Proof. exact (EQ_MP (@lem2708971) (@lem940073)). Qed.
Lemma lem2708973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708974 : term150 = term66.
Proof. exact (MK_COMB (@lem2708973) (@lem2708972)). Qed.
Lemma lem2708975 : term149 = term66.
Proof. exact (TRANS (@lem2708970) (@lem2708974)). Qed.
Lemma lem2708977 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2708978 : term211 = term214.
Proof. exact (@lem2708977 term67 term67). Qed.
Lemma lem2708979 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2708980 : term152 = term67.
Proof. exact (EQ_MP (@lem2708979) (@lem940073)). Qed.
Lemma lem2708981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2708982 : term150 = term66.
Proof. exact (MK_COMB (@lem2708981) (@lem2708980)). Qed.
Lemma lem2708983 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2708984 : term214 = term140.
Proof. exact (MK_COMB (@lem2708983) (@lem2708982)). Qed.
Lemma lem2708985 : term211 = term140.
Proof. exact (TRANS (@lem2708978) (@lem2708984)). Qed.
Lemma lem2708986 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2708987 : term215 = term216.
Proof. exact (MK_COMB (@lem2708986) (@lem2708985)). Qed.
Lemma lem2708988 : term213 = term141.
Proof. exact (MK_COMB (@lem2708987) (@lem2708975)). Qed.
Lemma lem2708989 : term212 = term141.
Proof. exact (TRANS (@lem2708967) (@lem2708988)). Qed.
Lemma lem2708990 : term211 = term141.
Proof. exact (TRANS (@lem2708966) (@lem2708989)). Qed.
Lemma lem2708992 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2708993 : term141 = term140.
Proof. exact (@lem2708992 term140). Qed.
Lemma lem2708994 : term211 = term140.
Proof. exact (TRANS (@lem2708990) (@lem2708993)). Qed.
Lemma lem2708995 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2708998 (n : int) : (term240 n) = (term241 n).
Proof. exact (MK_COMB (@lem2708995 n) (@lem2708994)). Qed.
Lemma lem2708999 (n : int) : (term239 n) = (term241 n).
Proof. exact (TRANS (@lem2708957 n) (@lem2708998 n)). Qed.
Lemma lem2709000 (n : int) : (term238 n) = (term241 n).
Proof. exact (TRANS (@lem2708956 n) (@lem2708999 n)). Qed.
Lemma lem2709001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709002 (n : int) : (term242 n) = (term243 n).
Proof. exact (MK_COMB (@lem2709001) (@lem2709000 n)). Qed.
Lemma lem2709003 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709004 (n : int) : (term236 n) = (term244 n).
Proof. exact (MK_COMB (@lem2709002 n) (@lem2709003)). Qed.
Lemma lem2709005 (n : int) : (term106 n) = (term244 n).
Proof. exact (TRANS (@lem2708945 n) (@lem2709004 n)). Qed.
Lemma lem2709006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709007 (n : int) : (term95 n) = (term245 n).
Proof. exact (MK_COMB (@lem2709006) (@lem2708944 n)). Qed.
Lemma lem2709008 (n : int) : (term107 n) = (term246 n).
Proof. exact (MK_COMB (@lem2709007 n) (@lem2709005 n)). Qed.
Lemma lem2709009 (n : int) : (term112 n) = (term247 n).
Proof. exact (@lem1988287 term66 (term69 n)). Qed.
Lemma lem2709021 (n : int) : (term248 n) = (term249 n).
Proof. exact (@lem1982792 term66 (term69 n)). Qed.
Lemma lem2709022 (n : int) : (term208 n) = (term209 n).
Proof. exact (@lem1982781 (term48 n) term140 term66). Qed.
Lemma lem2709024 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709025 : term66 = term210.
Proof. exact (@lem2709024 term67). Qed.
Lemma lem2709027 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709028 : term140 = term141.
Proof. exact (@lem2709027 term67). Qed.
Lemma lem2709029 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709030 : term142 = term143.
Proof. exact (MK_COMB (@lem2709029) (@lem2709028)). Qed.
Lemma lem2709031 : term211 = term212.
Proof. exact (MK_COMB (@lem2709030) (@lem2709025)). Qed.
Lemma lem2709032 : term212 = term213.
Proof. exact (@lem1981613 term140 term66 term66 term66). Qed.
Lemma lem2709034 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709035 : term149 = term150.
Proof. exact (@lem2709034 term67 term67). Qed.
Lemma lem2709036 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709037 : term152 = term67.
Proof. exact (EQ_MP (@lem2709036) (@lem940073)). Qed.
Lemma lem2709038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709039 : term150 = term66.
Proof. exact (MK_COMB (@lem2709038) (@lem2709037)). Qed.
Lemma lem2709040 : term149 = term66.
Proof. exact (TRANS (@lem2709035) (@lem2709039)). Qed.
Lemma lem2709042 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2709043 : term211 = term214.
Proof. exact (@lem2709042 term67 term67). Qed.
Lemma lem2709044 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709045 : term152 = term67.
Proof. exact (EQ_MP (@lem2709044) (@lem940073)). Qed.
Lemma lem2709046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709047 : term150 = term66.
Proof. exact (MK_COMB (@lem2709046) (@lem2709045)). Qed.
Lemma lem2709048 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2709049 : term214 = term140.
Proof. exact (MK_COMB (@lem2709048) (@lem2709047)). Qed.
Lemma lem2709050 : term211 = term140.
Proof. exact (TRANS (@lem2709043) (@lem2709049)). Qed.
Lemma lem2709051 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709052 : term215 = term216.
Proof. exact (MK_COMB (@lem2709051) (@lem2709050)). Qed.
Lemma lem2709053 : term213 = term141.
Proof. exact (MK_COMB (@lem2709052) (@lem2709040)). Qed.
Lemma lem2709054 : term212 = term141.
Proof. exact (TRANS (@lem2709032) (@lem2709053)). Qed.
Lemma lem2709055 : term211 = term141.
Proof. exact (TRANS (@lem2709031) (@lem2709054)). Qed.
Lemma lem2709057 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709058 : term141 = term140.
Proof. exact (@lem2709057 term140). Qed.
Lemma lem2709059 : term211 = term140.
Proof. exact (TRANS (@lem2709055) (@lem2709058)). Qed.
Lemma lem2709062 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2709063 (n : int) : (term209 n) = (term218 n).
Proof. exact (MK_COMB (@lem2709062 n) (@lem2709059)). Qed.
Lemma lem2709064 (n : int) : (term208 n) = (term218 n).
Proof. exact (TRANS (@lem2709022 n) (@lem2709063 n)). Qed.
Lemma lem2709065 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem2709066 (n : int) : (term249 n) = (term250 n).
Proof. exact (MK_COMB (@lem2709065) (@lem2709064 n)). Qed.
Lemma lem2709067 (n : int) : (term250 n) = (term251 n).
Proof. exact (@lem1982757 (term170 n) term66 term140). Qed.
Lemma lem2709069 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709070 : term140 = term141.
Proof. exact (@lem2709069 term67). Qed.
Lemma lem2709072 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709073 : term66 = term210.
Proof. exact (@lem2709072 term67). Qed.
Lemma lem2709074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709075 : term121 = term252.
Proof. exact (MK_COMB (@lem2709074) (@lem2709073)). Qed.
Lemma lem2709076 : term253 = term254.
Proof. exact (MK_COMB (@lem2709075) (@lem2709070)). Qed.
Lemma lem2709077 : term255.
Proof. exact (@lem1981473 term66 term66 term140 term66 term32 term66). Qed.
Lemma lem2709079 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709080 : term257 = term258.
Proof. exact (@lem2709079 (NUMERAL 0) term67). Qed.
Lemma lem2709081 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709082 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709083 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709082 h1) (fun h1 : term258 = True => @lem2709081)). Qed.
Lemma lem2709084 : term258 = True.
Proof. exact (EQ_MP (@lem2709083) (@lem2709081)). Qed.
Lemma lem2709085 : term257 = True.
Proof. exact (TRANS (@lem2709080) (@lem2709084)). Qed.
Lemma lem2709086 : True = term257.
Proof. exact (SYM (@lem2709085)). Qed.
Lemma lem2709087 : term257.
Proof. exact (EQ_MP (@lem2709086) (@lem0)). Qed.
Lemma lem2709088 : term260.
Proof. exact (@lem2709077 (@lem2709087)). Qed.
Lemma lem2709090 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709091 : term257 = term258.
Proof. exact (@lem2709090 (NUMERAL 0) term67). Qed.
Lemma lem2709092 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709093 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709094 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709093 h1) (fun h1 : term258 = True => @lem2709092)). Qed.
Lemma lem2709095 : term258 = True.
Proof. exact (EQ_MP (@lem2709094) (@lem2709092)). Qed.
Lemma lem2709096 : term257 = True.
Proof. exact (TRANS (@lem2709091) (@lem2709095)). Qed.
Lemma lem2709097 : True = term257.
Proof. exact (SYM (@lem2709096)). Qed.
Lemma lem2709098 : term257.
Proof. exact (EQ_MP (@lem2709097) (@lem0)). Qed.
Lemma lem2709099 : term261.
Proof. exact (@lem2709088 (@lem2709098)). Qed.
Lemma lem2709101 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709102 : term257 = term258.
Proof. exact (@lem2709101 (NUMERAL 0) term67). Qed.
Lemma lem2709103 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709104 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709105 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709104 h1) (fun h1 : term258 = True => @lem2709103)). Qed.
Lemma lem2709106 : term258 = True.
Proof. exact (EQ_MP (@lem2709105) (@lem2709103)). Qed.
Lemma lem2709107 : term257 = True.
Proof. exact (TRANS (@lem2709102) (@lem2709106)). Qed.
Lemma lem2709108 : True = term257.
Proof. exact (SYM (@lem2709107)). Qed.
Lemma lem2709109 : term257.
Proof. exact (EQ_MP (@lem2709108) (@lem0)). Qed.
Lemma lem2709110 : term262.
Proof. exact (@lem2709099 (@lem2709109)). Qed.
Lemma lem2709112 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2709113 : term211 = term214.
Proof. exact (@lem2709112 term67 term67). Qed.
Lemma lem2709114 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709115 : term152 = term67.
Proof. exact (EQ_MP (@lem2709114) (@lem940073)). Qed.
Lemma lem2709116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709117 : term150 = term66.
Proof. exact (MK_COMB (@lem2709116) (@lem2709115)). Qed.
Lemma lem2709118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2709119 : term214 = term140.
Proof. exact (MK_COMB (@lem2709118) (@lem2709117)). Qed.
Lemma lem2709120 : term211 = term140.
Proof. exact (TRANS (@lem2709113) (@lem2709119)). Qed.
Lemma lem2709122 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709123 : term149 = term150.
Proof. exact (@lem2709122 term67 term67). Qed.
Lemma lem2709124 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709125 : term152 = term67.
Proof. exact (EQ_MP (@lem2709124) (@lem940073)). Qed.
Lemma lem2709126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709127 : term150 = term66.
Proof. exact (MK_COMB (@lem2709126) (@lem2709125)). Qed.
Lemma lem2709128 : term149 = term66.
Proof. exact (TRANS (@lem2709123) (@lem2709127)). Qed.
Lemma lem2709129 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709130 : term263 = term121.
Proof. exact (MK_COMB (@lem2709129) (@lem2709128)). Qed.
Lemma lem2709131 : term264 = term253.
Proof. exact (MK_COMB (@lem2709130) (@lem2709120)). Qed.
Lemma lem2709133 (m : nat) : (term265 m) = term32.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2709134 : term253 = term32.
Proof. exact (@lem2709133 term67). Qed.
Lemma lem2709135 : term264 = term32.
Proof. exact (TRANS (@lem2709131) (@lem2709134)). Qed.
Lemma lem2709136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709137 : term266 = term267.
Proof. exact (MK_COMB (@lem2709136) (@lem2709135)). Qed.
Lemma lem2709138 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2709139 : term268 = term269.
Proof. exact (MK_COMB (@lem2709137) (@lem2709138)). Qed.
Lemma lem2709141 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2709142 : term269 = term32.
Proof. exact (@lem2709141 term67). Qed.
Lemma lem2709143 : term268 = term32.
Proof. exact (TRANS (@lem2709139) (@lem2709142)). Qed.
Lemma lem2709145 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709146 : term149 = term150.
Proof. exact (@lem2709145 term67 term67). Qed.
Lemma lem2709147 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709148 : term152 = term67.
Proof. exact (EQ_MP (@lem2709147) (@lem940073)). Qed.
Lemma lem2709149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709150 : term150 = term66.
Proof. exact (MK_COMB (@lem2709149) (@lem2709148)). Qed.
Lemma lem2709151 : term149 = term66.
Proof. exact (TRANS (@lem2709146) (@lem2709150)). Qed.
Lemma lem2709152 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2709153 : term271 = term269.
Proof. exact (MK_COMB (@lem2709152) (@lem2709151)). Qed.
Lemma lem2709155 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2709156 : term269 = term32.
Proof. exact (@lem2709155 term67). Qed.
Lemma lem2709157 : term271 = term32.
Proof. exact (TRANS (@lem2709153) (@lem2709156)). Qed.
Lemma lem2709158 : term32 = term271.
Proof. exact (SYM (@lem2709157)). Qed.
Lemma lem2709159 : term268 = term271.
Proof. exact (TRANS (@lem2709143) (@lem2709158)). Qed.
Lemma lem2709160 : term254 = term137.
Proof. exact (@lem2709110 (@lem2709159)). Qed.
Lemma lem2709161 : term253 = term137.
Proof. exact (TRANS (@lem2709076) (@lem2709160)). Qed.
Lemma lem2709163 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2709164 : term137 = term32.
Proof. exact (@lem2709163 term32). Qed.
Lemma lem2709165 : term253 = term32.
Proof. exact (TRANS (@lem2709161) (@lem2709164)). Qed.
Lemma lem2709166 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2709167 (n : int) : (term251 n) = (term272 n).
Proof. exact (MK_COMB (@lem2709166 n) (@lem2709165)). Qed.
Lemma lem2709168 (n : int) : (term250 n) = (term272 n).
Proof. exact (TRANS (@lem2709067 n) (@lem2709167 n)). Qed.
Lemma lem2709169 (n : int) : (term272 n) = (term170 n).
Proof. exact (@lem1982723 (term170 n)). Qed.
Lemma lem2709170 (n : int) : (term250 n) = (term170 n).
Proof. exact (TRANS (@lem2709168 n) (@lem2709169 n)). Qed.
Lemma lem2709171 (n : int) : (term249 n) = (term170 n).
Proof. exact (TRANS (@lem2709066 n) (@lem2709170 n)). Qed.
Lemma lem2709173 (n : int) : (term248 n) = (term170 n).
Proof. exact (TRANS (@lem2709021 n) (@lem2709171 n)). Qed.
Lemma lem2709174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709175 (n : int) : (term273 n) = (term274 n).
Proof. exact (MK_COMB (@lem2709174) (@lem2709173 n)). Qed.
Lemma lem2709176 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709177 (n : int) : (term247 n) = (term275 n).
Proof. exact (MK_COMB (@lem2709175 n) (@lem2709176)). Qed.
Lemma lem2709178 (n : int) : (term112 n) = (term275 n).
Proof. exact (TRANS (@lem2709009 n) (@lem2709177 n)). Qed.
Lemma lem2709179 (n : int) : (term125 n) = (term276 n).
Proof. exact (@lem1988287 (term48 n) term122). Qed.
Lemma lem2709186 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709187 : term66 = term210.
Proof. exact (@lem2709186 term67). Qed.
Lemma lem2709189 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709190 : term66 = term210.
Proof. exact (@lem2709189 term67). Qed.
Lemma lem2709191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709192 : term121 = term252.
Proof. exact (MK_COMB (@lem2709191) (@lem2709190)). Qed.
Lemma lem2709193 : term122 = term277.
Proof. exact (MK_COMB (@lem2709192) (@lem2709187)). Qed.
Lemma lem2709194 : term278.
Proof. exact (@lem1981473 term66 term66 term66 term66 term28 term66). Qed.
Lemma lem2709196 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709197 : term257 = term258.
Proof. exact (@lem2709196 (NUMERAL 0) term67). Qed.
Lemma lem2709198 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709199 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709200 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709199 h1) (fun h1 : term258 = True => @lem2709198)). Qed.
Lemma lem2709201 : term258 = True.
Proof. exact (EQ_MP (@lem2709200) (@lem2709198)). Qed.
Lemma lem2709202 : term257 = True.
Proof. exact (TRANS (@lem2709197) (@lem2709201)). Qed.
Lemma lem2709203 : True = term257.
Proof. exact (SYM (@lem2709202)). Qed.
Lemma lem2709204 : term257.
Proof. exact (EQ_MP (@lem2709203) (@lem0)). Qed.
Lemma lem2709205 : term279.
Proof. exact (@lem2709194 (@lem2709204)). Qed.
Lemma lem2709207 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709208 : term257 = term258.
Proof. exact (@lem2709207 (NUMERAL 0) term67). Qed.
Lemma lem2709209 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709210 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709211 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709210 h1) (fun h1 : term258 = True => @lem2709209)). Qed.
Lemma lem2709212 : term258 = True.
Proof. exact (EQ_MP (@lem2709211) (@lem2709209)). Qed.
Lemma lem2709213 : term257 = True.
Proof. exact (TRANS (@lem2709208) (@lem2709212)). Qed.
Lemma lem2709214 : True = term257.
Proof. exact (SYM (@lem2709213)). Qed.
Lemma lem2709215 : term257.
Proof. exact (EQ_MP (@lem2709214) (@lem0)). Qed.
Lemma lem2709216 : term280.
Proof. exact (@lem2709205 (@lem2709215)). Qed.
Lemma lem2709218 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709219 : term257 = term258.
Proof. exact (@lem2709218 (NUMERAL 0) term67). Qed.
Lemma lem2709220 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709221 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709222 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709221 h1) (fun h1 : term258 = True => @lem2709220)). Qed.
Lemma lem2709223 : term258 = True.
Proof. exact (EQ_MP (@lem2709222) (@lem2709220)). Qed.
Lemma lem2709224 : term257 = True.
Proof. exact (TRANS (@lem2709219) (@lem2709223)). Qed.
Lemma lem2709225 : True = term257.
Proof. exact (SYM (@lem2709224)). Qed.
Lemma lem2709226 : term257.
Proof. exact (EQ_MP (@lem2709225) (@lem0)). Qed.
Lemma lem2709227 : term281.
Proof. exact (@lem2709216 (@lem2709226)). Qed.
Lemma lem2709229 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709230 : term149 = term150.
Proof. exact (@lem2709229 term67 term67). Qed.
Lemma lem2709231 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709232 : term152 = term67.
Proof. exact (EQ_MP (@lem2709231) (@lem940073)). Qed.
Lemma lem2709233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709234 : term150 = term66.
Proof. exact (MK_COMB (@lem2709233) (@lem2709232)). Qed.
Lemma lem2709235 : term149 = term66.
Proof. exact (TRANS (@lem2709230) (@lem2709234)). Qed.
Lemma lem2709237 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709238 : term149 = term150.
Proof. exact (@lem2709237 term67 term67). Qed.
Lemma lem2709239 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709240 : term152 = term67.
Proof. exact (EQ_MP (@lem2709239) (@lem940073)). Qed.
Lemma lem2709241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709242 : term150 = term66.
Proof. exact (MK_COMB (@lem2709241) (@lem2709240)). Qed.
Lemma lem2709243 : term149 = term66.
Proof. exact (TRANS (@lem2709238) (@lem2709242)). Qed.
Lemma lem2709244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709245 : term263 = term121.
Proof. exact (MK_COMB (@lem2709244) (@lem2709243)). Qed.
Lemma lem2709246 : term282 = term122.
Proof. exact (MK_COMB (@lem2709245) (@lem2709235)). Qed.
Lemma lem2709247 : term122 = term283.
Proof. exact (@lem1367770 term67 term67). Qed.
Lemma lem2709248 : term284 = term181.
Proof. exact (@lem706885). Qed.
Lemma lem2709249 : (term284 = term181) = (term285 = term29).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term181). Qed.
Lemma lem2709250 : term285 = term29.
Proof. exact (EQ_MP (@lem2709249) (@lem2709248)). Qed.
Lemma lem2709251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709252 : term283 = term28.
Proof. exact (MK_COMB (@lem2709251) (@lem2709250)). Qed.
Lemma lem2709253 : term122 = term28.
Proof. exact (TRANS (@lem2709247) (@lem2709252)). Qed.
Lemma lem2709254 : term282 = term28.
Proof. exact (TRANS (@lem2709246) (@lem2709253)). Qed.
Lemma lem2709255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709256 : term286 = term287.
Proof. exact (MK_COMB (@lem2709255) (@lem2709254)). Qed.
Lemma lem2709257 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2709258 : term288 = term289.
Proof. exact (MK_COMB (@lem2709256) (@lem2709257)). Qed.
Lemma lem2709260 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709261 : term289 = term290.
Proof. exact (@lem2709260 term29 term67). Qed.
Lemma lem2709262 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2709263 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2709264 : term292 = term29.
Proof. exact (EQ_MP (@lem2709263) (@lem2709262)). Qed.
Lemma lem2709265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709266 : term290 = term28.
Proof. exact (MK_COMB (@lem2709265) (@lem2709264)). Qed.
Lemma lem2709267 : term289 = term28.
Proof. exact (TRANS (@lem2709261) (@lem2709266)). Qed.
Lemma lem2709268 : term288 = term28.
Proof. exact (TRANS (@lem2709258) (@lem2709267)). Qed.
Lemma lem2709270 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709271 : term149 = term150.
Proof. exact (@lem2709270 term67 term67). Qed.
Lemma lem2709272 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709273 : term152 = term67.
Proof. exact (EQ_MP (@lem2709272) (@lem940073)). Qed.
Lemma lem2709274 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709275 : term150 = term66.
Proof. exact (MK_COMB (@lem2709274) (@lem2709273)). Qed.
Lemma lem2709276 : term149 = term66.
Proof. exact (TRANS (@lem2709271) (@lem2709275)). Qed.
Lemma lem2709277 : term287 = term287.
Proof. exact (eq_refl term287). Qed.
Lemma lem2709278 : term293 = term289.
Proof. exact (MK_COMB (@lem2709277) (@lem2709276)). Qed.
Lemma lem2709280 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709281 : term289 = term290.
Proof. exact (@lem2709280 term29 term67). Qed.
Lemma lem2709282 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2709283 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2709284 : term292 = term29.
Proof. exact (EQ_MP (@lem2709283) (@lem2709282)). Qed.
Lemma lem2709285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709286 : term290 = term28.
Proof. exact (MK_COMB (@lem2709285) (@lem2709284)). Qed.
Lemma lem2709287 : term289 = term28.
Proof. exact (TRANS (@lem2709281) (@lem2709286)). Qed.
Lemma lem2709288 : term293 = term28.
Proof. exact (TRANS (@lem2709278) (@lem2709287)). Qed.
Lemma lem2709289 : term28 = term293.
Proof. exact (SYM (@lem2709288)). Qed.
Lemma lem2709290 : term288 = term293.
Proof. exact (TRANS (@lem2709268) (@lem2709289)). Qed.
Lemma lem2709291 : term277 = term173.
Proof. exact (@lem2709227 (@lem2709290)). Qed.
Lemma lem2709292 : term122 = term173.
Proof. exact (TRANS (@lem2709193) (@lem2709291)). Qed.
Lemma lem2709294 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2709295 : term173 = term28.
Proof. exact (@lem2709294 term28). Qed.
Lemma lem2709297 : term122 = term28.
Proof. exact (TRANS (@lem2709292) (@lem2709295)). Qed.
Lemma lem2709300 (n : int) : (term237 n) = (term237 n).
Proof. exact (eq_refl (term237 n)). Qed.
Lemma lem2709301 (n : int) : (term294 n) = (term295 n).
Proof. exact (MK_COMB (@lem2709300 n) (@lem2709297)). Qed.
Lemma lem2709302 (n : int) : (term295 n) = (term296 n).
Proof. exact (@lem1982792 (term48 n) term28). Qed.
Lemma lem2709304 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709305 : term28 = term173.
Proof. exact (@lem2709304 term29). Qed.
Lemma lem2709307 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709308 : term140 = term141.
Proof. exact (@lem2709307 term67). Qed.
Lemma lem2709309 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709310 : term142 = term143.
Proof. exact (MK_COMB (@lem2709309) (@lem2709308)). Qed.
Lemma lem2709311 : term174 = term175.
Proof. exact (MK_COMB (@lem2709310) (@lem2709305)). Qed.
Lemma lem2709312 : term175 = term176.
Proof. exact (@lem1981613 term140 term28 term66 term66). Qed.
Lemma lem2709314 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709315 : term149 = term150.
Proof. exact (@lem2709314 term67 term67). Qed.
Lemma lem2709316 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709317 : term152 = term67.
Proof. exact (EQ_MP (@lem2709316) (@lem940073)). Qed.
Lemma lem2709318 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709319 : term150 = term66.
Proof. exact (MK_COMB (@lem2709318) (@lem2709317)). Qed.
Lemma lem2709320 : term149 = term66.
Proof. exact (TRANS (@lem2709315) (@lem2709319)). Qed.
Lemma lem2709322 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2709323 : term174 = term179.
Proof. exact (@lem2709322 term67 term29). Qed.
Lemma lem2709324 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2709325 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2709326 : term182 = term29.
Proof. exact (EQ_MP (@lem2709325) (@lem2709324)). Qed.
Lemma lem2709327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709328 : term183 = term28.
Proof. exact (MK_COMB (@lem2709327) (@lem2709326)). Qed.
Lemma lem2709329 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2709330 : term179 = term184.
Proof. exact (MK_COMB (@lem2709329) (@lem2709328)). Qed.
Lemma lem2709331 : term174 = term184.
Proof. exact (TRANS (@lem2709323) (@lem2709330)). Qed.
Lemma lem2709332 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709333 : term185 = term186.
Proof. exact (MK_COMB (@lem2709332) (@lem2709331)). Qed.
Lemma lem2709334 : term176 = term187.
Proof. exact (MK_COMB (@lem2709333) (@lem2709320)). Qed.
Lemma lem2709335 : term175 = term187.
Proof. exact (TRANS (@lem2709312) (@lem2709334)). Qed.
Lemma lem2709336 : term174 = term187.
Proof. exact (TRANS (@lem2709311) (@lem2709335)). Qed.
Lemma lem2709338 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709339 : term187 = term184.
Proof. exact (@lem2709338 term184). Qed.
Lemma lem2709340 : term174 = term184.
Proof. exact (TRANS (@lem2709336) (@lem2709339)). Qed.
Lemma lem2709341 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2709344 (n : int) : (term296 n) = (term297 n).
Proof. exact (MK_COMB (@lem2709341 n) (@lem2709340)). Qed.
Lemma lem2709345 (n : int) : (term295 n) = (term297 n).
Proof. exact (TRANS (@lem2709302 n) (@lem2709344 n)). Qed.
Lemma lem2709346 (n : int) : (term294 n) = (term297 n).
Proof. exact (TRANS (@lem2709301 n) (@lem2709345 n)). Qed.
Lemma lem2709347 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709348 (n : int) : (term298 n) = (term299 n).
Proof. exact (MK_COMB (@lem2709347) (@lem2709346 n)). Qed.
Lemma lem2709349 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709350 (n : int) : (term276 n) = (term300 n).
Proof. exact (MK_COMB (@lem2709348 n) (@lem2709349)). Qed.
Lemma lem2709351 (n : int) : (term125 n) = (term300 n).
Proof. exact (TRANS (@lem2709179 n) (@lem2709350 n)). Qed.
Lemma lem2709352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709353 (n : int) : (term114 n) = (term301 n).
Proof. exact (MK_COMB (@lem2709352) (@lem2709178 n)). Qed.
Lemma lem2709354 (n : int) : (term126 n) = (term302 n).
Proof. exact (MK_COMB (@lem2709353 n) (@lem2709351 n)). Qed.
Lemma lem2709355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709356 (n : int) : (term128 n) = (term303 n).
Proof. exact (MK_COMB (@lem2709355) (@lem2709008 n)). Qed.
Lemma lem2709357 (n : int) : (term129 n) = (term304 n).
Proof. exact (MK_COMB (@lem2709356 n) (@lem2709354 n)). Qed.
Lemma lem2709358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709359 (n : int) : (term130 n) = (term305 n).
Proof. exact (MK_COMB (@lem2709358) (@lem2708877 n)). Qed.
Lemma lem2709360 (n : int) : (term131 n) = (term306 n).
Proof. exact (MK_COMB (@lem2709359 n) (@lem2709357 n)). Qed.
Lemma lem2709367 (n : int) : (term133 n) = (term306 n).
Proof. exact (TRANS (@lem2708623 n) (@lem2709360 n)). Qed.
Lemma lem2709381 (n : int) : (term304 n) = (term307 n).
Proof. exact (@lem19158 (term275 n) (term246 n) (term300 n)). Qed.
Lemma lem2709388 (n : int) : (term308 n) = (term309 n).
Proof. exact (@lem19367 (term235 n) (term244 n) (term300 n)). Qed.
Lemma lem2709395 (n : int) : (term310 n) = (term311 n).
Proof. exact (@lem19367 (term235 n) (term244 n) (term275 n)). Qed.
Lemma lem2709396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709397 (n : int) : (term312 n) = (term313 n).
Proof. exact (MK_COMB (@lem2709396) (@lem2709395 n)). Qed.
Lemma lem2709398 (n : int) : (term307 n) = (term314 n).
Proof. exact (MK_COMB (@lem2709397 n) (@lem2709388 n)). Qed.
Lemma lem2709400 (n : int) : (term304 n) = (term314 n).
Proof. exact (TRANS (@lem2709381 n) (@lem2709398 n)). Qed.
Lemma lem2709419 (n : int) : (term305 n) = (term305 n).
Proof. exact (eq_refl (term305 n)). Qed.
Lemma lem2709420 (n : int) : (term306 n) = (term315 n).
Proof. exact (MK_COMB (@lem2709419 n) (@lem2709400 n)). Qed.
Lemma lem2709421 (n : int) : (term315 n) = (term316 n).
Proof. exact (@lem19158 (term311 n) (term228 n) (term309 n)). Qed.
Lemma lem2709422 (n : int) : (term317 n) = (term318 n).
Proof. exact (@lem19158 (term319 n) (term228 n) (term320 n)). Qed.
Lemma lem2709429 (n : int) : (term321 n) = (term322 n).
Proof. exact (@lem19367 (term28 = term32) (term227 n) (term320 n)). Qed.
Lemma lem2709436 (n : int) : (term323 n) = (term324 n).
Proof. exact (@lem19367 (term28 = term32) (term227 n) (term319 n)). Qed.
Lemma lem2709437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709438 (n : int) : (term325 n) = (term326 n).
Proof. exact (MK_COMB (@lem2709437) (@lem2709436 n)). Qed.
Lemma lem2709439 (n : int) : (term318 n) = (term327 n).
Proof. exact (MK_COMB (@lem2709438 n) (@lem2709429 n)). Qed.
Lemma lem2709440 (n : int) : (term317 n) = (term327 n).
Proof. exact (TRANS (@lem2709422 n) (@lem2709439 n)). Qed.
Lemma lem2709441 (n : int) : (term328 n) = (term329 n).
Proof. exact (@lem19158 (term330 n) (term228 n) (term331 n)). Qed.
Lemma lem2709448 (n : int) : (term332 n) = (term333 n).
Proof. exact (@lem19367 (term28 = term32) (term227 n) (term331 n)). Qed.
Lemma lem2709455 (n : int) : (term334 n) = (term335 n).
Proof. exact (@lem19367 (term28 = term32) (term227 n) (term330 n)). Qed.
Lemma lem2709456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709457 (n : int) : (term336 n) = (term337 n).
Proof. exact (MK_COMB (@lem2709456) (@lem2709455 n)). Qed.
Lemma lem2709458 (n : int) : (term329 n) = (term338 n).
Proof. exact (MK_COMB (@lem2709457 n) (@lem2709448 n)). Qed.
Lemma lem2709459 (n : int) : (term328 n) = (term338 n).
Proof. exact (TRANS (@lem2709441 n) (@lem2709458 n)). Qed.
Lemma lem2709460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709461 (n : int) : (term339 n) = (term340 n).
Proof. exact (MK_COMB (@lem2709460) (@lem2709459 n)). Qed.
Lemma lem2709462 (n : int) : (term316 n) = (term341 n).
Proof. exact (MK_COMB (@lem2709461 n) (@lem2709440 n)). Qed.
Lemma lem2709463 (n : int) : (term315 n) = (term341 n).
Proof. exact (TRANS (@lem2709421 n) (@lem2709462 n)). Qed.
Lemma lem2709464 (n : int) : (term306 n) = (term341 n).
Proof. exact (TRANS (@lem2709420 n) (@lem2709463 n)). Qed.
Lemma lem2709465 (n : int) : (term133 n) = (term341 n).
Proof. exact (TRANS (@lem2709367 n) (@lem2709464 n)). Qed.
Lemma lem2709470 (n : int) : (term342 n) = (term343 n).
Proof. exact (eq_refl (term342 n)). Qed.
Lemma lem2709471 (n : int) : (term343 n) = (term342 n).
Proof. exact (SYM (@lem2709470 n)). Qed.
Lemma lem2709472 (n : int) : (term342 n) = (term344 n).
Proof. exact (@lem1482981 (term345 n) term28). Qed.
Lemma lem2709473 (n : int) : (term343 n) = (term344 n).
Proof. exact (TRANS (@lem2709471 n) (@lem2709472 n)). Qed.
Lemma lem2709474 (n : int) : (term346 n) = (term347 n).
Proof. exact (eq_refl (term346 n)). Qed.
Lemma lem2709475 : term348 = term348.
Proof. exact (eq_refl term348). Qed.
Lemma lem2709476 (n : int) : (term349 n) = (term350 n).
Proof. exact (MK_COMB (@lem2709475) (@lem2709474 n)). Qed.
Lemma lem2709477 (n : int) : (term351 n) = (term352 n).
Proof. exact (eq_refl (term351 n)). Qed.
Lemma lem2709478 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem2709479 (n : int) : (term354 n) = (term355 n).
Proof. exact (MK_COMB (@lem2709478) (@lem2709477 n)). Qed.
Lemma lem2709480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2709481 (n : int) : (term356 n) = (term357 n).
Proof. exact (MK_COMB (@lem2709480) (@lem2709479 n)). Qed.
Lemma lem2709482 (n : int) : (term344 n) = (term358 n).
Proof. exact (MK_COMB (@lem2709481 n) (@lem2709476 n)). Qed.
Lemma lem2709483 (n : int) : (term359 n) = (term359 n).
Proof. exact (eq_refl (term359 n)). Qed.
Lemma lem2709484 (n : int) : ((term343 n) = (term344 n)) = ((term343 n) = (term358 n)).
Proof. exact (MK_COMB (@lem2709483 n) (@lem2709482 n)). Qed.
Lemma lem2709485 (n : int) : (term343 n) = (term358 n).
Proof. exact (EQ_MP (@lem2709484 n) (@lem2709473 n)). Qed.
Lemma lem2709486 : term360 = term361.
Proof. exact (@lem1988291 term28 term32). Qed.
Lemma lem2709492 : term134 = term135.
Proof. exact (@lem1982792 term28 term32). Qed.
Lemma lem2709494 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709495 : term32 = term137.
Proof. exact (@lem2709494 (NUMERAL 0)). Qed.
Lemma lem2709497 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709498 : term140 = term141.
Proof. exact (@lem2709497 term67). Qed.
Lemma lem2709499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709500 : term142 = term143.
Proof. exact (MK_COMB (@lem2709499) (@lem2709498)). Qed.
Lemma lem2709501 : term144 = term145.
Proof. exact (MK_COMB (@lem2709500) (@lem2709495)). Qed.
Lemma lem2709502 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2709504 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709505 : term149 = term150.
Proof. exact (@lem2709504 term67 term67). Qed.
Lemma lem2709506 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709507 : term152 = term67.
Proof. exact (EQ_MP (@lem2709506) (@lem940073)). Qed.
Lemma lem2709508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709509 : term150 = term66.
Proof. exact (MK_COMB (@lem2709508) (@lem2709507)). Qed.
Lemma lem2709510 : term149 = term66.
Proof. exact (TRANS (@lem2709505) (@lem2709509)). Qed.
Lemma lem2709512 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2709513 : term144 = term32.
Proof. exact (@lem2709512 term67). Qed.
Lemma lem2709514 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709515 : term154 = term155.
Proof. exact (MK_COMB (@lem2709514) (@lem2709513)). Qed.
Lemma lem2709516 : term146 = term137.
Proof. exact (MK_COMB (@lem2709515) (@lem2709510)). Qed.
Lemma lem2709517 : term145 = term137.
Proof. exact (TRANS (@lem2709502) (@lem2709516)). Qed.
Lemma lem2709518 : term144 = term137.
Proof. exact (TRANS (@lem2709501) (@lem2709517)). Qed.
Lemma lem2709520 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709521 : term137 = term32.
Proof. exact (@lem2709520 term32). Qed.
Lemma lem2709522 : term144 = term32.
Proof. exact (TRANS (@lem2709518) (@lem2709521)). Qed.
Lemma lem2709523 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2709524 : term135 = term158.
Proof. exact (MK_COMB (@lem2709523) (@lem2709522)). Qed.
Lemma lem2709525 : term158 = term28.
Proof. exact (@lem1982723 term28). Qed.
Lemma lem2709526 : term135 = term28.
Proof. exact (TRANS (@lem2709524) (@lem2709525)). Qed.
Lemma lem2709528 : term134 = term28.
Proof. exact (TRANS (@lem2709492) (@lem2709526)). Qed.
Lemma lem2709529 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709530 : term362 = term363.
Proof. exact (MK_COMB (@lem2709529) (@lem2709528)). Qed.
Lemma lem2709531 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709532 : term361 = term360.
Proof. exact (MK_COMB (@lem2709530) (@lem2709531)). Qed.
Lemma lem2709533 : term360 = term360.
Proof. exact (TRANS (@lem2709486) (@lem2709532)). Qed.
Lemma lem2709534 (n : int) : ((term195 n) = term32) = ((term364 n) = term32).
Proof. exact (@lem1988293 (term195 n) term32). Qed.
Lemma lem2709564 (n : int) : (term364 n) = (term365 n).
Proof. exact (@lem1982792 (term195 n) term32). Qed.
Lemma lem2709566 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709567 : term32 = term137.
Proof. exact (@lem2709566 (NUMERAL 0)). Qed.
Lemma lem2709569 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709570 : term140 = term141.
Proof. exact (@lem2709569 term67). Qed.
Lemma lem2709571 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709572 : term142 = term143.
Proof. exact (MK_COMB (@lem2709571) (@lem2709570)). Qed.
Lemma lem2709573 : term144 = term145.
Proof. exact (MK_COMB (@lem2709572) (@lem2709567)). Qed.
Lemma lem2709574 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2709576 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709577 : term149 = term150.
Proof. exact (@lem2709576 term67 term67). Qed.
Lemma lem2709578 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709579 : term152 = term67.
Proof. exact (EQ_MP (@lem2709578) (@lem940073)). Qed.
Lemma lem2709580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709581 : term150 = term66.
Proof. exact (MK_COMB (@lem2709580) (@lem2709579)). Qed.
Lemma lem2709582 : term149 = term66.
Proof. exact (TRANS (@lem2709577) (@lem2709581)). Qed.
Lemma lem2709584 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2709585 : term144 = term32.
Proof. exact (@lem2709584 term67). Qed.
Lemma lem2709586 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709587 : term154 = term155.
Proof. exact (MK_COMB (@lem2709586) (@lem2709585)). Qed.
Lemma lem2709588 : term146 = term137.
Proof. exact (MK_COMB (@lem2709587) (@lem2709582)). Qed.
Lemma lem2709589 : term145 = term137.
Proof. exact (TRANS (@lem2709574) (@lem2709588)). Qed.
Lemma lem2709590 : term144 = term137.
Proof. exact (TRANS (@lem2709573) (@lem2709589)). Qed.
Lemma lem2709592 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709593 : term137 = term32.
Proof. exact (@lem2709592 term32). Qed.
Lemma lem2709594 : term144 = term32.
Proof. exact (TRANS (@lem2709590) (@lem2709593)). Qed.
Lemma lem2709595 (n : int) : (term366 n) = (term366 n).
Proof. exact (eq_refl (term366 n)). Qed.
Lemma lem2709596 (n : int) : (term365 n) = (term367 n).
Proof. exact (MK_COMB (@lem2709595 n) (@lem2709594)). Qed.
Lemma lem2709597 (n : int) : (term367 n) = (term195 n).
Proof. exact (@lem1982723 (term195 n)). Qed.
Lemma lem2709598 (n : int) : (term365 n) = (term195 n).
Proof. exact (TRANS (@lem2709596 n) (@lem2709597 n)). Qed.
Lemma lem2709600 (n : int) : (term364 n) = (term195 n).
Proof. exact (TRANS (@lem2709564 n) (@lem2709598 n)). Qed.
Lemma lem2709601 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2709602 (n : int) : (term368 n) = (term197 n).
Proof. exact (MK_COMB (@lem2709601) (@lem2709600 n)). Qed.
Lemma lem2709603 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709604 (n : int) : ((term364 n) = term32) = ((term195 n) = term32).
Proof. exact (MK_COMB (@lem2709602 n) (@lem2709603)). Qed.
Lemma lem2709605 (n : int) : ((term195 n) = term32) = ((term195 n) = term32).
Proof. exact (TRANS (@lem2709534 n) (@lem2709604 n)). Qed.
Lemma lem2709606 (n : int) : (term204 n) = (term198 n).
Proof. exact (@lem1988291 (term48 n) term32). Qed.
Lemma lem2709612 (n : int) : (term199 n) = (term200 n).
Proof. exact (@lem1982792 (term48 n) term32). Qed.
Lemma lem2709614 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709615 : term32 = term137.
Proof. exact (@lem2709614 (NUMERAL 0)). Qed.
Lemma lem2709617 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709618 : term140 = term141.
Proof. exact (@lem2709617 term67). Qed.
Lemma lem2709619 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709620 : term142 = term143.
Proof. exact (MK_COMB (@lem2709619) (@lem2709618)). Qed.
Lemma lem2709621 : term144 = term145.
Proof. exact (MK_COMB (@lem2709620) (@lem2709615)). Qed.
Lemma lem2709622 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2709624 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709625 : term149 = term150.
Proof. exact (@lem2709624 term67 term67). Qed.
Lemma lem2709626 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709627 : term152 = term67.
Proof. exact (EQ_MP (@lem2709626) (@lem940073)). Qed.
Lemma lem2709628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709629 : term150 = term66.
Proof. exact (MK_COMB (@lem2709628) (@lem2709627)). Qed.
Lemma lem2709630 : term149 = term66.
Proof. exact (TRANS (@lem2709625) (@lem2709629)). Qed.
Lemma lem2709632 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2709633 : term144 = term32.
Proof. exact (@lem2709632 term67). Qed.
Lemma lem2709634 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709635 : term154 = term155.
Proof. exact (MK_COMB (@lem2709634) (@lem2709633)). Qed.
Lemma lem2709636 : term146 = term137.
Proof. exact (MK_COMB (@lem2709635) (@lem2709630)). Qed.
Lemma lem2709637 : term145 = term137.
Proof. exact (TRANS (@lem2709622) (@lem2709636)). Qed.
Lemma lem2709638 : term144 = term137.
Proof. exact (TRANS (@lem2709621) (@lem2709637)). Qed.
Lemma lem2709640 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709641 : term137 = term32.
Proof. exact (@lem2709640 term32). Qed.
Lemma lem2709642 : term144 = term32.
Proof. exact (TRANS (@lem2709638) (@lem2709641)). Qed.
Lemma lem2709643 (n : int) : (term68 n) = (term68 n).
Proof. exact (eq_refl (term68 n)). Qed.
Lemma lem2709644 (n : int) : (term200 n) = (term201 n).
Proof. exact (MK_COMB (@lem2709643 n) (@lem2709642)). Qed.
Lemma lem2709645 (n : int) : (term201 n) = (term48 n).
Proof. exact (@lem1982723 (term48 n)). Qed.
Lemma lem2709646 (n : int) : (term200 n) = (term48 n).
Proof. exact (TRANS (@lem2709644 n) (@lem2709645 n)). Qed.
Lemma lem2709648 (n : int) : (term199 n) = (term48 n).
Proof. exact (TRANS (@lem2709612 n) (@lem2709646 n)). Qed.
Lemma lem2709649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709650 (n : int) : (term202 n) = (term203 n).
Proof. exact (MK_COMB (@lem2709649) (@lem2709648 n)). Qed.
Lemma lem2709651 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709652 (n : int) : (term198 n) = (term204 n).
Proof. exact (MK_COMB (@lem2709650 n) (@lem2709651)). Qed.
Lemma lem2709653 (n : int) : (term204 n) = (term204 n).
Proof. exact (TRANS (@lem2709606 n) (@lem2709652 n)). Qed.
Lemma lem2709654 (n : int) : (term369 n) = (term370 n).
Proof. exact (@lem1988291 (term371 n) term32). Qed.
Lemma lem2709655 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709673 (n : int) : (term371 n) = (term372 n).
Proof. exact (@lem1982757 (term170 n) term28 term140). Qed.
Lemma lem2709675 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709676 : term140 = term141.
Proof. exact (@lem2709675 term67). Qed.
Lemma lem2709678 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709679 : term28 = term173.
Proof. exact (@lem2709678 term29). Qed.
Lemma lem2709680 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709681 : term157 = term373.
Proof. exact (MK_COMB (@lem2709680) (@lem2709679)). Qed.
Lemma lem2709682 : term374 = term375.
Proof. exact (MK_COMB (@lem2709681) (@lem2709676)). Qed.
Lemma lem2709683 : term376.
Proof. exact (@lem1981473 term28 term66 term140 term66 term66 term66). Qed.
Lemma lem2709685 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709686 : term257 = term258.
Proof. exact (@lem2709685 (NUMERAL 0) term67). Qed.
Lemma lem2709687 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709688 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709689 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709688 h1) (fun h1 : term258 = True => @lem2709687)). Qed.
Lemma lem2709690 : term258 = True.
Proof. exact (EQ_MP (@lem2709689) (@lem2709687)). Qed.
Lemma lem2709691 : term257 = True.
Proof. exact (TRANS (@lem2709686) (@lem2709690)). Qed.
Lemma lem2709692 : True = term257.
Proof. exact (SYM (@lem2709691)). Qed.
Lemma lem2709693 : term257.
Proof. exact (EQ_MP (@lem2709692) (@lem0)). Qed.
Lemma lem2709694 : term377.
Proof. exact (@lem2709683 (@lem2709693)). Qed.
Lemma lem2709696 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709697 : term257 = term258.
Proof. exact (@lem2709696 (NUMERAL 0) term67). Qed.
Lemma lem2709698 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709699 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709700 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709699 h1) (fun h1 : term258 = True => @lem2709698)). Qed.
Lemma lem2709701 : term258 = True.
Proof. exact (EQ_MP (@lem2709700) (@lem2709698)). Qed.
Lemma lem2709702 : term257 = True.
Proof. exact (TRANS (@lem2709697) (@lem2709701)). Qed.
Lemma lem2709703 : True = term257.
Proof. exact (SYM (@lem2709702)). Qed.
Lemma lem2709704 : term257.
Proof. exact (EQ_MP (@lem2709703) (@lem0)). Qed.
Lemma lem2709705 : term378.
Proof. exact (@lem2709694 (@lem2709704)). Qed.
Lemma lem2709707 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2709708 : term257 = term258.
Proof. exact (@lem2709707 (NUMERAL 0) term67). Qed.
Lemma lem2709709 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2709710 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2709711 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2709710 h1) (fun h1 : term258 = True => @lem2709709)). Qed.
Lemma lem2709712 : term258 = True.
Proof. exact (EQ_MP (@lem2709711) (@lem2709709)). Qed.
Lemma lem2709713 : term257 = True.
Proof. exact (TRANS (@lem2709708) (@lem2709712)). Qed.
Lemma lem2709714 : True = term257.
Proof. exact (SYM (@lem2709713)). Qed.
Lemma lem2709715 : term257.
Proof. exact (EQ_MP (@lem2709714) (@lem0)). Qed.
Lemma lem2709716 : term379.
Proof. exact (@lem2709705 (@lem2709715)). Qed.
Lemma lem2709718 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2709719 : term211 = term214.
Proof. exact (@lem2709718 term67 term67). Qed.
Lemma lem2709720 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709721 : term152 = term67.
Proof. exact (EQ_MP (@lem2709720) (@lem940073)). Qed.
Lemma lem2709722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709723 : term150 = term66.
Proof. exact (MK_COMB (@lem2709722) (@lem2709721)). Qed.
Lemma lem2709724 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2709725 : term214 = term140.
Proof. exact (MK_COMB (@lem2709724) (@lem2709723)). Qed.
Lemma lem2709726 : term211 = term140.
Proof. exact (TRANS (@lem2709719) (@lem2709725)). Qed.
Lemma lem2709728 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709729 : term289 = term290.
Proof. exact (@lem2709728 term29 term67). Qed.
Lemma lem2709730 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2709731 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2709732 : term292 = term29.
Proof. exact (EQ_MP (@lem2709731) (@lem2709730)). Qed.
Lemma lem2709733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709734 : term290 = term28.
Proof. exact (MK_COMB (@lem2709733) (@lem2709732)). Qed.
Lemma lem2709735 : term289 = term28.
Proof. exact (TRANS (@lem2709729) (@lem2709734)). Qed.
Lemma lem2709736 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709737 : term380 = term157.
Proof. exact (MK_COMB (@lem2709736) (@lem2709735)). Qed.
Lemma lem2709738 : term381 = term374.
Proof. exact (MK_COMB (@lem2709737) (@lem2709726)). Qed.
Lemma lem2709741 : term382 = term66.
Proof. exact (@lem1367769 term67 term67). Qed.
Lemma lem2709742 : term284 = term181.
Proof. exact (@lem706885). Qed.
Lemma lem2709743 : (term284 = term181) = (term285 = term29).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term181). Qed.
Lemma lem2709744 : term285 = term29.
Proof. exact (EQ_MP (@lem2709743) (@lem2709742)). Qed.
Lemma lem2709745 : term29 = term285.
Proof. exact (SYM (@lem2709744)). Qed.
Lemma lem2709746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709747 : term28 = term283.
Proof. exact (MK_COMB (@lem2709746) (@lem2709745)). Qed.
Lemma lem2709748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2709749 : term157 = term383.
Proof. exact (MK_COMB (@lem2709748) (@lem2709747)). Qed.
Lemma lem2709750 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2709751 : term374 = term382.
Proof. exact (MK_COMB (@lem2709749) (@lem2709750)). Qed.
Lemma lem2709752 : term374 = term66.
Proof. exact (TRANS (@lem2709751) (@lem2709741)). Qed.
Lemma lem2709753 : term381 = term66.
Proof. exact (TRANS (@lem2709738) (@lem2709752)). Qed.
Lemma lem2709754 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709755 : term384 = term385.
Proof. exact (MK_COMB (@lem2709754) (@lem2709753)). Qed.
Lemma lem2709756 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2709757 : term386 = term149.
Proof. exact (MK_COMB (@lem2709755) (@lem2709756)). Qed.
Lemma lem2709759 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709760 : term149 = term150.
Proof. exact (@lem2709759 term67 term67). Qed.
Lemma lem2709761 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709762 : term152 = term67.
Proof. exact (EQ_MP (@lem2709761) (@lem940073)). Qed.
Lemma lem2709763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709764 : term150 = term66.
Proof. exact (MK_COMB (@lem2709763) (@lem2709762)). Qed.
Lemma lem2709765 : term149 = term66.
Proof. exact (TRANS (@lem2709760) (@lem2709764)). Qed.
Lemma lem2709766 : term386 = term66.
Proof. exact (TRANS (@lem2709757) (@lem2709765)). Qed.
Lemma lem2709768 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709769 : term149 = term150.
Proof. exact (@lem2709768 term67 term67). Qed.
Lemma lem2709770 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709771 : term152 = term67.
Proof. exact (EQ_MP (@lem2709770) (@lem940073)). Qed.
Lemma lem2709772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709773 : term150 = term66.
Proof. exact (MK_COMB (@lem2709772) (@lem2709771)). Qed.
Lemma lem2709774 : term149 = term66.
Proof. exact (TRANS (@lem2709769) (@lem2709773)). Qed.
Lemma lem2709775 : term385 = term385.
Proof. exact (eq_refl term385). Qed.
Lemma lem2709776 : term387 = term149.
Proof. exact (MK_COMB (@lem2709775) (@lem2709774)). Qed.
Lemma lem2709778 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709779 : term149 = term150.
Proof. exact (@lem2709778 term67 term67). Qed.
Lemma lem2709780 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709781 : term152 = term67.
Proof. exact (EQ_MP (@lem2709780) (@lem940073)). Qed.
Lemma lem2709782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709783 : term150 = term66.
Proof. exact (MK_COMB (@lem2709782) (@lem2709781)). Qed.
Lemma lem2709784 : term149 = term66.
Proof. exact (TRANS (@lem2709779) (@lem2709783)). Qed.
Lemma lem2709785 : term387 = term66.
Proof. exact (TRANS (@lem2709776) (@lem2709784)). Qed.
Lemma lem2709786 : term66 = term387.
Proof. exact (SYM (@lem2709785)). Qed.
Lemma lem2709787 : term386 = term387.
Proof. exact (TRANS (@lem2709766) (@lem2709786)). Qed.
Lemma lem2709788 : term375 = term210.
Proof. exact (@lem2709716 (@lem2709787)). Qed.
Lemma lem2709789 : term374 = term210.
Proof. exact (TRANS (@lem2709682) (@lem2709788)). Qed.
Lemma lem2709791 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2709792 : term210 = term66.
Proof. exact (@lem2709791 term66). Qed.
Lemma lem2709793 : term374 = term66.
Proof. exact (TRANS (@lem2709789) (@lem2709792)). Qed.
Lemma lem2709794 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2709795 (n : int) : (term372 n) = (term388 n).
Proof. exact (MK_COMB (@lem2709794 n) (@lem2709793)). Qed.
Lemma lem2709797 (n : int) : (term371 n) = (term388 n).
Proof. exact (TRANS (@lem2709673 n) (@lem2709795 n)). Qed.
Lemma lem2709798 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2709799 (n : int) : (term389 n) = (term390 n).
Proof. exact (MK_COMB (@lem2709798) (@lem2709797 n)). Qed.
Lemma lem2709800 (n : int) : (term391 n) = (term392 n).
Proof. exact (MK_COMB (@lem2709799 n) (@lem2709655)). Qed.
Lemma lem2709801 (n : int) : (term392 n) = (term393 n).
Proof. exact (@lem1982792 (term388 n) term32). Qed.
Lemma lem2709803 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709804 : term32 = term137.
Proof. exact (@lem2709803 (NUMERAL 0)). Qed.
Lemma lem2709806 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709807 : term140 = term141.
Proof. exact (@lem2709806 term67). Qed.
Lemma lem2709808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709809 : term142 = term143.
Proof. exact (MK_COMB (@lem2709808) (@lem2709807)). Qed.
Lemma lem2709810 : term144 = term145.
Proof. exact (MK_COMB (@lem2709809) (@lem2709804)). Qed.
Lemma lem2709811 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2709813 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709814 : term149 = term150.
Proof. exact (@lem2709813 term67 term67). Qed.
Lemma lem2709815 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709816 : term152 = term67.
Proof. exact (EQ_MP (@lem2709815) (@lem940073)). Qed.
Lemma lem2709817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709818 : term150 = term66.
Proof. exact (MK_COMB (@lem2709817) (@lem2709816)). Qed.
Lemma lem2709819 : term149 = term66.
Proof. exact (TRANS (@lem2709814) (@lem2709818)). Qed.
Lemma lem2709821 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2709822 : term144 = term32.
Proof. exact (@lem2709821 term67). Qed.
Lemma lem2709823 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709824 : term154 = term155.
Proof. exact (MK_COMB (@lem2709823) (@lem2709822)). Qed.
Lemma lem2709825 : term146 = term137.
Proof. exact (MK_COMB (@lem2709824) (@lem2709819)). Qed.
Lemma lem2709826 : term145 = term137.
Proof. exact (TRANS (@lem2709811) (@lem2709825)). Qed.
Lemma lem2709827 : term144 = term137.
Proof. exact (TRANS (@lem2709810) (@lem2709826)). Qed.
Lemma lem2709829 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709830 : term137 = term32.
Proof. exact (@lem2709829 term32). Qed.
Lemma lem2709831 : term144 = term32.
Proof. exact (TRANS (@lem2709827) (@lem2709830)). Qed.
Lemma lem2709832 (n : int) : (term394 n) = (term394 n).
Proof. exact (eq_refl (term394 n)). Qed.
Lemma lem2709833 (n : int) : (term393 n) = (term395 n).
Proof. exact (MK_COMB (@lem2709832 n) (@lem2709831)). Qed.
Lemma lem2709834 (n : int) : (term395 n) = (term388 n).
Proof. exact (@lem1982723 (term388 n)). Qed.
Lemma lem2709835 (n : int) : (term393 n) = (term388 n).
Proof. exact (TRANS (@lem2709833 n) (@lem2709834 n)). Qed.
Lemma lem2709836 (n : int) : (term392 n) = (term388 n).
Proof. exact (TRANS (@lem2709801 n) (@lem2709835 n)). Qed.
Lemma lem2709837 (n : int) : (term391 n) = (term388 n).
Proof. exact (TRANS (@lem2709800 n) (@lem2709836 n)). Qed.
Lemma lem2709838 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709839 (n : int) : (term396 n) = (term397 n).
Proof. exact (MK_COMB (@lem2709838) (@lem2709837 n)). Qed.
Lemma lem2709840 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709841 (n : int) : (term370 n) = (term398 n).
Proof. exact (MK_COMB (@lem2709839 n) (@lem2709840)). Qed.
Lemma lem2709842 (n : int) : (term369 n) = (term398 n).
Proof. exact (TRANS (@lem2709654 n) (@lem2709841 n)). Qed.
Lemma lem2709843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709844 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2709843) (@lem2709653 n)). Qed.
Lemma lem2709845 (n : int) : (term399 n) = (term400 n).
Proof. exact (MK_COMB (@lem2709844 n) (@lem2709842 n)). Qed.
Lemma lem2709846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709847 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2709846) (@lem2709605 n)). Qed.
Lemma lem2709848 (n : int) : (term401 n) = (term402 n).
Proof. exact (MK_COMB (@lem2709847 n) (@lem2709845 n)). Qed.
Lemma lem2709849 (n : int) : (term235 n) = (term403 n).
Proof. exact (@lem1988291 (term218 n) term32). Qed.
Lemma lem2709867 (n : int) : (term404 n) = (term405 n).
Proof. exact (@lem1982792 (term218 n) term32). Qed.
Lemma lem2709869 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709870 : term32 = term137.
Proof. exact (@lem2709869 (NUMERAL 0)). Qed.
Lemma lem2709872 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709873 : term140 = term141.
Proof. exact (@lem2709872 term67). Qed.
Lemma lem2709874 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709875 : term142 = term143.
Proof. exact (MK_COMB (@lem2709874) (@lem2709873)). Qed.
Lemma lem2709876 : term144 = term145.
Proof. exact (MK_COMB (@lem2709875) (@lem2709870)). Qed.
Lemma lem2709877 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2709879 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709880 : term149 = term150.
Proof. exact (@lem2709879 term67 term67). Qed.
Lemma lem2709881 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709882 : term152 = term67.
Proof. exact (EQ_MP (@lem2709881) (@lem940073)). Qed.
Lemma lem2709883 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709884 : term150 = term66.
Proof. exact (MK_COMB (@lem2709883) (@lem2709882)). Qed.
Lemma lem2709885 : term149 = term66.
Proof. exact (TRANS (@lem2709880) (@lem2709884)). Qed.
Lemma lem2709887 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2709888 : term144 = term32.
Proof. exact (@lem2709887 term67). Qed.
Lemma lem2709889 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709890 : term154 = term155.
Proof. exact (MK_COMB (@lem2709889) (@lem2709888)). Qed.
Lemma lem2709891 : term146 = term137.
Proof. exact (MK_COMB (@lem2709890) (@lem2709885)). Qed.
Lemma lem2709892 : term145 = term137.
Proof. exact (TRANS (@lem2709877) (@lem2709891)). Qed.
Lemma lem2709893 : term144 = term137.
Proof. exact (TRANS (@lem2709876) (@lem2709892)). Qed.
Lemma lem2709895 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709896 : term137 = term32.
Proof. exact (@lem2709895 term32). Qed.
Lemma lem2709897 : term144 = term32.
Proof. exact (TRANS (@lem2709893) (@lem2709896)). Qed.
Lemma lem2709898 (n : int) : (term406 n) = (term406 n).
Proof. exact (eq_refl (term406 n)). Qed.
Lemma lem2709899 (n : int) : (term405 n) = (term407 n).
Proof. exact (MK_COMB (@lem2709898 n) (@lem2709897)). Qed.
Lemma lem2709900 (n : int) : (term407 n) = (term218 n).
Proof. exact (@lem1982723 (term218 n)). Qed.
Lemma lem2709901 (n : int) : (term405 n) = (term218 n).
Proof. exact (TRANS (@lem2709899 n) (@lem2709900 n)). Qed.
Lemma lem2709903 (n : int) : (term404 n) = (term218 n).
Proof. exact (TRANS (@lem2709867 n) (@lem2709901 n)). Qed.
Lemma lem2709904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709905 (n : int) : (term408 n) = (term234 n).
Proof. exact (MK_COMB (@lem2709904) (@lem2709903 n)). Qed.
Lemma lem2709906 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709907 (n : int) : (term403 n) = (term235 n).
Proof. exact (MK_COMB (@lem2709905 n) (@lem2709906)). Qed.
Lemma lem2709908 (n : int) : (term235 n) = (term235 n).
Proof. exact (TRANS (@lem2709849 n) (@lem2709907 n)). Qed.
Lemma lem2709909 (n : int) : (term275 n) = (term409 n).
Proof. exact (@lem1988291 (term170 n) term32). Qed.
Lemma lem2709921 (n : int) : (term410 n) = (term411 n).
Proof. exact (@lem1982792 (term170 n) term32). Qed.
Lemma lem2709923 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709924 : term32 = term137.
Proof. exact (@lem2709923 (NUMERAL 0)). Qed.
Lemma lem2709926 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709927 : term140 = term141.
Proof. exact (@lem2709926 term67). Qed.
Lemma lem2709928 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709929 : term142 = term143.
Proof. exact (MK_COMB (@lem2709928) (@lem2709927)). Qed.
Lemma lem2709930 : term144 = term145.
Proof. exact (MK_COMB (@lem2709929) (@lem2709924)). Qed.
Lemma lem2709931 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2709933 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709934 : term149 = term150.
Proof. exact (@lem2709933 term67 term67). Qed.
Lemma lem2709935 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709936 : term152 = term67.
Proof. exact (EQ_MP (@lem2709935) (@lem940073)). Qed.
Lemma lem2709937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709938 : term150 = term66.
Proof. exact (MK_COMB (@lem2709937) (@lem2709936)). Qed.
Lemma lem2709939 : term149 = term66.
Proof. exact (TRANS (@lem2709934) (@lem2709938)). Qed.
Lemma lem2709941 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2709942 : term144 = term32.
Proof. exact (@lem2709941 term67). Qed.
Lemma lem2709943 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2709944 : term154 = term155.
Proof. exact (MK_COMB (@lem2709943) (@lem2709942)). Qed.
Lemma lem2709945 : term146 = term137.
Proof. exact (MK_COMB (@lem2709944) (@lem2709939)). Qed.
Lemma lem2709946 : term145 = term137.
Proof. exact (TRANS (@lem2709931) (@lem2709945)). Qed.
Lemma lem2709947 : term144 = term137.
Proof. exact (TRANS (@lem2709930) (@lem2709946)). Qed.
Lemma lem2709949 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2709950 : term137 = term32.
Proof. exact (@lem2709949 term32). Qed.
Lemma lem2709951 : term144 = term32.
Proof. exact (TRANS (@lem2709947) (@lem2709950)). Qed.
Lemma lem2709952 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2709953 (n : int) : (term411 n) = (term272 n).
Proof. exact (MK_COMB (@lem2709952 n) (@lem2709951)). Qed.
Lemma lem2709954 (n : int) : (term272 n) = (term170 n).
Proof. exact (@lem1982723 (term170 n)). Qed.
Lemma lem2709955 (n : int) : (term411 n) = (term170 n).
Proof. exact (TRANS (@lem2709953 n) (@lem2709954 n)). Qed.
Lemma lem2709957 (n : int) : (term410 n) = (term170 n).
Proof. exact (TRANS (@lem2709921 n) (@lem2709955 n)). Qed.
Lemma lem2709958 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2709959 (n : int) : (term412 n) = (term274 n).
Proof. exact (MK_COMB (@lem2709958) (@lem2709957 n)). Qed.
Lemma lem2709960 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2709961 (n : int) : (term409 n) = (term275 n).
Proof. exact (MK_COMB (@lem2709959 n) (@lem2709960)). Qed.
Lemma lem2709962 (n : int) : (term275 n) = (term275 n).
Proof. exact (TRANS (@lem2709909 n) (@lem2709961 n)). Qed.
Lemma lem2709963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709964 (n : int) : (term413 n) = (term413 n).
Proof. exact (MK_COMB (@lem2709963) (@lem2709908 n)). Qed.
Lemma lem2709965 (n : int) : (term330 n) = (term330 n).
Proof. exact (MK_COMB (@lem2709964 n) (@lem2709962 n)). Qed.
Lemma lem2709966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709967 (n : int) : (term414 n) = (term415 n).
Proof. exact (MK_COMB (@lem2709966) (@lem2709848 n)). Qed.
Lemma lem2709968 (n : int) : (term352 n) = (term416 n).
Proof. exact (MK_COMB (@lem2709967 n) (@lem2709965 n)). Qed.
Lemma lem2709969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2709970 : term353 = term353.
Proof. exact (MK_COMB (@lem2709969) (@lem2709533)). Qed.
Lemma lem2709971 (n : int) : (term355 n) = (term417 n).
Proof. exact (MK_COMB (@lem2709970) (@lem2709968 n)). Qed.
Lemma lem2709972 : term418 = term419.
Proof. exact (@lem1988289 term32 term28). Qed.
Lemma lem2709978 : term420 = term421.
Proof. exact (@lem1982792 term32 term28). Qed.
Lemma lem2709980 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2709981 : term28 = term173.
Proof. exact (@lem2709980 term29). Qed.
Lemma lem2709983 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2709984 : term140 = term141.
Proof. exact (@lem2709983 term67). Qed.
Lemma lem2709985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2709986 : term142 = term143.
Proof. exact (MK_COMB (@lem2709985) (@lem2709984)). Qed.
Lemma lem2709987 : term174 = term175.
Proof. exact (MK_COMB (@lem2709986) (@lem2709981)). Qed.
Lemma lem2709988 : term175 = term176.
Proof. exact (@lem1981613 term140 term28 term66 term66). Qed.
Lemma lem2709990 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2709991 : term149 = term150.
Proof. exact (@lem2709990 term67 term67). Qed.
Lemma lem2709992 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2709993 : term152 = term67.
Proof. exact (EQ_MP (@lem2709992) (@lem940073)). Qed.
Lemma lem2709994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2709995 : term150 = term66.
Proof. exact (MK_COMB (@lem2709994) (@lem2709993)). Qed.
Lemma lem2709996 : term149 = term66.
Proof. exact (TRANS (@lem2709991) (@lem2709995)). Qed.
Lemma lem2709998 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2709999 : term174 = term179.
Proof. exact (@lem2709998 term67 term29). Qed.
Lemma lem2710000 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2710001 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2710002 : term182 = term29.
Proof. exact (EQ_MP (@lem2710001) (@lem2710000)). Qed.
Lemma lem2710003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710004 : term183 = term28.
Proof. exact (MK_COMB (@lem2710003) (@lem2710002)). Qed.
Lemma lem2710005 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710006 : term179 = term184.
Proof. exact (MK_COMB (@lem2710005) (@lem2710004)). Qed.
Lemma lem2710007 : term174 = term184.
Proof. exact (TRANS (@lem2709999) (@lem2710006)). Qed.
Lemma lem2710008 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2710009 : term185 = term186.
Proof. exact (MK_COMB (@lem2710008) (@lem2710007)). Qed.
Lemma lem2710010 : term176 = term187.
Proof. exact (MK_COMB (@lem2710009) (@lem2709996)). Qed.
Lemma lem2710011 : term175 = term187.
Proof. exact (TRANS (@lem2709988) (@lem2710010)). Qed.
Lemma lem2710012 : term174 = term187.
Proof. exact (TRANS (@lem2709987) (@lem2710011)). Qed.
Lemma lem2710014 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2710015 : term187 = term184.
Proof. exact (@lem2710014 term184). Qed.
Lemma lem2710016 : term174 = term184.
Proof. exact (TRANS (@lem2710012) (@lem2710015)). Qed.
Lemma lem2710017 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem2710018 : term421 = term422.
Proof. exact (MK_COMB (@lem2710017) (@lem2710016)). Qed.
Lemma lem2710019 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2710020 : term421 = term184.
Proof. exact (TRANS (@lem2710018) (@lem2710019)). Qed.
Lemma lem2710022 : term420 = term184.
Proof. exact (TRANS (@lem2709978) (@lem2710020)). Qed.
Lemma lem2710023 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2710024 : term423 = term424.
Proof. exact (MK_COMB (@lem2710023) (@lem2710022)). Qed.
Lemma lem2710025 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710026 : term419 = term425.
Proof. exact (MK_COMB (@lem2710024) (@lem2710025)). Qed.
Lemma lem2710027 : term418 = term425.
Proof. exact (TRANS (@lem2709972) (@lem2710026)). Qed.
Lemma lem2710028 (n : int) : (term426 n) = (term427 n).
Proof. exact (@lem1988291 (term428 n) term32). Qed.
Lemma lem2710029 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710047 (n : int) : (term428 n) = (term429 n).
Proof. exact (@lem1982757 (term170 n) term184 term140). Qed.
Lemma lem2710049 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710050 : term140 = term141.
Proof. exact (@lem2710049 term67). Qed.
Lemma lem2710052 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710053 : term184 = term187.
Proof. exact (@lem2710052 term29). Qed.
Lemma lem2710054 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2710055 : term430 = term431.
Proof. exact (MK_COMB (@lem2710054) (@lem2710053)). Qed.
Lemma lem2710056 : term432 = term433.
Proof. exact (MK_COMB (@lem2710055) (@lem2710050)). Qed.
Lemma lem2710057 : term434.
Proof. exact (@lem1981473 term184 term66 term140 term66 term435 term66). Qed.
Lemma lem2710059 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710060 : term257 = term258.
Proof. exact (@lem2710059 (NUMERAL 0) term67). Qed.
Lemma lem2710061 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710062 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710063 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710062 h1) (fun h1 : term258 = True => @lem2710061)). Qed.
Lemma lem2710064 : term258 = True.
Proof. exact (EQ_MP (@lem2710063) (@lem2710061)). Qed.
Lemma lem2710065 : term257 = True.
Proof. exact (TRANS (@lem2710060) (@lem2710064)). Qed.
Lemma lem2710066 : True = term257.
Proof. exact (SYM (@lem2710065)). Qed.
Lemma lem2710067 : term257.
Proof. exact (EQ_MP (@lem2710066) (@lem0)). Qed.
Lemma lem2710068 : term436.
Proof. exact (@lem2710057 (@lem2710067)). Qed.
Lemma lem2710070 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710071 : term257 = term258.
Proof. exact (@lem2710070 (NUMERAL 0) term67). Qed.
Lemma lem2710072 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710073 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710074 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710073 h1) (fun h1 : term258 = True => @lem2710072)). Qed.
Lemma lem2710075 : term258 = True.
Proof. exact (EQ_MP (@lem2710074) (@lem2710072)). Qed.
Lemma lem2710076 : term257 = True.
Proof. exact (TRANS (@lem2710071) (@lem2710075)). Qed.
Lemma lem2710077 : True = term257.
Proof. exact (SYM (@lem2710076)). Qed.
Lemma lem2710078 : term257.
Proof. exact (EQ_MP (@lem2710077) (@lem0)). Qed.
Lemma lem2710079 : term437.
Proof. exact (@lem2710068 (@lem2710078)). Qed.
Lemma lem2710081 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710082 : term257 = term258.
Proof. exact (@lem2710081 (NUMERAL 0) term67). Qed.
Lemma lem2710083 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710084 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710085 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710084 h1) (fun h1 : term258 = True => @lem2710083)). Qed.
Lemma lem2710086 : term258 = True.
Proof. exact (EQ_MP (@lem2710085) (@lem2710083)). Qed.
Lemma lem2710087 : term257 = True.
Proof. exact (TRANS (@lem2710082) (@lem2710086)). Qed.
Lemma lem2710088 : True = term257.
Proof. exact (SYM (@lem2710087)). Qed.
Lemma lem2710089 : term257.
Proof. exact (EQ_MP (@lem2710088) (@lem0)). Qed.
Lemma lem2710090 : term438.
Proof. exact (@lem2710079 (@lem2710089)). Qed.
Lemma lem2710092 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2710093 : term211 = term214.
Proof. exact (@lem2710092 term67 term67). Qed.
Lemma lem2710094 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710095 : term152 = term67.
Proof. exact (EQ_MP (@lem2710094) (@lem940073)). Qed.
Lemma lem2710096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710097 : term150 = term66.
Proof. exact (MK_COMB (@lem2710096) (@lem2710095)). Qed.
Lemma lem2710098 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710099 : term214 = term140.
Proof. exact (MK_COMB (@lem2710098) (@lem2710097)). Qed.
Lemma lem2710100 : term211 = term140.
Proof. exact (TRANS (@lem2710093) (@lem2710099)). Qed.
Lemma lem2710102 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2710103 : term439 = term440.
Proof. exact (@lem2710102 term29 term67). Qed.
Lemma lem2710104 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2710105 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2710106 : term292 = term29.
Proof. exact (EQ_MP (@lem2710105) (@lem2710104)). Qed.
Lemma lem2710107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710108 : term290 = term28.
Proof. exact (MK_COMB (@lem2710107) (@lem2710106)). Qed.
Lemma lem2710109 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710110 : term440 = term184.
Proof. exact (MK_COMB (@lem2710109) (@lem2710108)). Qed.
Lemma lem2710111 : term439 = term184.
Proof. exact (TRANS (@lem2710103) (@lem2710110)). Qed.
Lemma lem2710112 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2710113 : term441 = term430.
Proof. exact (MK_COMB (@lem2710112) (@lem2710111)). Qed.
Lemma lem2710114 : term442 = term432.
Proof. exact (MK_COMB (@lem2710113) (@lem2710100)). Qed.
Lemma lem2710115 : term432 = term443.
Proof. exact (@lem1367763 term29 term67). Qed.
Lemma lem2710116 : term444 = term445.
Proof. exact (@lem706949). Qed.
Lemma lem2710117 : (term444 = term445) = (term446 = term447).
Proof. exact (@lem1006570 term181 (BIT1 0) term445). Qed.
Lemma lem2710118 : term446 = term447.
Proof. exact (EQ_MP (@lem2710117) (@lem2710116)). Qed.
Lemma lem2710119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710120 : term448 = term449.
Proof. exact (MK_COMB (@lem2710119) (@lem2710118)). Qed.
Lemma lem2710121 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710122 : term443 = term435.
Proof. exact (MK_COMB (@lem2710121) (@lem2710120)). Qed.
Lemma lem2710123 : term432 = term435.
Proof. exact (TRANS (@lem2710115) (@lem2710122)). Qed.
Lemma lem2710124 : term442 = term435.
Proof. exact (TRANS (@lem2710114) (@lem2710123)). Qed.
Lemma lem2710125 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710126 : term450 = term451.
Proof. exact (MK_COMB (@lem2710125) (@lem2710124)). Qed.
Lemma lem2710127 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2710128 : term452 = term453.
Proof. exact (MK_COMB (@lem2710126) (@lem2710127)). Qed.
Lemma lem2710130 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2710131 : term453 = term454.
Proof. exact (@lem2710130 term447 term67). Qed.
Lemma lem2710132 : term455 = term445.
Proof. exact (@lem996237 term445). Qed.
Lemma lem2710133 : (term455 = term445) = (term456 = term447).
Proof. exact (@lem1007663 term445 (BIT1 0) term445). Qed.
Lemma lem2710134 : term456 = term447.
Proof. exact (EQ_MP (@lem2710133) (@lem2710132)). Qed.
Lemma lem2710135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710136 : term457 = term449.
Proof. exact (MK_COMB (@lem2710135) (@lem2710134)). Qed.
Lemma lem2710137 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710138 : term454 = term435.
Proof. exact (MK_COMB (@lem2710137) (@lem2710136)). Qed.
Lemma lem2710139 : term453 = term435.
Proof. exact (TRANS (@lem2710131) (@lem2710138)). Qed.
Lemma lem2710140 : term452 = term435.
Proof. exact (TRANS (@lem2710128) (@lem2710139)). Qed.
Lemma lem2710142 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710143 : term149 = term150.
Proof. exact (@lem2710142 term67 term67). Qed.
Lemma lem2710144 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710145 : term152 = term67.
Proof. exact (EQ_MP (@lem2710144) (@lem940073)). Qed.
Lemma lem2710146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710147 : term150 = term66.
Proof. exact (MK_COMB (@lem2710146) (@lem2710145)). Qed.
Lemma lem2710148 : term149 = term66.
Proof. exact (TRANS (@lem2710143) (@lem2710147)). Qed.
Lemma lem2710149 : term451 = term451.
Proof. exact (eq_refl term451). Qed.
Lemma lem2710150 : term458 = term453.
Proof. exact (MK_COMB (@lem2710149) (@lem2710148)). Qed.
Lemma lem2710152 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2710153 : term453 = term454.
Proof. exact (@lem2710152 term447 term67). Qed.
Lemma lem2710154 : term455 = term445.
Proof. exact (@lem996237 term445). Qed.
Lemma lem2710155 : (term455 = term445) = (term456 = term447).
Proof. exact (@lem1007663 term445 (BIT1 0) term445). Qed.
Lemma lem2710156 : term456 = term447.
Proof. exact (EQ_MP (@lem2710155) (@lem2710154)). Qed.
Lemma lem2710157 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710158 : term457 = term449.
Proof. exact (MK_COMB (@lem2710157) (@lem2710156)). Qed.
Lemma lem2710159 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710160 : term454 = term435.
Proof. exact (MK_COMB (@lem2710159) (@lem2710158)). Qed.
Lemma lem2710161 : term453 = term435.
Proof. exact (TRANS (@lem2710153) (@lem2710160)). Qed.
Lemma lem2710162 : term458 = term435.
Proof. exact (TRANS (@lem2710150) (@lem2710161)). Qed.
Lemma lem2710163 : term435 = term458.
Proof. exact (SYM (@lem2710162)). Qed.
Lemma lem2710164 : term452 = term458.
Proof. exact (TRANS (@lem2710140) (@lem2710163)). Qed.
Lemma lem2710165 : term433 = term459.
Proof. exact (@lem2710090 (@lem2710164)). Qed.
Lemma lem2710166 : term432 = term459.
Proof. exact (TRANS (@lem2710056) (@lem2710165)). Qed.
Lemma lem2710168 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2710169 : term459 = term435.
Proof. exact (@lem2710168 term435). Qed.
Lemma lem2710170 : term432 = term435.
Proof. exact (TRANS (@lem2710166) (@lem2710169)). Qed.
Lemma lem2710171 (n : int) : (term217 n) = (term217 n).
Proof. exact (eq_refl (term217 n)). Qed.
Lemma lem2710172 (n : int) : (term429 n) = (term460 n).
Proof. exact (MK_COMB (@lem2710171 n) (@lem2710170)). Qed.
Lemma lem2710174 (n : int) : (term428 n) = (term460 n).
Proof. exact (TRANS (@lem2710047 n) (@lem2710172 n)). Qed.
Lemma lem2710175 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2710176 (n : int) : (term461 n) = (term462 n).
Proof. exact (MK_COMB (@lem2710175) (@lem2710174 n)). Qed.
Lemma lem2710177 (n : int) : (term463 n) = (term464 n).
Proof. exact (MK_COMB (@lem2710176 n) (@lem2710029)). Qed.
Lemma lem2710178 (n : int) : (term464 n) = (term465 n).
Proof. exact (@lem1982792 (term460 n) term32). Qed.
Lemma lem2710180 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710181 : term32 = term137.
Proof. exact (@lem2710180 (NUMERAL 0)). Qed.
Lemma lem2710183 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710184 : term140 = term141.
Proof. exact (@lem2710183 term67). Qed.
Lemma lem2710185 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710186 : term142 = term143.
Proof. exact (MK_COMB (@lem2710185) (@lem2710184)). Qed.
Lemma lem2710187 : term144 = term145.
Proof. exact (MK_COMB (@lem2710186) (@lem2710181)). Qed.
Lemma lem2710188 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2710190 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710191 : term149 = term150.
Proof. exact (@lem2710190 term67 term67). Qed.
Lemma lem2710192 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710193 : term152 = term67.
Proof. exact (EQ_MP (@lem2710192) (@lem940073)). Qed.
Lemma lem2710194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710195 : term150 = term66.
Proof. exact (MK_COMB (@lem2710194) (@lem2710193)). Qed.
Lemma lem2710196 : term149 = term66.
Proof. exact (TRANS (@lem2710191) (@lem2710195)). Qed.
Lemma lem2710198 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2710199 : term144 = term32.
Proof. exact (@lem2710198 term67). Qed.
Lemma lem2710200 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2710201 : term154 = term155.
Proof. exact (MK_COMB (@lem2710200) (@lem2710199)). Qed.
Lemma lem2710202 : term146 = term137.
Proof. exact (MK_COMB (@lem2710201) (@lem2710196)). Qed.
Lemma lem2710203 : term145 = term137.
Proof. exact (TRANS (@lem2710188) (@lem2710202)). Qed.
Lemma lem2710204 : term144 = term137.
Proof. exact (TRANS (@lem2710187) (@lem2710203)). Qed.
Lemma lem2710206 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2710207 : term137 = term32.
Proof. exact (@lem2710206 term32). Qed.
Lemma lem2710208 : term144 = term32.
Proof. exact (TRANS (@lem2710204) (@lem2710207)). Qed.
Lemma lem2710209 (n : int) : (term466 n) = (term466 n).
Proof. exact (eq_refl (term466 n)). Qed.
Lemma lem2710210 (n : int) : (term465 n) = (term467 n).
Proof. exact (MK_COMB (@lem2710209 n) (@lem2710208)). Qed.
Lemma lem2710211 (n : int) : (term467 n) = (term460 n).
Proof. exact (@lem1982723 (term460 n)). Qed.
Lemma lem2710212 (n : int) : (term465 n) = (term460 n).
Proof. exact (TRANS (@lem2710210 n) (@lem2710211 n)). Qed.
Lemma lem2710213 (n : int) : (term464 n) = (term460 n).
Proof. exact (TRANS (@lem2710178 n) (@lem2710212 n)). Qed.
Lemma lem2710214 (n : int) : (term463 n) = (term460 n).
Proof. exact (TRANS (@lem2710177 n) (@lem2710213 n)). Qed.
Lemma lem2710215 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2710216 (n : int) : (term468 n) = (term469 n).
Proof. exact (MK_COMB (@lem2710215) (@lem2710214 n)). Qed.
Lemma lem2710217 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710218 (n : int) : (term427 n) = (term470 n).
Proof. exact (MK_COMB (@lem2710216 n) (@lem2710217)). Qed.
Lemma lem2710219 (n : int) : (term426 n) = (term470 n).
Proof. exact (TRANS (@lem2710028 n) (@lem2710218 n)). Qed.
Lemma lem2710220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710221 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710220) (@lem2709653 n)). Qed.
Lemma lem2710222 (n : int) : (term471 n) = (term472 n).
Proof. exact (MK_COMB (@lem2710221 n) (@lem2710219 n)). Qed.
Lemma lem2710223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710224 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710223) (@lem2709605 n)). Qed.
Lemma lem2710225 (n : int) : (term473 n) = (term474 n).
Proof. exact (MK_COMB (@lem2710224 n) (@lem2710222 n)). Qed.
Lemma lem2710226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710227 (n : int) : (term413 n) = (term413 n).
Proof. exact (MK_COMB (@lem2710226) (@lem2709908 n)). Qed.
Lemma lem2710228 (n : int) : (term330 n) = (term330 n).
Proof. exact (MK_COMB (@lem2710227 n) (@lem2709962 n)). Qed.
Lemma lem2710229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710230 (n : int) : (term475 n) = (term476 n).
Proof. exact (MK_COMB (@lem2710229) (@lem2710225 n)). Qed.
Lemma lem2710231 (n : int) : (term347 n) = (term477 n).
Proof. exact (MK_COMB (@lem2710230 n) (@lem2710228 n)). Qed.
Lemma lem2710232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710233 : term348 = term478.
Proof. exact (MK_COMB (@lem2710232) (@lem2710027)). Qed.
Lemma lem2710234 (n : int) : (term350 n) = (term479 n).
Proof. exact (MK_COMB (@lem2710233) (@lem2710231 n)). Qed.
Lemma lem2710235 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710236 (n : int) : (term357 n) = (term480 n).
Proof. exact (MK_COMB (@lem2710235) (@lem2709971 n)). Qed.
Lemma lem2710237 (n : int) : (term358 n) = (term481 n).
Proof. exact (MK_COMB (@lem2710236 n) (@lem2710234 n)). Qed.
Lemma lem2710249 (n : int) : (term343 n) = (term481 n).
Proof. exact (TRANS (@lem2709485 n) (@lem2710237 n)). Qed.
Lemma lem2710251 (n : int) : (term482 n) = (term482 n).
Proof. exact (eq_refl (term482 n)). Qed.
Lemma lem2710252 (n : int) : (term335 n) = (term483 n).
Proof. exact (MK_COMB (@lem2710251 n) (@lem2710249 n)). Qed.
Lemma lem2710257 (n : int) : (term484 n) = (term485 n).
Proof. exact (eq_refl (term484 n)). Qed.
Lemma lem2710258 (n : int) : (term485 n) = (term484 n).
Proof. exact (SYM (@lem2710257 n)). Qed.
Lemma lem2710259 (n : int) : (term484 n) = (term486 n).
Proof. exact (@lem1482981 (term487 n) term28). Qed.
Lemma lem2710260 (n : int) : (term485 n) = (term486 n).
Proof. exact (TRANS (@lem2710258 n) (@lem2710259 n)). Qed.
Lemma lem2710261 (n : int) : (term488 n) = (term489 n).
Proof. exact (eq_refl (term488 n)). Qed.
Lemma lem2710262 : term348 = term348.
Proof. exact (eq_refl term348). Qed.
Lemma lem2710263 (n : int) : (term490 n) = (term491 n).
Proof. exact (MK_COMB (@lem2710262) (@lem2710261 n)). Qed.
Lemma lem2710264 (n : int) : (term492 n) = (term493 n).
Proof. exact (eq_refl (term492 n)). Qed.
Lemma lem2710265 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem2710266 (n : int) : (term494 n) = (term495 n).
Proof. exact (MK_COMB (@lem2710265) (@lem2710264 n)). Qed.
Lemma lem2710267 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710268 (n : int) : (term496 n) = (term497 n).
Proof. exact (MK_COMB (@lem2710267) (@lem2710266 n)). Qed.
Lemma lem2710269 (n : int) : (term486 n) = (term498 n).
Proof. exact (MK_COMB (@lem2710268 n) (@lem2710263 n)). Qed.
Lemma lem2710270 (n : int) : (term499 n) = (term499 n).
Proof. exact (eq_refl (term499 n)). Qed.
Lemma lem2710271 (n : int) : ((term485 n) = (term486 n)) = ((term485 n) = (term498 n)).
Proof. exact (MK_COMB (@lem2710270 n) (@lem2710269 n)). Qed.
Lemma lem2710272 (n : int) : (term485 n) = (term498 n).
Proof. exact (EQ_MP (@lem2710271 n) (@lem2710260 n)). Qed.
Lemma lem2710273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710274 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710273) (@lem2709653 n)). Qed.
Lemma lem2710275 (n : int) : (term399 n) = (term400 n).
Proof. exact (MK_COMB (@lem2710274 n) (@lem2709842 n)). Qed.
Lemma lem2710276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710277 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710276) (@lem2709605 n)). Qed.
Lemma lem2710278 (n : int) : (term401 n) = (term402 n).
Proof. exact (MK_COMB (@lem2710277 n) (@lem2710275 n)). Qed.
Lemma lem2710279 (n : int) : (term244 n) = (term500 n).
Proof. exact (@lem1988291 (term241 n) term32). Qed.
Lemma lem2710291 (n : int) : (term501 n) = (term502 n).
Proof. exact (@lem1982792 (term241 n) term32). Qed.
Lemma lem2710293 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710294 : term32 = term137.
Proof. exact (@lem2710293 (NUMERAL 0)). Qed.
Lemma lem2710296 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710297 : term140 = term141.
Proof. exact (@lem2710296 term67). Qed.
Lemma lem2710298 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710299 : term142 = term143.
Proof. exact (MK_COMB (@lem2710298) (@lem2710297)). Qed.
Lemma lem2710300 : term144 = term145.
Proof. exact (MK_COMB (@lem2710299) (@lem2710294)). Qed.
Lemma lem2710301 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2710303 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710304 : term149 = term150.
Proof. exact (@lem2710303 term67 term67). Qed.
Lemma lem2710305 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710306 : term152 = term67.
Proof. exact (EQ_MP (@lem2710305) (@lem940073)). Qed.
Lemma lem2710307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710308 : term150 = term66.
Proof. exact (MK_COMB (@lem2710307) (@lem2710306)). Qed.
Lemma lem2710309 : term149 = term66.
Proof. exact (TRANS (@lem2710304) (@lem2710308)). Qed.
Lemma lem2710311 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2710312 : term144 = term32.
Proof. exact (@lem2710311 term67). Qed.
Lemma lem2710313 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2710314 : term154 = term155.
Proof. exact (MK_COMB (@lem2710313) (@lem2710312)). Qed.
Lemma lem2710315 : term146 = term137.
Proof. exact (MK_COMB (@lem2710314) (@lem2710309)). Qed.
Lemma lem2710316 : term145 = term137.
Proof. exact (TRANS (@lem2710301) (@lem2710315)). Qed.
Lemma lem2710317 : term144 = term137.
Proof. exact (TRANS (@lem2710300) (@lem2710316)). Qed.
Lemma lem2710319 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2710320 : term137 = term32.
Proof. exact (@lem2710319 term32). Qed.
Lemma lem2710321 : term144 = term32.
Proof. exact (TRANS (@lem2710317) (@lem2710320)). Qed.
Lemma lem2710322 (n : int) : (term503 n) = (term503 n).
Proof. exact (eq_refl (term503 n)). Qed.
Lemma lem2710323 (n : int) : (term502 n) = (term504 n).
Proof. exact (MK_COMB (@lem2710322 n) (@lem2710321)). Qed.
Lemma lem2710324 (n : int) : (term504 n) = (term241 n).
Proof. exact (@lem1982723 (term241 n)). Qed.
Lemma lem2710325 (n : int) : (term502 n) = (term241 n).
Proof. exact (TRANS (@lem2710323 n) (@lem2710324 n)). Qed.
Lemma lem2710327 (n : int) : (term501 n) = (term241 n).
Proof. exact (TRANS (@lem2710291 n) (@lem2710325 n)). Qed.
Lemma lem2710328 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2710329 (n : int) : (term505 n) = (term243 n).
Proof. exact (MK_COMB (@lem2710328) (@lem2710327 n)). Qed.
Lemma lem2710330 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710331 (n : int) : (term500 n) = (term244 n).
Proof. exact (MK_COMB (@lem2710329 n) (@lem2710330)). Qed.
Lemma lem2710332 (n : int) : (term244 n) = (term244 n).
Proof. exact (TRANS (@lem2710279 n) (@lem2710331 n)). Qed.
Lemma lem2710333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710334 (n : int) : (term506 n) = (term506 n).
Proof. exact (MK_COMB (@lem2710333) (@lem2710332 n)). Qed.
Lemma lem2710335 (n : int) : (term331 n) = (term331 n).
Proof. exact (MK_COMB (@lem2710334 n) (@lem2709962 n)). Qed.
Lemma lem2710336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710337 (n : int) : (term414 n) = (term415 n).
Proof. exact (MK_COMB (@lem2710336) (@lem2710278 n)). Qed.
Lemma lem2710338 (n : int) : (term493 n) = (term507 n).
Proof. exact (MK_COMB (@lem2710337 n) (@lem2710335 n)). Qed.
Lemma lem2710339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710340 : term353 = term353.
Proof. exact (MK_COMB (@lem2710339) (@lem2709533)). Qed.
Lemma lem2710341 (n : int) : (term495 n) = (term508 n).
Proof. exact (MK_COMB (@lem2710340) (@lem2710338 n)). Qed.
Lemma lem2710342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710343 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710342) (@lem2709653 n)). Qed.
Lemma lem2710344 (n : int) : (term471 n) = (term472 n).
Proof. exact (MK_COMB (@lem2710343 n) (@lem2710219 n)). Qed.
Lemma lem2710345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710346 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710345) (@lem2709605 n)). Qed.
Lemma lem2710347 (n : int) : (term473 n) = (term474 n).
Proof. exact (MK_COMB (@lem2710346 n) (@lem2710344 n)). Qed.
Lemma lem2710348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710349 (n : int) : (term506 n) = (term506 n).
Proof. exact (MK_COMB (@lem2710348) (@lem2710332 n)). Qed.
Lemma lem2710350 (n : int) : (term331 n) = (term331 n).
Proof. exact (MK_COMB (@lem2710349 n) (@lem2709962 n)). Qed.
Lemma lem2710351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710352 (n : int) : (term475 n) = (term476 n).
Proof. exact (MK_COMB (@lem2710351) (@lem2710347 n)). Qed.
Lemma lem2710353 (n : int) : (term489 n) = (term509 n).
Proof. exact (MK_COMB (@lem2710352 n) (@lem2710350 n)). Qed.
Lemma lem2710354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710355 : term348 = term478.
Proof. exact (MK_COMB (@lem2710354) (@lem2710027)). Qed.
Lemma lem2710356 (n : int) : (term491 n) = (term510 n).
Proof. exact (MK_COMB (@lem2710355) (@lem2710353 n)). Qed.
Lemma lem2710357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710358 (n : int) : (term497 n) = (term511 n).
Proof. exact (MK_COMB (@lem2710357) (@lem2710341 n)). Qed.
Lemma lem2710359 (n : int) : (term498 n) = (term512 n).
Proof. exact (MK_COMB (@lem2710358 n) (@lem2710356 n)). Qed.
Lemma lem2710371 (n : int) : (term485 n) = (term512 n).
Proof. exact (TRANS (@lem2710272 n) (@lem2710359 n)). Qed.
Lemma lem2710373 (n : int) : (term513 n) = (term513 n).
Proof. exact (eq_refl (term513 n)). Qed.
Lemma lem2710374 (n : int) : (term333 n) = (term514 n).
Proof. exact (MK_COMB (@lem2710373 n) (@lem2710371 n)). Qed.
Lemma lem2710375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710376 (n : int) : (term337 n) = (term515 n).
Proof. exact (MK_COMB (@lem2710375) (@lem2710252 n)). Qed.
Lemma lem2710377 (n : int) : (term338 n) = (term516 n).
Proof. exact (MK_COMB (@lem2710376 n) (@lem2710374 n)). Qed.
Lemma lem2710382 (n : int) : (term517 n) = (term518 n).
Proof. exact (eq_refl (term517 n)). Qed.
Lemma lem2710383 (n : int) : (term518 n) = (term517 n).
Proof. exact (SYM (@lem2710382 n)). Qed.
Lemma lem2710384 (n : int) : (term517 n) = (term519 n).
Proof. exact (@lem1482981 (term520 n) term28). Qed.
Lemma lem2710385 (n : int) : (term518 n) = (term519 n).
Proof. exact (TRANS (@lem2710383 n) (@lem2710384 n)). Qed.
Lemma lem2710386 (n : int) : (term521 n) = (term522 n).
Proof. exact (eq_refl (term521 n)). Qed.
Lemma lem2710387 : term348 = term348.
Proof. exact (eq_refl term348). Qed.
Lemma lem2710388 (n : int) : (term523 n) = (term524 n).
Proof. exact (MK_COMB (@lem2710387) (@lem2710386 n)). Qed.
Lemma lem2710389 (n : int) : (term525 n) = (term526 n).
Proof. exact (eq_refl (term525 n)). Qed.
Lemma lem2710390 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem2710391 (n : int) : (term527 n) = (term528 n).
Proof. exact (MK_COMB (@lem2710390) (@lem2710389 n)). Qed.
Lemma lem2710392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710393 (n : int) : (term529 n) = (term530 n).
Proof. exact (MK_COMB (@lem2710392) (@lem2710391 n)). Qed.
Lemma lem2710394 (n : int) : (term519 n) = (term531 n).
Proof. exact (MK_COMB (@lem2710393 n) (@lem2710388 n)). Qed.
Lemma lem2710395 (n : int) : (term532 n) = (term532 n).
Proof. exact (eq_refl (term532 n)). Qed.
Lemma lem2710396 (n : int) : ((term518 n) = (term519 n)) = ((term518 n) = (term531 n)).
Proof. exact (MK_COMB (@lem2710395 n) (@lem2710394 n)). Qed.
Lemma lem2710397 (n : int) : (term518 n) = (term531 n).
Proof. exact (EQ_MP (@lem2710396 n) (@lem2710385 n)). Qed.
Lemma lem2710398 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710399 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710398) (@lem2709653 n)). Qed.
Lemma lem2710400 (n : int) : (term399 n) = (term400 n).
Proof. exact (MK_COMB (@lem2710399 n) (@lem2709842 n)). Qed.
Lemma lem2710401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710402 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710401) (@lem2709605 n)). Qed.
Lemma lem2710403 (n : int) : (term401 n) = (term402 n).
Proof. exact (MK_COMB (@lem2710402 n) (@lem2710400 n)). Qed.
Lemma lem2710404 (n : int) : (term300 n) = (term533 n).
Proof. exact (@lem1988291 (term297 n) term32). Qed.
Lemma lem2710416 (n : int) : (term534 n) = (term535 n).
Proof. exact (@lem1982792 (term297 n) term32). Qed.
Lemma lem2710418 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710419 : term32 = term137.
Proof. exact (@lem2710418 (NUMERAL 0)). Qed.
Lemma lem2710421 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710422 : term140 = term141.
Proof. exact (@lem2710421 term67). Qed.
Lemma lem2710423 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710424 : term142 = term143.
Proof. exact (MK_COMB (@lem2710423) (@lem2710422)). Qed.
Lemma lem2710425 : term144 = term145.
Proof. exact (MK_COMB (@lem2710424) (@lem2710419)). Qed.
Lemma lem2710426 : term145 = term146.
Proof. exact (@lem1981613 term140 term32 term66 term66). Qed.
Lemma lem2710428 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710429 : term149 = term150.
Proof. exact (@lem2710428 term67 term67). Qed.
Lemma lem2710430 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710431 : term152 = term67.
Proof. exact (EQ_MP (@lem2710430) (@lem940073)). Qed.
Lemma lem2710432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710433 : term150 = term66.
Proof. exact (MK_COMB (@lem2710432) (@lem2710431)). Qed.
Lemma lem2710434 : term149 = term66.
Proof. exact (TRANS (@lem2710429) (@lem2710433)). Qed.
Lemma lem2710436 (x : nat) : (term153 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2710437 : term144 = term32.
Proof. exact (@lem2710436 term67). Qed.
Lemma lem2710438 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2710439 : term154 = term155.
Proof. exact (MK_COMB (@lem2710438) (@lem2710437)). Qed.
Lemma lem2710440 : term146 = term137.
Proof. exact (MK_COMB (@lem2710439) (@lem2710434)). Qed.
Lemma lem2710441 : term145 = term137.
Proof. exact (TRANS (@lem2710426) (@lem2710440)). Qed.
Lemma lem2710442 : term144 = term137.
Proof. exact (TRANS (@lem2710425) (@lem2710441)). Qed.
Lemma lem2710444 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2710445 : term137 = term32.
Proof. exact (@lem2710444 term32). Qed.
Lemma lem2710446 : term144 = term32.
Proof. exact (TRANS (@lem2710442) (@lem2710445)). Qed.
Lemma lem2710447 (n : int) : (term536 n) = (term536 n).
Proof. exact (eq_refl (term536 n)). Qed.
Lemma lem2710448 (n : int) : (term535 n) = (term537 n).
Proof. exact (MK_COMB (@lem2710447 n) (@lem2710446)). Qed.
Lemma lem2710449 (n : int) : (term537 n) = (term297 n).
Proof. exact (@lem1982723 (term297 n)). Qed.
Lemma lem2710450 (n : int) : (term535 n) = (term297 n).
Proof. exact (TRANS (@lem2710448 n) (@lem2710449 n)). Qed.
Lemma lem2710452 (n : int) : (term534 n) = (term297 n).
Proof. exact (TRANS (@lem2710416 n) (@lem2710450 n)). Qed.
Lemma lem2710453 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2710454 (n : int) : (term538 n) = (term299 n).
Proof. exact (MK_COMB (@lem2710453) (@lem2710452 n)). Qed.
Lemma lem2710455 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710456 (n : int) : (term533 n) = (term300 n).
Proof. exact (MK_COMB (@lem2710454 n) (@lem2710455)). Qed.
Lemma lem2710457 (n : int) : (term300 n) = (term300 n).
Proof. exact (TRANS (@lem2710404 n) (@lem2710456 n)). Qed.
Lemma lem2710458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710459 (n : int) : (term413 n) = (term413 n).
Proof. exact (MK_COMB (@lem2710458) (@lem2709908 n)). Qed.
Lemma lem2710460 (n : int) : (term319 n) = (term319 n).
Proof. exact (MK_COMB (@lem2710459 n) (@lem2710457 n)). Qed.
Lemma lem2710461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710462 (n : int) : (term414 n) = (term415 n).
Proof. exact (MK_COMB (@lem2710461) (@lem2710403 n)). Qed.
Lemma lem2710463 (n : int) : (term526 n) = (term539 n).
Proof. exact (MK_COMB (@lem2710462 n) (@lem2710460 n)). Qed.
Lemma lem2710464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710465 : term353 = term353.
Proof. exact (MK_COMB (@lem2710464) (@lem2709533)). Qed.
Lemma lem2710466 (n : int) : (term528 n) = (term540 n).
Proof. exact (MK_COMB (@lem2710465) (@lem2710463 n)). Qed.
Lemma lem2710467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710468 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710467) (@lem2709653 n)). Qed.
Lemma lem2710469 (n : int) : (term471 n) = (term472 n).
Proof. exact (MK_COMB (@lem2710468 n) (@lem2710219 n)). Qed.
Lemma lem2710470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710471 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710470) (@lem2709605 n)). Qed.
Lemma lem2710472 (n : int) : (term473 n) = (term474 n).
Proof. exact (MK_COMB (@lem2710471 n) (@lem2710469 n)). Qed.
Lemma lem2710473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710474 (n : int) : (term413 n) = (term413 n).
Proof. exact (MK_COMB (@lem2710473) (@lem2709908 n)). Qed.
Lemma lem2710475 (n : int) : (term319 n) = (term319 n).
Proof. exact (MK_COMB (@lem2710474 n) (@lem2710457 n)). Qed.
Lemma lem2710476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710477 (n : int) : (term475 n) = (term476 n).
Proof. exact (MK_COMB (@lem2710476) (@lem2710472 n)). Qed.
Lemma lem2710478 (n : int) : (term522 n) = (term541 n).
Proof. exact (MK_COMB (@lem2710477 n) (@lem2710475 n)). Qed.
Lemma lem2710479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710480 : term348 = term478.
Proof. exact (MK_COMB (@lem2710479) (@lem2710027)). Qed.
Lemma lem2710481 (n : int) : (term524 n) = (term542 n).
Proof. exact (MK_COMB (@lem2710480) (@lem2710478 n)). Qed.
Lemma lem2710482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710483 (n : int) : (term530 n) = (term543 n).
Proof. exact (MK_COMB (@lem2710482) (@lem2710466 n)). Qed.
Lemma lem2710484 (n : int) : (term531 n) = (term544 n).
Proof. exact (MK_COMB (@lem2710483 n) (@lem2710481 n)). Qed.
Lemma lem2710496 (n : int) : (term518 n) = (term544 n).
Proof. exact (TRANS (@lem2710397 n) (@lem2710484 n)). Qed.
Lemma lem2710498 (n : int) : (term545 n) = (term545 n).
Proof. exact (eq_refl (term545 n)). Qed.
Lemma lem2710499 (n : int) : (term324 n) = (term546 n).
Proof. exact (MK_COMB (@lem2710498 n) (@lem2710496 n)). Qed.
Lemma lem2710504 (n : int) : (term547 n) = (term548 n).
Proof. exact (eq_refl (term547 n)). Qed.
Lemma lem2710505 (n : int) : (term548 n) = (term547 n).
Proof. exact (SYM (@lem2710504 n)). Qed.
Lemma lem2710506 (n : int) : (term547 n) = (term549 n).
Proof. exact (@lem1482981 (term550 n) term28). Qed.
Lemma lem2710507 (n : int) : (term548 n) = (term549 n).
Proof. exact (TRANS (@lem2710505 n) (@lem2710506 n)). Qed.
Lemma lem2710508 (n : int) : (term551 n) = (term552 n).
Proof. exact (eq_refl (term551 n)). Qed.
Lemma lem2710509 : term348 = term348.
Proof. exact (eq_refl term348). Qed.
Lemma lem2710510 (n : int) : (term553 n) = (term554 n).
Proof. exact (MK_COMB (@lem2710509) (@lem2710508 n)). Qed.
Lemma lem2710511 (n : int) : (term555 n) = (term556 n).
Proof. exact (eq_refl (term555 n)). Qed.
Lemma lem2710512 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem2710513 (n : int) : (term557 n) = (term558 n).
Proof. exact (MK_COMB (@lem2710512) (@lem2710511 n)). Qed.
Lemma lem2710514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710515 (n : int) : (term559 n) = (term560 n).
Proof. exact (MK_COMB (@lem2710514) (@lem2710513 n)). Qed.
Lemma lem2710516 (n : int) : (term549 n) = (term561 n).
Proof. exact (MK_COMB (@lem2710515 n) (@lem2710510 n)). Qed.
Lemma lem2710517 (n : int) : (term562 n) = (term562 n).
Proof. exact (eq_refl (term562 n)). Qed.
Lemma lem2710518 (n : int) : ((term548 n) = (term549 n)) = ((term548 n) = (term561 n)).
Proof. exact (MK_COMB (@lem2710517 n) (@lem2710516 n)). Qed.
Lemma lem2710519 (n : int) : (term548 n) = (term561 n).
Proof. exact (EQ_MP (@lem2710518 n) (@lem2710507 n)). Qed.
Lemma lem2710520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710521 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710520) (@lem2709653 n)). Qed.
Lemma lem2710522 (n : int) : (term399 n) = (term400 n).
Proof. exact (MK_COMB (@lem2710521 n) (@lem2709842 n)). Qed.
Lemma lem2710523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710524 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710523) (@lem2709605 n)). Qed.
Lemma lem2710525 (n : int) : (term401 n) = (term402 n).
Proof. exact (MK_COMB (@lem2710524 n) (@lem2710522 n)). Qed.
Lemma lem2710526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710527 (n : int) : (term506 n) = (term506 n).
Proof. exact (MK_COMB (@lem2710526) (@lem2710332 n)). Qed.
Lemma lem2710528 (n : int) : (term320 n) = (term320 n).
Proof. exact (MK_COMB (@lem2710527 n) (@lem2710457 n)). Qed.
Lemma lem2710529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710530 (n : int) : (term414 n) = (term415 n).
Proof. exact (MK_COMB (@lem2710529) (@lem2710525 n)). Qed.
Lemma lem2710531 (n : int) : (term556 n) = (term563 n).
Proof. exact (MK_COMB (@lem2710530 n) (@lem2710528 n)). Qed.
Lemma lem2710532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710533 : term353 = term353.
Proof. exact (MK_COMB (@lem2710532) (@lem2709533)). Qed.
Lemma lem2710534 (n : int) : (term558 n) = (term564 n).
Proof. exact (MK_COMB (@lem2710533) (@lem2710531 n)). Qed.
Lemma lem2710535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710536 (n : int) : (term224 n) = (term224 n).
Proof. exact (MK_COMB (@lem2710535) (@lem2709653 n)). Qed.
Lemma lem2710537 (n : int) : (term471 n) = (term472 n).
Proof. exact (MK_COMB (@lem2710536 n) (@lem2710219 n)). Qed.
Lemma lem2710538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710539 (n : int) : (term226 n) = (term226 n).
Proof. exact (MK_COMB (@lem2710538) (@lem2709605 n)). Qed.
Lemma lem2710540 (n : int) : (term473 n) = (term474 n).
Proof. exact (MK_COMB (@lem2710539 n) (@lem2710537 n)). Qed.
Lemma lem2710541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710542 (n : int) : (term506 n) = (term506 n).
Proof. exact (MK_COMB (@lem2710541) (@lem2710332 n)). Qed.
Lemma lem2710543 (n : int) : (term320 n) = (term320 n).
Proof. exact (MK_COMB (@lem2710542 n) (@lem2710457 n)). Qed.
Lemma lem2710544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710545 (n : int) : (term475 n) = (term476 n).
Proof. exact (MK_COMB (@lem2710544) (@lem2710540 n)). Qed.
Lemma lem2710546 (n : int) : (term552 n) = (term565 n).
Proof. exact (MK_COMB (@lem2710545 n) (@lem2710543 n)). Qed.
Lemma lem2710547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2710548 : term348 = term478.
Proof. exact (MK_COMB (@lem2710547) (@lem2710027)). Qed.
Lemma lem2710549 (n : int) : (term554 n) = (term566 n).
Proof. exact (MK_COMB (@lem2710548) (@lem2710546 n)). Qed.
Lemma lem2710550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710551 (n : int) : (term560 n) = (term567 n).
Proof. exact (MK_COMB (@lem2710550) (@lem2710534 n)). Qed.
Lemma lem2710552 (n : int) : (term561 n) = (term568 n).
Proof. exact (MK_COMB (@lem2710551 n) (@lem2710549 n)). Qed.
Lemma lem2710564 (n : int) : (term548 n) = (term568 n).
Proof. exact (TRANS (@lem2710519 n) (@lem2710552 n)). Qed.
Lemma lem2710566 (n : int) : (term569 n) = (term569 n).
Proof. exact (eq_refl (term569 n)). Qed.
Lemma lem2710567 (n : int) : (term322 n) = (term570 n).
Proof. exact (MK_COMB (@lem2710566 n) (@lem2710564 n)). Qed.
Lemma lem2710568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710569 (n : int) : (term326 n) = (term571 n).
Proof. exact (MK_COMB (@lem2710568) (@lem2710499 n)). Qed.
Lemma lem2710570 (n : int) : (term327 n) = (term572 n).
Proof. exact (MK_COMB (@lem2710569 n) (@lem2710567 n)). Qed.
Lemma lem2710571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2710572 (n : int) : (term340 n) = (term573 n).
Proof. exact (MK_COMB (@lem2710571) (@lem2710377 n)). Qed.
Lemma lem2710573 (n : int) : (term341 n) = (term574 n).
Proof. exact (MK_COMB (@lem2710572 n) (@lem2710570 n)). Qed.
Lemma lem2710574 (n : int) (h1 : term574 n) : term574 n.
Proof. exact (h1). Qed.
Lemma lem2710575 (n : int) (h1 : term516 n) : term516 n.
Proof. exact (h1). Qed.
Lemma lem2710576 (n : int) (h1 : term483 n) : term483 n.
Proof. exact (h1). Qed.
Lemma lem2710577 (n : int) (h1 : term575 n) : term575 n.
Proof. exact (h1). Qed.
Lemma lem2710579 (n : int) (h1 : term575 n) : term28 = term32.
Proof. exact (proj1 (@lem2710577 n h1)). Qed.
Lemma lem2710583 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710584 : term32 = term137.
Proof. exact (@lem2710583 (NUMERAL 0)). Qed.
Lemma lem2710586 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710587 : term28 = term173.
Proof. exact (@lem2710586 term29). Qed.
Lemma lem2710588 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2710589 : term31 = term576.
Proof. exact (MK_COMB (@lem2710588) (@lem2710587)). Qed.
Lemma lem2710590 : (term28 = term32) = (term173 = term137).
Proof. exact (MK_COMB (@lem2710589) (@lem2710584)). Qed.
Lemma lem2710591 : term577.
Proof. exact (@lem1980277 term28 term66 term32 term66). Qed.
Lemma lem2710593 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710594 : term257 = term258.
Proof. exact (@lem2710593 (NUMERAL 0) term67). Qed.
Lemma lem2710595 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710596 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710597 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710596 h1) (fun h1 : term258 = True => @lem2710595)). Qed.
Lemma lem2710598 : term258 = True.
Proof. exact (EQ_MP (@lem2710597) (@lem2710595)). Qed.
Lemma lem2710599 : term257 = True.
Proof. exact (TRANS (@lem2710594) (@lem2710598)). Qed.
Lemma lem2710600 : True = term257.
Proof. exact (SYM (@lem2710599)). Qed.
Lemma lem2710601 : term257.
Proof. exact (EQ_MP (@lem2710600) (@lem0)). Qed.
Lemma lem2710602 : term578.
Proof. exact (@lem2710591 (@lem2710601)). Qed.
Lemma lem2710604 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710605 : term257 = term258.
Proof. exact (@lem2710604 (NUMERAL 0) term67). Qed.
Lemma lem2710606 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710607 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710608 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710607 h1) (fun h1 : term258 = True => @lem2710606)). Qed.
Lemma lem2710609 : term258 = True.
Proof. exact (EQ_MP (@lem2710608) (@lem2710606)). Qed.
Lemma lem2710610 : term257 = True.
Proof. exact (TRANS (@lem2710605) (@lem2710609)). Qed.
Lemma lem2710611 : True = term257.
Proof. exact (SYM (@lem2710610)). Qed.
Lemma lem2710612 : term257.
Proof. exact (EQ_MP (@lem2710611) (@lem0)). Qed.
Lemma lem2710613 : (term173 = term137) = (term289 = term269).
Proof. exact (@lem2710602 (@lem2710612)). Qed.
Lemma lem2710615 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2710616 : term269 = term32.
Proof. exact (@lem2710615 term67). Qed.
Lemma lem2710618 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710619 : term289 = term290.
Proof. exact (@lem2710618 term29 term67). Qed.
Lemma lem2710620 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2710621 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2710622 : term292 = term29.
Proof. exact (EQ_MP (@lem2710621) (@lem2710620)). Qed.
Lemma lem2710623 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710624 : term290 = term28.
Proof. exact (MK_COMB (@lem2710623) (@lem2710622)). Qed.
Lemma lem2710625 : term289 = term28.
Proof. exact (TRANS (@lem2710619) (@lem2710624)). Qed.
Lemma lem2710626 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2710627 : term579 = term31.
Proof. exact (MK_COMB (@lem2710626) (@lem2710625)). Qed.
Lemma lem2710628 : (term289 = term269) = (term28 = term32).
Proof. exact (MK_COMB (@lem2710627) (@lem2710616)). Qed.
Lemma lem2710630 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem2710631 : (term28 = term32) = (term29 = (NUMERAL 0)).
Proof. exact (@lem2710630 term29 (NUMERAL 0)). Qed.
Lemma lem2710632 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2710633 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2710634 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2710633 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2710632)). Qed.
Lemma lem2710635 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2710634) (@lem2710632)). Qed.
Lemma lem2710636 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2710631) (@lem2710635)). Qed.
Lemma lem2710637 : (term289 = term269) = False.
Proof. exact (TRANS (@lem2710628) (@lem2710636)). Qed.
Lemma lem2710638 : (term173 = term137) = False.
Proof. exact (TRANS (@lem2710613) (@lem2710637)). Qed.
Lemma lem2710639 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2710590) (@lem2710638)). Qed.
Lemma lem2710640 (n : int) (h1 : term575 n) : False.
Proof. exact (EQ_MP (@lem2710639) (@lem2710579 n h1)). Qed.
Lemma lem2710641 (n : int) (h1 : term481 n) : term481 n.
Proof. exact (h1). Qed.
Lemma lem2710642 (n : int) (h1 : term417 n) : term417 n.
Proof. exact (h1). Qed.
Lemma lem2710643 (n : int) (h1 : term417 n) : term416 n.
Proof. exact (proj2 (@lem2710642 n h1)). Qed.
Lemma lem2710645 (n : int) (h1 : term417 n) : term330 n.
Proof. exact (proj2 (@lem2710643 n h1)). Qed.
Lemma lem2710646 (n : int) (h1 : term417 n) : term402 n.
Proof. exact (proj1 (@lem2710643 n h1)). Qed.
Lemma lem2710647 (n : int) (h1 : term417 n) : term400 n.
Proof. exact (proj2 (@lem2710646 n h1)). Qed.
Lemma lem2710648 (n : int) (h1 : term417 n) : (term195 n) = term32.
Proof. exact (proj1 (@lem2710646 n h1)). Qed.
Lemma lem2710650 (n : int) (h1 : term417 n) : term204 n.
Proof. exact (proj1 (@lem2710647 n h1)). Qed.
Lemma lem2710652 (n : int) (h1 : term417 n) : term235 n.
Proof. exact (proj1 (@lem2710645 n h1)). Qed.
Lemma lem2710654 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2710655 : term581 = term257.
Proof. exact (@lem2710654 term32 term66). Qed.
Lemma lem2710657 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710658 : term66 = term210.
Proof. exact (@lem2710657 term67). Qed.
Lemma lem2710660 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710661 : term32 = term137.
Proof. exact (@lem2710660 (NUMERAL 0)). Qed.
Lemma lem2710662 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2710663 : term582 = term583.
Proof. exact (MK_COMB (@lem2710662) (@lem2710661)). Qed.
Lemma lem2710664 : term257 = term584.
Proof. exact (MK_COMB (@lem2710663) (@lem2710658)). Qed.
Lemma lem2710665 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2710667 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710668 : term257 = term258.
Proof. exact (@lem2710667 (NUMERAL 0) term67). Qed.
Lemma lem2710669 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710670 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710671 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710670 h1) (fun h1 : term258 = True => @lem2710669)). Qed.
Lemma lem2710672 : term258 = True.
Proof. exact (EQ_MP (@lem2710671) (@lem2710669)). Qed.
Lemma lem2710673 : term257 = True.
Proof. exact (TRANS (@lem2710668) (@lem2710672)). Qed.
Lemma lem2710674 : True = term257.
Proof. exact (SYM (@lem2710673)). Qed.
Lemma lem2710675 : term257.
Proof. exact (EQ_MP (@lem2710674) (@lem0)). Qed.
Lemma lem2710676 : term586.
Proof. exact (@lem2710665 (@lem2710675)). Qed.
Lemma lem2710678 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710679 : term257 = term258.
Proof. exact (@lem2710678 (NUMERAL 0) term67). Qed.
Lemma lem2710680 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710681 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710682 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710681 h1) (fun h1 : term258 = True => @lem2710680)). Qed.
Lemma lem2710683 : term258 = True.
Proof. exact (EQ_MP (@lem2710682) (@lem2710680)). Qed.
Lemma lem2710684 : term257 = True.
Proof. exact (TRANS (@lem2710679) (@lem2710683)). Qed.
Lemma lem2710685 : True = term257.
Proof. exact (SYM (@lem2710684)). Qed.
Lemma lem2710686 : term257.
Proof. exact (EQ_MP (@lem2710685) (@lem0)). Qed.
Lemma lem2710687 : term584 = term587.
Proof. exact (@lem2710676 (@lem2710686)). Qed.
Lemma lem2710689 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710690 : term149 = term150.
Proof. exact (@lem2710689 term67 term67). Qed.
Lemma lem2710691 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710692 : term152 = term67.
Proof. exact (EQ_MP (@lem2710691) (@lem940073)). Qed.
Lemma lem2710693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710694 : term150 = term66.
Proof. exact (MK_COMB (@lem2710693) (@lem2710692)). Qed.
Lemma lem2710695 : term149 = term66.
Proof. exact (TRANS (@lem2710690) (@lem2710694)). Qed.
Lemma lem2710697 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2710698 : term269 = term32.
Proof. exact (@lem2710697 term67). Qed.
Lemma lem2710699 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2710700 : term588 = term582.
Proof. exact (MK_COMB (@lem2710699) (@lem2710698)). Qed.
Lemma lem2710701 : term587 = term257.
Proof. exact (MK_COMB (@lem2710700) (@lem2710695)). Qed.
Lemma lem2710703 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710704 : term257 = term258.
Proof. exact (@lem2710703 (NUMERAL 0) term67). Qed.
Lemma lem2710705 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710706 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710707 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710706 h1) (fun h1 : term258 = True => @lem2710705)). Qed.
Lemma lem2710708 : term258 = True.
Proof. exact (EQ_MP (@lem2710707) (@lem2710705)). Qed.
Lemma lem2710709 : term257 = True.
Proof. exact (TRANS (@lem2710704) (@lem2710708)). Qed.
Lemma lem2710710 : term587 = True.
Proof. exact (TRANS (@lem2710701) (@lem2710709)). Qed.
Lemma lem2710711 : term584 = True.
Proof. exact (TRANS (@lem2710687) (@lem2710710)). Qed.
Lemma lem2710712 : term257 = True.
Proof. exact (TRANS (@lem2710664) (@lem2710711)). Qed.
Lemma lem2710713 : term581 = True.
Proof. exact (TRANS (@lem2710655) (@lem2710712)). Qed.
Lemma lem2710714 : True = term581.
Proof. exact (SYM (@lem2710713)). Qed.
Lemma lem2710715 : term581.
Proof. exact (EQ_MP (@lem2710714) (@lem0)). Qed.
Lemma lem2710716 (n : int) (h1 : term417 n) : term589 n.
Proof. exact (conj (@lem2710715) (@lem2710652 n h1)). Qed.
Lemma lem2710718 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2710719 (n : int) : term591 n.
Proof. exact (@lem2710718 term66 (term218 n)). Qed.
Lemma lem2710720 (n : int) (h1 : term417 n) : term592 n.
Proof. exact (@lem2710719 n (@lem2710716 n h1)). Qed.
Lemma lem2710721 (n : int) : (term593 n) = (term218 n).
Proof. exact (@lem1982733 (term218 n)). Qed.
Lemma lem2710722 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2710723 (n : int) : (term594 n) = (term234 n).
Proof. exact (MK_COMB (@lem2710722) (@lem2710721 n)). Qed.
Lemma lem2710724 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710725 (n : int) : (term592 n) = (term235 n).
Proof. exact (MK_COMB (@lem2710723 n) (@lem2710724)). Qed.
Lemma lem2710726 (n : int) (h1 : term417 n) : term235 n.
Proof. exact (EQ_MP (@lem2710725 n) (@lem2710720 n h1)). Qed.
Lemma lem2710728 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2710729 (n : int) : term596 n.
Proof. exact (@lem2710728 (term195 n)). Qed.
Lemma lem2710730 (n : int) (h1 : term417 n) : term597 n.
Proof. exact (@lem2710729 n (@lem2710648 n h1)). Qed.
Lemma lem2710731 (n : int) (h1 : term417 n) : term598 n.
Proof. exact (@lem2710730 n h1 term140). Qed.
Lemma lem2710732 (n : int) : (term598 n) = ((term599 n) = term32).
Proof. exact (eq_refl (term598 n)). Qed.
Lemma lem2710733 (n : int) (h1 : term417 n) : (term599 n) = term32.
Proof. exact (EQ_MP (@lem2710732 n) (@lem2710731 n h1)). Qed.
Lemma lem2710734 (n : int) : (term599 n) = (term600 n).
Proof. exact (@lem1982781 (real_of_int n) term140 (term193 n)). Qed.
Lemma lem2710735 (n : int) : (term601 n) = (term602 n).
Proof. exact (@lem1982781 (term190 n) term140 (term170 n)). Qed.
Lemma lem2710736 (n : int) : (term603 n) = (term604 n).
Proof. exact (@lem1982749 term140 term140 (term48 n)). Qed.
Lemma lem2710738 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710739 : term140 = term141.
Proof. exact (@lem2710738 term67). Qed.
Lemma lem2710741 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710742 : term140 = term141.
Proof. exact (@lem2710741 term67). Qed.
Lemma lem2710743 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710744 : term142 = term143.
Proof. exact (MK_COMB (@lem2710743) (@lem2710742)). Qed.
Lemma lem2710745 : term605 = term606.
Proof. exact (MK_COMB (@lem2710744) (@lem2710739)). Qed.
Lemma lem2710746 : term606 = term607.
Proof. exact (@lem1981613 term140 term140 term66 term66). Qed.
Lemma lem2710748 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710749 : term149 = term150.
Proof. exact (@lem2710748 term67 term67). Qed.
Lemma lem2710750 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710751 : term152 = term67.
Proof. exact (EQ_MP (@lem2710750) (@lem940073)). Qed.
Lemma lem2710752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710753 : term150 = term66.
Proof. exact (MK_COMB (@lem2710752) (@lem2710751)). Qed.
Lemma lem2710754 : term149 = term66.
Proof. exact (TRANS (@lem2710749) (@lem2710753)). Qed.
Lemma lem2710756 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2710757 : term605 = term150.
Proof. exact (@lem2710756 term67 term67). Qed.
Lemma lem2710758 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710759 : term152 = term67.
Proof. exact (EQ_MP (@lem2710758) (@lem940073)). Qed.
Lemma lem2710760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710761 : term150 = term66.
Proof. exact (MK_COMB (@lem2710760) (@lem2710759)). Qed.
Lemma lem2710762 : term605 = term66.
Proof. exact (TRANS (@lem2710757) (@lem2710761)). Qed.
Lemma lem2710763 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2710764 : term609 = term610.
Proof. exact (MK_COMB (@lem2710763) (@lem2710762)). Qed.
Lemma lem2710765 : term607 = term210.
Proof. exact (MK_COMB (@lem2710764) (@lem2710754)). Qed.
Lemma lem2710766 : term606 = term210.
Proof. exact (TRANS (@lem2710746) (@lem2710765)). Qed.
Lemma lem2710767 : term605 = term210.
Proof. exact (TRANS (@lem2710745) (@lem2710766)). Qed.
Lemma lem2710769 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2710770 : term210 = term66.
Proof. exact (@lem2710769 term66). Qed.
Lemma lem2710771 : term605 = term66.
Proof. exact (TRANS (@lem2710767) (@lem2710770)). Qed.
Lemma lem2710772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710773 : term611 = term385.
Proof. exact (MK_COMB (@lem2710772) (@lem2710771)). Qed.
Lemma lem2710774 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2710775 (n : int) : (term604 n) = (term612 n).
Proof. exact (MK_COMB (@lem2710773) (@lem2710774 n)). Qed.
Lemma lem2710776 (n : int) : (term603 n) = (term612 n).
Proof. exact (TRANS (@lem2710736 n) (@lem2710775 n)). Qed.
Lemma lem2710777 (n : int) : (term612 n) = (term48 n).
Proof. exact (@lem1982709 (term48 n)). Qed.
Lemma lem2710778 (n : int) : (term603 n) = (term48 n).
Proof. exact (TRANS (@lem2710776 n) (@lem2710777 n)). Qed.
Lemma lem2710779 (n : int) : (term613 n) = (term614 n).
Proof. exact (@lem1982749 term140 term184 (term162 n)). Qed.
Lemma lem2710781 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710782 : term184 = term187.
Proof. exact (@lem2710781 term29). Qed.
Lemma lem2710784 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710785 : term140 = term141.
Proof. exact (@lem2710784 term67). Qed.
Lemma lem2710786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710787 : term142 = term143.
Proof. exact (MK_COMB (@lem2710786) (@lem2710785)). Qed.
Lemma lem2710788 : term615 = term616.
Proof. exact (MK_COMB (@lem2710787) (@lem2710782)). Qed.
Lemma lem2710789 : term616 = term617.
Proof. exact (@lem1981613 term140 term184 term66 term66). Qed.
Lemma lem2710791 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710792 : term149 = term150.
Proof. exact (@lem2710791 term67 term67). Qed.
Lemma lem2710793 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710794 : term152 = term67.
Proof. exact (EQ_MP (@lem2710793) (@lem940073)). Qed.
Lemma lem2710795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710796 : term150 = term66.
Proof. exact (MK_COMB (@lem2710795) (@lem2710794)). Qed.
Lemma lem2710797 : term149 = term66.
Proof. exact (TRANS (@lem2710792) (@lem2710796)). Qed.
Lemma lem2710799 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2710800 : term615 = term183.
Proof. exact (@lem2710799 term67 term29). Qed.
Lemma lem2710801 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2710802 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2710803 : term182 = term29.
Proof. exact (EQ_MP (@lem2710802) (@lem2710801)). Qed.
Lemma lem2710804 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710805 : term183 = term28.
Proof. exact (MK_COMB (@lem2710804) (@lem2710803)). Qed.
Lemma lem2710806 : term615 = term28.
Proof. exact (TRANS (@lem2710800) (@lem2710805)). Qed.
Lemma lem2710807 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2710808 : term618 = term619.
Proof. exact (MK_COMB (@lem2710807) (@lem2710806)). Qed.
Lemma lem2710809 : term617 = term173.
Proof. exact (MK_COMB (@lem2710808) (@lem2710797)). Qed.
Lemma lem2710810 : term616 = term173.
Proof. exact (TRANS (@lem2710789) (@lem2710809)). Qed.
Lemma lem2710811 : term615 = term173.
Proof. exact (TRANS (@lem2710788) (@lem2710810)). Qed.
Lemma lem2710813 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2710814 : term173 = term28.
Proof. exact (@lem2710813 term28). Qed.
Lemma lem2710815 : term615 = term28.
Proof. exact (TRANS (@lem2710811) (@lem2710814)). Qed.
Lemma lem2710816 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710817 : term620 = term287.
Proof. exact (MK_COMB (@lem2710816) (@lem2710815)). Qed.
Lemma lem2710818 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2710819 (n : int) : (term614 n) = (term161 n).
Proof. exact (MK_COMB (@lem2710817) (@lem2710818 n)). Qed.
Lemma lem2710820 (n : int) : (term613 n) = (term161 n).
Proof. exact (TRANS (@lem2710779 n) (@lem2710819 n)). Qed.
Lemma lem2710821 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2710822 (n : int) : (term621 n) = (term163 n).
Proof. exact (MK_COMB (@lem2710821) (@lem2710820 n)). Qed.
Lemma lem2710823 (n : int) : (term602 n) = (term164 n).
Proof. exact (MK_COMB (@lem2710822 n) (@lem2710778 n)). Qed.
Lemma lem2710824 (n : int) : (term601 n) = (term164 n).
Proof. exact (TRANS (@lem2710735 n) (@lem2710823 n)). Qed.
Lemma lem2710827 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2710828 (n : int) : (term600 n) = (term623 n).
Proof. exact (MK_COMB (@lem2710827 n) (@lem2710824 n)). Qed.
Lemma lem2710829 (n : int) : (term599 n) = (term623 n).
Proof. exact (TRANS (@lem2710734 n) (@lem2710828 n)). Qed.
Lemma lem2710830 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2710831 (n : int) : (term624 n) = (term625 n).
Proof. exact (MK_COMB (@lem2710830) (@lem2710829 n)). Qed.
Lemma lem2710832 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710833 (n : int) : ((term599 n) = term32) = ((term623 n) = term32).
Proof. exact (MK_COMB (@lem2710831 n) (@lem2710832)). Qed.
Lemma lem2710834 (n : int) (h1 : term417 n) : (term623 n) = term32.
Proof. exact (EQ_MP (@lem2710833 n) (@lem2710733 n h1)). Qed.
Lemma lem2710835 (n : int) (h1 : term417 n) : term626 n.
Proof. exact (conj (@lem2710834 n h1) (@lem2710726 n h1)). Qed.
Lemma lem2710837 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2710838 (n : int) : term628 n.
Proof. exact (@lem2710837 (term623 n) (term218 n)). Qed.
Lemma lem2710839 (n : int) (h1 : term417 n) : term629 n.
Proof. exact (@lem2710838 n (@lem2710835 n h1)). Qed.
Lemma lem2710840 (n : int) : (term630 n) = (term631 n).
Proof. exact (@lem1982755 (term632 n) (term164 n) (term218 n)). Qed.
Lemma lem2710841 (n : int) : (term633 n) = (term634 n).
Proof. exact (@lem1982755 (term161 n) (term48 n) (term218 n)). Qed.
Lemma lem2710842 (n : int) : (term635 n) = (term636 n).
Proof. exact (@lem1982763 (term48 n) (term170 n) term140). Qed.
Lemma lem2710843 (n : int) : (term637 n) = (term638 n).
Proof. exact (@lem1982715 term140 (term48 n)). Qed.
Lemma lem2710845 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710846 : term66 = term210.
Proof. exact (@lem2710845 term67). Qed.
Lemma lem2710848 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2710849 : term140 = term141.
Proof. exact (@lem2710848 term67). Qed.
Lemma lem2710850 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2710851 : term639 = term640.
Proof. exact (MK_COMB (@lem2710850) (@lem2710849)). Qed.
Lemma lem2710852 : term641 = term642.
Proof. exact (MK_COMB (@lem2710851) (@lem2710846)). Qed.
Lemma lem2710853 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2710855 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710856 : term257 = term258.
Proof. exact (@lem2710855 (NUMERAL 0) term67). Qed.
Lemma lem2710857 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710858 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710859 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710858 h1) (fun h1 : term258 = True => @lem2710857)). Qed.
Lemma lem2710860 : term258 = True.
Proof. exact (EQ_MP (@lem2710859) (@lem2710857)). Qed.
Lemma lem2710861 : term257 = True.
Proof. exact (TRANS (@lem2710856) (@lem2710860)). Qed.
Lemma lem2710862 : True = term257.
Proof. exact (SYM (@lem2710861)). Qed.
Lemma lem2710863 : term257.
Proof. exact (EQ_MP (@lem2710862) (@lem0)). Qed.
Lemma lem2710864 : term644.
Proof. exact (@lem2710853 (@lem2710863)). Qed.
Lemma lem2710866 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710867 : term257 = term258.
Proof. exact (@lem2710866 (NUMERAL 0) term67). Qed.
Lemma lem2710868 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710869 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710870 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710869 h1) (fun h1 : term258 = True => @lem2710868)). Qed.
Lemma lem2710871 : term258 = True.
Proof. exact (EQ_MP (@lem2710870) (@lem2710868)). Qed.
Lemma lem2710872 : term257 = True.
Proof. exact (TRANS (@lem2710867) (@lem2710871)). Qed.
Lemma lem2710873 : True = term257.
Proof. exact (SYM (@lem2710872)). Qed.
Lemma lem2710874 : term257.
Proof. exact (EQ_MP (@lem2710873) (@lem0)). Qed.
Lemma lem2710875 : term645.
Proof. exact (@lem2710864 (@lem2710874)). Qed.
Lemma lem2710877 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710878 : term257 = term258.
Proof. exact (@lem2710877 (NUMERAL 0) term67). Qed.
Lemma lem2710879 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710880 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710881 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710880 h1) (fun h1 : term258 = True => @lem2710879)). Qed.
Lemma lem2710882 : term258 = True.
Proof. exact (EQ_MP (@lem2710881) (@lem2710879)). Qed.
Lemma lem2710883 : term257 = True.
Proof. exact (TRANS (@lem2710878) (@lem2710882)). Qed.
Lemma lem2710884 : True = term257.
Proof. exact (SYM (@lem2710883)). Qed.
Lemma lem2710885 : term257.
Proof. exact (EQ_MP (@lem2710884) (@lem0)). Qed.
Lemma lem2710886 : term646.
Proof. exact (@lem2710875 (@lem2710885)). Qed.
Lemma lem2710888 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710889 : term149 = term150.
Proof. exact (@lem2710888 term67 term67). Qed.
Lemma lem2710890 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710891 : term152 = term67.
Proof. exact (EQ_MP (@lem2710890) (@lem940073)). Qed.
Lemma lem2710892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710893 : term150 = term66.
Proof. exact (MK_COMB (@lem2710892) (@lem2710891)). Qed.
Lemma lem2710894 : term149 = term66.
Proof. exact (TRANS (@lem2710889) (@lem2710893)). Qed.
Lemma lem2710896 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2710897 : term211 = term214.
Proof. exact (@lem2710896 term67 term67). Qed.
Lemma lem2710898 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710899 : term152 = term67.
Proof. exact (EQ_MP (@lem2710898) (@lem940073)). Qed.
Lemma lem2710900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710901 : term150 = term66.
Proof. exact (MK_COMB (@lem2710900) (@lem2710899)). Qed.
Lemma lem2710902 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2710903 : term214 = term140.
Proof. exact (MK_COMB (@lem2710902) (@lem2710901)). Qed.
Lemma lem2710904 : term211 = term140.
Proof. exact (TRANS (@lem2710897) (@lem2710903)). Qed.
Lemma lem2710905 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2710906 : term647 = term639.
Proof. exact (MK_COMB (@lem2710905) (@lem2710904)). Qed.
Lemma lem2710907 : term648 = term641.
Proof. exact (MK_COMB (@lem2710906) (@lem2710894)). Qed.
Lemma lem2710909 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2710910 : term641 = term32.
Proof. exact (@lem2710909 term67). Qed.
Lemma lem2710911 : term648 = term32.
Proof. exact (TRANS (@lem2710907) (@lem2710910)). Qed.
Lemma lem2710912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710913 : term650 = term267.
Proof. exact (MK_COMB (@lem2710912) (@lem2710911)). Qed.
Lemma lem2710914 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2710915 : term651 = term269.
Proof. exact (MK_COMB (@lem2710913) (@lem2710914)). Qed.
Lemma lem2710917 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2710918 : term269 = term32.
Proof. exact (@lem2710917 term67). Qed.
Lemma lem2710919 : term651 = term32.
Proof. exact (TRANS (@lem2710915) (@lem2710918)). Qed.
Lemma lem2710921 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2710922 : term149 = term150.
Proof. exact (@lem2710921 term67 term67). Qed.
Lemma lem2710923 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2710924 : term152 = term67.
Proof. exact (EQ_MP (@lem2710923) (@lem940073)). Qed.
Lemma lem2710925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2710926 : term150 = term66.
Proof. exact (MK_COMB (@lem2710925) (@lem2710924)). Qed.
Lemma lem2710927 : term149 = term66.
Proof. exact (TRANS (@lem2710922) (@lem2710926)). Qed.
Lemma lem2710928 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2710929 : term271 = term269.
Proof. exact (MK_COMB (@lem2710928) (@lem2710927)). Qed.
Lemma lem2710931 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2710932 : term269 = term32.
Proof. exact (@lem2710931 term67). Qed.
Lemma lem2710933 : term271 = term32.
Proof. exact (TRANS (@lem2710929) (@lem2710932)). Qed.
Lemma lem2710934 : term32 = term271.
Proof. exact (SYM (@lem2710933)). Qed.
Lemma lem2710935 : term651 = term271.
Proof. exact (TRANS (@lem2710919) (@lem2710934)). Qed.
Lemma lem2710936 : term642 = term137.
Proof. exact (@lem2710886 (@lem2710935)). Qed.
Lemma lem2710937 : term641 = term137.
Proof. exact (TRANS (@lem2710852) (@lem2710936)). Qed.
Lemma lem2710939 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2710940 : term137 = term32.
Proof. exact (@lem2710939 term32). Qed.
Lemma lem2710941 : term641 = term32.
Proof. exact (TRANS (@lem2710937) (@lem2710940)). Qed.
Lemma lem2710942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2710943 : term652 = term267.
Proof. exact (MK_COMB (@lem2710942) (@lem2710941)). Qed.
Lemma lem2710944 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2710945 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2710943) (@lem2710944 n)). Qed.
Lemma lem2710946 (n : int) : (term637 n) = (term653 n).
Proof. exact (TRANS (@lem2710843 n) (@lem2710945 n)). Qed.
Lemma lem2710947 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2710948 (n : int) : (term637 n) = term32.
Proof. exact (TRANS (@lem2710946 n) (@lem2710947 n)). Qed.
Lemma lem2710949 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2710950 (n : int) : (term654 n) = term102.
Proof. exact (MK_COMB (@lem2710949) (@lem2710948 n)). Qed.
Lemma lem2710951 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2710952 (n : int) : (term636 n) = term655.
Proof. exact (MK_COMB (@lem2710950 n) (@lem2710951)). Qed.
Lemma lem2710953 (n : int) : (term635 n) = term655.
Proof. exact (TRANS (@lem2710842 n) (@lem2710952 n)). Qed.
Lemma lem2710954 : term655 = term140.
Proof. exact (@lem1982721 term140). Qed.
Lemma lem2710955 (n : int) : (term635 n) = term140.
Proof. exact (TRANS (@lem2710953 n) (@lem2710954)). Qed.
Lemma lem2710956 (n : int) : (term163 n) = (term163 n).
Proof. exact (eq_refl (term163 n)). Qed.
Lemma lem2710957 (n : int) : (term634 n) = (term656 n).
Proof. exact (MK_COMB (@lem2710956 n) (@lem2710955 n)). Qed.
Lemma lem2710958 (n : int) : (term633 n) = (term656 n).
Proof. exact (TRANS (@lem2710841 n) (@lem2710957 n)). Qed.
Lemma lem2710959 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2710960 (n : int) : (term631 n) = (term657 n).
Proof. exact (MK_COMB (@lem2710959 n) (@lem2710958 n)). Qed.
Lemma lem2710961 (n : int) : (term630 n) = (term657 n).
Proof. exact (TRANS (@lem2710840 n) (@lem2710960 n)). Qed.
Lemma lem2710962 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2710963 (n : int) : (term658 n) = (term659 n).
Proof. exact (MK_COMB (@lem2710962) (@lem2710961 n)). Qed.
Lemma lem2710964 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2710965 (n : int) : (term629 n) = (term660 n).
Proof. exact (MK_COMB (@lem2710963 n) (@lem2710964)). Qed.
Lemma lem2710966 (n : int) (h1 : term417 n) : term660 n.
Proof. exact (EQ_MP (@lem2710965 n) (@lem2710839 n h1)). Qed.
Lemma lem2710968 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2710969 : term661 = term662.
Proof. exact (@lem2710968 term32 term28). Qed.
Lemma lem2710971 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710972 : term28 = term173.
Proof. exact (@lem2710971 term29). Qed.
Lemma lem2710974 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2710975 : term32 = term137.
Proof. exact (@lem2710974 (NUMERAL 0)). Qed.
Lemma lem2710976 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2710977 : term582 = term583.
Proof. exact (MK_COMB (@lem2710976) (@lem2710975)). Qed.
Lemma lem2710978 : term662 = term663.
Proof. exact (MK_COMB (@lem2710977) (@lem2710972)). Qed.
Lemma lem2710979 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2710981 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710982 : term257 = term258.
Proof. exact (@lem2710981 (NUMERAL 0) term67). Qed.
Lemma lem2710983 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710984 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710985 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710984 h1) (fun h1 : term258 = True => @lem2710983)). Qed.
Lemma lem2710986 : term258 = True.
Proof. exact (EQ_MP (@lem2710985) (@lem2710983)). Qed.
Lemma lem2710987 : term257 = True.
Proof. exact (TRANS (@lem2710982) (@lem2710986)). Qed.
Lemma lem2710988 : True = term257.
Proof. exact (SYM (@lem2710987)). Qed.
Lemma lem2710989 : term257.
Proof. exact (EQ_MP (@lem2710988) (@lem0)). Qed.
Lemma lem2710990 : term665.
Proof. exact (@lem2710979 (@lem2710989)). Qed.
Lemma lem2710992 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2710993 : term257 = term258.
Proof. exact (@lem2710992 (NUMERAL 0) term67). Qed.
Lemma lem2710994 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2710995 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2710996 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2710995 h1) (fun h1 : term258 = True => @lem2710994)). Qed.
Lemma lem2710997 : term258 = True.
Proof. exact (EQ_MP (@lem2710996) (@lem2710994)). Qed.
Lemma lem2710998 : term257 = True.
Proof. exact (TRANS (@lem2710993) (@lem2710997)). Qed.
Lemma lem2710999 : True = term257.
Proof. exact (SYM (@lem2710998)). Qed.
Lemma lem2711000 : term257.
Proof. exact (EQ_MP (@lem2710999) (@lem0)). Qed.
Lemma lem2711001 : term663 = term666.
Proof. exact (@lem2710990 (@lem2711000)). Qed.
Lemma lem2711003 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711004 : term289 = term290.
Proof. exact (@lem2711003 term29 term67). Qed.
Lemma lem2711005 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711006 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711007 : term292 = term29.
Proof. exact (EQ_MP (@lem2711006) (@lem2711005)). Qed.
Lemma lem2711008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711009 : term290 = term28.
Proof. exact (MK_COMB (@lem2711008) (@lem2711007)). Qed.
Lemma lem2711010 : term289 = term28.
Proof. exact (TRANS (@lem2711004) (@lem2711009)). Qed.
Lemma lem2711012 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711013 : term269 = term32.
Proof. exact (@lem2711012 term67). Qed.
Lemma lem2711014 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711015 : term588 = term582.
Proof. exact (MK_COMB (@lem2711014) (@lem2711013)). Qed.
Lemma lem2711016 : term666 = term662.
Proof. exact (MK_COMB (@lem2711015) (@lem2711010)). Qed.
Lemma lem2711018 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711019 : term662 = term667.
Proof. exact (@lem2711018 (NUMERAL 0) term29). Qed.
Lemma lem2711020 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2711021 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2711022 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2711021 h1) (fun h1 : term667 = True => @lem2711020)). Qed.
Lemma lem2711023 : term667 = True.
Proof. exact (EQ_MP (@lem2711022) (@lem2711020)). Qed.
Lemma lem2711024 : term662 = True.
Proof. exact (TRANS (@lem2711019) (@lem2711023)). Qed.
Lemma lem2711025 : term666 = True.
Proof. exact (TRANS (@lem2711016) (@lem2711024)). Qed.
Lemma lem2711026 : term663 = True.
Proof. exact (TRANS (@lem2711001) (@lem2711025)). Qed.
Lemma lem2711027 : term662 = True.
Proof. exact (TRANS (@lem2710978) (@lem2711026)). Qed.
Lemma lem2711028 : term661 = True.
Proof. exact (TRANS (@lem2710969) (@lem2711027)). Qed.
Lemma lem2711029 : True = term661.
Proof. exact (SYM (@lem2711028)). Qed.
Lemma lem2711030 : term661.
Proof. exact (EQ_MP (@lem2711029) (@lem0)). Qed.
Lemma lem2711031 (n : int) (h1 : term417 n) : term668 n.
Proof. exact (conj (@lem2711030) (@lem2710966 n h1)). Qed.
Lemma lem2711033 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2711034 (n : int) : term669 n.
Proof. exact (@lem2711033 term28 (term657 n)). Qed.
Lemma lem2711035 (n : int) (h1 : term417 n) : term670 n.
Proof. exact (@lem2711034 n (@lem2711031 n h1)). Qed.
Lemma lem2711036 (n : int) : (term671 n) = (term672 n).
Proof. exact (@lem1982781 (term632 n) term28 (term656 n)). Qed.
Lemma lem2711037 (n : int) : (term673 n) = (term674 n).
Proof. exact (@lem1982781 (term161 n) term28 term140). Qed.
Lemma lem2711039 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711040 : term140 = term141.
Proof. exact (@lem2711039 term67). Qed.
Lemma lem2711042 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711043 : term28 = term173.
Proof. exact (@lem2711042 term29). Qed.
Lemma lem2711044 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711045 : term287 = term675.
Proof. exact (MK_COMB (@lem2711044) (@lem2711043)). Qed.
Lemma lem2711046 : term676 = term677.
Proof. exact (MK_COMB (@lem2711045) (@lem2711040)). Qed.
Lemma lem2711047 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2711049 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711050 : term149 = term150.
Proof. exact (@lem2711049 term67 term67). Qed.
Lemma lem2711051 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711052 : term152 = term67.
Proof. exact (EQ_MP (@lem2711051) (@lem940073)). Qed.
Lemma lem2711053 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711054 : term150 = term66.
Proof. exact (MK_COMB (@lem2711053) (@lem2711052)). Qed.
Lemma lem2711055 : term149 = term66.
Proof. exact (TRANS (@lem2711050) (@lem2711054)). Qed.
Lemma lem2711057 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2711058 : term676 = term440.
Proof. exact (@lem2711057 term29 term67). Qed.
Lemma lem2711059 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711060 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711061 : term292 = term29.
Proof. exact (EQ_MP (@lem2711060) (@lem2711059)). Qed.
Lemma lem2711062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711063 : term290 = term28.
Proof. exact (MK_COMB (@lem2711062) (@lem2711061)). Qed.
Lemma lem2711064 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711065 : term440 = term184.
Proof. exact (MK_COMB (@lem2711064) (@lem2711063)). Qed.
Lemma lem2711066 : term676 = term184.
Proof. exact (TRANS (@lem2711058) (@lem2711065)). Qed.
Lemma lem2711067 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2711068 : term680 = term186.
Proof. exact (MK_COMB (@lem2711067) (@lem2711066)). Qed.
Lemma lem2711069 : term678 = term187.
Proof. exact (MK_COMB (@lem2711068) (@lem2711055)). Qed.
Lemma lem2711070 : term677 = term187.
Proof. exact (TRANS (@lem2711047) (@lem2711069)). Qed.
Lemma lem2711071 : term676 = term187.
Proof. exact (TRANS (@lem2711046) (@lem2711070)). Qed.
Lemma lem2711073 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2711074 : term187 = term184.
Proof. exact (@lem2711073 term184). Qed.
Lemma lem2711075 : term676 = term184.
Proof. exact (TRANS (@lem2711071) (@lem2711074)). Qed.
Lemma lem2711076 (n : int) : (term681 n) = (term682 n).
Proof. exact (@lem1982749 term28 term28 (term162 n)). Qed.
Lemma lem2711078 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711079 : term28 = term173.
Proof. exact (@lem2711078 term29). Qed.
Lemma lem2711081 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711082 : term28 = term173.
Proof. exact (@lem2711081 term29). Qed.
Lemma lem2711083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711084 : term287 = term675.
Proof. exact (MK_COMB (@lem2711083) (@lem2711082)). Qed.
Lemma lem2711085 : term683 = term684.
Proof. exact (MK_COMB (@lem2711084) (@lem2711079)). Qed.
Lemma lem2711086 : term684 = term685.
Proof. exact (@lem1981613 term28 term28 term66 term66). Qed.
Lemma lem2711088 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711089 : term149 = term150.
Proof. exact (@lem2711088 term67 term67). Qed.
Lemma lem2711090 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711091 : term152 = term67.
Proof. exact (EQ_MP (@lem2711090) (@lem940073)). Qed.
Lemma lem2711092 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711093 : term150 = term66.
Proof. exact (MK_COMB (@lem2711092) (@lem2711091)). Qed.
Lemma lem2711094 : term149 = term66.
Proof. exact (TRANS (@lem2711089) (@lem2711093)). Qed.
Lemma lem2711096 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711097 : term683 = term686.
Proof. exact (@lem2711096 term29 term29). Qed.
Lemma lem2711098 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711099 : term687 = term688.
Proof. exact (EQ_MP (@lem2711098) (@lem940073)). Qed.
Lemma lem2711100 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2711101 : term689 = term690.
Proof. exact (EQ_MP (@lem2711100) (@lem2711099)). Qed.
Lemma lem2711102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711103 : term686 = term691.
Proof. exact (MK_COMB (@lem2711102) (@lem2711101)). Qed.
Lemma lem2711104 : term683 = term691.
Proof. exact (TRANS (@lem2711097) (@lem2711103)). Qed.
Lemma lem2711105 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2711106 : term692 = term693.
Proof. exact (MK_COMB (@lem2711105) (@lem2711104)). Qed.
Lemma lem2711107 : term685 = term694.
Proof. exact (MK_COMB (@lem2711106) (@lem2711094)). Qed.
Lemma lem2711108 : term684 = term694.
Proof. exact (TRANS (@lem2711086) (@lem2711107)). Qed.
Lemma lem2711109 : term683 = term694.
Proof. exact (TRANS (@lem2711085) (@lem2711108)). Qed.
Lemma lem2711111 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2711112 : term694 = term691.
Proof. exact (@lem2711111 term691). Qed.
Lemma lem2711113 : term683 = term691.
Proof. exact (TRANS (@lem2711109) (@lem2711112)). Qed.
Lemma lem2711114 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711115 : term695 = term696.
Proof. exact (MK_COMB (@lem2711114) (@lem2711113)). Qed.
Lemma lem2711116 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2711117 (n : int) : (term682 n) = (term697 n).
Proof. exact (MK_COMB (@lem2711115) (@lem2711116 n)). Qed.
Lemma lem2711118 (n : int) : (term681 n) = (term697 n).
Proof. exact (TRANS (@lem2711076 n) (@lem2711117 n)). Qed.
Lemma lem2711119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711120 (n : int) : (term698 n) = (term699 n).
Proof. exact (MK_COMB (@lem2711119) (@lem2711118 n)). Qed.
Lemma lem2711121 (n : int) : (term674 n) = (term700 n).
Proof. exact (MK_COMB (@lem2711120 n) (@lem2711075)). Qed.
Lemma lem2711122 (n : int) : (term673 n) = (term700 n).
Proof. exact (TRANS (@lem2711037 n) (@lem2711121 n)). Qed.
Lemma lem2711123 (n : int) : (term701 n) = (term702 n).
Proof. exact (@lem1982749 term28 term140 (real_of_int n)). Qed.
Lemma lem2711125 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711126 : term140 = term141.
Proof. exact (@lem2711125 term67). Qed.
Lemma lem2711128 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711129 : term28 = term173.
Proof. exact (@lem2711128 term29). Qed.
Lemma lem2711130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711131 : term287 = term675.
Proof. exact (MK_COMB (@lem2711130) (@lem2711129)). Qed.
Lemma lem2711132 : term676 = term677.
Proof. exact (MK_COMB (@lem2711131) (@lem2711126)). Qed.
Lemma lem2711133 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2711135 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711136 : term149 = term150.
Proof. exact (@lem2711135 term67 term67). Qed.
Lemma lem2711137 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711138 : term152 = term67.
Proof. exact (EQ_MP (@lem2711137) (@lem940073)). Qed.
Lemma lem2711139 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711140 : term150 = term66.
Proof. exact (MK_COMB (@lem2711139) (@lem2711138)). Qed.
Lemma lem2711141 : term149 = term66.
Proof. exact (TRANS (@lem2711136) (@lem2711140)). Qed.
Lemma lem2711143 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2711144 : term676 = term440.
Proof. exact (@lem2711143 term29 term67). Qed.
Lemma lem2711145 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711146 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711147 : term292 = term29.
Proof. exact (EQ_MP (@lem2711146) (@lem2711145)). Qed.
Lemma lem2711148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711149 : term290 = term28.
Proof. exact (MK_COMB (@lem2711148) (@lem2711147)). Qed.
Lemma lem2711150 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711151 : term440 = term184.
Proof. exact (MK_COMB (@lem2711150) (@lem2711149)). Qed.
Lemma lem2711152 : term676 = term184.
Proof. exact (TRANS (@lem2711144) (@lem2711151)). Qed.
Lemma lem2711153 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2711154 : term680 = term186.
Proof. exact (MK_COMB (@lem2711153) (@lem2711152)). Qed.
Lemma lem2711155 : term678 = term187.
Proof. exact (MK_COMB (@lem2711154) (@lem2711141)). Qed.
Lemma lem2711156 : term677 = term187.
Proof. exact (TRANS (@lem2711133) (@lem2711155)). Qed.
Lemma lem2711157 : term676 = term187.
Proof. exact (TRANS (@lem2711132) (@lem2711156)). Qed.
Lemma lem2711159 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2711160 : term187 = term184.
Proof. exact (@lem2711159 term184). Qed.
Lemma lem2711161 : term676 = term184.
Proof. exact (TRANS (@lem2711157) (@lem2711160)). Qed.
Lemma lem2711162 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711163 : term703 = term189.
Proof. exact (MK_COMB (@lem2711162) (@lem2711161)). Qed.
Lemma lem2711164 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2711165 (n : int) : (term702 n) = (term704 n).
Proof. exact (MK_COMB (@lem2711163) (@lem2711164 n)). Qed.
Lemma lem2711166 (n : int) : (term701 n) = (term704 n).
Proof. exact (TRANS (@lem2711123 n) (@lem2711165 n)). Qed.
Lemma lem2711167 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711168 (n : int) : (term705 n) = (term706 n).
Proof. exact (MK_COMB (@lem2711167) (@lem2711166 n)). Qed.
Lemma lem2711169 (n : int) : (term672 n) = (term707 n).
Proof. exact (MK_COMB (@lem2711168 n) (@lem2711122 n)). Qed.
Lemma lem2711170 (n : int) : (term671 n) = (term707 n).
Proof. exact (TRANS (@lem2711036 n) (@lem2711169 n)). Qed.
Lemma lem2711171 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2711172 (n : int) : (term708 n) = (term709 n).
Proof. exact (MK_COMB (@lem2711171) (@lem2711170 n)). Qed.
Lemma lem2711173 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2711174 (n : int) : (term670 n) = (term710 n).
Proof. exact (MK_COMB (@lem2711172 n) (@lem2711173)). Qed.
Lemma lem2711175 (n : int) (h1 : term417 n) : term710 n.
Proof. exact (EQ_MP (@lem2711174 n) (@lem2711035 n h1)). Qed.
Lemma lem2711177 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2711178 : term581 = term257.
Proof. exact (@lem2711177 term32 term66). Qed.
Lemma lem2711180 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711181 : term66 = term210.
Proof. exact (@lem2711180 term67). Qed.
Lemma lem2711183 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711184 : term32 = term137.
Proof. exact (@lem2711183 (NUMERAL 0)). Qed.
Lemma lem2711185 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711186 : term582 = term583.
Proof. exact (MK_COMB (@lem2711185) (@lem2711184)). Qed.
Lemma lem2711187 : term257 = term584.
Proof. exact (MK_COMB (@lem2711186) (@lem2711181)). Qed.
Lemma lem2711188 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2711190 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711191 : term257 = term258.
Proof. exact (@lem2711190 (NUMERAL 0) term67). Qed.
Lemma lem2711192 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711193 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711194 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711193 h1) (fun h1 : term258 = True => @lem2711192)). Qed.
Lemma lem2711195 : term258 = True.
Proof. exact (EQ_MP (@lem2711194) (@lem2711192)). Qed.
Lemma lem2711196 : term257 = True.
Proof. exact (TRANS (@lem2711191) (@lem2711195)). Qed.
Lemma lem2711197 : True = term257.
Proof. exact (SYM (@lem2711196)). Qed.
Lemma lem2711198 : term257.
Proof. exact (EQ_MP (@lem2711197) (@lem0)). Qed.
Lemma lem2711199 : term586.
Proof. exact (@lem2711188 (@lem2711198)). Qed.
Lemma lem2711201 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711202 : term257 = term258.
Proof. exact (@lem2711201 (NUMERAL 0) term67). Qed.
Lemma lem2711203 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711204 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711205 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711204 h1) (fun h1 : term258 = True => @lem2711203)). Qed.
Lemma lem2711206 : term258 = True.
Proof. exact (EQ_MP (@lem2711205) (@lem2711203)). Qed.
Lemma lem2711207 : term257 = True.
Proof. exact (TRANS (@lem2711202) (@lem2711206)). Qed.
Lemma lem2711208 : True = term257.
Proof. exact (SYM (@lem2711207)). Qed.
Lemma lem2711209 : term257.
Proof. exact (EQ_MP (@lem2711208) (@lem0)). Qed.
Lemma lem2711210 : term584 = term587.
Proof. exact (@lem2711199 (@lem2711209)). Qed.
Lemma lem2711212 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711213 : term149 = term150.
Proof. exact (@lem2711212 term67 term67). Qed.
Lemma lem2711214 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711215 : term152 = term67.
Proof. exact (EQ_MP (@lem2711214) (@lem940073)). Qed.
Lemma lem2711216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711217 : term150 = term66.
Proof. exact (MK_COMB (@lem2711216) (@lem2711215)). Qed.
Lemma lem2711218 : term149 = term66.
Proof. exact (TRANS (@lem2711213) (@lem2711217)). Qed.
Lemma lem2711220 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711221 : term269 = term32.
Proof. exact (@lem2711220 term67). Qed.
Lemma lem2711222 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711223 : term588 = term582.
Proof. exact (MK_COMB (@lem2711222) (@lem2711221)). Qed.
Lemma lem2711224 : term587 = term257.
Proof. exact (MK_COMB (@lem2711223) (@lem2711218)). Qed.
Lemma lem2711226 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711227 : term257 = term258.
Proof. exact (@lem2711226 (NUMERAL 0) term67). Qed.
Lemma lem2711228 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711229 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711230 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711229 h1) (fun h1 : term258 = True => @lem2711228)). Qed.
Lemma lem2711231 : term258 = True.
Proof. exact (EQ_MP (@lem2711230) (@lem2711228)). Qed.
Lemma lem2711232 : term257 = True.
Proof. exact (TRANS (@lem2711227) (@lem2711231)). Qed.
Lemma lem2711233 : term587 = True.
Proof. exact (TRANS (@lem2711224) (@lem2711232)). Qed.
Lemma lem2711234 : term584 = True.
Proof. exact (TRANS (@lem2711210) (@lem2711233)). Qed.
Lemma lem2711235 : term257 = True.
Proof. exact (TRANS (@lem2711187) (@lem2711234)). Qed.
Lemma lem2711236 : term581 = True.
Proof. exact (TRANS (@lem2711178) (@lem2711235)). Qed.
Lemma lem2711237 : True = term581.
Proof. exact (SYM (@lem2711236)). Qed.
Lemma lem2711238 : term581.
Proof. exact (EQ_MP (@lem2711237) (@lem0)). Qed.
Lemma lem2711239 (n : int) (h1 : term417 n) : term711 n.
Proof. exact (conj (@lem2711238) (@lem2710650 n h1)). Qed.
Lemma lem2711241 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2711242 (n : int) : term712 n.
Proof. exact (@lem2711241 term66 (term48 n)). Qed.
Lemma lem2711243 (n : int) (h1 : term417 n) : term713 n.
Proof. exact (@lem2711242 n (@lem2711239 n h1)). Qed.
Lemma lem2711244 (n : int) : (term612 n) = (term48 n).
Proof. exact (@lem1982733 (term48 n)). Qed.
Lemma lem2711245 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2711246 (n : int) : (term714 n) = (term203 n).
Proof. exact (MK_COMB (@lem2711245) (@lem2711244 n)). Qed.
Lemma lem2711247 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2711248 (n : int) : (term713 n) = (term204 n).
Proof. exact (MK_COMB (@lem2711246 n) (@lem2711247)). Qed.
Lemma lem2711249 (n : int) (h1 : term417 n) : term204 n.
Proof. exact (EQ_MP (@lem2711248 n) (@lem2711243 n h1)). Qed.
Lemma lem2711251 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2711252 (n : int) : term596 n.
Proof. exact (@lem2711251 (term195 n)). Qed.
Lemma lem2711253 (n : int) (h1 : term417 n) : term597 n.
Proof. exact (@lem2711252 n (@lem2710648 n h1)). Qed.
Lemma lem2711254 (n : int) (h1 : term417 n) : term715 n.
Proof. exact (@lem2711253 n h1 term66). Qed.
Lemma lem2711255 (n : int) : (term715 n) = ((term716 n) = term32).
Proof. exact (eq_refl (term715 n)). Qed.
Lemma lem2711256 (n : int) (h1 : term417 n) : (term716 n) = term32.
Proof. exact (EQ_MP (@lem2711255 n) (@lem2711254 n h1)). Qed.
Lemma lem2711257 (n : int) : (term716 n) = (term195 n).
Proof. exact (@lem1982733 (term195 n)). Qed.
Lemma lem2711258 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2711259 (n : int) : (term717 n) = (term197 n).
Proof. exact (MK_COMB (@lem2711258) (@lem2711257 n)). Qed.
Lemma lem2711260 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2711261 (n : int) : ((term716 n) = term32) = ((term195 n) = term32).
Proof. exact (MK_COMB (@lem2711259 n) (@lem2711260)). Qed.
Lemma lem2711262 (n : int) (h1 : term417 n) : (term195 n) = term32.
Proof. exact (EQ_MP (@lem2711261 n) (@lem2711256 n h1)). Qed.
Lemma lem2711263 (n : int) (h1 : term417 n) : term718 n.
Proof. exact (conj (@lem2711262 n h1) (@lem2711249 n h1)). Qed.
Lemma lem2711265 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2711266 (n : int) : term719 n.
Proof. exact (@lem2711265 (term195 n) (term48 n)). Qed.
Lemma lem2711267 (n : int) (h1 : term417 n) : term720 n.
Proof. exact (@lem2711266 n (@lem2711263 n h1)). Qed.
Lemma lem2711268 (n : int) : (term721 n) = (term722 n).
Proof. exact (@lem1982755 (real_of_int n) (term193 n) (term48 n)). Qed.
Lemma lem2711269 (n : int) : (term723 n) = (term724 n).
Proof. exact (@lem1982755 (term190 n) (term170 n) (term48 n)). Qed.
Lemma lem2711270 (n : int) : (term725 n) = (term638 n).
Proof. exact (@lem1982713 term140 (term48 n)). Qed.
Lemma lem2711272 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711273 : term66 = term210.
Proof. exact (@lem2711272 term67). Qed.
Lemma lem2711275 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711276 : term140 = term141.
Proof. exact (@lem2711275 term67). Qed.
Lemma lem2711277 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711278 : term639 = term640.
Proof. exact (MK_COMB (@lem2711277) (@lem2711276)). Qed.
Lemma lem2711279 : term641 = term642.
Proof. exact (MK_COMB (@lem2711278) (@lem2711273)). Qed.
Lemma lem2711280 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2711282 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711283 : term257 = term258.
Proof. exact (@lem2711282 (NUMERAL 0) term67). Qed.
Lemma lem2711284 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711285 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711286 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711285 h1) (fun h1 : term258 = True => @lem2711284)). Qed.
Lemma lem2711287 : term258 = True.
Proof. exact (EQ_MP (@lem2711286) (@lem2711284)). Qed.
Lemma lem2711288 : term257 = True.
Proof. exact (TRANS (@lem2711283) (@lem2711287)). Qed.
Lemma lem2711289 : True = term257.
Proof. exact (SYM (@lem2711288)). Qed.
Lemma lem2711290 : term257.
Proof. exact (EQ_MP (@lem2711289) (@lem0)). Qed.
Lemma lem2711291 : term644.
Proof. exact (@lem2711280 (@lem2711290)). Qed.
Lemma lem2711293 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711294 : term257 = term258.
Proof. exact (@lem2711293 (NUMERAL 0) term67). Qed.
Lemma lem2711295 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711296 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711297 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711296 h1) (fun h1 : term258 = True => @lem2711295)). Qed.
Lemma lem2711298 : term258 = True.
Proof. exact (EQ_MP (@lem2711297) (@lem2711295)). Qed.
Lemma lem2711299 : term257 = True.
Proof. exact (TRANS (@lem2711294) (@lem2711298)). Qed.
Lemma lem2711300 : True = term257.
Proof. exact (SYM (@lem2711299)). Qed.
Lemma lem2711301 : term257.
Proof. exact (EQ_MP (@lem2711300) (@lem0)). Qed.
Lemma lem2711302 : term645.
Proof. exact (@lem2711291 (@lem2711301)). Qed.
Lemma lem2711304 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711305 : term257 = term258.
Proof. exact (@lem2711304 (NUMERAL 0) term67). Qed.
Lemma lem2711306 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711307 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711308 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711307 h1) (fun h1 : term258 = True => @lem2711306)). Qed.
Lemma lem2711309 : term258 = True.
Proof. exact (EQ_MP (@lem2711308) (@lem2711306)). Qed.
Lemma lem2711310 : term257 = True.
Proof. exact (TRANS (@lem2711305) (@lem2711309)). Qed.
Lemma lem2711311 : True = term257.
Proof. exact (SYM (@lem2711310)). Qed.
Lemma lem2711312 : term257.
Proof. exact (EQ_MP (@lem2711311) (@lem0)). Qed.
Lemma lem2711313 : term646.
Proof. exact (@lem2711302 (@lem2711312)). Qed.
Lemma lem2711315 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711316 : term149 = term150.
Proof. exact (@lem2711315 term67 term67). Qed.
Lemma lem2711317 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711318 : term152 = term67.
Proof. exact (EQ_MP (@lem2711317) (@lem940073)). Qed.
Lemma lem2711319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711320 : term150 = term66.
Proof. exact (MK_COMB (@lem2711319) (@lem2711318)). Qed.
Lemma lem2711321 : term149 = term66.
Proof. exact (TRANS (@lem2711316) (@lem2711320)). Qed.
Lemma lem2711323 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2711324 : term211 = term214.
Proof. exact (@lem2711323 term67 term67). Qed.
Lemma lem2711325 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711326 : term152 = term67.
Proof. exact (EQ_MP (@lem2711325) (@lem940073)). Qed.
Lemma lem2711327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711328 : term150 = term66.
Proof. exact (MK_COMB (@lem2711327) (@lem2711326)). Qed.
Lemma lem2711329 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711330 : term214 = term140.
Proof. exact (MK_COMB (@lem2711329) (@lem2711328)). Qed.
Lemma lem2711331 : term211 = term140.
Proof. exact (TRANS (@lem2711324) (@lem2711330)). Qed.
Lemma lem2711332 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711333 : term647 = term639.
Proof. exact (MK_COMB (@lem2711332) (@lem2711331)). Qed.
Lemma lem2711334 : term648 = term641.
Proof. exact (MK_COMB (@lem2711333) (@lem2711321)). Qed.
Lemma lem2711336 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2711337 : term641 = term32.
Proof. exact (@lem2711336 term67). Qed.
Lemma lem2711338 : term648 = term32.
Proof. exact (TRANS (@lem2711334) (@lem2711337)). Qed.
Lemma lem2711339 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711340 : term650 = term267.
Proof. exact (MK_COMB (@lem2711339) (@lem2711338)). Qed.
Lemma lem2711341 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2711342 : term651 = term269.
Proof. exact (MK_COMB (@lem2711340) (@lem2711341)). Qed.
Lemma lem2711344 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711345 : term269 = term32.
Proof. exact (@lem2711344 term67). Qed.
Lemma lem2711346 : term651 = term32.
Proof. exact (TRANS (@lem2711342) (@lem2711345)). Qed.
Lemma lem2711348 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711349 : term149 = term150.
Proof. exact (@lem2711348 term67 term67). Qed.
Lemma lem2711350 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711351 : term152 = term67.
Proof. exact (EQ_MP (@lem2711350) (@lem940073)). Qed.
Lemma lem2711352 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711353 : term150 = term66.
Proof. exact (MK_COMB (@lem2711352) (@lem2711351)). Qed.
Lemma lem2711354 : term149 = term66.
Proof. exact (TRANS (@lem2711349) (@lem2711353)). Qed.
Lemma lem2711355 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2711356 : term271 = term269.
Proof. exact (MK_COMB (@lem2711355) (@lem2711354)). Qed.
Lemma lem2711358 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711359 : term269 = term32.
Proof. exact (@lem2711358 term67). Qed.
Lemma lem2711360 : term271 = term32.
Proof. exact (TRANS (@lem2711356) (@lem2711359)). Qed.
Lemma lem2711361 : term32 = term271.
Proof. exact (SYM (@lem2711360)). Qed.
Lemma lem2711362 : term651 = term271.
Proof. exact (TRANS (@lem2711346) (@lem2711361)). Qed.
Lemma lem2711363 : term642 = term137.
Proof. exact (@lem2711313 (@lem2711362)). Qed.
Lemma lem2711364 : term641 = term137.
Proof. exact (TRANS (@lem2711279) (@lem2711363)). Qed.
Lemma lem2711366 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2711367 : term137 = term32.
Proof. exact (@lem2711366 term32). Qed.
Lemma lem2711368 : term641 = term32.
Proof. exact (TRANS (@lem2711364) (@lem2711367)). Qed.
Lemma lem2711369 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711370 : term652 = term267.
Proof. exact (MK_COMB (@lem2711369) (@lem2711368)). Qed.
Lemma lem2711371 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2711372 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2711370) (@lem2711371 n)). Qed.
Lemma lem2711373 (n : int) : (term725 n) = (term653 n).
Proof. exact (TRANS (@lem2711270 n) (@lem2711372 n)). Qed.
Lemma lem2711374 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2711375 (n : int) : (term725 n) = term32.
Proof. exact (TRANS (@lem2711373 n) (@lem2711374 n)). Qed.
Lemma lem2711376 (n : int) : (term192 n) = (term192 n).
Proof. exact (eq_refl (term192 n)). Qed.
Lemma lem2711377 (n : int) : (term724 n) = (term726 n).
Proof. exact (MK_COMB (@lem2711376 n) (@lem2711375 n)). Qed.
Lemma lem2711378 (n : int) : (term723 n) = (term726 n).
Proof. exact (TRANS (@lem2711269 n) (@lem2711377 n)). Qed.
Lemma lem2711379 (n : int) : (term726 n) = (term190 n).
Proof. exact (@lem1982723 (term190 n)). Qed.
Lemma lem2711380 (n : int) : (term723 n) = (term190 n).
Proof. exact (TRANS (@lem2711378 n) (@lem2711379 n)). Qed.
Lemma lem2711381 (n : int) : (term194 n) = (term194 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem2711382 (n : int) : (term722 n) = (term727 n).
Proof. exact (MK_COMB (@lem2711381 n) (@lem2711380 n)). Qed.
Lemma lem2711383 (n : int) : (term721 n) = (term727 n).
Proof. exact (TRANS (@lem2711268 n) (@lem2711382 n)). Qed.
Lemma lem2711384 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2711385 (n : int) : (term728 n) = (term729 n).
Proof. exact (MK_COMB (@lem2711384) (@lem2711383 n)). Qed.
Lemma lem2711386 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2711387 (n : int) : (term720 n) = (term730 n).
Proof. exact (MK_COMB (@lem2711385 n) (@lem2711386)). Qed.
Lemma lem2711388 (n : int) (h1 : term417 n) : term730 n.
Proof. exact (EQ_MP (@lem2711387 n) (@lem2711267 n h1)). Qed.
Lemma lem2711390 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2711391 : term661 = term662.
Proof. exact (@lem2711390 term32 term28). Qed.
Lemma lem2711393 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711394 : term28 = term173.
Proof. exact (@lem2711393 term29). Qed.
Lemma lem2711396 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711397 : term32 = term137.
Proof. exact (@lem2711396 (NUMERAL 0)). Qed.
Lemma lem2711398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711399 : term582 = term583.
Proof. exact (MK_COMB (@lem2711398) (@lem2711397)). Qed.
Lemma lem2711400 : term662 = term663.
Proof. exact (MK_COMB (@lem2711399) (@lem2711394)). Qed.
Lemma lem2711401 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2711403 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711404 : term257 = term258.
Proof. exact (@lem2711403 (NUMERAL 0) term67). Qed.
Lemma lem2711405 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711406 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711407 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711406 h1) (fun h1 : term258 = True => @lem2711405)). Qed.
Lemma lem2711408 : term258 = True.
Proof. exact (EQ_MP (@lem2711407) (@lem2711405)). Qed.
Lemma lem2711409 : term257 = True.
Proof. exact (TRANS (@lem2711404) (@lem2711408)). Qed.
Lemma lem2711410 : True = term257.
Proof. exact (SYM (@lem2711409)). Qed.
Lemma lem2711411 : term257.
Proof. exact (EQ_MP (@lem2711410) (@lem0)). Qed.
Lemma lem2711412 : term665.
Proof. exact (@lem2711401 (@lem2711411)). Qed.
Lemma lem2711414 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711415 : term257 = term258.
Proof. exact (@lem2711414 (NUMERAL 0) term67). Qed.
Lemma lem2711416 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711417 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711418 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711417 h1) (fun h1 : term258 = True => @lem2711416)). Qed.
Lemma lem2711419 : term258 = True.
Proof. exact (EQ_MP (@lem2711418) (@lem2711416)). Qed.
Lemma lem2711420 : term257 = True.
Proof. exact (TRANS (@lem2711415) (@lem2711419)). Qed.
Lemma lem2711421 : True = term257.
Proof. exact (SYM (@lem2711420)). Qed.
Lemma lem2711422 : term257.
Proof. exact (EQ_MP (@lem2711421) (@lem0)). Qed.
Lemma lem2711423 : term663 = term666.
Proof. exact (@lem2711412 (@lem2711422)). Qed.
Lemma lem2711425 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711426 : term289 = term290.
Proof. exact (@lem2711425 term29 term67). Qed.
Lemma lem2711427 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711428 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711429 : term292 = term29.
Proof. exact (EQ_MP (@lem2711428) (@lem2711427)). Qed.
Lemma lem2711430 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711431 : term290 = term28.
Proof. exact (MK_COMB (@lem2711430) (@lem2711429)). Qed.
Lemma lem2711432 : term289 = term28.
Proof. exact (TRANS (@lem2711426) (@lem2711431)). Qed.
Lemma lem2711434 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711435 : term269 = term32.
Proof. exact (@lem2711434 term67). Qed.
Lemma lem2711436 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711437 : term588 = term582.
Proof. exact (MK_COMB (@lem2711436) (@lem2711435)). Qed.
Lemma lem2711438 : term666 = term662.
Proof. exact (MK_COMB (@lem2711437) (@lem2711432)). Qed.
Lemma lem2711440 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711441 : term662 = term667.
Proof. exact (@lem2711440 (NUMERAL 0) term29). Qed.
Lemma lem2711442 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2711443 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2711444 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2711443 h1) (fun h1 : term667 = True => @lem2711442)). Qed.
Lemma lem2711445 : term667 = True.
Proof. exact (EQ_MP (@lem2711444) (@lem2711442)). Qed.
Lemma lem2711446 : term662 = True.
Proof. exact (TRANS (@lem2711441) (@lem2711445)). Qed.
Lemma lem2711447 : term666 = True.
Proof. exact (TRANS (@lem2711438) (@lem2711446)). Qed.
Lemma lem2711448 : term663 = True.
Proof. exact (TRANS (@lem2711423) (@lem2711447)). Qed.
Lemma lem2711449 : term662 = True.
Proof. exact (TRANS (@lem2711400) (@lem2711448)). Qed.
Lemma lem2711450 : term661 = True.
Proof. exact (TRANS (@lem2711391) (@lem2711449)). Qed.
Lemma lem2711451 : True = term661.
Proof. exact (SYM (@lem2711450)). Qed.
Lemma lem2711452 : term661.
Proof. exact (EQ_MP (@lem2711451) (@lem0)). Qed.
Lemma lem2711453 (n : int) (h1 : term417 n) : term731 n.
Proof. exact (conj (@lem2711452) (@lem2711388 n h1)). Qed.
Lemma lem2711455 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2711456 (n : int) : term732 n.
Proof. exact (@lem2711455 term28 (term727 n)). Qed.
Lemma lem2711457 (n : int) (h1 : term417 n) : term733 n.
Proof. exact (@lem2711456 n (@lem2711453 n h1)). Qed.
Lemma lem2711458 (n : int) : (term734 n) = (term735 n).
Proof. exact (@lem1982781 (real_of_int n) term28 (term190 n)). Qed.
Lemma lem2711459 (n : int) : (term736 n) = (term737 n).
Proof. exact (@lem1982749 term28 term184 (term162 n)). Qed.
Lemma lem2711461 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711462 : term184 = term187.
Proof. exact (@lem2711461 term29). Qed.
Lemma lem2711464 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711465 : term28 = term173.
Proof. exact (@lem2711464 term29). Qed.
Lemma lem2711466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711467 : term287 = term675.
Proof. exact (MK_COMB (@lem2711466) (@lem2711465)). Qed.
Lemma lem2711468 : term738 = term739.
Proof. exact (MK_COMB (@lem2711467) (@lem2711462)). Qed.
Lemma lem2711469 : term739 = term740.
Proof. exact (@lem1981613 term28 term184 term66 term66). Qed.
Lemma lem2711471 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711472 : term149 = term150.
Proof. exact (@lem2711471 term67 term67). Qed.
Lemma lem2711473 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711474 : term152 = term67.
Proof. exact (EQ_MP (@lem2711473) (@lem940073)). Qed.
Lemma lem2711475 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711476 : term150 = term66.
Proof. exact (MK_COMB (@lem2711475) (@lem2711474)). Qed.
Lemma lem2711477 : term149 = term66.
Proof. exact (TRANS (@lem2711472) (@lem2711476)). Qed.
Lemma lem2711479 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2711480 : term738 = term741.
Proof. exact (@lem2711479 term29 term29). Qed.
Lemma lem2711481 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711482 : term687 = term688.
Proof. exact (EQ_MP (@lem2711481) (@lem940073)). Qed.
Lemma lem2711483 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2711484 : term689 = term690.
Proof. exact (EQ_MP (@lem2711483) (@lem2711482)). Qed.
Lemma lem2711485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711486 : term686 = term691.
Proof. exact (MK_COMB (@lem2711485) (@lem2711484)). Qed.
Lemma lem2711487 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711488 : term741 = term742.
Proof. exact (MK_COMB (@lem2711487) (@lem2711486)). Qed.
Lemma lem2711489 : term738 = term742.
Proof. exact (TRANS (@lem2711480) (@lem2711488)). Qed.
Lemma lem2711490 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2711491 : term743 = term744.
Proof. exact (MK_COMB (@lem2711490) (@lem2711489)). Qed.
Lemma lem2711492 : term740 = term745.
Proof. exact (MK_COMB (@lem2711491) (@lem2711477)). Qed.
Lemma lem2711493 : term739 = term745.
Proof. exact (TRANS (@lem2711469) (@lem2711492)). Qed.
Lemma lem2711494 : term738 = term745.
Proof. exact (TRANS (@lem2711468) (@lem2711493)). Qed.
Lemma lem2711496 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2711497 : term745 = term742.
Proof. exact (@lem2711496 term742). Qed.
Lemma lem2711498 : term738 = term742.
Proof. exact (TRANS (@lem2711494) (@lem2711497)). Qed.
Lemma lem2711499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711500 : term746 = term747.
Proof. exact (MK_COMB (@lem2711499) (@lem2711498)). Qed.
Lemma lem2711501 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2711502 (n : int) : (term737 n) = (term748 n).
Proof. exact (MK_COMB (@lem2711500) (@lem2711501 n)). Qed.
Lemma lem2711503 (n : int) : (term736 n) = (term748 n).
Proof. exact (TRANS (@lem2711459 n) (@lem2711502 n)). Qed.
Lemma lem2711506 (n : int) : (term749 n) = (term749 n).
Proof. exact (eq_refl (term749 n)). Qed.
Lemma lem2711507 (n : int) : (term735 n) = (term750 n).
Proof. exact (MK_COMB (@lem2711506 n) (@lem2711503 n)). Qed.
Lemma lem2711508 (n : int) : (term734 n) = (term750 n).
Proof. exact (TRANS (@lem2711458 n) (@lem2711507 n)). Qed.
Lemma lem2711509 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2711510 (n : int) : (term751 n) = (term752 n).
Proof. exact (MK_COMB (@lem2711509) (@lem2711508 n)). Qed.
Lemma lem2711511 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2711512 (n : int) : (term733 n) = (term753 n).
Proof. exact (MK_COMB (@lem2711510 n) (@lem2711511)). Qed.
Lemma lem2711513 (n : int) (h1 : term417 n) : term753 n.
Proof. exact (EQ_MP (@lem2711512 n) (@lem2711457 n h1)). Qed.
Lemma lem2711514 (n : int) (h1 : term417 n) : term754 n.
Proof. exact (conj (@lem2711513 n h1) (@lem2711175 n h1)). Qed.
Lemma lem2711516 (x : real) (y : real) : term755 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2711517 (n : int) : term756 n.
Proof. exact (@lem2711516 (term750 n) (term707 n)). Qed.
Lemma lem2711518 (n : int) (h1 : term417 n) : term757 n.
Proof. exact (@lem2711517 n (@lem2711514 n h1)). Qed.
Lemma lem2711519 (n : int) : (term758 n) = (term759 n).
Proof. exact (@lem1982753 (term760 n) (term704 n) (term748 n) (term700 n)). Qed.
Lemma lem2711520 (n : int) : (term761 n) = (term762 n).
Proof. exact (@lem1982711 term28 term184 (real_of_int n)). Qed.
Lemma lem2711522 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711523 : term184 = term187.
Proof. exact (@lem2711522 term29). Qed.
Lemma lem2711525 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711526 : term28 = term173.
Proof. exact (@lem2711525 term29). Qed.
Lemma lem2711527 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711528 : term157 = term373.
Proof. exact (MK_COMB (@lem2711527) (@lem2711526)). Qed.
Lemma lem2711529 : term763 = term764.
Proof. exact (MK_COMB (@lem2711528) (@lem2711523)). Qed.
Lemma lem2711530 : term765.
Proof. exact (@lem1981473 term28 term66 term184 term66 term32 term66). Qed.
Lemma lem2711532 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711533 : term257 = term258.
Proof. exact (@lem2711532 (NUMERAL 0) term67). Qed.
Lemma lem2711534 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711535 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711536 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711535 h1) (fun h1 : term258 = True => @lem2711534)). Qed.
Lemma lem2711537 : term258 = True.
Proof. exact (EQ_MP (@lem2711536) (@lem2711534)). Qed.
Lemma lem2711538 : term257 = True.
Proof. exact (TRANS (@lem2711533) (@lem2711537)). Qed.
Lemma lem2711539 : True = term257.
Proof. exact (SYM (@lem2711538)). Qed.
Lemma lem2711540 : term257.
Proof. exact (EQ_MP (@lem2711539) (@lem0)). Qed.
Lemma lem2711541 : term766.
Proof. exact (@lem2711530 (@lem2711540)). Qed.
Lemma lem2711543 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711544 : term257 = term258.
Proof. exact (@lem2711543 (NUMERAL 0) term67). Qed.
Lemma lem2711545 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711546 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711547 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711546 h1) (fun h1 : term258 = True => @lem2711545)). Qed.
Lemma lem2711548 : term258 = True.
Proof. exact (EQ_MP (@lem2711547) (@lem2711545)). Qed.
Lemma lem2711549 : term257 = True.
Proof. exact (TRANS (@lem2711544) (@lem2711548)). Qed.
Lemma lem2711550 : True = term257.
Proof. exact (SYM (@lem2711549)). Qed.
Lemma lem2711551 : term257.
Proof. exact (EQ_MP (@lem2711550) (@lem0)). Qed.
Lemma lem2711552 : term767.
Proof. exact (@lem2711541 (@lem2711551)). Qed.
Lemma lem2711554 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711555 : term257 = term258.
Proof. exact (@lem2711554 (NUMERAL 0) term67). Qed.
Lemma lem2711556 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711557 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711558 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711557 h1) (fun h1 : term258 = True => @lem2711556)). Qed.
Lemma lem2711559 : term258 = True.
Proof. exact (EQ_MP (@lem2711558) (@lem2711556)). Qed.
Lemma lem2711560 : term257 = True.
Proof. exact (TRANS (@lem2711555) (@lem2711559)). Qed.
Lemma lem2711561 : True = term257.
Proof. exact (SYM (@lem2711560)). Qed.
Lemma lem2711562 : term257.
Proof. exact (EQ_MP (@lem2711561) (@lem0)). Qed.
Lemma lem2711563 : term768.
Proof. exact (@lem2711552 (@lem2711562)). Qed.
Lemma lem2711565 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2711566 : term439 = term440.
Proof. exact (@lem2711565 term29 term67). Qed.
Lemma lem2711567 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711568 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711569 : term292 = term29.
Proof. exact (EQ_MP (@lem2711568) (@lem2711567)). Qed.
Lemma lem2711570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711571 : term290 = term28.
Proof. exact (MK_COMB (@lem2711570) (@lem2711569)). Qed.
Lemma lem2711572 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711573 : term440 = term184.
Proof. exact (MK_COMB (@lem2711572) (@lem2711571)). Qed.
Lemma lem2711574 : term439 = term184.
Proof. exact (TRANS (@lem2711566) (@lem2711573)). Qed.
Lemma lem2711576 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711577 : term289 = term290.
Proof. exact (@lem2711576 term29 term67). Qed.
Lemma lem2711578 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711579 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711580 : term292 = term29.
Proof. exact (EQ_MP (@lem2711579) (@lem2711578)). Qed.
Lemma lem2711581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711582 : term290 = term28.
Proof. exact (MK_COMB (@lem2711581) (@lem2711580)). Qed.
Lemma lem2711583 : term289 = term28.
Proof. exact (TRANS (@lem2711577) (@lem2711582)). Qed.
Lemma lem2711584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711585 : term380 = term157.
Proof. exact (MK_COMB (@lem2711584) (@lem2711583)). Qed.
Lemma lem2711586 : term769 = term763.
Proof. exact (MK_COMB (@lem2711585) (@lem2711574)). Qed.
Lemma lem2711588 (m : nat) : (term265 m) = term32.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2711589 : term763 = term32.
Proof. exact (@lem2711588 term29). Qed.
Lemma lem2711590 : term769 = term32.
Proof. exact (TRANS (@lem2711586) (@lem2711589)). Qed.
Lemma lem2711591 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711592 : term770 = term267.
Proof. exact (MK_COMB (@lem2711591) (@lem2711590)). Qed.
Lemma lem2711593 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2711594 : term771 = term269.
Proof. exact (MK_COMB (@lem2711592) (@lem2711593)). Qed.
Lemma lem2711596 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711597 : term269 = term32.
Proof. exact (@lem2711596 term67). Qed.
Lemma lem2711598 : term771 = term32.
Proof. exact (TRANS (@lem2711594) (@lem2711597)). Qed.
Lemma lem2711600 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711601 : term149 = term150.
Proof. exact (@lem2711600 term67 term67). Qed.
Lemma lem2711602 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711603 : term152 = term67.
Proof. exact (EQ_MP (@lem2711602) (@lem940073)). Qed.
Lemma lem2711604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711605 : term150 = term66.
Proof. exact (MK_COMB (@lem2711604) (@lem2711603)). Qed.
Lemma lem2711606 : term149 = term66.
Proof. exact (TRANS (@lem2711601) (@lem2711605)). Qed.
Lemma lem2711607 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2711608 : term271 = term269.
Proof. exact (MK_COMB (@lem2711607) (@lem2711606)). Qed.
Lemma lem2711610 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711611 : term269 = term32.
Proof. exact (@lem2711610 term67). Qed.
Lemma lem2711612 : term271 = term32.
Proof. exact (TRANS (@lem2711608) (@lem2711611)). Qed.
Lemma lem2711613 : term32 = term271.
Proof. exact (SYM (@lem2711612)). Qed.
Lemma lem2711614 : term771 = term271.
Proof. exact (TRANS (@lem2711598) (@lem2711613)). Qed.
Lemma lem2711615 : term764 = term137.
Proof. exact (@lem2711563 (@lem2711614)). Qed.
Lemma lem2711616 : term763 = term137.
Proof. exact (TRANS (@lem2711529) (@lem2711615)). Qed.
Lemma lem2711618 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2711619 : term137 = term32.
Proof. exact (@lem2711618 term32). Qed.
Lemma lem2711620 : term763 = term32.
Proof. exact (TRANS (@lem2711616) (@lem2711619)). Qed.
Lemma lem2711621 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711622 : term772 = term267.
Proof. exact (MK_COMB (@lem2711621) (@lem2711620)). Qed.
Lemma lem2711623 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2711624 (n : int) : (term762 n) = (term773 n).
Proof. exact (MK_COMB (@lem2711622) (@lem2711623 n)). Qed.
Lemma lem2711625 (n : int) : (term761 n) = (term773 n).
Proof. exact (TRANS (@lem2711520 n) (@lem2711624 n)). Qed.
Lemma lem2711626 (n : int) : (term773 n) = term32.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2711627 (n : int) : (term761 n) = term32.
Proof. exact (TRANS (@lem2711625 n) (@lem2711626 n)). Qed.
Lemma lem2711628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711629 (n : int) : (term774 n) = term102.
Proof. exact (MK_COMB (@lem2711628) (@lem2711627 n)). Qed.
Lemma lem2711630 (n : int) : (term775 n) = (term776 n).
Proof. exact (@lem1982763 (term748 n) (term697 n) term184). Qed.
Lemma lem2711631 (n : int) : (term777 n) = (term778 n).
Proof. exact (@lem1982711 term742 term691 (term162 n)). Qed.
Lemma lem2711633 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711634 : term691 = term694.
Proof. exact (@lem2711633 term690). Qed.
Lemma lem2711636 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711637 : term742 = term745.
Proof. exact (@lem2711636 term690). Qed.
Lemma lem2711638 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711639 : term779 = term780.
Proof. exact (MK_COMB (@lem2711638) (@lem2711637)). Qed.
Lemma lem2711640 : term781 = term782.
Proof. exact (MK_COMB (@lem2711639) (@lem2711634)). Qed.
Lemma lem2711641 : term783.
Proof. exact (@lem1981473 term742 term66 term691 term66 term32 term66). Qed.
Lemma lem2711643 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711644 : term257 = term258.
Proof. exact (@lem2711643 (NUMERAL 0) term67). Qed.
Lemma lem2711645 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711646 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711647 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711646 h1) (fun h1 : term258 = True => @lem2711645)). Qed.
Lemma lem2711648 : term258 = True.
Proof. exact (EQ_MP (@lem2711647) (@lem2711645)). Qed.
Lemma lem2711649 : term257 = True.
Proof. exact (TRANS (@lem2711644) (@lem2711648)). Qed.
Lemma lem2711650 : True = term257.
Proof. exact (SYM (@lem2711649)). Qed.
Lemma lem2711651 : term257.
Proof. exact (EQ_MP (@lem2711650) (@lem0)). Qed.
Lemma lem2711652 : term784.
Proof. exact (@lem2711641 (@lem2711651)). Qed.
Lemma lem2711654 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711655 : term257 = term258.
Proof. exact (@lem2711654 (NUMERAL 0) term67). Qed.
Lemma lem2711656 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711657 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711658 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711657 h1) (fun h1 : term258 = True => @lem2711656)). Qed.
Lemma lem2711659 : term258 = True.
Proof. exact (EQ_MP (@lem2711658) (@lem2711656)). Qed.
Lemma lem2711660 : term257 = True.
Proof. exact (TRANS (@lem2711655) (@lem2711659)). Qed.
Lemma lem2711661 : True = term257.
Proof. exact (SYM (@lem2711660)). Qed.
Lemma lem2711662 : term257.
Proof. exact (EQ_MP (@lem2711661) (@lem0)). Qed.
Lemma lem2711663 : term785.
Proof. exact (@lem2711652 (@lem2711662)). Qed.
Lemma lem2711665 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711666 : term257 = term258.
Proof. exact (@lem2711665 (NUMERAL 0) term67). Qed.
Lemma lem2711667 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711668 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711669 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711668 h1) (fun h1 : term258 = True => @lem2711667)). Qed.
Lemma lem2711670 : term258 = True.
Proof. exact (EQ_MP (@lem2711669) (@lem2711667)). Qed.
Lemma lem2711671 : term257 = True.
Proof. exact (TRANS (@lem2711666) (@lem2711670)). Qed.
Lemma lem2711672 : True = term257.
Proof. exact (SYM (@lem2711671)). Qed.
Lemma lem2711673 : term257.
Proof. exact (EQ_MP (@lem2711672) (@lem0)). Qed.
Lemma lem2711674 : term786.
Proof. exact (@lem2711663 (@lem2711673)). Qed.
Lemma lem2711676 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711677 : term787 = term788.
Proof. exact (@lem2711676 term690 term67). Qed.
Lemma lem2711678 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2711679 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2711680 : term790 = term690.
Proof. exact (EQ_MP (@lem2711679) (@lem2711678)). Qed.
Lemma lem2711681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711682 : term788 = term691.
Proof. exact (MK_COMB (@lem2711681) (@lem2711680)). Qed.
Lemma lem2711683 : term787 = term691.
Proof. exact (TRANS (@lem2711677) (@lem2711682)). Qed.
Lemma lem2711685 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2711686 : term791 = term792.
Proof. exact (@lem2711685 term690 term67). Qed.
Lemma lem2711687 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2711688 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2711689 : term790 = term690.
Proof. exact (EQ_MP (@lem2711688) (@lem2711687)). Qed.
Lemma lem2711690 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711691 : term788 = term691.
Proof. exact (MK_COMB (@lem2711690) (@lem2711689)). Qed.
Lemma lem2711692 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711693 : term792 = term742.
Proof. exact (MK_COMB (@lem2711692) (@lem2711691)). Qed.
Lemma lem2711694 : term791 = term742.
Proof. exact (TRANS (@lem2711686) (@lem2711693)). Qed.
Lemma lem2711695 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711696 : term793 = term779.
Proof. exact (MK_COMB (@lem2711695) (@lem2711694)). Qed.
Lemma lem2711697 : term794 = term781.
Proof. exact (MK_COMB (@lem2711696) (@lem2711683)). Qed.
Lemma lem2711699 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2711700 : term781 = term32.
Proof. exact (@lem2711699 term690). Qed.
Lemma lem2711701 : term794 = term32.
Proof. exact (TRANS (@lem2711697) (@lem2711700)). Qed.
Lemma lem2711702 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711703 : term795 = term267.
Proof. exact (MK_COMB (@lem2711702) (@lem2711701)). Qed.
Lemma lem2711704 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2711705 : term796 = term269.
Proof. exact (MK_COMB (@lem2711703) (@lem2711704)). Qed.
Lemma lem2711707 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711708 : term269 = term32.
Proof. exact (@lem2711707 term67). Qed.
Lemma lem2711709 : term796 = term32.
Proof. exact (TRANS (@lem2711705) (@lem2711708)). Qed.
Lemma lem2711711 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711712 : term149 = term150.
Proof. exact (@lem2711711 term67 term67). Qed.
Lemma lem2711713 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2711714 : term152 = term67.
Proof. exact (EQ_MP (@lem2711713) (@lem940073)). Qed.
Lemma lem2711715 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711716 : term150 = term66.
Proof. exact (MK_COMB (@lem2711715) (@lem2711714)). Qed.
Lemma lem2711717 : term149 = term66.
Proof. exact (TRANS (@lem2711712) (@lem2711716)). Qed.
Lemma lem2711718 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2711719 : term271 = term269.
Proof. exact (MK_COMB (@lem2711718) (@lem2711717)). Qed.
Lemma lem2711721 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711722 : term269 = term32.
Proof. exact (@lem2711721 term67). Qed.
Lemma lem2711723 : term271 = term32.
Proof. exact (TRANS (@lem2711719) (@lem2711722)). Qed.
Lemma lem2711724 : term32 = term271.
Proof. exact (SYM (@lem2711723)). Qed.
Lemma lem2711725 : term796 = term271.
Proof. exact (TRANS (@lem2711709) (@lem2711724)). Qed.
Lemma lem2711726 : term782 = term137.
Proof. exact (@lem2711674 (@lem2711725)). Qed.
Lemma lem2711727 : term781 = term137.
Proof. exact (TRANS (@lem2711640) (@lem2711726)). Qed.
Lemma lem2711729 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2711730 : term137 = term32.
Proof. exact (@lem2711729 term32). Qed.
Lemma lem2711731 : term781 = term32.
Proof. exact (TRANS (@lem2711727) (@lem2711730)). Qed.
Lemma lem2711732 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2711733 : term797 = term267.
Proof. exact (MK_COMB (@lem2711732) (@lem2711731)). Qed.
Lemma lem2711734 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2711735 (n : int) : (term778 n) = (term798 n).
Proof. exact (MK_COMB (@lem2711733) (@lem2711734 n)). Qed.
Lemma lem2711736 (n : int) : (term777 n) = (term798 n).
Proof. exact (TRANS (@lem2711631 n) (@lem2711735 n)). Qed.
Lemma lem2711737 (n : int) : (term798 n) = term32.
Proof. exact (@lem1982719 (term162 n)). Qed.
Lemma lem2711738 (n : int) : (term777 n) = term32.
Proof. exact (TRANS (@lem2711736 n) (@lem2711737 n)). Qed.
Lemma lem2711739 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2711740 (n : int) : (term799 n) = term102.
Proof. exact (MK_COMB (@lem2711739) (@lem2711738 n)). Qed.
Lemma lem2711741 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2711742 (n : int) : (term776 n) = term422.
Proof. exact (MK_COMB (@lem2711740 n) (@lem2711741)). Qed.
Lemma lem2711743 (n : int) : (term775 n) = term422.
Proof. exact (TRANS (@lem2711630 n) (@lem2711742 n)). Qed.
Lemma lem2711744 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2711745 (n : int) : (term775 n) = term184.
Proof. exact (TRANS (@lem2711743 n) (@lem2711744)). Qed.
Lemma lem2711746 (n : int) : (term759 n) = term422.
Proof. exact (MK_COMB (@lem2711629 n) (@lem2711745 n)). Qed.
Lemma lem2711747 (n : int) : (term758 n) = term422.
Proof. exact (TRANS (@lem2711519 n) (@lem2711746 n)). Qed.
Lemma lem2711748 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2711749 (n : int) : (term758 n) = term184.
Proof. exact (TRANS (@lem2711747 n) (@lem2711748)). Qed.
Lemma lem2711750 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2711751 (n : int) : (term800 n) = term801.
Proof. exact (MK_COMB (@lem2711750) (@lem2711749 n)). Qed.
Lemma lem2711752 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2711753 (n : int) : (term757 n) = term802.
Proof. exact (MK_COMB (@lem2711751 n) (@lem2711752)). Qed.
Lemma lem2711754 (n : int) (h1 : term417 n) : term802.
Proof. exact (EQ_MP (@lem2711753 n) (@lem2711518 n h1)). Qed.
Lemma lem2711756 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2711757 : term802 = term803.
Proof. exact (@lem2711756 term32 term184). Qed.
Lemma lem2711759 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711760 : term184 = term187.
Proof. exact (@lem2711759 term29). Qed.
Lemma lem2711762 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711763 : term32 = term137.
Proof. exact (@lem2711762 (NUMERAL 0)). Qed.
Lemma lem2711764 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2711765 : term55 = term804.
Proof. exact (MK_COMB (@lem2711764) (@lem2711763)). Qed.
Lemma lem2711766 : term803 = term805.
Proof. exact (MK_COMB (@lem2711765) (@lem2711760)). Qed.
Lemma lem2711767 : term806.
Proof. exact (@lem1980026 term32 term66 term184 term66). Qed.
Lemma lem2711769 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711770 : term257 = term258.
Proof. exact (@lem2711769 (NUMERAL 0) term67). Qed.
Lemma lem2711771 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711772 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711773 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711772 h1) (fun h1 : term258 = True => @lem2711771)). Qed.
Lemma lem2711774 : term258 = True.
Proof. exact (EQ_MP (@lem2711773) (@lem2711771)). Qed.
Lemma lem2711775 : term257 = True.
Proof. exact (TRANS (@lem2711770) (@lem2711774)). Qed.
Lemma lem2711776 : True = term257.
Proof. exact (SYM (@lem2711775)). Qed.
Lemma lem2711777 : term257.
Proof. exact (EQ_MP (@lem2711776) (@lem0)). Qed.
Lemma lem2711778 : term807.
Proof. exact (@lem2711767 (@lem2711777)). Qed.
Lemma lem2711780 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711781 : term257 = term258.
Proof. exact (@lem2711780 (NUMERAL 0) term67). Qed.
Lemma lem2711782 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711783 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711784 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711783 h1) (fun h1 : term258 = True => @lem2711782)). Qed.
Lemma lem2711785 : term258 = True.
Proof. exact (EQ_MP (@lem2711784) (@lem2711782)). Qed.
Lemma lem2711786 : term257 = True.
Proof. exact (TRANS (@lem2711781) (@lem2711785)). Qed.
Lemma lem2711787 : True = term257.
Proof. exact (SYM (@lem2711786)). Qed.
Lemma lem2711788 : term257.
Proof. exact (EQ_MP (@lem2711787) (@lem0)). Qed.
Lemma lem2711789 : term805 = term808.
Proof. exact (@lem2711778 (@lem2711788)). Qed.
Lemma lem2711791 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2711792 : term439 = term440.
Proof. exact (@lem2711791 term29 term67). Qed.
Lemma lem2711793 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711794 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711795 : term292 = term29.
Proof. exact (EQ_MP (@lem2711794) (@lem2711793)). Qed.
Lemma lem2711796 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711797 : term290 = term28.
Proof. exact (MK_COMB (@lem2711796) (@lem2711795)). Qed.
Lemma lem2711798 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711799 : term440 = term184.
Proof. exact (MK_COMB (@lem2711798) (@lem2711797)). Qed.
Lemma lem2711800 : term439 = term184.
Proof. exact (TRANS (@lem2711792) (@lem2711799)). Qed.
Lemma lem2711802 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711803 : term269 = term32.
Proof. exact (@lem2711802 term67). Qed.
Lemma lem2711804 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2711805 : term809 = term55.
Proof. exact (MK_COMB (@lem2711804) (@lem2711803)). Qed.
Lemma lem2711806 : term808 = term803.
Proof. exact (MK_COMB (@lem2711805) (@lem2711800)). Qed.
Lemma lem2711808 (m : nat) (n : nat) : (term810 m n) = (term811 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2711809 : term803 = term812.
Proof. exact (@lem2711808 (NUMERAL 0) term29). Qed.
Lemma lem2711810 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2711811 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2711812 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2711811 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2711810)). Qed.
Lemma lem2711813 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2711812) (@lem2711810)). Qed.
Lemma lem2711814 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2711815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2711816 : term813 = (and True).
Proof. exact (MK_COMB (@lem2711815) (@lem2711814)). Qed.
Lemma lem2711817 : term812 = (True /\ False).
Proof. exact (MK_COMB (@lem2711816) (@lem2711813)). Qed.
Lemma lem2711819 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2711820 : term812 = False.
Proof. exact (TRANS (@lem2711817) (@lem2711819)). Qed.
Lemma lem2711821 : term803 = False.
Proof. exact (TRANS (@lem2711809) (@lem2711820)). Qed.
Lemma lem2711822 : term808 = False.
Proof. exact (TRANS (@lem2711806) (@lem2711821)). Qed.
Lemma lem2711823 : term805 = False.
Proof. exact (TRANS (@lem2711789) (@lem2711822)). Qed.
Lemma lem2711824 : term803 = False.
Proof. exact (TRANS (@lem2711766) (@lem2711823)). Qed.
Lemma lem2711825 : term802 = False.
Proof. exact (TRANS (@lem2711757) (@lem2711824)). Qed.
Lemma lem2711826 (n : int) (h1 : term417 n) : False.
Proof. exact (EQ_MP (@lem2711825) (@lem2711754 n h1)). Qed.
Lemma lem2711827 (n : int) (h1 : term479 n) : term479 n.
Proof. exact (h1). Qed.
Lemma lem2711829 (n : int) (h1 : term479 n) : term425.
Proof. exact (proj1 (@lem2711827 n h1)). Qed.
Lemma lem2711839 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2711840 : term425 = term814.
Proof. exact (@lem2711839 term32 term184). Qed.
Lemma lem2711842 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2711843 : term184 = term187.
Proof. exact (@lem2711842 term29). Qed.
Lemma lem2711845 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711846 : term32 = term137.
Proof. exact (@lem2711845 (NUMERAL 0)). Qed.
Lemma lem2711847 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711848 : term582 = term583.
Proof. exact (MK_COMB (@lem2711847) (@lem2711846)). Qed.
Lemma lem2711849 : term814 = term815.
Proof. exact (MK_COMB (@lem2711848) (@lem2711843)). Qed.
Lemma lem2711850 : term816.
Proof. exact (@lem1980255 term32 term66 term184 term66). Qed.
Lemma lem2711852 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711853 : term257 = term258.
Proof. exact (@lem2711852 (NUMERAL 0) term67). Qed.
Lemma lem2711854 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711855 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711856 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711855 h1) (fun h1 : term258 = True => @lem2711854)). Qed.
Lemma lem2711857 : term258 = True.
Proof. exact (EQ_MP (@lem2711856) (@lem2711854)). Qed.
Lemma lem2711858 : term257 = True.
Proof. exact (TRANS (@lem2711853) (@lem2711857)). Qed.
Lemma lem2711859 : True = term257.
Proof. exact (SYM (@lem2711858)). Qed.
Lemma lem2711860 : term257.
Proof. exact (EQ_MP (@lem2711859) (@lem0)). Qed.
Lemma lem2711861 : term817.
Proof. exact (@lem2711850 (@lem2711860)). Qed.
Lemma lem2711863 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711864 : term257 = term258.
Proof. exact (@lem2711863 (NUMERAL 0) term67). Qed.
Lemma lem2711865 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711866 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711867 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711866 h1) (fun h1 : term258 = True => @lem2711865)). Qed.
Lemma lem2711868 : term258 = True.
Proof. exact (EQ_MP (@lem2711867) (@lem2711865)). Qed.
Lemma lem2711869 : term257 = True.
Proof. exact (TRANS (@lem2711864) (@lem2711868)). Qed.
Lemma lem2711870 : True = term257.
Proof. exact (SYM (@lem2711869)). Qed.
Lemma lem2711871 : term257.
Proof. exact (EQ_MP (@lem2711870) (@lem0)). Qed.
Lemma lem2711872 : term815 = term818.
Proof. exact (@lem2711861 (@lem2711871)). Qed.
Lemma lem2711874 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2711875 : term439 = term440.
Proof. exact (@lem2711874 term29 term67). Qed.
Lemma lem2711876 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711877 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711878 : term292 = term29.
Proof. exact (EQ_MP (@lem2711877) (@lem2711876)). Qed.
Lemma lem2711879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711880 : term290 = term28.
Proof. exact (MK_COMB (@lem2711879) (@lem2711878)). Qed.
Lemma lem2711881 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2711882 : term440 = term184.
Proof. exact (MK_COMB (@lem2711881) (@lem2711880)). Qed.
Lemma lem2711883 : term439 = term184.
Proof. exact (TRANS (@lem2711875) (@lem2711882)). Qed.
Lemma lem2711885 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711886 : term269 = term32.
Proof. exact (@lem2711885 term67). Qed.
Lemma lem2711887 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711888 : term588 = term582.
Proof. exact (MK_COMB (@lem2711887) (@lem2711886)). Qed.
Lemma lem2711889 : term818 = term814.
Proof. exact (MK_COMB (@lem2711888) (@lem2711883)). Qed.
Lemma lem2711891 (m : nat) (n : nat) : (term819 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2711892 : term814 = False.
Proof. exact (@lem2711891 (NUMERAL 0) term29). Qed.
Lemma lem2711893 : term818 = False.
Proof. exact (TRANS (@lem2711889) (@lem2711892)). Qed.
Lemma lem2711894 : term815 = False.
Proof. exact (TRANS (@lem2711872) (@lem2711893)). Qed.
Lemma lem2711895 : term814 = False.
Proof. exact (TRANS (@lem2711849) (@lem2711894)). Qed.
Lemma lem2711896 : term425 = False.
Proof. exact (TRANS (@lem2711840) (@lem2711895)). Qed.
Lemma lem2711897 (n : int) (h1 : term479 n) : False.
Proof. exact (EQ_MP (@lem2711896) (@lem2711829 n h1)). Qed.
Lemma lem2711898 (n : int) (h1 : term481 n) : False.
Proof. exact (or_elim (@lem2710641 n h1) (fun h0 : term417 n => @lem2711826 n h0) (fun h0 : term479 n => @lem2711897 n h0)). Qed.
Lemma lem2711899 (n : int) (h1 : term483 n) : False.
Proof. exact (or_elim (@lem2710576 n h1) (fun h0 : term575 n => @lem2710640 n h0) (fun h0 : term481 n => @lem2711898 n h0)). Qed.
Lemma lem2711900 (n : int) (h1 : term514 n) : term514 n.
Proof. exact (h1). Qed.
Lemma lem2711901 (n : int) (h1 : term820 n) : term820 n.
Proof. exact (h1). Qed.
Lemma lem2711903 (n : int) (h1 : term820 n) : term28 = term32.
Proof. exact (proj1 (@lem2711901 n h1)). Qed.
Lemma lem2711907 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711908 : term32 = term137.
Proof. exact (@lem2711907 (NUMERAL 0)). Qed.
Lemma lem2711910 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711911 : term28 = term173.
Proof. exact (@lem2711910 term29). Qed.
Lemma lem2711912 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2711913 : term31 = term576.
Proof. exact (MK_COMB (@lem2711912) (@lem2711911)). Qed.
Lemma lem2711914 : (term28 = term32) = (term173 = term137).
Proof. exact (MK_COMB (@lem2711913) (@lem2711908)). Qed.
Lemma lem2711915 : term577.
Proof. exact (@lem1980277 term28 term66 term32 term66). Qed.
Lemma lem2711917 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711918 : term257 = term258.
Proof. exact (@lem2711917 (NUMERAL 0) term67). Qed.
Lemma lem2711919 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711920 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711921 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711920 h1) (fun h1 : term258 = True => @lem2711919)). Qed.
Lemma lem2711922 : term258 = True.
Proof. exact (EQ_MP (@lem2711921) (@lem2711919)). Qed.
Lemma lem2711923 : term257 = True.
Proof. exact (TRANS (@lem2711918) (@lem2711922)). Qed.
Lemma lem2711924 : True = term257.
Proof. exact (SYM (@lem2711923)). Qed.
Lemma lem2711925 : term257.
Proof. exact (EQ_MP (@lem2711924) (@lem0)). Qed.
Lemma lem2711926 : term578.
Proof. exact (@lem2711915 (@lem2711925)). Qed.
Lemma lem2711928 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711929 : term257 = term258.
Proof. exact (@lem2711928 (NUMERAL 0) term67). Qed.
Lemma lem2711930 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711931 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711932 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711931 h1) (fun h1 : term258 = True => @lem2711930)). Qed.
Lemma lem2711933 : term258 = True.
Proof. exact (EQ_MP (@lem2711932) (@lem2711930)). Qed.
Lemma lem2711934 : term257 = True.
Proof. exact (TRANS (@lem2711929) (@lem2711933)). Qed.
Lemma lem2711935 : True = term257.
Proof. exact (SYM (@lem2711934)). Qed.
Lemma lem2711936 : term257.
Proof. exact (EQ_MP (@lem2711935) (@lem0)). Qed.
Lemma lem2711937 : (term173 = term137) = (term289 = term269).
Proof. exact (@lem2711926 (@lem2711936)). Qed.
Lemma lem2711939 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2711940 : term269 = term32.
Proof. exact (@lem2711939 term67). Qed.
Lemma lem2711942 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2711943 : term289 = term290.
Proof. exact (@lem2711942 term29 term67). Qed.
Lemma lem2711944 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2711945 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2711946 : term292 = term29.
Proof. exact (EQ_MP (@lem2711945) (@lem2711944)). Qed.
Lemma lem2711947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2711948 : term290 = term28.
Proof. exact (MK_COMB (@lem2711947) (@lem2711946)). Qed.
Lemma lem2711949 : term289 = term28.
Proof. exact (TRANS (@lem2711943) (@lem2711948)). Qed.
Lemma lem2711950 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2711951 : term579 = term31.
Proof. exact (MK_COMB (@lem2711950) (@lem2711949)). Qed.
Lemma lem2711952 : (term289 = term269) = (term28 = term32).
Proof. exact (MK_COMB (@lem2711951) (@lem2711940)). Qed.
Lemma lem2711954 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem2711955 : (term28 = term32) = (term29 = (NUMERAL 0)).
Proof. exact (@lem2711954 term29 (NUMERAL 0)). Qed.
Lemma lem2711956 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2711957 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2711958 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2711957 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2711956)). Qed.
Lemma lem2711959 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2711958) (@lem2711956)). Qed.
Lemma lem2711960 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2711955) (@lem2711959)). Qed.
Lemma lem2711961 : (term289 = term269) = False.
Proof. exact (TRANS (@lem2711952) (@lem2711960)). Qed.
Lemma lem2711962 : (term173 = term137) = False.
Proof. exact (TRANS (@lem2711937) (@lem2711961)). Qed.
Lemma lem2711963 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2711914) (@lem2711962)). Qed.
Lemma lem2711964 (n : int) (h1 : term820 n) : False.
Proof. exact (EQ_MP (@lem2711963) (@lem2711903 n h1)). Qed.
Lemma lem2711965 (n : int) (h1 : term512 n) : term512 n.
Proof. exact (h1). Qed.
Lemma lem2711966 (n : int) (h1 : term508 n) : term508 n.
Proof. exact (h1). Qed.
Lemma lem2711967 (n : int) (h1 : term508 n) : term507 n.
Proof. exact (proj2 (@lem2711966 n h1)). Qed.
Lemma lem2711969 (n : int) (h1 : term508 n) : term331 n.
Proof. exact (proj2 (@lem2711967 n h1)). Qed.
Lemma lem2711970 (n : int) (h1 : term508 n) : term402 n.
Proof. exact (proj1 (@lem2711967 n h1)). Qed.
Lemma lem2711972 (n : int) (h1 : term508 n) : (term195 n) = term32.
Proof. exact (proj1 (@lem2711970 n h1)). Qed.
Lemma lem2711975 (n : int) (h1 : term508 n) : term275 n.
Proof. exact (proj2 (@lem2711969 n h1)). Qed.
Lemma lem2711976 (n : int) (h1 : term508 n) : term244 n.
Proof. exact (proj1 (@lem2711969 n h1)). Qed.
Lemma lem2711978 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2711979 : term581 = term257.
Proof. exact (@lem2711978 term32 term66). Qed.
Lemma lem2711981 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711982 : term66 = term210.
Proof. exact (@lem2711981 term67). Qed.
Lemma lem2711984 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2711985 : term32 = term137.
Proof. exact (@lem2711984 (NUMERAL 0)). Qed.
Lemma lem2711986 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2711987 : term582 = term583.
Proof. exact (MK_COMB (@lem2711986) (@lem2711985)). Qed.
Lemma lem2711988 : term257 = term584.
Proof. exact (MK_COMB (@lem2711987) (@lem2711982)). Qed.
Lemma lem2711989 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2711991 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2711992 : term257 = term258.
Proof. exact (@lem2711991 (NUMERAL 0) term67). Qed.
Lemma lem2711993 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2711994 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2711995 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2711994 h1) (fun h1 : term258 = True => @lem2711993)). Qed.
Lemma lem2711996 : term258 = True.
Proof. exact (EQ_MP (@lem2711995) (@lem2711993)). Qed.
Lemma lem2711997 : term257 = True.
Proof. exact (TRANS (@lem2711992) (@lem2711996)). Qed.
Lemma lem2711998 : True = term257.
Proof. exact (SYM (@lem2711997)). Qed.
Lemma lem2711999 : term257.
Proof. exact (EQ_MP (@lem2711998) (@lem0)). Qed.
Lemma lem2712000 : term586.
Proof. exact (@lem2711989 (@lem2711999)). Qed.
Lemma lem2712002 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712003 : term257 = term258.
Proof. exact (@lem2712002 (NUMERAL 0) term67). Qed.
Lemma lem2712004 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712005 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712006 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712005 h1) (fun h1 : term258 = True => @lem2712004)). Qed.
Lemma lem2712007 : term258 = True.
Proof. exact (EQ_MP (@lem2712006) (@lem2712004)). Qed.
Lemma lem2712008 : term257 = True.
Proof. exact (TRANS (@lem2712003) (@lem2712007)). Qed.
Lemma lem2712009 : True = term257.
Proof. exact (SYM (@lem2712008)). Qed.
Lemma lem2712010 : term257.
Proof. exact (EQ_MP (@lem2712009) (@lem0)). Qed.
Lemma lem2712011 : term584 = term587.
Proof. exact (@lem2712000 (@lem2712010)). Qed.
Lemma lem2712013 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712014 : term149 = term150.
Proof. exact (@lem2712013 term67 term67). Qed.
Lemma lem2712015 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712016 : term152 = term67.
Proof. exact (EQ_MP (@lem2712015) (@lem940073)). Qed.
Lemma lem2712017 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712018 : term150 = term66.
Proof. exact (MK_COMB (@lem2712017) (@lem2712016)). Qed.
Lemma lem2712019 : term149 = term66.
Proof. exact (TRANS (@lem2712014) (@lem2712018)). Qed.
Lemma lem2712021 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712022 : term269 = term32.
Proof. exact (@lem2712021 term67). Qed.
Lemma lem2712023 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712024 : term588 = term582.
Proof. exact (MK_COMB (@lem2712023) (@lem2712022)). Qed.
Lemma lem2712025 : term587 = term257.
Proof. exact (MK_COMB (@lem2712024) (@lem2712019)). Qed.
Lemma lem2712027 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712028 : term257 = term258.
Proof. exact (@lem2712027 (NUMERAL 0) term67). Qed.
Lemma lem2712029 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712030 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712031 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712030 h1) (fun h1 : term258 = True => @lem2712029)). Qed.
Lemma lem2712032 : term258 = True.
Proof. exact (EQ_MP (@lem2712031) (@lem2712029)). Qed.
Lemma lem2712033 : term257 = True.
Proof. exact (TRANS (@lem2712028) (@lem2712032)). Qed.
Lemma lem2712034 : term587 = True.
Proof. exact (TRANS (@lem2712025) (@lem2712033)). Qed.
Lemma lem2712035 : term584 = True.
Proof. exact (TRANS (@lem2712011) (@lem2712034)). Qed.
Lemma lem2712036 : term257 = True.
Proof. exact (TRANS (@lem2711988) (@lem2712035)). Qed.
Lemma lem2712037 : term581 = True.
Proof. exact (TRANS (@lem2711979) (@lem2712036)). Qed.
Lemma lem2712038 : True = term581.
Proof. exact (SYM (@lem2712037)). Qed.
Lemma lem2712039 : term581.
Proof. exact (EQ_MP (@lem2712038) (@lem0)). Qed.
Lemma lem2712040 (n : int) (h1 : term508 n) : term821 n.
Proof. exact (conj (@lem2712039) (@lem2711975 n h1)). Qed.
Lemma lem2712042 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2712043 (n : int) : term822 n.
Proof. exact (@lem2712042 term66 (term170 n)). Qed.
Lemma lem2712044 (n : int) (h1 : term508 n) : term823 n.
Proof. exact (@lem2712043 n (@lem2712040 n h1)). Qed.
Lemma lem2712045 (n : int) : (term824 n) = (term170 n).
Proof. exact (@lem1982733 (term170 n)). Qed.
Lemma lem2712046 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2712047 (n : int) : (term825 n) = (term274 n).
Proof. exact (MK_COMB (@lem2712046) (@lem2712045 n)). Qed.
Lemma lem2712048 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712049 (n : int) : (term823 n) = (term275 n).
Proof. exact (MK_COMB (@lem2712047 n) (@lem2712048)). Qed.
Lemma lem2712050 (n : int) (h1 : term508 n) : term275 n.
Proof. exact (EQ_MP (@lem2712049 n) (@lem2712044 n h1)). Qed.
Lemma lem2712052 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2712053 (n : int) : term596 n.
Proof. exact (@lem2712052 (term195 n)). Qed.
Lemma lem2712054 (n : int) (h1 : term508 n) : term597 n.
Proof. exact (@lem2712053 n (@lem2711972 n h1)). Qed.
Lemma lem2712055 (n : int) (h1 : term508 n) : term598 n.
Proof. exact (@lem2712054 n h1 term140). Qed.
Lemma lem2712056 (n : int) : (term598 n) = ((term599 n) = term32).
Proof. exact (eq_refl (term598 n)). Qed.
Lemma lem2712057 (n : int) (h1 : term508 n) : (term599 n) = term32.
Proof. exact (EQ_MP (@lem2712056 n) (@lem2712055 n h1)). Qed.
Lemma lem2712058 (n : int) : (term599 n) = (term600 n).
Proof. exact (@lem1982781 (real_of_int n) term140 (term193 n)). Qed.
Lemma lem2712059 (n : int) : (term601 n) = (term602 n).
Proof. exact (@lem1982781 (term190 n) term140 (term170 n)). Qed.
Lemma lem2712060 (n : int) : (term603 n) = (term604 n).
Proof. exact (@lem1982749 term140 term140 (term48 n)). Qed.
Lemma lem2712062 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712063 : term140 = term141.
Proof. exact (@lem2712062 term67). Qed.
Lemma lem2712065 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712066 : term140 = term141.
Proof. exact (@lem2712065 term67). Qed.
Lemma lem2712067 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712068 : term142 = term143.
Proof. exact (MK_COMB (@lem2712067) (@lem2712066)). Qed.
Lemma lem2712069 : term605 = term606.
Proof. exact (MK_COMB (@lem2712068) (@lem2712063)). Qed.
Lemma lem2712070 : term606 = term607.
Proof. exact (@lem1981613 term140 term140 term66 term66). Qed.
Lemma lem2712072 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712073 : term149 = term150.
Proof. exact (@lem2712072 term67 term67). Qed.
Lemma lem2712074 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712075 : term152 = term67.
Proof. exact (EQ_MP (@lem2712074) (@lem940073)). Qed.
Lemma lem2712076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712077 : term150 = term66.
Proof. exact (MK_COMB (@lem2712076) (@lem2712075)). Qed.
Lemma lem2712078 : term149 = term66.
Proof. exact (TRANS (@lem2712073) (@lem2712077)). Qed.
Lemma lem2712080 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2712081 : term605 = term150.
Proof. exact (@lem2712080 term67 term67). Qed.
Lemma lem2712082 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712083 : term152 = term67.
Proof. exact (EQ_MP (@lem2712082) (@lem940073)). Qed.
Lemma lem2712084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712085 : term150 = term66.
Proof. exact (MK_COMB (@lem2712084) (@lem2712083)). Qed.
Lemma lem2712086 : term605 = term66.
Proof. exact (TRANS (@lem2712081) (@lem2712085)). Qed.
Lemma lem2712087 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2712088 : term609 = term610.
Proof. exact (MK_COMB (@lem2712087) (@lem2712086)). Qed.
Lemma lem2712089 : term607 = term210.
Proof. exact (MK_COMB (@lem2712088) (@lem2712078)). Qed.
Lemma lem2712090 : term606 = term210.
Proof. exact (TRANS (@lem2712070) (@lem2712089)). Qed.
Lemma lem2712091 : term605 = term210.
Proof. exact (TRANS (@lem2712069) (@lem2712090)). Qed.
Lemma lem2712093 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2712094 : term210 = term66.
Proof. exact (@lem2712093 term66). Qed.
Lemma lem2712095 : term605 = term66.
Proof. exact (TRANS (@lem2712091) (@lem2712094)). Qed.
Lemma lem2712096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712097 : term611 = term385.
Proof. exact (MK_COMB (@lem2712096) (@lem2712095)). Qed.
Lemma lem2712098 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2712099 (n : int) : (term604 n) = (term612 n).
Proof. exact (MK_COMB (@lem2712097) (@lem2712098 n)). Qed.
Lemma lem2712100 (n : int) : (term603 n) = (term612 n).
Proof. exact (TRANS (@lem2712060 n) (@lem2712099 n)). Qed.
Lemma lem2712101 (n : int) : (term612 n) = (term48 n).
Proof. exact (@lem1982709 (term48 n)). Qed.
Lemma lem2712102 (n : int) : (term603 n) = (term48 n).
Proof. exact (TRANS (@lem2712100 n) (@lem2712101 n)). Qed.
Lemma lem2712103 (n : int) : (term613 n) = (term614 n).
Proof. exact (@lem1982749 term140 term184 (term162 n)). Qed.
Lemma lem2712105 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712106 : term184 = term187.
Proof. exact (@lem2712105 term29). Qed.
Lemma lem2712108 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712109 : term140 = term141.
Proof. exact (@lem2712108 term67). Qed.
Lemma lem2712110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712111 : term142 = term143.
Proof. exact (MK_COMB (@lem2712110) (@lem2712109)). Qed.
Lemma lem2712112 : term615 = term616.
Proof. exact (MK_COMB (@lem2712111) (@lem2712106)). Qed.
Lemma lem2712113 : term616 = term617.
Proof. exact (@lem1981613 term140 term184 term66 term66). Qed.
Lemma lem2712115 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712116 : term149 = term150.
Proof. exact (@lem2712115 term67 term67). Qed.
Lemma lem2712117 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712118 : term152 = term67.
Proof. exact (EQ_MP (@lem2712117) (@lem940073)). Qed.
Lemma lem2712119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712120 : term150 = term66.
Proof. exact (MK_COMB (@lem2712119) (@lem2712118)). Qed.
Lemma lem2712121 : term149 = term66.
Proof. exact (TRANS (@lem2712116) (@lem2712120)). Qed.
Lemma lem2712123 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2712124 : term615 = term183.
Proof. exact (@lem2712123 term67 term29). Qed.
Lemma lem2712125 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2712126 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2712127 : term182 = term29.
Proof. exact (EQ_MP (@lem2712126) (@lem2712125)). Qed.
Lemma lem2712128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712129 : term183 = term28.
Proof. exact (MK_COMB (@lem2712128) (@lem2712127)). Qed.
Lemma lem2712130 : term615 = term28.
Proof. exact (TRANS (@lem2712124) (@lem2712129)). Qed.
Lemma lem2712131 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2712132 : term618 = term619.
Proof. exact (MK_COMB (@lem2712131) (@lem2712130)). Qed.
Lemma lem2712133 : term617 = term173.
Proof. exact (MK_COMB (@lem2712132) (@lem2712121)). Qed.
Lemma lem2712134 : term616 = term173.
Proof. exact (TRANS (@lem2712113) (@lem2712133)). Qed.
Lemma lem2712135 : term615 = term173.
Proof. exact (TRANS (@lem2712112) (@lem2712134)). Qed.
Lemma lem2712137 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2712138 : term173 = term28.
Proof. exact (@lem2712137 term28). Qed.
Lemma lem2712139 : term615 = term28.
Proof. exact (TRANS (@lem2712135) (@lem2712138)). Qed.
Lemma lem2712140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712141 : term620 = term287.
Proof. exact (MK_COMB (@lem2712140) (@lem2712139)). Qed.
Lemma lem2712142 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2712143 (n : int) : (term614 n) = (term161 n).
Proof. exact (MK_COMB (@lem2712141) (@lem2712142 n)). Qed.
Lemma lem2712144 (n : int) : (term613 n) = (term161 n).
Proof. exact (TRANS (@lem2712103 n) (@lem2712143 n)). Qed.
Lemma lem2712145 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712146 (n : int) : (term621 n) = (term163 n).
Proof. exact (MK_COMB (@lem2712145) (@lem2712144 n)). Qed.
Lemma lem2712147 (n : int) : (term602 n) = (term164 n).
Proof. exact (MK_COMB (@lem2712146 n) (@lem2712102 n)). Qed.
Lemma lem2712148 (n : int) : (term601 n) = (term164 n).
Proof. exact (TRANS (@lem2712059 n) (@lem2712147 n)). Qed.
Lemma lem2712151 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2712152 (n : int) : (term600 n) = (term623 n).
Proof. exact (MK_COMB (@lem2712151 n) (@lem2712148 n)). Qed.
Lemma lem2712153 (n : int) : (term599 n) = (term623 n).
Proof. exact (TRANS (@lem2712058 n) (@lem2712152 n)). Qed.
Lemma lem2712154 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2712155 (n : int) : (term624 n) = (term625 n).
Proof. exact (MK_COMB (@lem2712154) (@lem2712153 n)). Qed.
Lemma lem2712156 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712157 (n : int) : ((term599 n) = term32) = ((term623 n) = term32).
Proof. exact (MK_COMB (@lem2712155 n) (@lem2712156)). Qed.
Lemma lem2712158 (n : int) (h1 : term508 n) : (term623 n) = term32.
Proof. exact (EQ_MP (@lem2712157 n) (@lem2712057 n h1)). Qed.
Lemma lem2712159 (n : int) (h1 : term508 n) : term826 n.
Proof. exact (conj (@lem2712158 n h1) (@lem2712050 n h1)). Qed.
Lemma lem2712161 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2712162 (n : int) : term827 n.
Proof. exact (@lem2712161 (term623 n) (term170 n)). Qed.
Lemma lem2712163 (n : int) (h1 : term508 n) : term828 n.
Proof. exact (@lem2712162 n (@lem2712159 n h1)). Qed.
Lemma lem2712164 (n : int) : (term829 n) = (term830 n).
Proof. exact (@lem1982755 (term632 n) (term164 n) (term170 n)). Qed.
Lemma lem2712165 (n : int) : (term831 n) = (term832 n).
Proof. exact (@lem1982755 (term161 n) (term48 n) (term170 n)). Qed.
Lemma lem2712166 (n : int) : (term637 n) = (term638 n).
Proof. exact (@lem1982715 term140 (term48 n)). Qed.
Lemma lem2712168 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712169 : term66 = term210.
Proof. exact (@lem2712168 term67). Qed.
Lemma lem2712171 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712172 : term140 = term141.
Proof. exact (@lem2712171 term67). Qed.
Lemma lem2712173 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712174 : term639 = term640.
Proof. exact (MK_COMB (@lem2712173) (@lem2712172)). Qed.
Lemma lem2712175 : term641 = term642.
Proof. exact (MK_COMB (@lem2712174) (@lem2712169)). Qed.
Lemma lem2712176 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2712178 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712179 : term257 = term258.
Proof. exact (@lem2712178 (NUMERAL 0) term67). Qed.
Lemma lem2712180 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712181 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712182 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712181 h1) (fun h1 : term258 = True => @lem2712180)). Qed.
Lemma lem2712183 : term258 = True.
Proof. exact (EQ_MP (@lem2712182) (@lem2712180)). Qed.
Lemma lem2712184 : term257 = True.
Proof. exact (TRANS (@lem2712179) (@lem2712183)). Qed.
Lemma lem2712185 : True = term257.
Proof. exact (SYM (@lem2712184)). Qed.
Lemma lem2712186 : term257.
Proof. exact (EQ_MP (@lem2712185) (@lem0)). Qed.
Lemma lem2712187 : term644.
Proof. exact (@lem2712176 (@lem2712186)). Qed.
Lemma lem2712189 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712190 : term257 = term258.
Proof. exact (@lem2712189 (NUMERAL 0) term67). Qed.
Lemma lem2712191 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712192 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712193 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712192 h1) (fun h1 : term258 = True => @lem2712191)). Qed.
Lemma lem2712194 : term258 = True.
Proof. exact (EQ_MP (@lem2712193) (@lem2712191)). Qed.
Lemma lem2712195 : term257 = True.
Proof. exact (TRANS (@lem2712190) (@lem2712194)). Qed.
Lemma lem2712196 : True = term257.
Proof. exact (SYM (@lem2712195)). Qed.
Lemma lem2712197 : term257.
Proof. exact (EQ_MP (@lem2712196) (@lem0)). Qed.
Lemma lem2712198 : term645.
Proof. exact (@lem2712187 (@lem2712197)). Qed.
Lemma lem2712200 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712201 : term257 = term258.
Proof. exact (@lem2712200 (NUMERAL 0) term67). Qed.
Lemma lem2712202 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712203 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712204 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712203 h1) (fun h1 : term258 = True => @lem2712202)). Qed.
Lemma lem2712205 : term258 = True.
Proof. exact (EQ_MP (@lem2712204) (@lem2712202)). Qed.
Lemma lem2712206 : term257 = True.
Proof. exact (TRANS (@lem2712201) (@lem2712205)). Qed.
Lemma lem2712207 : True = term257.
Proof. exact (SYM (@lem2712206)). Qed.
Lemma lem2712208 : term257.
Proof. exact (EQ_MP (@lem2712207) (@lem0)). Qed.
Lemma lem2712209 : term646.
Proof. exact (@lem2712198 (@lem2712208)). Qed.
Lemma lem2712211 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712212 : term149 = term150.
Proof. exact (@lem2712211 term67 term67). Qed.
Lemma lem2712213 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712214 : term152 = term67.
Proof. exact (EQ_MP (@lem2712213) (@lem940073)). Qed.
Lemma lem2712215 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712216 : term150 = term66.
Proof. exact (MK_COMB (@lem2712215) (@lem2712214)). Qed.
Lemma lem2712217 : term149 = term66.
Proof. exact (TRANS (@lem2712212) (@lem2712216)). Qed.
Lemma lem2712219 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2712220 : term211 = term214.
Proof. exact (@lem2712219 term67 term67). Qed.
Lemma lem2712221 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712222 : term152 = term67.
Proof. exact (EQ_MP (@lem2712221) (@lem940073)). Qed.
Lemma lem2712223 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712224 : term150 = term66.
Proof. exact (MK_COMB (@lem2712223) (@lem2712222)). Qed.
Lemma lem2712225 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2712226 : term214 = term140.
Proof. exact (MK_COMB (@lem2712225) (@lem2712224)). Qed.
Lemma lem2712227 : term211 = term140.
Proof. exact (TRANS (@lem2712220) (@lem2712226)). Qed.
Lemma lem2712228 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712229 : term647 = term639.
Proof. exact (MK_COMB (@lem2712228) (@lem2712227)). Qed.
Lemma lem2712230 : term648 = term641.
Proof. exact (MK_COMB (@lem2712229) (@lem2712217)). Qed.
Lemma lem2712232 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2712233 : term641 = term32.
Proof. exact (@lem2712232 term67). Qed.
Lemma lem2712234 : term648 = term32.
Proof. exact (TRANS (@lem2712230) (@lem2712233)). Qed.
Lemma lem2712235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712236 : term650 = term267.
Proof. exact (MK_COMB (@lem2712235) (@lem2712234)). Qed.
Lemma lem2712237 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2712238 : term651 = term269.
Proof. exact (MK_COMB (@lem2712236) (@lem2712237)). Qed.
Lemma lem2712240 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712241 : term269 = term32.
Proof. exact (@lem2712240 term67). Qed.
Lemma lem2712242 : term651 = term32.
Proof. exact (TRANS (@lem2712238) (@lem2712241)). Qed.
Lemma lem2712244 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712245 : term149 = term150.
Proof. exact (@lem2712244 term67 term67). Qed.
Lemma lem2712246 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712247 : term152 = term67.
Proof. exact (EQ_MP (@lem2712246) (@lem940073)). Qed.
Lemma lem2712248 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712249 : term150 = term66.
Proof. exact (MK_COMB (@lem2712248) (@lem2712247)). Qed.
Lemma lem2712250 : term149 = term66.
Proof. exact (TRANS (@lem2712245) (@lem2712249)). Qed.
Lemma lem2712251 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2712252 : term271 = term269.
Proof. exact (MK_COMB (@lem2712251) (@lem2712250)). Qed.
Lemma lem2712254 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712255 : term269 = term32.
Proof. exact (@lem2712254 term67). Qed.
Lemma lem2712256 : term271 = term32.
Proof. exact (TRANS (@lem2712252) (@lem2712255)). Qed.
Lemma lem2712257 : term32 = term271.
Proof. exact (SYM (@lem2712256)). Qed.
Lemma lem2712258 : term651 = term271.
Proof. exact (TRANS (@lem2712242) (@lem2712257)). Qed.
Lemma lem2712259 : term642 = term137.
Proof. exact (@lem2712209 (@lem2712258)). Qed.
Lemma lem2712260 : term641 = term137.
Proof. exact (TRANS (@lem2712175) (@lem2712259)). Qed.
Lemma lem2712262 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2712263 : term137 = term32.
Proof. exact (@lem2712262 term32). Qed.
Lemma lem2712264 : term641 = term32.
Proof. exact (TRANS (@lem2712260) (@lem2712263)). Qed.
Lemma lem2712265 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712266 : term652 = term267.
Proof. exact (MK_COMB (@lem2712265) (@lem2712264)). Qed.
Lemma lem2712267 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2712268 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2712266) (@lem2712267 n)). Qed.
Lemma lem2712269 (n : int) : (term637 n) = (term653 n).
Proof. exact (TRANS (@lem2712166 n) (@lem2712268 n)). Qed.
Lemma lem2712270 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2712271 (n : int) : (term637 n) = term32.
Proof. exact (TRANS (@lem2712269 n) (@lem2712270 n)). Qed.
Lemma lem2712272 (n : int) : (term163 n) = (term163 n).
Proof. exact (eq_refl (term163 n)). Qed.
Lemma lem2712273 (n : int) : (term832 n) = (term833 n).
Proof. exact (MK_COMB (@lem2712272 n) (@lem2712271 n)). Qed.
Lemma lem2712274 (n : int) : (term831 n) = (term833 n).
Proof. exact (TRANS (@lem2712165 n) (@lem2712273 n)). Qed.
Lemma lem2712275 (n : int) : (term833 n) = (term161 n).
Proof. exact (@lem1982723 (term161 n)). Qed.
Lemma lem2712276 (n : int) : (term831 n) = (term161 n).
Proof. exact (TRANS (@lem2712274 n) (@lem2712275 n)). Qed.
Lemma lem2712277 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2712278 (n : int) : (term830 n) = (term834 n).
Proof. exact (MK_COMB (@lem2712277 n) (@lem2712276 n)). Qed.
Lemma lem2712279 (n : int) : (term829 n) = (term834 n).
Proof. exact (TRANS (@lem2712164 n) (@lem2712278 n)). Qed.
Lemma lem2712280 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2712281 (n : int) : (term835 n) = (term836 n).
Proof. exact (MK_COMB (@lem2712280) (@lem2712279 n)). Qed.
Lemma lem2712282 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712283 (n : int) : (term828 n) = (term837 n).
Proof. exact (MK_COMB (@lem2712281 n) (@lem2712282)). Qed.
Lemma lem2712284 (n : int) (h1 : term508 n) : term837 n.
Proof. exact (EQ_MP (@lem2712283 n) (@lem2712163 n h1)). Qed.
Lemma lem2712286 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2712287 : term661 = term662.
Proof. exact (@lem2712286 term32 term28). Qed.
Lemma lem2712289 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712290 : term28 = term173.
Proof. exact (@lem2712289 term29). Qed.
Lemma lem2712292 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712293 : term32 = term137.
Proof. exact (@lem2712292 (NUMERAL 0)). Qed.
Lemma lem2712294 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712295 : term582 = term583.
Proof. exact (MK_COMB (@lem2712294) (@lem2712293)). Qed.
Lemma lem2712296 : term662 = term663.
Proof. exact (MK_COMB (@lem2712295) (@lem2712290)). Qed.
Lemma lem2712297 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2712299 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712300 : term257 = term258.
Proof. exact (@lem2712299 (NUMERAL 0) term67). Qed.
Lemma lem2712301 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712302 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712303 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712302 h1) (fun h1 : term258 = True => @lem2712301)). Qed.
Lemma lem2712304 : term258 = True.
Proof. exact (EQ_MP (@lem2712303) (@lem2712301)). Qed.
Lemma lem2712305 : term257 = True.
Proof. exact (TRANS (@lem2712300) (@lem2712304)). Qed.
Lemma lem2712306 : True = term257.
Proof. exact (SYM (@lem2712305)). Qed.
Lemma lem2712307 : term257.
Proof. exact (EQ_MP (@lem2712306) (@lem0)). Qed.
Lemma lem2712308 : term665.
Proof. exact (@lem2712297 (@lem2712307)). Qed.
Lemma lem2712310 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712311 : term257 = term258.
Proof. exact (@lem2712310 (NUMERAL 0) term67). Qed.
Lemma lem2712312 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712313 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712314 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712313 h1) (fun h1 : term258 = True => @lem2712312)). Qed.
Lemma lem2712315 : term258 = True.
Proof. exact (EQ_MP (@lem2712314) (@lem2712312)). Qed.
Lemma lem2712316 : term257 = True.
Proof. exact (TRANS (@lem2712311) (@lem2712315)). Qed.
Lemma lem2712317 : True = term257.
Proof. exact (SYM (@lem2712316)). Qed.
Lemma lem2712318 : term257.
Proof. exact (EQ_MP (@lem2712317) (@lem0)). Qed.
Lemma lem2712319 : term663 = term666.
Proof. exact (@lem2712308 (@lem2712318)). Qed.
Lemma lem2712321 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712322 : term289 = term290.
Proof. exact (@lem2712321 term29 term67). Qed.
Lemma lem2712323 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2712324 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2712325 : term292 = term29.
Proof. exact (EQ_MP (@lem2712324) (@lem2712323)). Qed.
Lemma lem2712326 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712327 : term290 = term28.
Proof. exact (MK_COMB (@lem2712326) (@lem2712325)). Qed.
Lemma lem2712328 : term289 = term28.
Proof. exact (TRANS (@lem2712322) (@lem2712327)). Qed.
Lemma lem2712330 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712331 : term269 = term32.
Proof. exact (@lem2712330 term67). Qed.
Lemma lem2712332 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712333 : term588 = term582.
Proof. exact (MK_COMB (@lem2712332) (@lem2712331)). Qed.
Lemma lem2712334 : term666 = term662.
Proof. exact (MK_COMB (@lem2712333) (@lem2712328)). Qed.
Lemma lem2712336 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712337 : term662 = term667.
Proof. exact (@lem2712336 (NUMERAL 0) term29). Qed.
Lemma lem2712338 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2712339 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2712340 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2712339 h1) (fun h1 : term667 = True => @lem2712338)). Qed.
Lemma lem2712341 : term667 = True.
Proof. exact (EQ_MP (@lem2712340) (@lem2712338)). Qed.
Lemma lem2712342 : term662 = True.
Proof. exact (TRANS (@lem2712337) (@lem2712341)). Qed.
Lemma lem2712343 : term666 = True.
Proof. exact (TRANS (@lem2712334) (@lem2712342)). Qed.
Lemma lem2712344 : term663 = True.
Proof. exact (TRANS (@lem2712319) (@lem2712343)). Qed.
Lemma lem2712345 : term662 = True.
Proof. exact (TRANS (@lem2712296) (@lem2712344)). Qed.
Lemma lem2712346 : term661 = True.
Proof. exact (TRANS (@lem2712287) (@lem2712345)). Qed.
Lemma lem2712347 : True = term661.
Proof. exact (SYM (@lem2712346)). Qed.
Lemma lem2712348 : term661.
Proof. exact (EQ_MP (@lem2712347) (@lem0)). Qed.
Lemma lem2712349 (n : int) (h1 : term508 n) : term838 n.
Proof. exact (conj (@lem2712348) (@lem2712284 n h1)). Qed.
Lemma lem2712351 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2712352 (n : int) : term839 n.
Proof. exact (@lem2712351 term28 (term834 n)). Qed.
Lemma lem2712353 (n : int) (h1 : term508 n) : term840 n.
Proof. exact (@lem2712352 n (@lem2712349 n h1)). Qed.
Lemma lem2712354 (n : int) : (term841 n) = (term842 n).
Proof. exact (@lem1982781 (term632 n) term28 (term161 n)). Qed.
Lemma lem2712355 (n : int) : (term681 n) = (term682 n).
Proof. exact (@lem1982749 term28 term28 (term162 n)). Qed.
Lemma lem2712357 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712358 : term28 = term173.
Proof. exact (@lem2712357 term29). Qed.
Lemma lem2712360 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712361 : term28 = term173.
Proof. exact (@lem2712360 term29). Qed.
Lemma lem2712362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712363 : term287 = term675.
Proof. exact (MK_COMB (@lem2712362) (@lem2712361)). Qed.
Lemma lem2712364 : term683 = term684.
Proof. exact (MK_COMB (@lem2712363) (@lem2712358)). Qed.
Lemma lem2712365 : term684 = term685.
Proof. exact (@lem1981613 term28 term28 term66 term66). Qed.
Lemma lem2712367 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712368 : term149 = term150.
Proof. exact (@lem2712367 term67 term67). Qed.
Lemma lem2712369 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712370 : term152 = term67.
Proof. exact (EQ_MP (@lem2712369) (@lem940073)). Qed.
Lemma lem2712371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712372 : term150 = term66.
Proof. exact (MK_COMB (@lem2712371) (@lem2712370)). Qed.
Lemma lem2712373 : term149 = term66.
Proof. exact (TRANS (@lem2712368) (@lem2712372)). Qed.
Lemma lem2712375 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712376 : term683 = term686.
Proof. exact (@lem2712375 term29 term29). Qed.
Lemma lem2712377 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712378 : term687 = term688.
Proof. exact (EQ_MP (@lem2712377) (@lem940073)). Qed.
Lemma lem2712379 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2712380 : term689 = term690.
Proof. exact (EQ_MP (@lem2712379) (@lem2712378)). Qed.
Lemma lem2712381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712382 : term686 = term691.
Proof. exact (MK_COMB (@lem2712381) (@lem2712380)). Qed.
Lemma lem2712383 : term683 = term691.
Proof. exact (TRANS (@lem2712376) (@lem2712382)). Qed.
Lemma lem2712384 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2712385 : term692 = term693.
Proof. exact (MK_COMB (@lem2712384) (@lem2712383)). Qed.
Lemma lem2712386 : term685 = term694.
Proof. exact (MK_COMB (@lem2712385) (@lem2712373)). Qed.
Lemma lem2712387 : term684 = term694.
Proof. exact (TRANS (@lem2712365) (@lem2712386)). Qed.
Lemma lem2712388 : term683 = term694.
Proof. exact (TRANS (@lem2712364) (@lem2712387)). Qed.
Lemma lem2712390 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2712391 : term694 = term691.
Proof. exact (@lem2712390 term691). Qed.
Lemma lem2712392 : term683 = term691.
Proof. exact (TRANS (@lem2712388) (@lem2712391)). Qed.
Lemma lem2712393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712394 : term695 = term696.
Proof. exact (MK_COMB (@lem2712393) (@lem2712392)). Qed.
Lemma lem2712395 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2712396 (n : int) : (term682 n) = (term697 n).
Proof. exact (MK_COMB (@lem2712394) (@lem2712395 n)). Qed.
Lemma lem2712397 (n : int) : (term681 n) = (term697 n).
Proof. exact (TRANS (@lem2712355 n) (@lem2712396 n)). Qed.
Lemma lem2712398 (n : int) : (term701 n) = (term702 n).
Proof. exact (@lem1982749 term28 term140 (real_of_int n)). Qed.
Lemma lem2712400 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712401 : term140 = term141.
Proof. exact (@lem2712400 term67). Qed.
Lemma lem2712403 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712404 : term28 = term173.
Proof. exact (@lem2712403 term29). Qed.
Lemma lem2712405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712406 : term287 = term675.
Proof. exact (MK_COMB (@lem2712405) (@lem2712404)). Qed.
Lemma lem2712407 : term676 = term677.
Proof. exact (MK_COMB (@lem2712406) (@lem2712401)). Qed.
Lemma lem2712408 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2712410 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712411 : term149 = term150.
Proof. exact (@lem2712410 term67 term67). Qed.
Lemma lem2712412 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712413 : term152 = term67.
Proof. exact (EQ_MP (@lem2712412) (@lem940073)). Qed.
Lemma lem2712414 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712415 : term150 = term66.
Proof. exact (MK_COMB (@lem2712414) (@lem2712413)). Qed.
Lemma lem2712416 : term149 = term66.
Proof. exact (TRANS (@lem2712411) (@lem2712415)). Qed.
Lemma lem2712418 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2712419 : term676 = term440.
Proof. exact (@lem2712418 term29 term67). Qed.
Lemma lem2712420 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2712421 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2712422 : term292 = term29.
Proof. exact (EQ_MP (@lem2712421) (@lem2712420)). Qed.
Lemma lem2712423 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712424 : term290 = term28.
Proof. exact (MK_COMB (@lem2712423) (@lem2712422)). Qed.
Lemma lem2712425 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2712426 : term440 = term184.
Proof. exact (MK_COMB (@lem2712425) (@lem2712424)). Qed.
Lemma lem2712427 : term676 = term184.
Proof. exact (TRANS (@lem2712419) (@lem2712426)). Qed.
Lemma lem2712428 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2712429 : term680 = term186.
Proof. exact (MK_COMB (@lem2712428) (@lem2712427)). Qed.
Lemma lem2712430 : term678 = term187.
Proof. exact (MK_COMB (@lem2712429) (@lem2712416)). Qed.
Lemma lem2712431 : term677 = term187.
Proof. exact (TRANS (@lem2712408) (@lem2712430)). Qed.
Lemma lem2712432 : term676 = term187.
Proof. exact (TRANS (@lem2712407) (@lem2712431)). Qed.
Lemma lem2712434 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2712435 : term187 = term184.
Proof. exact (@lem2712434 term184). Qed.
Lemma lem2712436 : term676 = term184.
Proof. exact (TRANS (@lem2712432) (@lem2712435)). Qed.
Lemma lem2712437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712438 : term703 = term189.
Proof. exact (MK_COMB (@lem2712437) (@lem2712436)). Qed.
Lemma lem2712439 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2712440 (n : int) : (term702 n) = (term704 n).
Proof. exact (MK_COMB (@lem2712438) (@lem2712439 n)). Qed.
Lemma lem2712441 (n : int) : (term701 n) = (term704 n).
Proof. exact (TRANS (@lem2712398 n) (@lem2712440 n)). Qed.
Lemma lem2712442 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712443 (n : int) : (term705 n) = (term706 n).
Proof. exact (MK_COMB (@lem2712442) (@lem2712441 n)). Qed.
Lemma lem2712444 (n : int) : (term842 n) = (term843 n).
Proof. exact (MK_COMB (@lem2712443 n) (@lem2712397 n)). Qed.
Lemma lem2712445 (n : int) : (term841 n) = (term843 n).
Proof. exact (TRANS (@lem2712354 n) (@lem2712444 n)). Qed.
Lemma lem2712446 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2712447 (n : int) : (term844 n) = (term845 n).
Proof. exact (MK_COMB (@lem2712446) (@lem2712445 n)). Qed.
Lemma lem2712448 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712449 (n : int) : (term840 n) = (term846 n).
Proof. exact (MK_COMB (@lem2712447 n) (@lem2712448)). Qed.
Lemma lem2712450 (n : int) (h1 : term508 n) : term846 n.
Proof. exact (EQ_MP (@lem2712449 n) (@lem2712353 n h1)). Qed.
Lemma lem2712452 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2712453 : term581 = term257.
Proof. exact (@lem2712452 term32 term66). Qed.
Lemma lem2712455 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712456 : term66 = term210.
Proof. exact (@lem2712455 term67). Qed.
Lemma lem2712458 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712459 : term32 = term137.
Proof. exact (@lem2712458 (NUMERAL 0)). Qed.
Lemma lem2712460 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712461 : term582 = term583.
Proof. exact (MK_COMB (@lem2712460) (@lem2712459)). Qed.
Lemma lem2712462 : term257 = term584.
Proof. exact (MK_COMB (@lem2712461) (@lem2712456)). Qed.
Lemma lem2712463 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2712465 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712466 : term257 = term258.
Proof. exact (@lem2712465 (NUMERAL 0) term67). Qed.
Lemma lem2712467 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712468 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712469 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712468 h1) (fun h1 : term258 = True => @lem2712467)). Qed.
Lemma lem2712470 : term258 = True.
Proof. exact (EQ_MP (@lem2712469) (@lem2712467)). Qed.
Lemma lem2712471 : term257 = True.
Proof. exact (TRANS (@lem2712466) (@lem2712470)). Qed.
Lemma lem2712472 : True = term257.
Proof. exact (SYM (@lem2712471)). Qed.
Lemma lem2712473 : term257.
Proof. exact (EQ_MP (@lem2712472) (@lem0)). Qed.
Lemma lem2712474 : term586.
Proof. exact (@lem2712463 (@lem2712473)). Qed.
Lemma lem2712476 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712477 : term257 = term258.
Proof. exact (@lem2712476 (NUMERAL 0) term67). Qed.
Lemma lem2712478 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712479 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712480 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712479 h1) (fun h1 : term258 = True => @lem2712478)). Qed.
Lemma lem2712481 : term258 = True.
Proof. exact (EQ_MP (@lem2712480) (@lem2712478)). Qed.
Lemma lem2712482 : term257 = True.
Proof. exact (TRANS (@lem2712477) (@lem2712481)). Qed.
Lemma lem2712483 : True = term257.
Proof. exact (SYM (@lem2712482)). Qed.
Lemma lem2712484 : term257.
Proof. exact (EQ_MP (@lem2712483) (@lem0)). Qed.
Lemma lem2712485 : term584 = term587.
Proof. exact (@lem2712474 (@lem2712484)). Qed.
Lemma lem2712487 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712488 : term149 = term150.
Proof. exact (@lem2712487 term67 term67). Qed.
Lemma lem2712489 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712490 : term152 = term67.
Proof. exact (EQ_MP (@lem2712489) (@lem940073)). Qed.
Lemma lem2712491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712492 : term150 = term66.
Proof. exact (MK_COMB (@lem2712491) (@lem2712490)). Qed.
Lemma lem2712493 : term149 = term66.
Proof. exact (TRANS (@lem2712488) (@lem2712492)). Qed.
Lemma lem2712495 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712496 : term269 = term32.
Proof. exact (@lem2712495 term67). Qed.
Lemma lem2712497 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712498 : term588 = term582.
Proof. exact (MK_COMB (@lem2712497) (@lem2712496)). Qed.
Lemma lem2712499 : term587 = term257.
Proof. exact (MK_COMB (@lem2712498) (@lem2712493)). Qed.
Lemma lem2712501 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712502 : term257 = term258.
Proof. exact (@lem2712501 (NUMERAL 0) term67). Qed.
Lemma lem2712503 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712504 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712505 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712504 h1) (fun h1 : term258 = True => @lem2712503)). Qed.
Lemma lem2712506 : term258 = True.
Proof. exact (EQ_MP (@lem2712505) (@lem2712503)). Qed.
Lemma lem2712507 : term257 = True.
Proof. exact (TRANS (@lem2712502) (@lem2712506)). Qed.
Lemma lem2712508 : term587 = True.
Proof. exact (TRANS (@lem2712499) (@lem2712507)). Qed.
Lemma lem2712509 : term584 = True.
Proof. exact (TRANS (@lem2712485) (@lem2712508)). Qed.
Lemma lem2712510 : term257 = True.
Proof. exact (TRANS (@lem2712462) (@lem2712509)). Qed.
Lemma lem2712511 : term581 = True.
Proof. exact (TRANS (@lem2712453) (@lem2712510)). Qed.
Lemma lem2712512 : True = term581.
Proof. exact (SYM (@lem2712511)). Qed.
Lemma lem2712513 : term581.
Proof. exact (EQ_MP (@lem2712512) (@lem0)). Qed.
Lemma lem2712514 (n : int) (h1 : term508 n) : term847 n.
Proof. exact (conj (@lem2712513) (@lem2711976 n h1)). Qed.
Lemma lem2712516 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2712517 (n : int) : term848 n.
Proof. exact (@lem2712516 term66 (term241 n)). Qed.
Lemma lem2712518 (n : int) (h1 : term508 n) : term849 n.
Proof. exact (@lem2712517 n (@lem2712514 n h1)). Qed.
Lemma lem2712519 (n : int) : (term850 n) = (term241 n).
Proof. exact (@lem1982733 (term241 n)). Qed.
Lemma lem2712520 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2712521 (n : int) : (term851 n) = (term243 n).
Proof. exact (MK_COMB (@lem2712520) (@lem2712519 n)). Qed.
Lemma lem2712522 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712523 (n : int) : (term849 n) = (term244 n).
Proof. exact (MK_COMB (@lem2712521 n) (@lem2712522)). Qed.
Lemma lem2712524 (n : int) (h1 : term508 n) : term244 n.
Proof. exact (EQ_MP (@lem2712523 n) (@lem2712518 n h1)). Qed.
Lemma lem2712526 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2712527 (n : int) : term596 n.
Proof. exact (@lem2712526 (term195 n)). Qed.
Lemma lem2712528 (n : int) (h1 : term508 n) : term597 n.
Proof. exact (@lem2712527 n (@lem2711972 n h1)). Qed.
Lemma lem2712529 (n : int) (h1 : term508 n) : term715 n.
Proof. exact (@lem2712528 n h1 term66). Qed.
Lemma lem2712530 (n : int) : (term715 n) = ((term716 n) = term32).
Proof. exact (eq_refl (term715 n)). Qed.
Lemma lem2712531 (n : int) (h1 : term508 n) : (term716 n) = term32.
Proof. exact (EQ_MP (@lem2712530 n) (@lem2712529 n h1)). Qed.
Lemma lem2712532 (n : int) : (term716 n) = (term195 n).
Proof. exact (@lem1982733 (term195 n)). Qed.
Lemma lem2712533 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2712534 (n : int) : (term717 n) = (term197 n).
Proof. exact (MK_COMB (@lem2712533) (@lem2712532 n)). Qed.
Lemma lem2712535 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712536 (n : int) : ((term716 n) = term32) = ((term195 n) = term32).
Proof. exact (MK_COMB (@lem2712534 n) (@lem2712535)). Qed.
Lemma lem2712537 (n : int) (h1 : term508 n) : (term195 n) = term32.
Proof. exact (EQ_MP (@lem2712536 n) (@lem2712531 n h1)). Qed.
Lemma lem2712538 (n : int) (h1 : term508 n) : term852 n.
Proof. exact (conj (@lem2712537 n h1) (@lem2712524 n h1)). Qed.
Lemma lem2712540 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2712541 (n : int) : term853 n.
Proof. exact (@lem2712540 (term195 n) (term241 n)). Qed.
Lemma lem2712542 (n : int) (h1 : term508 n) : term854 n.
Proof. exact (@lem2712541 n (@lem2712538 n h1)). Qed.
Lemma lem2712543 (n : int) : (term855 n) = (term856 n).
Proof. exact (@lem1982755 (real_of_int n) (term193 n) (term241 n)). Qed.
Lemma lem2712544 (n : int) : (term857 n) = (term858 n).
Proof. exact (@lem1982755 (term190 n) (term170 n) (term241 n)). Qed.
Lemma lem2712545 (n : int) : (term859 n) = (term860 n).
Proof. exact (@lem1982763 (term170 n) (term48 n) term140). Qed.
Lemma lem2712546 (n : int) : (term725 n) = (term638 n).
Proof. exact (@lem1982713 term140 (term48 n)). Qed.
Lemma lem2712548 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712549 : term66 = term210.
Proof. exact (@lem2712548 term67). Qed.
Lemma lem2712551 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712552 : term140 = term141.
Proof. exact (@lem2712551 term67). Qed.
Lemma lem2712553 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712554 : term639 = term640.
Proof. exact (MK_COMB (@lem2712553) (@lem2712552)). Qed.
Lemma lem2712555 : term641 = term642.
Proof. exact (MK_COMB (@lem2712554) (@lem2712549)). Qed.
Lemma lem2712556 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2712558 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712559 : term257 = term258.
Proof. exact (@lem2712558 (NUMERAL 0) term67). Qed.
Lemma lem2712560 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712561 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712562 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712561 h1) (fun h1 : term258 = True => @lem2712560)). Qed.
Lemma lem2712563 : term258 = True.
Proof. exact (EQ_MP (@lem2712562) (@lem2712560)). Qed.
Lemma lem2712564 : term257 = True.
Proof. exact (TRANS (@lem2712559) (@lem2712563)). Qed.
Lemma lem2712565 : True = term257.
Proof. exact (SYM (@lem2712564)). Qed.
Lemma lem2712566 : term257.
Proof. exact (EQ_MP (@lem2712565) (@lem0)). Qed.
Lemma lem2712567 : term644.
Proof. exact (@lem2712556 (@lem2712566)). Qed.
Lemma lem2712569 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712570 : term257 = term258.
Proof. exact (@lem2712569 (NUMERAL 0) term67). Qed.
Lemma lem2712571 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712572 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712573 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712572 h1) (fun h1 : term258 = True => @lem2712571)). Qed.
Lemma lem2712574 : term258 = True.
Proof. exact (EQ_MP (@lem2712573) (@lem2712571)). Qed.
Lemma lem2712575 : term257 = True.
Proof. exact (TRANS (@lem2712570) (@lem2712574)). Qed.
Lemma lem2712576 : True = term257.
Proof. exact (SYM (@lem2712575)). Qed.
Lemma lem2712577 : term257.
Proof. exact (EQ_MP (@lem2712576) (@lem0)). Qed.
Lemma lem2712578 : term645.
Proof. exact (@lem2712567 (@lem2712577)). Qed.
Lemma lem2712580 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712581 : term257 = term258.
Proof. exact (@lem2712580 (NUMERAL 0) term67). Qed.
Lemma lem2712582 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712583 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712584 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712583 h1) (fun h1 : term258 = True => @lem2712582)). Qed.
Lemma lem2712585 : term258 = True.
Proof. exact (EQ_MP (@lem2712584) (@lem2712582)). Qed.
Lemma lem2712586 : term257 = True.
Proof. exact (TRANS (@lem2712581) (@lem2712585)). Qed.
Lemma lem2712587 : True = term257.
Proof. exact (SYM (@lem2712586)). Qed.
Lemma lem2712588 : term257.
Proof. exact (EQ_MP (@lem2712587) (@lem0)). Qed.
Lemma lem2712589 : term646.
Proof. exact (@lem2712578 (@lem2712588)). Qed.
Lemma lem2712591 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712592 : term149 = term150.
Proof. exact (@lem2712591 term67 term67). Qed.
Lemma lem2712593 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712594 : term152 = term67.
Proof. exact (EQ_MP (@lem2712593) (@lem940073)). Qed.
Lemma lem2712595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712596 : term150 = term66.
Proof. exact (MK_COMB (@lem2712595) (@lem2712594)). Qed.
Lemma lem2712597 : term149 = term66.
Proof. exact (TRANS (@lem2712592) (@lem2712596)). Qed.
Lemma lem2712599 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2712600 : term211 = term214.
Proof. exact (@lem2712599 term67 term67). Qed.
Lemma lem2712601 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712602 : term152 = term67.
Proof. exact (EQ_MP (@lem2712601) (@lem940073)). Qed.
Lemma lem2712603 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712604 : term150 = term66.
Proof. exact (MK_COMB (@lem2712603) (@lem2712602)). Qed.
Lemma lem2712605 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2712606 : term214 = term140.
Proof. exact (MK_COMB (@lem2712605) (@lem2712604)). Qed.
Lemma lem2712607 : term211 = term140.
Proof. exact (TRANS (@lem2712600) (@lem2712606)). Qed.
Lemma lem2712608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712609 : term647 = term639.
Proof. exact (MK_COMB (@lem2712608) (@lem2712607)). Qed.
Lemma lem2712610 : term648 = term641.
Proof. exact (MK_COMB (@lem2712609) (@lem2712597)). Qed.
Lemma lem2712612 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2712613 : term641 = term32.
Proof. exact (@lem2712612 term67). Qed.
Lemma lem2712614 : term648 = term32.
Proof. exact (TRANS (@lem2712610) (@lem2712613)). Qed.
Lemma lem2712615 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712616 : term650 = term267.
Proof. exact (MK_COMB (@lem2712615) (@lem2712614)). Qed.
Lemma lem2712617 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2712618 : term651 = term269.
Proof. exact (MK_COMB (@lem2712616) (@lem2712617)). Qed.
Lemma lem2712620 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712621 : term269 = term32.
Proof. exact (@lem2712620 term67). Qed.
Lemma lem2712622 : term651 = term32.
Proof. exact (TRANS (@lem2712618) (@lem2712621)). Qed.
Lemma lem2712624 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712625 : term149 = term150.
Proof. exact (@lem2712624 term67 term67). Qed.
Lemma lem2712626 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712627 : term152 = term67.
Proof. exact (EQ_MP (@lem2712626) (@lem940073)). Qed.
Lemma lem2712628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712629 : term150 = term66.
Proof. exact (MK_COMB (@lem2712628) (@lem2712627)). Qed.
Lemma lem2712630 : term149 = term66.
Proof. exact (TRANS (@lem2712625) (@lem2712629)). Qed.
Lemma lem2712631 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2712632 : term271 = term269.
Proof. exact (MK_COMB (@lem2712631) (@lem2712630)). Qed.
Lemma lem2712634 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712635 : term269 = term32.
Proof. exact (@lem2712634 term67). Qed.
Lemma lem2712636 : term271 = term32.
Proof. exact (TRANS (@lem2712632) (@lem2712635)). Qed.
Lemma lem2712637 : term32 = term271.
Proof. exact (SYM (@lem2712636)). Qed.
Lemma lem2712638 : term651 = term271.
Proof. exact (TRANS (@lem2712622) (@lem2712637)). Qed.
Lemma lem2712639 : term642 = term137.
Proof. exact (@lem2712589 (@lem2712638)). Qed.
Lemma lem2712640 : term641 = term137.
Proof. exact (TRANS (@lem2712555) (@lem2712639)). Qed.
Lemma lem2712642 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2712643 : term137 = term32.
Proof. exact (@lem2712642 term32). Qed.
Lemma lem2712644 : term641 = term32.
Proof. exact (TRANS (@lem2712640) (@lem2712643)). Qed.
Lemma lem2712645 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712646 : term652 = term267.
Proof. exact (MK_COMB (@lem2712645) (@lem2712644)). Qed.
Lemma lem2712647 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2712648 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2712646) (@lem2712647 n)). Qed.
Lemma lem2712649 (n : int) : (term725 n) = (term653 n).
Proof. exact (TRANS (@lem2712546 n) (@lem2712648 n)). Qed.
Lemma lem2712650 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2712651 (n : int) : (term725 n) = term32.
Proof. exact (TRANS (@lem2712649 n) (@lem2712650 n)). Qed.
Lemma lem2712652 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712653 (n : int) : (term861 n) = term102.
Proof. exact (MK_COMB (@lem2712652) (@lem2712651 n)). Qed.
Lemma lem2712654 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2712655 (n : int) : (term860 n) = term655.
Proof. exact (MK_COMB (@lem2712653 n) (@lem2712654)). Qed.
Lemma lem2712656 (n : int) : (term859 n) = term655.
Proof. exact (TRANS (@lem2712545 n) (@lem2712655 n)). Qed.
Lemma lem2712657 : term655 = term140.
Proof. exact (@lem1982721 term140). Qed.
Lemma lem2712658 (n : int) : (term859 n) = term140.
Proof. exact (TRANS (@lem2712656 n) (@lem2712657)). Qed.
Lemma lem2712659 (n : int) : (term192 n) = (term192 n).
Proof. exact (eq_refl (term192 n)). Qed.
Lemma lem2712660 (n : int) : (term858 n) = (term862 n).
Proof. exact (MK_COMB (@lem2712659 n) (@lem2712658 n)). Qed.
Lemma lem2712661 (n : int) : (term857 n) = (term862 n).
Proof. exact (TRANS (@lem2712544 n) (@lem2712660 n)). Qed.
Lemma lem2712662 (n : int) : (term194 n) = (term194 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem2712663 (n : int) : (term856 n) = (term863 n).
Proof. exact (MK_COMB (@lem2712662 n) (@lem2712661 n)). Qed.
Lemma lem2712664 (n : int) : (term855 n) = (term863 n).
Proof. exact (TRANS (@lem2712543 n) (@lem2712663 n)). Qed.
Lemma lem2712665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2712666 (n : int) : (term864 n) = (term865 n).
Proof. exact (MK_COMB (@lem2712665) (@lem2712664 n)). Qed.
Lemma lem2712667 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712668 (n : int) : (term854 n) = (term866 n).
Proof. exact (MK_COMB (@lem2712666 n) (@lem2712667)). Qed.
Lemma lem2712669 (n : int) (h1 : term508 n) : term866 n.
Proof. exact (EQ_MP (@lem2712668 n) (@lem2712542 n h1)). Qed.
Lemma lem2712671 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2712672 : term661 = term662.
Proof. exact (@lem2712671 term32 term28). Qed.
Lemma lem2712674 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712675 : term28 = term173.
Proof. exact (@lem2712674 term29). Qed.
Lemma lem2712677 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712678 : term32 = term137.
Proof. exact (@lem2712677 (NUMERAL 0)). Qed.
Lemma lem2712679 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712680 : term582 = term583.
Proof. exact (MK_COMB (@lem2712679) (@lem2712678)). Qed.
Lemma lem2712681 : term662 = term663.
Proof. exact (MK_COMB (@lem2712680) (@lem2712675)). Qed.
Lemma lem2712682 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2712684 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712685 : term257 = term258.
Proof. exact (@lem2712684 (NUMERAL 0) term67). Qed.
Lemma lem2712686 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712687 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712688 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712687 h1) (fun h1 : term258 = True => @lem2712686)). Qed.
Lemma lem2712689 : term258 = True.
Proof. exact (EQ_MP (@lem2712688) (@lem2712686)). Qed.
Lemma lem2712690 : term257 = True.
Proof. exact (TRANS (@lem2712685) (@lem2712689)). Qed.
Lemma lem2712691 : True = term257.
Proof. exact (SYM (@lem2712690)). Qed.
Lemma lem2712692 : term257.
Proof. exact (EQ_MP (@lem2712691) (@lem0)). Qed.
Lemma lem2712693 : term665.
Proof. exact (@lem2712682 (@lem2712692)). Qed.
Lemma lem2712695 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712696 : term257 = term258.
Proof. exact (@lem2712695 (NUMERAL 0) term67). Qed.
Lemma lem2712697 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712698 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712699 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712698 h1) (fun h1 : term258 = True => @lem2712697)). Qed.
Lemma lem2712700 : term258 = True.
Proof. exact (EQ_MP (@lem2712699) (@lem2712697)). Qed.
Lemma lem2712701 : term257 = True.
Proof. exact (TRANS (@lem2712696) (@lem2712700)). Qed.
Lemma lem2712702 : True = term257.
Proof. exact (SYM (@lem2712701)). Qed.
Lemma lem2712703 : term257.
Proof. exact (EQ_MP (@lem2712702) (@lem0)). Qed.
Lemma lem2712704 : term663 = term666.
Proof. exact (@lem2712693 (@lem2712703)). Qed.
Lemma lem2712706 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712707 : term289 = term290.
Proof. exact (@lem2712706 term29 term67). Qed.
Lemma lem2712708 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2712709 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2712710 : term292 = term29.
Proof. exact (EQ_MP (@lem2712709) (@lem2712708)). Qed.
Lemma lem2712711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712712 : term290 = term28.
Proof. exact (MK_COMB (@lem2712711) (@lem2712710)). Qed.
Lemma lem2712713 : term289 = term28.
Proof. exact (TRANS (@lem2712707) (@lem2712712)). Qed.
Lemma lem2712715 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712716 : term269 = term32.
Proof. exact (@lem2712715 term67). Qed.
Lemma lem2712717 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2712718 : term588 = term582.
Proof. exact (MK_COMB (@lem2712717) (@lem2712716)). Qed.
Lemma lem2712719 : term666 = term662.
Proof. exact (MK_COMB (@lem2712718) (@lem2712713)). Qed.
Lemma lem2712721 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712722 : term662 = term667.
Proof. exact (@lem2712721 (NUMERAL 0) term29). Qed.
Lemma lem2712723 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2712724 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2712725 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2712724 h1) (fun h1 : term667 = True => @lem2712723)). Qed.
Lemma lem2712726 : term667 = True.
Proof. exact (EQ_MP (@lem2712725) (@lem2712723)). Qed.
Lemma lem2712727 : term662 = True.
Proof. exact (TRANS (@lem2712722) (@lem2712726)). Qed.
Lemma lem2712728 : term666 = True.
Proof. exact (TRANS (@lem2712719) (@lem2712727)). Qed.
Lemma lem2712729 : term663 = True.
Proof. exact (TRANS (@lem2712704) (@lem2712728)). Qed.
Lemma lem2712730 : term662 = True.
Proof. exact (TRANS (@lem2712681) (@lem2712729)). Qed.
Lemma lem2712731 : term661 = True.
Proof. exact (TRANS (@lem2712672) (@lem2712730)). Qed.
Lemma lem2712732 : True = term661.
Proof. exact (SYM (@lem2712731)). Qed.
Lemma lem2712733 : term661.
Proof. exact (EQ_MP (@lem2712732) (@lem0)). Qed.
Lemma lem2712734 (n : int) (h1 : term508 n) : term867 n.
Proof. exact (conj (@lem2712733) (@lem2712669 n h1)). Qed.
Lemma lem2712736 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2712737 (n : int) : term868 n.
Proof. exact (@lem2712736 term28 (term863 n)). Qed.
Lemma lem2712738 (n : int) (h1 : term508 n) : term869 n.
Proof. exact (@lem2712737 n (@lem2712734 n h1)). Qed.
Lemma lem2712739 (n : int) : (term870 n) = (term871 n).
Proof. exact (@lem1982781 (real_of_int n) term28 (term862 n)). Qed.
Lemma lem2712740 (n : int) : (term872 n) = (term873 n).
Proof. exact (@lem1982781 (term190 n) term28 term140). Qed.
Lemma lem2712742 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712743 : term140 = term141.
Proof. exact (@lem2712742 term67). Qed.
Lemma lem2712745 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712746 : term28 = term173.
Proof. exact (@lem2712745 term29). Qed.
Lemma lem2712747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712748 : term287 = term675.
Proof. exact (MK_COMB (@lem2712747) (@lem2712746)). Qed.
Lemma lem2712749 : term676 = term677.
Proof. exact (MK_COMB (@lem2712748) (@lem2712743)). Qed.
Lemma lem2712750 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2712752 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712753 : term149 = term150.
Proof. exact (@lem2712752 term67 term67). Qed.
Lemma lem2712754 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712755 : term152 = term67.
Proof. exact (EQ_MP (@lem2712754) (@lem940073)). Qed.
Lemma lem2712756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712757 : term150 = term66.
Proof. exact (MK_COMB (@lem2712756) (@lem2712755)). Qed.
Lemma lem2712758 : term149 = term66.
Proof. exact (TRANS (@lem2712753) (@lem2712757)). Qed.
Lemma lem2712760 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2712761 : term676 = term440.
Proof. exact (@lem2712760 term29 term67). Qed.
Lemma lem2712762 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2712763 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2712764 : term292 = term29.
Proof. exact (EQ_MP (@lem2712763) (@lem2712762)). Qed.
Lemma lem2712765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712766 : term290 = term28.
Proof. exact (MK_COMB (@lem2712765) (@lem2712764)). Qed.
Lemma lem2712767 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2712768 : term440 = term184.
Proof. exact (MK_COMB (@lem2712767) (@lem2712766)). Qed.
Lemma lem2712769 : term676 = term184.
Proof. exact (TRANS (@lem2712761) (@lem2712768)). Qed.
Lemma lem2712770 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2712771 : term680 = term186.
Proof. exact (MK_COMB (@lem2712770) (@lem2712769)). Qed.
Lemma lem2712772 : term678 = term187.
Proof. exact (MK_COMB (@lem2712771) (@lem2712758)). Qed.
Lemma lem2712773 : term677 = term187.
Proof. exact (TRANS (@lem2712750) (@lem2712772)). Qed.
Lemma lem2712774 : term676 = term187.
Proof. exact (TRANS (@lem2712749) (@lem2712773)). Qed.
Lemma lem2712776 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2712777 : term187 = term184.
Proof. exact (@lem2712776 term184). Qed.
Lemma lem2712778 : term676 = term184.
Proof. exact (TRANS (@lem2712774) (@lem2712777)). Qed.
Lemma lem2712779 (n : int) : (term736 n) = (term737 n).
Proof. exact (@lem1982749 term28 term184 (term162 n)). Qed.
Lemma lem2712781 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712782 : term184 = term187.
Proof. exact (@lem2712781 term29). Qed.
Lemma lem2712784 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712785 : term28 = term173.
Proof. exact (@lem2712784 term29). Qed.
Lemma lem2712786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712787 : term287 = term675.
Proof. exact (MK_COMB (@lem2712786) (@lem2712785)). Qed.
Lemma lem2712788 : term738 = term739.
Proof. exact (MK_COMB (@lem2712787) (@lem2712782)). Qed.
Lemma lem2712789 : term739 = term740.
Proof. exact (@lem1981613 term28 term184 term66 term66). Qed.
Lemma lem2712791 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712792 : term149 = term150.
Proof. exact (@lem2712791 term67 term67). Qed.
Lemma lem2712793 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712794 : term152 = term67.
Proof. exact (EQ_MP (@lem2712793) (@lem940073)). Qed.
Lemma lem2712795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712796 : term150 = term66.
Proof. exact (MK_COMB (@lem2712795) (@lem2712794)). Qed.
Lemma lem2712797 : term149 = term66.
Proof. exact (TRANS (@lem2712792) (@lem2712796)). Qed.
Lemma lem2712799 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2712800 : term738 = term741.
Proof. exact (@lem2712799 term29 term29). Qed.
Lemma lem2712801 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712802 : term687 = term688.
Proof. exact (EQ_MP (@lem2712801) (@lem940073)). Qed.
Lemma lem2712803 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2712804 : term689 = term690.
Proof. exact (EQ_MP (@lem2712803) (@lem2712802)). Qed.
Lemma lem2712805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712806 : term686 = term691.
Proof. exact (MK_COMB (@lem2712805) (@lem2712804)). Qed.
Lemma lem2712807 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2712808 : term741 = term742.
Proof. exact (MK_COMB (@lem2712807) (@lem2712806)). Qed.
Lemma lem2712809 : term738 = term742.
Proof. exact (TRANS (@lem2712800) (@lem2712808)). Qed.
Lemma lem2712810 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2712811 : term743 = term744.
Proof. exact (MK_COMB (@lem2712810) (@lem2712809)). Qed.
Lemma lem2712812 : term740 = term745.
Proof. exact (MK_COMB (@lem2712811) (@lem2712797)). Qed.
Lemma lem2712813 : term739 = term745.
Proof. exact (TRANS (@lem2712789) (@lem2712812)). Qed.
Lemma lem2712814 : term738 = term745.
Proof. exact (TRANS (@lem2712788) (@lem2712813)). Qed.
Lemma lem2712816 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2712817 : term745 = term742.
Proof. exact (@lem2712816 term742). Qed.
Lemma lem2712818 : term738 = term742.
Proof. exact (TRANS (@lem2712814) (@lem2712817)). Qed.
Lemma lem2712819 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712820 : term746 = term747.
Proof. exact (MK_COMB (@lem2712819) (@lem2712818)). Qed.
Lemma lem2712821 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2712822 (n : int) : (term737 n) = (term748 n).
Proof. exact (MK_COMB (@lem2712820) (@lem2712821 n)). Qed.
Lemma lem2712823 (n : int) : (term736 n) = (term748 n).
Proof. exact (TRANS (@lem2712779 n) (@lem2712822 n)). Qed.
Lemma lem2712824 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712825 (n : int) : (term874 n) = (term875 n).
Proof. exact (MK_COMB (@lem2712824) (@lem2712823 n)). Qed.
Lemma lem2712826 (n : int) : (term873 n) = (term876 n).
Proof. exact (MK_COMB (@lem2712825 n) (@lem2712778)). Qed.
Lemma lem2712827 (n : int) : (term872 n) = (term876 n).
Proof. exact (TRANS (@lem2712740 n) (@lem2712826 n)). Qed.
Lemma lem2712830 (n : int) : (term749 n) = (term749 n).
Proof. exact (eq_refl (term749 n)). Qed.
Lemma lem2712831 (n : int) : (term871 n) = (term877 n).
Proof. exact (MK_COMB (@lem2712830 n) (@lem2712827 n)). Qed.
Lemma lem2712832 (n : int) : (term870 n) = (term877 n).
Proof. exact (TRANS (@lem2712739 n) (@lem2712831 n)). Qed.
Lemma lem2712833 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2712834 (n : int) : (term878 n) = (term879 n).
Proof. exact (MK_COMB (@lem2712833) (@lem2712832 n)). Qed.
Lemma lem2712835 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2712836 (n : int) : (term869 n) = (term880 n).
Proof. exact (MK_COMB (@lem2712834 n) (@lem2712835)). Qed.
Lemma lem2712837 (n : int) (h1 : term508 n) : term880 n.
Proof. exact (EQ_MP (@lem2712836 n) (@lem2712738 n h1)). Qed.
Lemma lem2712838 (n : int) (h1 : term508 n) : term881 n.
Proof. exact (conj (@lem2712837 n h1) (@lem2712450 n h1)). Qed.
Lemma lem2712840 (x : real) (y : real) : term755 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2712841 (n : int) : term882 n.
Proof. exact (@lem2712840 (term877 n) (term843 n)). Qed.
Lemma lem2712842 (n : int) (h1 : term508 n) : term883 n.
Proof. exact (@lem2712841 n (@lem2712838 n h1)). Qed.
Lemma lem2712843 (n : int) : (term884 n) = (term885 n).
Proof. exact (@lem1982753 (term760 n) (term704 n) (term876 n) (term697 n)). Qed.
Lemma lem2712844 (n : int) : (term761 n) = (term762 n).
Proof. exact (@lem1982711 term28 term184 (real_of_int n)). Qed.
Lemma lem2712846 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712847 : term184 = term187.
Proof. exact (@lem2712846 term29). Qed.
Lemma lem2712849 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712850 : term28 = term173.
Proof. exact (@lem2712849 term29). Qed.
Lemma lem2712851 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712852 : term157 = term373.
Proof. exact (MK_COMB (@lem2712851) (@lem2712850)). Qed.
Lemma lem2712853 : term763 = term764.
Proof. exact (MK_COMB (@lem2712852) (@lem2712847)). Qed.
Lemma lem2712854 : term765.
Proof. exact (@lem1981473 term28 term66 term184 term66 term32 term66). Qed.
Lemma lem2712856 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712857 : term257 = term258.
Proof. exact (@lem2712856 (NUMERAL 0) term67). Qed.
Lemma lem2712858 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712859 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712860 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712859 h1) (fun h1 : term258 = True => @lem2712858)). Qed.
Lemma lem2712861 : term258 = True.
Proof. exact (EQ_MP (@lem2712860) (@lem2712858)). Qed.
Lemma lem2712862 : term257 = True.
Proof. exact (TRANS (@lem2712857) (@lem2712861)). Qed.
Lemma lem2712863 : True = term257.
Proof. exact (SYM (@lem2712862)). Qed.
Lemma lem2712864 : term257.
Proof. exact (EQ_MP (@lem2712863) (@lem0)). Qed.
Lemma lem2712865 : term766.
Proof. exact (@lem2712854 (@lem2712864)). Qed.
Lemma lem2712867 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712868 : term257 = term258.
Proof. exact (@lem2712867 (NUMERAL 0) term67). Qed.
Lemma lem2712869 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712870 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712871 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712870 h1) (fun h1 : term258 = True => @lem2712869)). Qed.
Lemma lem2712872 : term258 = True.
Proof. exact (EQ_MP (@lem2712871) (@lem2712869)). Qed.
Lemma lem2712873 : term257 = True.
Proof. exact (TRANS (@lem2712868) (@lem2712872)). Qed.
Lemma lem2712874 : True = term257.
Proof. exact (SYM (@lem2712873)). Qed.
Lemma lem2712875 : term257.
Proof. exact (EQ_MP (@lem2712874) (@lem0)). Qed.
Lemma lem2712876 : term767.
Proof. exact (@lem2712865 (@lem2712875)). Qed.
Lemma lem2712878 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712879 : term257 = term258.
Proof. exact (@lem2712878 (NUMERAL 0) term67). Qed.
Lemma lem2712880 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712881 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712882 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712881 h1) (fun h1 : term258 = True => @lem2712880)). Qed.
Lemma lem2712883 : term258 = True.
Proof. exact (EQ_MP (@lem2712882) (@lem2712880)). Qed.
Lemma lem2712884 : term257 = True.
Proof. exact (TRANS (@lem2712879) (@lem2712883)). Qed.
Lemma lem2712885 : True = term257.
Proof. exact (SYM (@lem2712884)). Qed.
Lemma lem2712886 : term257.
Proof. exact (EQ_MP (@lem2712885) (@lem0)). Qed.
Lemma lem2712887 : term768.
Proof. exact (@lem2712876 (@lem2712886)). Qed.
Lemma lem2712889 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2712890 : term439 = term440.
Proof. exact (@lem2712889 term29 term67). Qed.
Lemma lem2712891 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2712892 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2712893 : term292 = term29.
Proof. exact (EQ_MP (@lem2712892) (@lem2712891)). Qed.
Lemma lem2712894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712895 : term290 = term28.
Proof. exact (MK_COMB (@lem2712894) (@lem2712893)). Qed.
Lemma lem2712896 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2712897 : term440 = term184.
Proof. exact (MK_COMB (@lem2712896) (@lem2712895)). Qed.
Lemma lem2712898 : term439 = term184.
Proof. exact (TRANS (@lem2712890) (@lem2712897)). Qed.
Lemma lem2712900 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712901 : term289 = term290.
Proof. exact (@lem2712900 term29 term67). Qed.
Lemma lem2712902 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2712903 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2712904 : term292 = term29.
Proof. exact (EQ_MP (@lem2712903) (@lem2712902)). Qed.
Lemma lem2712905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712906 : term290 = term28.
Proof. exact (MK_COMB (@lem2712905) (@lem2712904)). Qed.
Lemma lem2712907 : term289 = term28.
Proof. exact (TRANS (@lem2712901) (@lem2712906)). Qed.
Lemma lem2712908 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712909 : term380 = term157.
Proof. exact (MK_COMB (@lem2712908) (@lem2712907)). Qed.
Lemma lem2712910 : term769 = term763.
Proof. exact (MK_COMB (@lem2712909) (@lem2712898)). Qed.
Lemma lem2712912 (m : nat) : (term265 m) = term32.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2712913 : term763 = term32.
Proof. exact (@lem2712912 term29). Qed.
Lemma lem2712914 : term769 = term32.
Proof. exact (TRANS (@lem2712910) (@lem2712913)). Qed.
Lemma lem2712915 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712916 : term770 = term267.
Proof. exact (MK_COMB (@lem2712915) (@lem2712914)). Qed.
Lemma lem2712917 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2712918 : term771 = term269.
Proof. exact (MK_COMB (@lem2712916) (@lem2712917)). Qed.
Lemma lem2712920 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712921 : term269 = term32.
Proof. exact (@lem2712920 term67). Qed.
Lemma lem2712922 : term771 = term32.
Proof. exact (TRANS (@lem2712918) (@lem2712921)). Qed.
Lemma lem2712924 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2712925 : term149 = term150.
Proof. exact (@lem2712924 term67 term67). Qed.
Lemma lem2712926 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2712927 : term152 = term67.
Proof. exact (EQ_MP (@lem2712926) (@lem940073)). Qed.
Lemma lem2712928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2712929 : term150 = term66.
Proof. exact (MK_COMB (@lem2712928) (@lem2712927)). Qed.
Lemma lem2712930 : term149 = term66.
Proof. exact (TRANS (@lem2712925) (@lem2712929)). Qed.
Lemma lem2712931 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2712932 : term271 = term269.
Proof. exact (MK_COMB (@lem2712931) (@lem2712930)). Qed.
Lemma lem2712934 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2712935 : term269 = term32.
Proof. exact (@lem2712934 term67). Qed.
Lemma lem2712936 : term271 = term32.
Proof. exact (TRANS (@lem2712932) (@lem2712935)). Qed.
Lemma lem2712937 : term32 = term271.
Proof. exact (SYM (@lem2712936)). Qed.
Lemma lem2712938 : term771 = term271.
Proof. exact (TRANS (@lem2712922) (@lem2712937)). Qed.
Lemma lem2712939 : term764 = term137.
Proof. exact (@lem2712887 (@lem2712938)). Qed.
Lemma lem2712940 : term763 = term137.
Proof. exact (TRANS (@lem2712853) (@lem2712939)). Qed.
Lemma lem2712942 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2712943 : term137 = term32.
Proof. exact (@lem2712942 term32). Qed.
Lemma lem2712944 : term763 = term32.
Proof. exact (TRANS (@lem2712940) (@lem2712943)). Qed.
Lemma lem2712945 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2712946 : term772 = term267.
Proof. exact (MK_COMB (@lem2712945) (@lem2712944)). Qed.
Lemma lem2712947 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2712948 (n : int) : (term762 n) = (term773 n).
Proof. exact (MK_COMB (@lem2712946) (@lem2712947 n)). Qed.
Lemma lem2712949 (n : int) : (term761 n) = (term773 n).
Proof. exact (TRANS (@lem2712844 n) (@lem2712948 n)). Qed.
Lemma lem2712950 (n : int) : (term773 n) = term32.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2712951 (n : int) : (term761 n) = term32.
Proof. exact (TRANS (@lem2712949 n) (@lem2712950 n)). Qed.
Lemma lem2712952 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712953 (n : int) : (term774 n) = term102.
Proof. exact (MK_COMB (@lem2712952) (@lem2712951 n)). Qed.
Lemma lem2712954 (n : int) : (term886 n) = (term776 n).
Proof. exact (@lem1982759 (term748 n) (term697 n) term184). Qed.
Lemma lem2712955 (n : int) : (term777 n) = (term778 n).
Proof. exact (@lem1982711 term742 term691 (term162 n)). Qed.
Lemma lem2712957 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2712958 : term691 = term694.
Proof. exact (@lem2712957 term690). Qed.
Lemma lem2712960 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2712961 : term742 = term745.
Proof. exact (@lem2712960 term690). Qed.
Lemma lem2712962 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2712963 : term779 = term780.
Proof. exact (MK_COMB (@lem2712962) (@lem2712961)). Qed.
Lemma lem2712964 : term781 = term782.
Proof. exact (MK_COMB (@lem2712963) (@lem2712958)). Qed.
Lemma lem2712965 : term783.
Proof. exact (@lem1981473 term742 term66 term691 term66 term32 term66). Qed.
Lemma lem2712967 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712968 : term257 = term258.
Proof. exact (@lem2712967 (NUMERAL 0) term67). Qed.
Lemma lem2712969 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712970 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712971 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712970 h1) (fun h1 : term258 = True => @lem2712969)). Qed.
Lemma lem2712972 : term258 = True.
Proof. exact (EQ_MP (@lem2712971) (@lem2712969)). Qed.
Lemma lem2712973 : term257 = True.
Proof. exact (TRANS (@lem2712968) (@lem2712972)). Qed.
Lemma lem2712974 : True = term257.
Proof. exact (SYM (@lem2712973)). Qed.
Lemma lem2712975 : term257.
Proof. exact (EQ_MP (@lem2712974) (@lem0)). Qed.
Lemma lem2712976 : term784.
Proof. exact (@lem2712965 (@lem2712975)). Qed.
Lemma lem2712978 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712979 : term257 = term258.
Proof. exact (@lem2712978 (NUMERAL 0) term67). Qed.
Lemma lem2712980 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712981 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712982 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712981 h1) (fun h1 : term258 = True => @lem2712980)). Qed.
Lemma lem2712983 : term258 = True.
Proof. exact (EQ_MP (@lem2712982) (@lem2712980)). Qed.
Lemma lem2712984 : term257 = True.
Proof. exact (TRANS (@lem2712979) (@lem2712983)). Qed.
Lemma lem2712985 : True = term257.
Proof. exact (SYM (@lem2712984)). Qed.
Lemma lem2712986 : term257.
Proof. exact (EQ_MP (@lem2712985) (@lem0)). Qed.
Lemma lem2712987 : term785.
Proof. exact (@lem2712976 (@lem2712986)). Qed.
Lemma lem2712989 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2712990 : term257 = term258.
Proof. exact (@lem2712989 (NUMERAL 0) term67). Qed.
Lemma lem2712991 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2712992 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2712993 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2712992 h1) (fun h1 : term258 = True => @lem2712991)). Qed.
Lemma lem2712994 : term258 = True.
Proof. exact (EQ_MP (@lem2712993) (@lem2712991)). Qed.
Lemma lem2712995 : term257 = True.
Proof. exact (TRANS (@lem2712990) (@lem2712994)). Qed.
Lemma lem2712996 : True = term257.
Proof. exact (SYM (@lem2712995)). Qed.
Lemma lem2712997 : term257.
Proof. exact (EQ_MP (@lem2712996) (@lem0)). Qed.
Lemma lem2712998 : term786.
Proof. exact (@lem2712987 (@lem2712997)). Qed.
Lemma lem2713000 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713001 : term787 = term788.
Proof. exact (@lem2713000 term690 term67). Qed.
Lemma lem2713002 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2713003 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2713004 : term790 = term690.
Proof. exact (EQ_MP (@lem2713003) (@lem2713002)). Qed.
Lemma lem2713005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713006 : term788 = term691.
Proof. exact (MK_COMB (@lem2713005) (@lem2713004)). Qed.
Lemma lem2713007 : term787 = term691.
Proof. exact (TRANS (@lem2713001) (@lem2713006)). Qed.
Lemma lem2713009 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2713010 : term791 = term792.
Proof. exact (@lem2713009 term690 term67). Qed.
Lemma lem2713011 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2713012 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2713013 : term790 = term690.
Proof. exact (EQ_MP (@lem2713012) (@lem2713011)). Qed.
Lemma lem2713014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713015 : term788 = term691.
Proof. exact (MK_COMB (@lem2713014) (@lem2713013)). Qed.
Lemma lem2713016 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713017 : term792 = term742.
Proof. exact (MK_COMB (@lem2713016) (@lem2713015)). Qed.
Lemma lem2713018 : term791 = term742.
Proof. exact (TRANS (@lem2713010) (@lem2713017)). Qed.
Lemma lem2713019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713020 : term793 = term779.
Proof. exact (MK_COMB (@lem2713019) (@lem2713018)). Qed.
Lemma lem2713021 : term794 = term781.
Proof. exact (MK_COMB (@lem2713020) (@lem2713007)). Qed.
Lemma lem2713023 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2713024 : term781 = term32.
Proof. exact (@lem2713023 term690). Qed.
Lemma lem2713025 : term794 = term32.
Proof. exact (TRANS (@lem2713021) (@lem2713024)). Qed.
Lemma lem2713026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713027 : term795 = term267.
Proof. exact (MK_COMB (@lem2713026) (@lem2713025)). Qed.
Lemma lem2713028 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2713029 : term796 = term269.
Proof. exact (MK_COMB (@lem2713027) (@lem2713028)). Qed.
Lemma lem2713031 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713032 : term269 = term32.
Proof. exact (@lem2713031 term67). Qed.
Lemma lem2713033 : term796 = term32.
Proof. exact (TRANS (@lem2713029) (@lem2713032)). Qed.
Lemma lem2713035 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713036 : term149 = term150.
Proof. exact (@lem2713035 term67 term67). Qed.
Lemma lem2713037 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713038 : term152 = term67.
Proof. exact (EQ_MP (@lem2713037) (@lem940073)). Qed.
Lemma lem2713039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713040 : term150 = term66.
Proof. exact (MK_COMB (@lem2713039) (@lem2713038)). Qed.
Lemma lem2713041 : term149 = term66.
Proof. exact (TRANS (@lem2713036) (@lem2713040)). Qed.
Lemma lem2713042 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2713043 : term271 = term269.
Proof. exact (MK_COMB (@lem2713042) (@lem2713041)). Qed.
Lemma lem2713045 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713046 : term269 = term32.
Proof. exact (@lem2713045 term67). Qed.
Lemma lem2713047 : term271 = term32.
Proof. exact (TRANS (@lem2713043) (@lem2713046)). Qed.
Lemma lem2713048 : term32 = term271.
Proof. exact (SYM (@lem2713047)). Qed.
Lemma lem2713049 : term796 = term271.
Proof. exact (TRANS (@lem2713033) (@lem2713048)). Qed.
Lemma lem2713050 : term782 = term137.
Proof. exact (@lem2712998 (@lem2713049)). Qed.
Lemma lem2713051 : term781 = term137.
Proof. exact (TRANS (@lem2712964) (@lem2713050)). Qed.
Lemma lem2713053 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2713054 : term137 = term32.
Proof. exact (@lem2713053 term32). Qed.
Lemma lem2713055 : term781 = term32.
Proof. exact (TRANS (@lem2713051) (@lem2713054)). Qed.
Lemma lem2713056 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713057 : term797 = term267.
Proof. exact (MK_COMB (@lem2713056) (@lem2713055)). Qed.
Lemma lem2713058 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2713059 (n : int) : (term778 n) = (term798 n).
Proof. exact (MK_COMB (@lem2713057) (@lem2713058 n)). Qed.
Lemma lem2713060 (n : int) : (term777 n) = (term798 n).
Proof. exact (TRANS (@lem2712955 n) (@lem2713059 n)). Qed.
Lemma lem2713061 (n : int) : (term798 n) = term32.
Proof. exact (@lem1982719 (term162 n)). Qed.
Lemma lem2713062 (n : int) : (term777 n) = term32.
Proof. exact (TRANS (@lem2713060 n) (@lem2713061 n)). Qed.
Lemma lem2713063 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713064 (n : int) : (term799 n) = term102.
Proof. exact (MK_COMB (@lem2713063) (@lem2713062 n)). Qed.
Lemma lem2713065 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2713066 (n : int) : (term776 n) = term422.
Proof. exact (MK_COMB (@lem2713064 n) (@lem2713065)). Qed.
Lemma lem2713067 (n : int) : (term886 n) = term422.
Proof. exact (TRANS (@lem2712954 n) (@lem2713066 n)). Qed.
Lemma lem2713068 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2713069 (n : int) : (term886 n) = term184.
Proof. exact (TRANS (@lem2713067 n) (@lem2713068)). Qed.
Lemma lem2713070 (n : int) : (term885 n) = term422.
Proof. exact (MK_COMB (@lem2712953 n) (@lem2713069 n)). Qed.
Lemma lem2713071 (n : int) : (term884 n) = term422.
Proof. exact (TRANS (@lem2712843 n) (@lem2713070 n)). Qed.
Lemma lem2713072 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2713073 (n : int) : (term884 n) = term184.
Proof. exact (TRANS (@lem2713071 n) (@lem2713072)). Qed.
Lemma lem2713074 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2713075 (n : int) : (term887 n) = term801.
Proof. exact (MK_COMB (@lem2713074) (@lem2713073 n)). Qed.
Lemma lem2713076 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713077 (n : int) : (term883 n) = term802.
Proof. exact (MK_COMB (@lem2713075 n) (@lem2713076)). Qed.
Lemma lem2713078 (n : int) (h1 : term508 n) : term802.
Proof. exact (EQ_MP (@lem2713077 n) (@lem2712842 n h1)). Qed.
Lemma lem2713080 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2713081 : term802 = term803.
Proof. exact (@lem2713080 term32 term184). Qed.
Lemma lem2713083 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713084 : term184 = term187.
Proof. exact (@lem2713083 term29). Qed.
Lemma lem2713086 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713087 : term32 = term137.
Proof. exact (@lem2713086 (NUMERAL 0)). Qed.
Lemma lem2713088 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2713089 : term55 = term804.
Proof. exact (MK_COMB (@lem2713088) (@lem2713087)). Qed.
Lemma lem2713090 : term803 = term805.
Proof. exact (MK_COMB (@lem2713089) (@lem2713084)). Qed.
Lemma lem2713091 : term806.
Proof. exact (@lem1980026 term32 term66 term184 term66). Qed.
Lemma lem2713093 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713094 : term257 = term258.
Proof. exact (@lem2713093 (NUMERAL 0) term67). Qed.
Lemma lem2713095 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713096 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713097 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713096 h1) (fun h1 : term258 = True => @lem2713095)). Qed.
Lemma lem2713098 : term258 = True.
Proof. exact (EQ_MP (@lem2713097) (@lem2713095)). Qed.
Lemma lem2713099 : term257 = True.
Proof. exact (TRANS (@lem2713094) (@lem2713098)). Qed.
Lemma lem2713100 : True = term257.
Proof. exact (SYM (@lem2713099)). Qed.
Lemma lem2713101 : term257.
Proof. exact (EQ_MP (@lem2713100) (@lem0)). Qed.
Lemma lem2713102 : term807.
Proof. exact (@lem2713091 (@lem2713101)). Qed.
Lemma lem2713104 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713105 : term257 = term258.
Proof. exact (@lem2713104 (NUMERAL 0) term67). Qed.
Lemma lem2713106 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713107 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713108 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713107 h1) (fun h1 : term258 = True => @lem2713106)). Qed.
Lemma lem2713109 : term258 = True.
Proof. exact (EQ_MP (@lem2713108) (@lem2713106)). Qed.
Lemma lem2713110 : term257 = True.
Proof. exact (TRANS (@lem2713105) (@lem2713109)). Qed.
Lemma lem2713111 : True = term257.
Proof. exact (SYM (@lem2713110)). Qed.
Lemma lem2713112 : term257.
Proof. exact (EQ_MP (@lem2713111) (@lem0)). Qed.
Lemma lem2713113 : term805 = term808.
Proof. exact (@lem2713102 (@lem2713112)). Qed.
Lemma lem2713115 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2713116 : term439 = term440.
Proof. exact (@lem2713115 term29 term67). Qed.
Lemma lem2713117 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2713118 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2713119 : term292 = term29.
Proof. exact (EQ_MP (@lem2713118) (@lem2713117)). Qed.
Lemma lem2713120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713121 : term290 = term28.
Proof. exact (MK_COMB (@lem2713120) (@lem2713119)). Qed.
Lemma lem2713122 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713123 : term440 = term184.
Proof. exact (MK_COMB (@lem2713122) (@lem2713121)). Qed.
Lemma lem2713124 : term439 = term184.
Proof. exact (TRANS (@lem2713116) (@lem2713123)). Qed.
Lemma lem2713126 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713127 : term269 = term32.
Proof. exact (@lem2713126 term67). Qed.
Lemma lem2713128 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2713129 : term809 = term55.
Proof. exact (MK_COMB (@lem2713128) (@lem2713127)). Qed.
Lemma lem2713130 : term808 = term803.
Proof. exact (MK_COMB (@lem2713129) (@lem2713124)). Qed.
Lemma lem2713132 (m : nat) (n : nat) : (term810 m n) = (term811 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2713133 : term803 = term812.
Proof. exact (@lem2713132 (NUMERAL 0) term29). Qed.
Lemma lem2713134 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2713135 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2713136 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2713135 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2713134)). Qed.
Lemma lem2713137 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2713136) (@lem2713134)). Qed.
Lemma lem2713138 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2713139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2713140 : term813 = (and True).
Proof. exact (MK_COMB (@lem2713139) (@lem2713138)). Qed.
Lemma lem2713141 : term812 = (True /\ False).
Proof. exact (MK_COMB (@lem2713140) (@lem2713137)). Qed.
Lemma lem2713143 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2713144 : term812 = False.
Proof. exact (TRANS (@lem2713141) (@lem2713143)). Qed.
Lemma lem2713145 : term803 = False.
Proof. exact (TRANS (@lem2713133) (@lem2713144)). Qed.
Lemma lem2713146 : term808 = False.
Proof. exact (TRANS (@lem2713130) (@lem2713145)). Qed.
Lemma lem2713147 : term805 = False.
Proof. exact (TRANS (@lem2713113) (@lem2713146)). Qed.
Lemma lem2713148 : term803 = False.
Proof. exact (TRANS (@lem2713090) (@lem2713147)). Qed.
Lemma lem2713149 : term802 = False.
Proof. exact (TRANS (@lem2713081) (@lem2713148)). Qed.
Lemma lem2713150 (n : int) (h1 : term508 n) : False.
Proof. exact (EQ_MP (@lem2713149) (@lem2713078 n h1)). Qed.
Lemma lem2713151 (n : int) (h1 : term510 n) : term510 n.
Proof. exact (h1). Qed.
Lemma lem2713153 (n : int) (h1 : term510 n) : term425.
Proof. exact (proj1 (@lem2713151 n h1)). Qed.
Lemma lem2713163 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2713164 : term425 = term814.
Proof. exact (@lem2713163 term32 term184). Qed.
Lemma lem2713166 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713167 : term184 = term187.
Proof. exact (@lem2713166 term29). Qed.
Lemma lem2713169 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713170 : term32 = term137.
Proof. exact (@lem2713169 (NUMERAL 0)). Qed.
Lemma lem2713171 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713172 : term582 = term583.
Proof. exact (MK_COMB (@lem2713171) (@lem2713170)). Qed.
Lemma lem2713173 : term814 = term815.
Proof. exact (MK_COMB (@lem2713172) (@lem2713167)). Qed.
Lemma lem2713174 : term816.
Proof. exact (@lem1980255 term32 term66 term184 term66). Qed.
Lemma lem2713176 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713177 : term257 = term258.
Proof. exact (@lem2713176 (NUMERAL 0) term67). Qed.
Lemma lem2713178 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713179 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713180 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713179 h1) (fun h1 : term258 = True => @lem2713178)). Qed.
Lemma lem2713181 : term258 = True.
Proof. exact (EQ_MP (@lem2713180) (@lem2713178)). Qed.
Lemma lem2713182 : term257 = True.
Proof. exact (TRANS (@lem2713177) (@lem2713181)). Qed.
Lemma lem2713183 : True = term257.
Proof. exact (SYM (@lem2713182)). Qed.
Lemma lem2713184 : term257.
Proof. exact (EQ_MP (@lem2713183) (@lem0)). Qed.
Lemma lem2713185 : term817.
Proof. exact (@lem2713174 (@lem2713184)). Qed.
Lemma lem2713187 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713188 : term257 = term258.
Proof. exact (@lem2713187 (NUMERAL 0) term67). Qed.
Lemma lem2713189 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713190 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713191 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713190 h1) (fun h1 : term258 = True => @lem2713189)). Qed.
Lemma lem2713192 : term258 = True.
Proof. exact (EQ_MP (@lem2713191) (@lem2713189)). Qed.
Lemma lem2713193 : term257 = True.
Proof. exact (TRANS (@lem2713188) (@lem2713192)). Qed.
Lemma lem2713194 : True = term257.
Proof. exact (SYM (@lem2713193)). Qed.
Lemma lem2713195 : term257.
Proof. exact (EQ_MP (@lem2713194) (@lem0)). Qed.
Lemma lem2713196 : term815 = term818.
Proof. exact (@lem2713185 (@lem2713195)). Qed.
Lemma lem2713198 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2713199 : term439 = term440.
Proof. exact (@lem2713198 term29 term67). Qed.
Lemma lem2713200 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2713201 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2713202 : term292 = term29.
Proof. exact (EQ_MP (@lem2713201) (@lem2713200)). Qed.
Lemma lem2713203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713204 : term290 = term28.
Proof. exact (MK_COMB (@lem2713203) (@lem2713202)). Qed.
Lemma lem2713205 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713206 : term440 = term184.
Proof. exact (MK_COMB (@lem2713205) (@lem2713204)). Qed.
Lemma lem2713207 : term439 = term184.
Proof. exact (TRANS (@lem2713199) (@lem2713206)). Qed.
Lemma lem2713209 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713210 : term269 = term32.
Proof. exact (@lem2713209 term67). Qed.
Lemma lem2713211 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713212 : term588 = term582.
Proof. exact (MK_COMB (@lem2713211) (@lem2713210)). Qed.
Lemma lem2713213 : term818 = term814.
Proof. exact (MK_COMB (@lem2713212) (@lem2713207)). Qed.
Lemma lem2713215 (m : nat) (n : nat) : (term819 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2713216 : term814 = False.
Proof. exact (@lem2713215 (NUMERAL 0) term29). Qed.
Lemma lem2713217 : term818 = False.
Proof. exact (TRANS (@lem2713213) (@lem2713216)). Qed.
Lemma lem2713218 : term815 = False.
Proof. exact (TRANS (@lem2713196) (@lem2713217)). Qed.
Lemma lem2713219 : term814 = False.
Proof. exact (TRANS (@lem2713173) (@lem2713218)). Qed.
Lemma lem2713220 : term425 = False.
Proof. exact (TRANS (@lem2713164) (@lem2713219)). Qed.
Lemma lem2713221 (n : int) (h1 : term510 n) : False.
Proof. exact (EQ_MP (@lem2713220) (@lem2713153 n h1)). Qed.
Lemma lem2713222 (n : int) (h1 : term512 n) : False.
Proof. exact (or_elim (@lem2711965 n h1) (fun h0 : term508 n => @lem2713150 n h0) (fun h0 : term510 n => @lem2713221 n h0)). Qed.
Lemma lem2713223 (n : int) (h1 : term514 n) : False.
Proof. exact (or_elim (@lem2711900 n h1) (fun h0 : term820 n => @lem2711964 n h0) (fun h0 : term512 n => @lem2713222 n h0)). Qed.
Lemma lem2713224 (n : int) (h1 : term516 n) : False.
Proof. exact (or_elim (@lem2710575 n h1) (fun h0 : term483 n => @lem2711899 n h0) (fun h0 : term514 n => @lem2713223 n h0)). Qed.
Lemma lem2713225 (n : int) (h1 : term572 n) : term572 n.
Proof. exact (h1). Qed.
Lemma lem2713226 (n : int) (h1 : term546 n) : term546 n.
Proof. exact (h1). Qed.
Lemma lem2713227 (n : int) (h1 : term888 n) : term888 n.
Proof. exact (h1). Qed.
Lemma lem2713229 (n : int) (h1 : term888 n) : term28 = term32.
Proof. exact (proj1 (@lem2713227 n h1)). Qed.
Lemma lem2713233 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713234 : term32 = term137.
Proof. exact (@lem2713233 (NUMERAL 0)). Qed.
Lemma lem2713236 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713237 : term28 = term173.
Proof. exact (@lem2713236 term29). Qed.
Lemma lem2713238 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2713239 : term31 = term576.
Proof. exact (MK_COMB (@lem2713238) (@lem2713237)). Qed.
Lemma lem2713240 : (term28 = term32) = (term173 = term137).
Proof. exact (MK_COMB (@lem2713239) (@lem2713234)). Qed.
Lemma lem2713241 : term577.
Proof. exact (@lem1980277 term28 term66 term32 term66). Qed.
Lemma lem2713243 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713244 : term257 = term258.
Proof. exact (@lem2713243 (NUMERAL 0) term67). Qed.
Lemma lem2713245 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713246 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713247 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713246 h1) (fun h1 : term258 = True => @lem2713245)). Qed.
Lemma lem2713248 : term258 = True.
Proof. exact (EQ_MP (@lem2713247) (@lem2713245)). Qed.
Lemma lem2713249 : term257 = True.
Proof. exact (TRANS (@lem2713244) (@lem2713248)). Qed.
Lemma lem2713250 : True = term257.
Proof. exact (SYM (@lem2713249)). Qed.
Lemma lem2713251 : term257.
Proof. exact (EQ_MP (@lem2713250) (@lem0)). Qed.
Lemma lem2713252 : term578.
Proof. exact (@lem2713241 (@lem2713251)). Qed.
Lemma lem2713254 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713255 : term257 = term258.
Proof. exact (@lem2713254 (NUMERAL 0) term67). Qed.
Lemma lem2713256 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713257 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713258 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713257 h1) (fun h1 : term258 = True => @lem2713256)). Qed.
Lemma lem2713259 : term258 = True.
Proof. exact (EQ_MP (@lem2713258) (@lem2713256)). Qed.
Lemma lem2713260 : term257 = True.
Proof. exact (TRANS (@lem2713255) (@lem2713259)). Qed.
Lemma lem2713261 : True = term257.
Proof. exact (SYM (@lem2713260)). Qed.
Lemma lem2713262 : term257.
Proof. exact (EQ_MP (@lem2713261) (@lem0)). Qed.
Lemma lem2713263 : (term173 = term137) = (term289 = term269).
Proof. exact (@lem2713252 (@lem2713262)). Qed.
Lemma lem2713265 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713266 : term269 = term32.
Proof. exact (@lem2713265 term67). Qed.
Lemma lem2713268 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713269 : term289 = term290.
Proof. exact (@lem2713268 term29 term67). Qed.
Lemma lem2713270 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2713271 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2713272 : term292 = term29.
Proof. exact (EQ_MP (@lem2713271) (@lem2713270)). Qed.
Lemma lem2713273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713274 : term290 = term28.
Proof. exact (MK_COMB (@lem2713273) (@lem2713272)). Qed.
Lemma lem2713275 : term289 = term28.
Proof. exact (TRANS (@lem2713269) (@lem2713274)). Qed.
Lemma lem2713276 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2713277 : term579 = term31.
Proof. exact (MK_COMB (@lem2713276) (@lem2713275)). Qed.
Lemma lem2713278 : (term289 = term269) = (term28 = term32).
Proof. exact (MK_COMB (@lem2713277) (@lem2713266)). Qed.
Lemma lem2713280 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem2713281 : (term28 = term32) = (term29 = (NUMERAL 0)).
Proof. exact (@lem2713280 term29 (NUMERAL 0)). Qed.
Lemma lem2713282 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2713283 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2713284 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2713283 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2713282)). Qed.
Lemma lem2713285 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2713284) (@lem2713282)). Qed.
Lemma lem2713286 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2713281) (@lem2713285)). Qed.
Lemma lem2713287 : (term289 = term269) = False.
Proof. exact (TRANS (@lem2713278) (@lem2713286)). Qed.
Lemma lem2713288 : (term173 = term137) = False.
Proof. exact (TRANS (@lem2713263) (@lem2713287)). Qed.
Lemma lem2713289 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2713240) (@lem2713288)). Qed.
Lemma lem2713290 (n : int) (h1 : term888 n) : False.
Proof. exact (EQ_MP (@lem2713289) (@lem2713229 n h1)). Qed.
Lemma lem2713291 (n : int) (h1 : term544 n) : term544 n.
Proof. exact (h1). Qed.
Lemma lem2713292 (n : int) (h1 : term540 n) : term540 n.
Proof. exact (h1). Qed.
Lemma lem2713293 (n : int) (h1 : term540 n) : term539 n.
Proof. exact (proj2 (@lem2713292 n h1)). Qed.
Lemma lem2713295 (n : int) (h1 : term540 n) : term319 n.
Proof. exact (proj2 (@lem2713293 n h1)). Qed.
Lemma lem2713296 (n : int) (h1 : term540 n) : term402 n.
Proof. exact (proj1 (@lem2713293 n h1)). Qed.
Lemma lem2713298 (n : int) (h1 : term540 n) : (term195 n) = term32.
Proof. exact (proj1 (@lem2713296 n h1)). Qed.
Lemma lem2713301 (n : int) (h1 : term540 n) : term300 n.
Proof. exact (proj2 (@lem2713295 n h1)). Qed.
Lemma lem2713302 (n : int) (h1 : term540 n) : term235 n.
Proof. exact (proj1 (@lem2713295 n h1)). Qed.
Lemma lem2713304 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2713305 : term581 = term257.
Proof. exact (@lem2713304 term32 term66). Qed.
Lemma lem2713307 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713308 : term66 = term210.
Proof. exact (@lem2713307 term67). Qed.
Lemma lem2713310 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713311 : term32 = term137.
Proof. exact (@lem2713310 (NUMERAL 0)). Qed.
Lemma lem2713312 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713313 : term582 = term583.
Proof. exact (MK_COMB (@lem2713312) (@lem2713311)). Qed.
Lemma lem2713314 : term257 = term584.
Proof. exact (MK_COMB (@lem2713313) (@lem2713308)). Qed.
Lemma lem2713315 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2713317 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713318 : term257 = term258.
Proof. exact (@lem2713317 (NUMERAL 0) term67). Qed.
Lemma lem2713319 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713320 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713321 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713320 h1) (fun h1 : term258 = True => @lem2713319)). Qed.
Lemma lem2713322 : term258 = True.
Proof. exact (EQ_MP (@lem2713321) (@lem2713319)). Qed.
Lemma lem2713323 : term257 = True.
Proof. exact (TRANS (@lem2713318) (@lem2713322)). Qed.
Lemma lem2713324 : True = term257.
Proof. exact (SYM (@lem2713323)). Qed.
Lemma lem2713325 : term257.
Proof. exact (EQ_MP (@lem2713324) (@lem0)). Qed.
Lemma lem2713326 : term586.
Proof. exact (@lem2713315 (@lem2713325)). Qed.
Lemma lem2713328 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713329 : term257 = term258.
Proof. exact (@lem2713328 (NUMERAL 0) term67). Qed.
Lemma lem2713330 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713331 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713332 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713331 h1) (fun h1 : term258 = True => @lem2713330)). Qed.
Lemma lem2713333 : term258 = True.
Proof. exact (EQ_MP (@lem2713332) (@lem2713330)). Qed.
Lemma lem2713334 : term257 = True.
Proof. exact (TRANS (@lem2713329) (@lem2713333)). Qed.
Lemma lem2713335 : True = term257.
Proof. exact (SYM (@lem2713334)). Qed.
Lemma lem2713336 : term257.
Proof. exact (EQ_MP (@lem2713335) (@lem0)). Qed.
Lemma lem2713337 : term584 = term587.
Proof. exact (@lem2713326 (@lem2713336)). Qed.
Lemma lem2713339 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713340 : term149 = term150.
Proof. exact (@lem2713339 term67 term67). Qed.
Lemma lem2713341 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713342 : term152 = term67.
Proof. exact (EQ_MP (@lem2713341) (@lem940073)). Qed.
Lemma lem2713343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713344 : term150 = term66.
Proof. exact (MK_COMB (@lem2713343) (@lem2713342)). Qed.
Lemma lem2713345 : term149 = term66.
Proof. exact (TRANS (@lem2713340) (@lem2713344)). Qed.
Lemma lem2713347 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713348 : term269 = term32.
Proof. exact (@lem2713347 term67). Qed.
Lemma lem2713349 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713350 : term588 = term582.
Proof. exact (MK_COMB (@lem2713349) (@lem2713348)). Qed.
Lemma lem2713351 : term587 = term257.
Proof. exact (MK_COMB (@lem2713350) (@lem2713345)). Qed.
Lemma lem2713353 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713354 : term257 = term258.
Proof. exact (@lem2713353 (NUMERAL 0) term67). Qed.
Lemma lem2713355 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713356 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713357 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713356 h1) (fun h1 : term258 = True => @lem2713355)). Qed.
Lemma lem2713358 : term258 = True.
Proof. exact (EQ_MP (@lem2713357) (@lem2713355)). Qed.
Lemma lem2713359 : term257 = True.
Proof. exact (TRANS (@lem2713354) (@lem2713358)). Qed.
Lemma lem2713360 : term587 = True.
Proof. exact (TRANS (@lem2713351) (@lem2713359)). Qed.
Lemma lem2713361 : term584 = True.
Proof. exact (TRANS (@lem2713337) (@lem2713360)). Qed.
Lemma lem2713362 : term257 = True.
Proof. exact (TRANS (@lem2713314) (@lem2713361)). Qed.
Lemma lem2713363 : term581 = True.
Proof. exact (TRANS (@lem2713305) (@lem2713362)). Qed.
Lemma lem2713364 : True = term581.
Proof. exact (SYM (@lem2713363)). Qed.
Lemma lem2713365 : term581.
Proof. exact (EQ_MP (@lem2713364) (@lem0)). Qed.
Lemma lem2713366 (n : int) (h1 : term540 n) : term589 n.
Proof. exact (conj (@lem2713365) (@lem2713302 n h1)). Qed.
Lemma lem2713368 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2713369 (n : int) : term591 n.
Proof. exact (@lem2713368 term66 (term218 n)). Qed.
Lemma lem2713370 (n : int) (h1 : term540 n) : term592 n.
Proof. exact (@lem2713369 n (@lem2713366 n h1)). Qed.
Lemma lem2713371 (n : int) : (term593 n) = (term218 n).
Proof. exact (@lem1982733 (term218 n)). Qed.
Lemma lem2713372 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2713373 (n : int) : (term594 n) = (term234 n).
Proof. exact (MK_COMB (@lem2713372) (@lem2713371 n)). Qed.
Lemma lem2713374 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713375 (n : int) : (term592 n) = (term235 n).
Proof. exact (MK_COMB (@lem2713373 n) (@lem2713374)). Qed.
Lemma lem2713376 (n : int) (h1 : term540 n) : term235 n.
Proof. exact (EQ_MP (@lem2713375 n) (@lem2713370 n h1)). Qed.
Lemma lem2713378 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2713379 (n : int) : term596 n.
Proof. exact (@lem2713378 (term195 n)). Qed.
Lemma lem2713380 (n : int) (h1 : term540 n) : term597 n.
Proof. exact (@lem2713379 n (@lem2713298 n h1)). Qed.
Lemma lem2713381 (n : int) (h1 : term540 n) : term598 n.
Proof. exact (@lem2713380 n h1 term140). Qed.
Lemma lem2713382 (n : int) : (term598 n) = ((term599 n) = term32).
Proof. exact (eq_refl (term598 n)). Qed.
Lemma lem2713383 (n : int) (h1 : term540 n) : (term599 n) = term32.
Proof. exact (EQ_MP (@lem2713382 n) (@lem2713381 n h1)). Qed.
Lemma lem2713384 (n : int) : (term599 n) = (term600 n).
Proof. exact (@lem1982781 (real_of_int n) term140 (term193 n)). Qed.
Lemma lem2713385 (n : int) : (term601 n) = (term602 n).
Proof. exact (@lem1982781 (term190 n) term140 (term170 n)). Qed.
Lemma lem2713386 (n : int) : (term603 n) = (term604 n).
Proof. exact (@lem1982749 term140 term140 (term48 n)). Qed.
Lemma lem2713388 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713389 : term140 = term141.
Proof. exact (@lem2713388 term67). Qed.
Lemma lem2713391 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713392 : term140 = term141.
Proof. exact (@lem2713391 term67). Qed.
Lemma lem2713393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713394 : term142 = term143.
Proof. exact (MK_COMB (@lem2713393) (@lem2713392)). Qed.
Lemma lem2713395 : term605 = term606.
Proof. exact (MK_COMB (@lem2713394) (@lem2713389)). Qed.
Lemma lem2713396 : term606 = term607.
Proof. exact (@lem1981613 term140 term140 term66 term66). Qed.
Lemma lem2713398 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713399 : term149 = term150.
Proof. exact (@lem2713398 term67 term67). Qed.
Lemma lem2713400 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713401 : term152 = term67.
Proof. exact (EQ_MP (@lem2713400) (@lem940073)). Qed.
Lemma lem2713402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713403 : term150 = term66.
Proof. exact (MK_COMB (@lem2713402) (@lem2713401)). Qed.
Lemma lem2713404 : term149 = term66.
Proof. exact (TRANS (@lem2713399) (@lem2713403)). Qed.
Lemma lem2713406 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2713407 : term605 = term150.
Proof. exact (@lem2713406 term67 term67). Qed.
Lemma lem2713408 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713409 : term152 = term67.
Proof. exact (EQ_MP (@lem2713408) (@lem940073)). Qed.
Lemma lem2713410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713411 : term150 = term66.
Proof. exact (MK_COMB (@lem2713410) (@lem2713409)). Qed.
Lemma lem2713412 : term605 = term66.
Proof. exact (TRANS (@lem2713407) (@lem2713411)). Qed.
Lemma lem2713413 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2713414 : term609 = term610.
Proof. exact (MK_COMB (@lem2713413) (@lem2713412)). Qed.
Lemma lem2713415 : term607 = term210.
Proof. exact (MK_COMB (@lem2713414) (@lem2713404)). Qed.
Lemma lem2713416 : term606 = term210.
Proof. exact (TRANS (@lem2713396) (@lem2713415)). Qed.
Lemma lem2713417 : term605 = term210.
Proof. exact (TRANS (@lem2713395) (@lem2713416)). Qed.
Lemma lem2713419 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2713420 : term210 = term66.
Proof. exact (@lem2713419 term66). Qed.
Lemma lem2713421 : term605 = term66.
Proof. exact (TRANS (@lem2713417) (@lem2713420)). Qed.
Lemma lem2713422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713423 : term611 = term385.
Proof. exact (MK_COMB (@lem2713422) (@lem2713421)). Qed.
Lemma lem2713424 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2713425 (n : int) : (term604 n) = (term612 n).
Proof. exact (MK_COMB (@lem2713423) (@lem2713424 n)). Qed.
Lemma lem2713426 (n : int) : (term603 n) = (term612 n).
Proof. exact (TRANS (@lem2713386 n) (@lem2713425 n)). Qed.
Lemma lem2713427 (n : int) : (term612 n) = (term48 n).
Proof. exact (@lem1982709 (term48 n)). Qed.
Lemma lem2713428 (n : int) : (term603 n) = (term48 n).
Proof. exact (TRANS (@lem2713426 n) (@lem2713427 n)). Qed.
Lemma lem2713429 (n : int) : (term613 n) = (term614 n).
Proof. exact (@lem1982749 term140 term184 (term162 n)). Qed.
Lemma lem2713431 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713432 : term184 = term187.
Proof. exact (@lem2713431 term29). Qed.
Lemma lem2713434 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713435 : term140 = term141.
Proof. exact (@lem2713434 term67). Qed.
Lemma lem2713436 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713437 : term142 = term143.
Proof. exact (MK_COMB (@lem2713436) (@lem2713435)). Qed.
Lemma lem2713438 : term615 = term616.
Proof. exact (MK_COMB (@lem2713437) (@lem2713432)). Qed.
Lemma lem2713439 : term616 = term617.
Proof. exact (@lem1981613 term140 term184 term66 term66). Qed.
Lemma lem2713441 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713442 : term149 = term150.
Proof. exact (@lem2713441 term67 term67). Qed.
Lemma lem2713443 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713444 : term152 = term67.
Proof. exact (EQ_MP (@lem2713443) (@lem940073)). Qed.
Lemma lem2713445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713446 : term150 = term66.
Proof. exact (MK_COMB (@lem2713445) (@lem2713444)). Qed.
Lemma lem2713447 : term149 = term66.
Proof. exact (TRANS (@lem2713442) (@lem2713446)). Qed.
Lemma lem2713449 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2713450 : term615 = term183.
Proof. exact (@lem2713449 term67 term29). Qed.
Lemma lem2713451 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2713452 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2713453 : term182 = term29.
Proof. exact (EQ_MP (@lem2713452) (@lem2713451)). Qed.
Lemma lem2713454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713455 : term183 = term28.
Proof. exact (MK_COMB (@lem2713454) (@lem2713453)). Qed.
Lemma lem2713456 : term615 = term28.
Proof. exact (TRANS (@lem2713450) (@lem2713455)). Qed.
Lemma lem2713457 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2713458 : term618 = term619.
Proof. exact (MK_COMB (@lem2713457) (@lem2713456)). Qed.
Lemma lem2713459 : term617 = term173.
Proof. exact (MK_COMB (@lem2713458) (@lem2713447)). Qed.
Lemma lem2713460 : term616 = term173.
Proof. exact (TRANS (@lem2713439) (@lem2713459)). Qed.
Lemma lem2713461 : term615 = term173.
Proof. exact (TRANS (@lem2713438) (@lem2713460)). Qed.
Lemma lem2713463 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2713464 : term173 = term28.
Proof. exact (@lem2713463 term28). Qed.
Lemma lem2713465 : term615 = term28.
Proof. exact (TRANS (@lem2713461) (@lem2713464)). Qed.
Lemma lem2713466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713467 : term620 = term287.
Proof. exact (MK_COMB (@lem2713466) (@lem2713465)). Qed.
Lemma lem2713468 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2713469 (n : int) : (term614 n) = (term161 n).
Proof. exact (MK_COMB (@lem2713467) (@lem2713468 n)). Qed.
Lemma lem2713470 (n : int) : (term613 n) = (term161 n).
Proof. exact (TRANS (@lem2713429 n) (@lem2713469 n)). Qed.
Lemma lem2713471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713472 (n : int) : (term621 n) = (term163 n).
Proof. exact (MK_COMB (@lem2713471) (@lem2713470 n)). Qed.
Lemma lem2713473 (n : int) : (term602 n) = (term164 n).
Proof. exact (MK_COMB (@lem2713472 n) (@lem2713428 n)). Qed.
Lemma lem2713474 (n : int) : (term601 n) = (term164 n).
Proof. exact (TRANS (@lem2713385 n) (@lem2713473 n)). Qed.
Lemma lem2713477 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2713478 (n : int) : (term600 n) = (term623 n).
Proof. exact (MK_COMB (@lem2713477 n) (@lem2713474 n)). Qed.
Lemma lem2713479 (n : int) : (term599 n) = (term623 n).
Proof. exact (TRANS (@lem2713384 n) (@lem2713478 n)). Qed.
Lemma lem2713480 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2713481 (n : int) : (term624 n) = (term625 n).
Proof. exact (MK_COMB (@lem2713480) (@lem2713479 n)). Qed.
Lemma lem2713482 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713483 (n : int) : ((term599 n) = term32) = ((term623 n) = term32).
Proof. exact (MK_COMB (@lem2713481 n) (@lem2713482)). Qed.
Lemma lem2713484 (n : int) (h1 : term540 n) : (term623 n) = term32.
Proof. exact (EQ_MP (@lem2713483 n) (@lem2713383 n h1)). Qed.
Lemma lem2713485 (n : int) (h1 : term540 n) : term626 n.
Proof. exact (conj (@lem2713484 n h1) (@lem2713376 n h1)). Qed.
Lemma lem2713487 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2713488 (n : int) : term628 n.
Proof. exact (@lem2713487 (term623 n) (term218 n)). Qed.
Lemma lem2713489 (n : int) (h1 : term540 n) : term629 n.
Proof. exact (@lem2713488 n (@lem2713485 n h1)). Qed.
Lemma lem2713490 (n : int) : (term630 n) = (term631 n).
Proof. exact (@lem1982755 (term632 n) (term164 n) (term218 n)). Qed.
Lemma lem2713491 (n : int) : (term633 n) = (term634 n).
Proof. exact (@lem1982755 (term161 n) (term48 n) (term218 n)). Qed.
Lemma lem2713492 (n : int) : (term635 n) = (term636 n).
Proof. exact (@lem1982763 (term48 n) (term170 n) term140). Qed.
Lemma lem2713493 (n : int) : (term637 n) = (term638 n).
Proof. exact (@lem1982715 term140 (term48 n)). Qed.
Lemma lem2713495 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713496 : term66 = term210.
Proof. exact (@lem2713495 term67). Qed.
Lemma lem2713498 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713499 : term140 = term141.
Proof. exact (@lem2713498 term67). Qed.
Lemma lem2713500 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713501 : term639 = term640.
Proof. exact (MK_COMB (@lem2713500) (@lem2713499)). Qed.
Lemma lem2713502 : term641 = term642.
Proof. exact (MK_COMB (@lem2713501) (@lem2713496)). Qed.
Lemma lem2713503 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2713505 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713506 : term257 = term258.
Proof. exact (@lem2713505 (NUMERAL 0) term67). Qed.
Lemma lem2713507 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713508 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713509 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713508 h1) (fun h1 : term258 = True => @lem2713507)). Qed.
Lemma lem2713510 : term258 = True.
Proof. exact (EQ_MP (@lem2713509) (@lem2713507)). Qed.
Lemma lem2713511 : term257 = True.
Proof. exact (TRANS (@lem2713506) (@lem2713510)). Qed.
Lemma lem2713512 : True = term257.
Proof. exact (SYM (@lem2713511)). Qed.
Lemma lem2713513 : term257.
Proof. exact (EQ_MP (@lem2713512) (@lem0)). Qed.
Lemma lem2713514 : term644.
Proof. exact (@lem2713503 (@lem2713513)). Qed.
Lemma lem2713516 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713517 : term257 = term258.
Proof. exact (@lem2713516 (NUMERAL 0) term67). Qed.
Lemma lem2713518 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713519 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713520 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713519 h1) (fun h1 : term258 = True => @lem2713518)). Qed.
Lemma lem2713521 : term258 = True.
Proof. exact (EQ_MP (@lem2713520) (@lem2713518)). Qed.
Lemma lem2713522 : term257 = True.
Proof. exact (TRANS (@lem2713517) (@lem2713521)). Qed.
Lemma lem2713523 : True = term257.
Proof. exact (SYM (@lem2713522)). Qed.
Lemma lem2713524 : term257.
Proof. exact (EQ_MP (@lem2713523) (@lem0)). Qed.
Lemma lem2713525 : term645.
Proof. exact (@lem2713514 (@lem2713524)). Qed.
Lemma lem2713527 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713528 : term257 = term258.
Proof. exact (@lem2713527 (NUMERAL 0) term67). Qed.
Lemma lem2713529 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713530 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713531 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713530 h1) (fun h1 : term258 = True => @lem2713529)). Qed.
Lemma lem2713532 : term258 = True.
Proof. exact (EQ_MP (@lem2713531) (@lem2713529)). Qed.
Lemma lem2713533 : term257 = True.
Proof. exact (TRANS (@lem2713528) (@lem2713532)). Qed.
Lemma lem2713534 : True = term257.
Proof. exact (SYM (@lem2713533)). Qed.
Lemma lem2713535 : term257.
Proof. exact (EQ_MP (@lem2713534) (@lem0)). Qed.
Lemma lem2713536 : term646.
Proof. exact (@lem2713525 (@lem2713535)). Qed.
Lemma lem2713538 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713539 : term149 = term150.
Proof. exact (@lem2713538 term67 term67). Qed.
Lemma lem2713540 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713541 : term152 = term67.
Proof. exact (EQ_MP (@lem2713540) (@lem940073)). Qed.
Lemma lem2713542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713543 : term150 = term66.
Proof. exact (MK_COMB (@lem2713542) (@lem2713541)). Qed.
Lemma lem2713544 : term149 = term66.
Proof. exact (TRANS (@lem2713539) (@lem2713543)). Qed.
Lemma lem2713546 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2713547 : term211 = term214.
Proof. exact (@lem2713546 term67 term67). Qed.
Lemma lem2713548 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713549 : term152 = term67.
Proof. exact (EQ_MP (@lem2713548) (@lem940073)). Qed.
Lemma lem2713550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713551 : term150 = term66.
Proof. exact (MK_COMB (@lem2713550) (@lem2713549)). Qed.
Lemma lem2713552 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713553 : term214 = term140.
Proof. exact (MK_COMB (@lem2713552) (@lem2713551)). Qed.
Lemma lem2713554 : term211 = term140.
Proof. exact (TRANS (@lem2713547) (@lem2713553)). Qed.
Lemma lem2713555 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713556 : term647 = term639.
Proof. exact (MK_COMB (@lem2713555) (@lem2713554)). Qed.
Lemma lem2713557 : term648 = term641.
Proof. exact (MK_COMB (@lem2713556) (@lem2713544)). Qed.
Lemma lem2713559 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2713560 : term641 = term32.
Proof. exact (@lem2713559 term67). Qed.
Lemma lem2713561 : term648 = term32.
Proof. exact (TRANS (@lem2713557) (@lem2713560)). Qed.
Lemma lem2713562 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713563 : term650 = term267.
Proof. exact (MK_COMB (@lem2713562) (@lem2713561)). Qed.
Lemma lem2713564 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2713565 : term651 = term269.
Proof. exact (MK_COMB (@lem2713563) (@lem2713564)). Qed.
Lemma lem2713567 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713568 : term269 = term32.
Proof. exact (@lem2713567 term67). Qed.
Lemma lem2713569 : term651 = term32.
Proof. exact (TRANS (@lem2713565) (@lem2713568)). Qed.
Lemma lem2713571 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713572 : term149 = term150.
Proof. exact (@lem2713571 term67 term67). Qed.
Lemma lem2713573 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713574 : term152 = term67.
Proof. exact (EQ_MP (@lem2713573) (@lem940073)). Qed.
Lemma lem2713575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713576 : term150 = term66.
Proof. exact (MK_COMB (@lem2713575) (@lem2713574)). Qed.
Lemma lem2713577 : term149 = term66.
Proof. exact (TRANS (@lem2713572) (@lem2713576)). Qed.
Lemma lem2713578 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2713579 : term271 = term269.
Proof. exact (MK_COMB (@lem2713578) (@lem2713577)). Qed.
Lemma lem2713581 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713582 : term269 = term32.
Proof. exact (@lem2713581 term67). Qed.
Lemma lem2713583 : term271 = term32.
Proof. exact (TRANS (@lem2713579) (@lem2713582)). Qed.
Lemma lem2713584 : term32 = term271.
Proof. exact (SYM (@lem2713583)). Qed.
Lemma lem2713585 : term651 = term271.
Proof. exact (TRANS (@lem2713569) (@lem2713584)). Qed.
Lemma lem2713586 : term642 = term137.
Proof. exact (@lem2713536 (@lem2713585)). Qed.
Lemma lem2713587 : term641 = term137.
Proof. exact (TRANS (@lem2713502) (@lem2713586)). Qed.
Lemma lem2713589 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2713590 : term137 = term32.
Proof. exact (@lem2713589 term32). Qed.
Lemma lem2713591 : term641 = term32.
Proof. exact (TRANS (@lem2713587) (@lem2713590)). Qed.
Lemma lem2713592 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713593 : term652 = term267.
Proof. exact (MK_COMB (@lem2713592) (@lem2713591)). Qed.
Lemma lem2713594 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2713595 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2713593) (@lem2713594 n)). Qed.
Lemma lem2713596 (n : int) : (term637 n) = (term653 n).
Proof. exact (TRANS (@lem2713493 n) (@lem2713595 n)). Qed.
Lemma lem2713597 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2713598 (n : int) : (term637 n) = term32.
Proof. exact (TRANS (@lem2713596 n) (@lem2713597 n)). Qed.
Lemma lem2713599 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713600 (n : int) : (term654 n) = term102.
Proof. exact (MK_COMB (@lem2713599) (@lem2713598 n)). Qed.
Lemma lem2713601 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem2713602 (n : int) : (term636 n) = term655.
Proof. exact (MK_COMB (@lem2713600 n) (@lem2713601)). Qed.
Lemma lem2713603 (n : int) : (term635 n) = term655.
Proof. exact (TRANS (@lem2713492 n) (@lem2713602 n)). Qed.
Lemma lem2713604 : term655 = term140.
Proof. exact (@lem1982721 term140). Qed.
Lemma lem2713605 (n : int) : (term635 n) = term140.
Proof. exact (TRANS (@lem2713603 n) (@lem2713604)). Qed.
Lemma lem2713606 (n : int) : (term163 n) = (term163 n).
Proof. exact (eq_refl (term163 n)). Qed.
Lemma lem2713607 (n : int) : (term634 n) = (term656 n).
Proof. exact (MK_COMB (@lem2713606 n) (@lem2713605 n)). Qed.
Lemma lem2713608 (n : int) : (term633 n) = (term656 n).
Proof. exact (TRANS (@lem2713491 n) (@lem2713607 n)). Qed.
Lemma lem2713609 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2713610 (n : int) : (term631 n) = (term657 n).
Proof. exact (MK_COMB (@lem2713609 n) (@lem2713608 n)). Qed.
Lemma lem2713611 (n : int) : (term630 n) = (term657 n).
Proof. exact (TRANS (@lem2713490 n) (@lem2713610 n)). Qed.
Lemma lem2713612 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2713613 (n : int) : (term658 n) = (term659 n).
Proof. exact (MK_COMB (@lem2713612) (@lem2713611 n)). Qed.
Lemma lem2713614 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713615 (n : int) : (term629 n) = (term660 n).
Proof. exact (MK_COMB (@lem2713613 n) (@lem2713614)). Qed.
Lemma lem2713616 (n : int) (h1 : term540 n) : term660 n.
Proof. exact (EQ_MP (@lem2713615 n) (@lem2713489 n h1)). Qed.
Lemma lem2713618 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2713619 : term661 = term662.
Proof. exact (@lem2713618 term32 term28). Qed.
Lemma lem2713621 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713622 : term28 = term173.
Proof. exact (@lem2713621 term29). Qed.
Lemma lem2713624 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713625 : term32 = term137.
Proof. exact (@lem2713624 (NUMERAL 0)). Qed.
Lemma lem2713626 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713627 : term582 = term583.
Proof. exact (MK_COMB (@lem2713626) (@lem2713625)). Qed.
Lemma lem2713628 : term662 = term663.
Proof. exact (MK_COMB (@lem2713627) (@lem2713622)). Qed.
Lemma lem2713629 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2713631 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713632 : term257 = term258.
Proof. exact (@lem2713631 (NUMERAL 0) term67). Qed.
Lemma lem2713633 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713634 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713635 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713634 h1) (fun h1 : term258 = True => @lem2713633)). Qed.
Lemma lem2713636 : term258 = True.
Proof. exact (EQ_MP (@lem2713635) (@lem2713633)). Qed.
Lemma lem2713637 : term257 = True.
Proof. exact (TRANS (@lem2713632) (@lem2713636)). Qed.
Lemma lem2713638 : True = term257.
Proof. exact (SYM (@lem2713637)). Qed.
Lemma lem2713639 : term257.
Proof. exact (EQ_MP (@lem2713638) (@lem0)). Qed.
Lemma lem2713640 : term665.
Proof. exact (@lem2713629 (@lem2713639)). Qed.
Lemma lem2713642 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713643 : term257 = term258.
Proof. exact (@lem2713642 (NUMERAL 0) term67). Qed.
Lemma lem2713644 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713645 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713646 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713645 h1) (fun h1 : term258 = True => @lem2713644)). Qed.
Lemma lem2713647 : term258 = True.
Proof. exact (EQ_MP (@lem2713646) (@lem2713644)). Qed.
Lemma lem2713648 : term257 = True.
Proof. exact (TRANS (@lem2713643) (@lem2713647)). Qed.
Lemma lem2713649 : True = term257.
Proof. exact (SYM (@lem2713648)). Qed.
Lemma lem2713650 : term257.
Proof. exact (EQ_MP (@lem2713649) (@lem0)). Qed.
Lemma lem2713651 : term663 = term666.
Proof. exact (@lem2713640 (@lem2713650)). Qed.
Lemma lem2713653 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713654 : term289 = term290.
Proof. exact (@lem2713653 term29 term67). Qed.
Lemma lem2713655 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2713656 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2713657 : term292 = term29.
Proof. exact (EQ_MP (@lem2713656) (@lem2713655)). Qed.
Lemma lem2713658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713659 : term290 = term28.
Proof. exact (MK_COMB (@lem2713658) (@lem2713657)). Qed.
Lemma lem2713660 : term289 = term28.
Proof. exact (TRANS (@lem2713654) (@lem2713659)). Qed.
Lemma lem2713662 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713663 : term269 = term32.
Proof. exact (@lem2713662 term67). Qed.
Lemma lem2713664 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713665 : term588 = term582.
Proof. exact (MK_COMB (@lem2713664) (@lem2713663)). Qed.
Lemma lem2713666 : term666 = term662.
Proof. exact (MK_COMB (@lem2713665) (@lem2713660)). Qed.
Lemma lem2713668 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713669 : term662 = term667.
Proof. exact (@lem2713668 (NUMERAL 0) term29). Qed.
Lemma lem2713670 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2713671 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2713672 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2713671 h1) (fun h1 : term667 = True => @lem2713670)). Qed.
Lemma lem2713673 : term667 = True.
Proof. exact (EQ_MP (@lem2713672) (@lem2713670)). Qed.
Lemma lem2713674 : term662 = True.
Proof. exact (TRANS (@lem2713669) (@lem2713673)). Qed.
Lemma lem2713675 : term666 = True.
Proof. exact (TRANS (@lem2713666) (@lem2713674)). Qed.
Lemma lem2713676 : term663 = True.
Proof. exact (TRANS (@lem2713651) (@lem2713675)). Qed.
Lemma lem2713677 : term662 = True.
Proof. exact (TRANS (@lem2713628) (@lem2713676)). Qed.
Lemma lem2713678 : term661 = True.
Proof. exact (TRANS (@lem2713619) (@lem2713677)). Qed.
Lemma lem2713679 : True = term661.
Proof. exact (SYM (@lem2713678)). Qed.
Lemma lem2713680 : term661.
Proof. exact (EQ_MP (@lem2713679) (@lem0)). Qed.
Lemma lem2713681 (n : int) (h1 : term540 n) : term668 n.
Proof. exact (conj (@lem2713680) (@lem2713616 n h1)). Qed.
Lemma lem2713683 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2713684 (n : int) : term669 n.
Proof. exact (@lem2713683 term28 (term657 n)). Qed.
Lemma lem2713685 (n : int) (h1 : term540 n) : term670 n.
Proof. exact (@lem2713684 n (@lem2713681 n h1)). Qed.
Lemma lem2713686 (n : int) : (term671 n) = (term672 n).
Proof. exact (@lem1982781 (term632 n) term28 (term656 n)). Qed.
Lemma lem2713687 (n : int) : (term673 n) = (term674 n).
Proof. exact (@lem1982781 (term161 n) term28 term140). Qed.
Lemma lem2713689 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713690 : term140 = term141.
Proof. exact (@lem2713689 term67). Qed.
Lemma lem2713692 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713693 : term28 = term173.
Proof. exact (@lem2713692 term29). Qed.
Lemma lem2713694 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713695 : term287 = term675.
Proof. exact (MK_COMB (@lem2713694) (@lem2713693)). Qed.
Lemma lem2713696 : term676 = term677.
Proof. exact (MK_COMB (@lem2713695) (@lem2713690)). Qed.
Lemma lem2713697 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2713699 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713700 : term149 = term150.
Proof. exact (@lem2713699 term67 term67). Qed.
Lemma lem2713701 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713702 : term152 = term67.
Proof. exact (EQ_MP (@lem2713701) (@lem940073)). Qed.
Lemma lem2713703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713704 : term150 = term66.
Proof. exact (MK_COMB (@lem2713703) (@lem2713702)). Qed.
Lemma lem2713705 : term149 = term66.
Proof. exact (TRANS (@lem2713700) (@lem2713704)). Qed.
Lemma lem2713707 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2713708 : term676 = term440.
Proof. exact (@lem2713707 term29 term67). Qed.
Lemma lem2713709 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2713710 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2713711 : term292 = term29.
Proof. exact (EQ_MP (@lem2713710) (@lem2713709)). Qed.
Lemma lem2713712 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713713 : term290 = term28.
Proof. exact (MK_COMB (@lem2713712) (@lem2713711)). Qed.
Lemma lem2713714 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713715 : term440 = term184.
Proof. exact (MK_COMB (@lem2713714) (@lem2713713)). Qed.
Lemma lem2713716 : term676 = term184.
Proof. exact (TRANS (@lem2713708) (@lem2713715)). Qed.
Lemma lem2713717 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2713718 : term680 = term186.
Proof. exact (MK_COMB (@lem2713717) (@lem2713716)). Qed.
Lemma lem2713719 : term678 = term187.
Proof. exact (MK_COMB (@lem2713718) (@lem2713705)). Qed.
Lemma lem2713720 : term677 = term187.
Proof. exact (TRANS (@lem2713697) (@lem2713719)). Qed.
Lemma lem2713721 : term676 = term187.
Proof. exact (TRANS (@lem2713696) (@lem2713720)). Qed.
Lemma lem2713723 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2713724 : term187 = term184.
Proof. exact (@lem2713723 term184). Qed.
Lemma lem2713725 : term676 = term184.
Proof. exact (TRANS (@lem2713721) (@lem2713724)). Qed.
Lemma lem2713726 (n : int) : (term681 n) = (term682 n).
Proof. exact (@lem1982749 term28 term28 (term162 n)). Qed.
Lemma lem2713728 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713729 : term28 = term173.
Proof. exact (@lem2713728 term29). Qed.
Lemma lem2713731 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713732 : term28 = term173.
Proof. exact (@lem2713731 term29). Qed.
Lemma lem2713733 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713734 : term287 = term675.
Proof. exact (MK_COMB (@lem2713733) (@lem2713732)). Qed.
Lemma lem2713735 : term683 = term684.
Proof. exact (MK_COMB (@lem2713734) (@lem2713729)). Qed.
Lemma lem2713736 : term684 = term685.
Proof. exact (@lem1981613 term28 term28 term66 term66). Qed.
Lemma lem2713738 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713739 : term149 = term150.
Proof. exact (@lem2713738 term67 term67). Qed.
Lemma lem2713740 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713741 : term152 = term67.
Proof. exact (EQ_MP (@lem2713740) (@lem940073)). Qed.
Lemma lem2713742 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713743 : term150 = term66.
Proof. exact (MK_COMB (@lem2713742) (@lem2713741)). Qed.
Lemma lem2713744 : term149 = term66.
Proof. exact (TRANS (@lem2713739) (@lem2713743)). Qed.
Lemma lem2713746 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713747 : term683 = term686.
Proof. exact (@lem2713746 term29 term29). Qed.
Lemma lem2713748 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713749 : term687 = term688.
Proof. exact (EQ_MP (@lem2713748) (@lem940073)). Qed.
Lemma lem2713750 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2713751 : term689 = term690.
Proof. exact (EQ_MP (@lem2713750) (@lem2713749)). Qed.
Lemma lem2713752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713753 : term686 = term691.
Proof. exact (MK_COMB (@lem2713752) (@lem2713751)). Qed.
Lemma lem2713754 : term683 = term691.
Proof. exact (TRANS (@lem2713747) (@lem2713753)). Qed.
Lemma lem2713755 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2713756 : term692 = term693.
Proof. exact (MK_COMB (@lem2713755) (@lem2713754)). Qed.
Lemma lem2713757 : term685 = term694.
Proof. exact (MK_COMB (@lem2713756) (@lem2713744)). Qed.
Lemma lem2713758 : term684 = term694.
Proof. exact (TRANS (@lem2713736) (@lem2713757)). Qed.
Lemma lem2713759 : term683 = term694.
Proof. exact (TRANS (@lem2713735) (@lem2713758)). Qed.
Lemma lem2713761 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2713762 : term694 = term691.
Proof. exact (@lem2713761 term691). Qed.
Lemma lem2713763 : term683 = term691.
Proof. exact (TRANS (@lem2713759) (@lem2713762)). Qed.
Lemma lem2713764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713765 : term695 = term696.
Proof. exact (MK_COMB (@lem2713764) (@lem2713763)). Qed.
Lemma lem2713766 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2713767 (n : int) : (term682 n) = (term697 n).
Proof. exact (MK_COMB (@lem2713765) (@lem2713766 n)). Qed.
Lemma lem2713768 (n : int) : (term681 n) = (term697 n).
Proof. exact (TRANS (@lem2713726 n) (@lem2713767 n)). Qed.
Lemma lem2713769 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713770 (n : int) : (term698 n) = (term699 n).
Proof. exact (MK_COMB (@lem2713769) (@lem2713768 n)). Qed.
Lemma lem2713771 (n : int) : (term674 n) = (term700 n).
Proof. exact (MK_COMB (@lem2713770 n) (@lem2713725)). Qed.
Lemma lem2713772 (n : int) : (term673 n) = (term700 n).
Proof. exact (TRANS (@lem2713687 n) (@lem2713771 n)). Qed.
Lemma lem2713773 (n : int) : (term701 n) = (term702 n).
Proof. exact (@lem1982749 term28 term140 (real_of_int n)). Qed.
Lemma lem2713775 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713776 : term140 = term141.
Proof. exact (@lem2713775 term67). Qed.
Lemma lem2713778 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713779 : term28 = term173.
Proof. exact (@lem2713778 term29). Qed.
Lemma lem2713780 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713781 : term287 = term675.
Proof. exact (MK_COMB (@lem2713780) (@lem2713779)). Qed.
Lemma lem2713782 : term676 = term677.
Proof. exact (MK_COMB (@lem2713781) (@lem2713776)). Qed.
Lemma lem2713783 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2713785 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713786 : term149 = term150.
Proof. exact (@lem2713785 term67 term67). Qed.
Lemma lem2713787 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713788 : term152 = term67.
Proof. exact (EQ_MP (@lem2713787) (@lem940073)). Qed.
Lemma lem2713789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713790 : term150 = term66.
Proof. exact (MK_COMB (@lem2713789) (@lem2713788)). Qed.
Lemma lem2713791 : term149 = term66.
Proof. exact (TRANS (@lem2713786) (@lem2713790)). Qed.
Lemma lem2713793 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2713794 : term676 = term440.
Proof. exact (@lem2713793 term29 term67). Qed.
Lemma lem2713795 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2713796 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2713797 : term292 = term29.
Proof. exact (EQ_MP (@lem2713796) (@lem2713795)). Qed.
Lemma lem2713798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713799 : term290 = term28.
Proof. exact (MK_COMB (@lem2713798) (@lem2713797)). Qed.
Lemma lem2713800 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713801 : term440 = term184.
Proof. exact (MK_COMB (@lem2713800) (@lem2713799)). Qed.
Lemma lem2713802 : term676 = term184.
Proof. exact (TRANS (@lem2713794) (@lem2713801)). Qed.
Lemma lem2713803 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2713804 : term680 = term186.
Proof. exact (MK_COMB (@lem2713803) (@lem2713802)). Qed.
Lemma lem2713805 : term678 = term187.
Proof. exact (MK_COMB (@lem2713804) (@lem2713791)). Qed.
Lemma lem2713806 : term677 = term187.
Proof. exact (TRANS (@lem2713783) (@lem2713805)). Qed.
Lemma lem2713807 : term676 = term187.
Proof. exact (TRANS (@lem2713782) (@lem2713806)). Qed.
Lemma lem2713809 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2713810 : term187 = term184.
Proof. exact (@lem2713809 term184). Qed.
Lemma lem2713811 : term676 = term184.
Proof. exact (TRANS (@lem2713807) (@lem2713810)). Qed.
Lemma lem2713812 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713813 : term703 = term189.
Proof. exact (MK_COMB (@lem2713812) (@lem2713811)). Qed.
Lemma lem2713814 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2713815 (n : int) : (term702 n) = (term704 n).
Proof. exact (MK_COMB (@lem2713813) (@lem2713814 n)). Qed.
Lemma lem2713816 (n : int) : (term701 n) = (term704 n).
Proof. exact (TRANS (@lem2713773 n) (@lem2713815 n)). Qed.
Lemma lem2713817 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713818 (n : int) : (term705 n) = (term706 n).
Proof. exact (MK_COMB (@lem2713817) (@lem2713816 n)). Qed.
Lemma lem2713819 (n : int) : (term672 n) = (term707 n).
Proof. exact (MK_COMB (@lem2713818 n) (@lem2713772 n)). Qed.
Lemma lem2713820 (n : int) : (term671 n) = (term707 n).
Proof. exact (TRANS (@lem2713686 n) (@lem2713819 n)). Qed.
Lemma lem2713821 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2713822 (n : int) : (term708 n) = (term709 n).
Proof. exact (MK_COMB (@lem2713821) (@lem2713820 n)). Qed.
Lemma lem2713823 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713824 (n : int) : (term670 n) = (term710 n).
Proof. exact (MK_COMB (@lem2713822 n) (@lem2713823)). Qed.
Lemma lem2713825 (n : int) (h1 : term540 n) : term710 n.
Proof. exact (EQ_MP (@lem2713824 n) (@lem2713685 n h1)). Qed.
Lemma lem2713827 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2713828 : term581 = term257.
Proof. exact (@lem2713827 term32 term66). Qed.
Lemma lem2713830 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713831 : term66 = term210.
Proof. exact (@lem2713830 term67). Qed.
Lemma lem2713833 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713834 : term32 = term137.
Proof. exact (@lem2713833 (NUMERAL 0)). Qed.
Lemma lem2713835 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713836 : term582 = term583.
Proof. exact (MK_COMB (@lem2713835) (@lem2713834)). Qed.
Lemma lem2713837 : term257 = term584.
Proof. exact (MK_COMB (@lem2713836) (@lem2713831)). Qed.
Lemma lem2713838 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2713840 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713841 : term257 = term258.
Proof. exact (@lem2713840 (NUMERAL 0) term67). Qed.
Lemma lem2713842 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713843 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713844 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713843 h1) (fun h1 : term258 = True => @lem2713842)). Qed.
Lemma lem2713845 : term258 = True.
Proof. exact (EQ_MP (@lem2713844) (@lem2713842)). Qed.
Lemma lem2713846 : term257 = True.
Proof. exact (TRANS (@lem2713841) (@lem2713845)). Qed.
Lemma lem2713847 : True = term257.
Proof. exact (SYM (@lem2713846)). Qed.
Lemma lem2713848 : term257.
Proof. exact (EQ_MP (@lem2713847) (@lem0)). Qed.
Lemma lem2713849 : term586.
Proof. exact (@lem2713838 (@lem2713848)). Qed.
Lemma lem2713851 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713852 : term257 = term258.
Proof. exact (@lem2713851 (NUMERAL 0) term67). Qed.
Lemma lem2713853 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713854 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713855 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713854 h1) (fun h1 : term258 = True => @lem2713853)). Qed.
Lemma lem2713856 : term258 = True.
Proof. exact (EQ_MP (@lem2713855) (@lem2713853)). Qed.
Lemma lem2713857 : term257 = True.
Proof. exact (TRANS (@lem2713852) (@lem2713856)). Qed.
Lemma lem2713858 : True = term257.
Proof. exact (SYM (@lem2713857)). Qed.
Lemma lem2713859 : term257.
Proof. exact (EQ_MP (@lem2713858) (@lem0)). Qed.
Lemma lem2713860 : term584 = term587.
Proof. exact (@lem2713849 (@lem2713859)). Qed.
Lemma lem2713862 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713863 : term149 = term150.
Proof. exact (@lem2713862 term67 term67). Qed.
Lemma lem2713864 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713865 : term152 = term67.
Proof. exact (EQ_MP (@lem2713864) (@lem940073)). Qed.
Lemma lem2713866 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713867 : term150 = term66.
Proof. exact (MK_COMB (@lem2713866) (@lem2713865)). Qed.
Lemma lem2713868 : term149 = term66.
Proof. exact (TRANS (@lem2713863) (@lem2713867)). Qed.
Lemma lem2713870 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713871 : term269 = term32.
Proof. exact (@lem2713870 term67). Qed.
Lemma lem2713872 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2713873 : term588 = term582.
Proof. exact (MK_COMB (@lem2713872) (@lem2713871)). Qed.
Lemma lem2713874 : term587 = term257.
Proof. exact (MK_COMB (@lem2713873) (@lem2713868)). Qed.
Lemma lem2713876 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713877 : term257 = term258.
Proof. exact (@lem2713876 (NUMERAL 0) term67). Qed.
Lemma lem2713878 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713879 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713880 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713879 h1) (fun h1 : term258 = True => @lem2713878)). Qed.
Lemma lem2713881 : term258 = True.
Proof. exact (EQ_MP (@lem2713880) (@lem2713878)). Qed.
Lemma lem2713882 : term257 = True.
Proof. exact (TRANS (@lem2713877) (@lem2713881)). Qed.
Lemma lem2713883 : term587 = True.
Proof. exact (TRANS (@lem2713874) (@lem2713882)). Qed.
Lemma lem2713884 : term584 = True.
Proof. exact (TRANS (@lem2713860) (@lem2713883)). Qed.
Lemma lem2713885 : term257 = True.
Proof. exact (TRANS (@lem2713837) (@lem2713884)). Qed.
Lemma lem2713886 : term581 = True.
Proof. exact (TRANS (@lem2713828) (@lem2713885)). Qed.
Lemma lem2713887 : True = term581.
Proof. exact (SYM (@lem2713886)). Qed.
Lemma lem2713888 : term581.
Proof. exact (EQ_MP (@lem2713887) (@lem0)). Qed.
Lemma lem2713889 (n : int) (h1 : term540 n) : term889 n.
Proof. exact (conj (@lem2713888) (@lem2713301 n h1)). Qed.
Lemma lem2713891 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2713892 (n : int) : term890 n.
Proof. exact (@lem2713891 term66 (term297 n)). Qed.
Lemma lem2713893 (n : int) (h1 : term540 n) : term891 n.
Proof. exact (@lem2713892 n (@lem2713889 n h1)). Qed.
Lemma lem2713894 (n : int) : (term892 n) = (term297 n).
Proof. exact (@lem1982733 (term297 n)). Qed.
Lemma lem2713895 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2713896 (n : int) : (term893 n) = (term299 n).
Proof. exact (MK_COMB (@lem2713895) (@lem2713894 n)). Qed.
Lemma lem2713897 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713898 (n : int) : (term891 n) = (term300 n).
Proof. exact (MK_COMB (@lem2713896 n) (@lem2713897)). Qed.
Lemma lem2713899 (n : int) (h1 : term540 n) : term300 n.
Proof. exact (EQ_MP (@lem2713898 n) (@lem2713893 n h1)). Qed.
Lemma lem2713901 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2713902 (n : int) : term596 n.
Proof. exact (@lem2713901 (term195 n)). Qed.
Lemma lem2713903 (n : int) (h1 : term540 n) : term597 n.
Proof. exact (@lem2713902 n (@lem2713298 n h1)). Qed.
Lemma lem2713904 (n : int) (h1 : term540 n) : term715 n.
Proof. exact (@lem2713903 n h1 term66). Qed.
Lemma lem2713905 (n : int) : (term715 n) = ((term716 n) = term32).
Proof. exact (eq_refl (term715 n)). Qed.
Lemma lem2713906 (n : int) (h1 : term540 n) : (term716 n) = term32.
Proof. exact (EQ_MP (@lem2713905 n) (@lem2713904 n h1)). Qed.
Lemma lem2713907 (n : int) : (term716 n) = (term195 n).
Proof. exact (@lem1982733 (term195 n)). Qed.
Lemma lem2713908 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2713909 (n : int) : (term717 n) = (term197 n).
Proof. exact (MK_COMB (@lem2713908) (@lem2713907 n)). Qed.
Lemma lem2713910 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2713911 (n : int) : ((term716 n) = term32) = ((term195 n) = term32).
Proof. exact (MK_COMB (@lem2713909 n) (@lem2713910)). Qed.
Lemma lem2713912 (n : int) (h1 : term540 n) : (term195 n) = term32.
Proof. exact (EQ_MP (@lem2713911 n) (@lem2713906 n h1)). Qed.
Lemma lem2713913 (n : int) (h1 : term540 n) : term894 n.
Proof. exact (conj (@lem2713912 n h1) (@lem2713899 n h1)). Qed.
Lemma lem2713915 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2713916 (n : int) : term895 n.
Proof. exact (@lem2713915 (term195 n) (term297 n)). Qed.
Lemma lem2713917 (n : int) (h1 : term540 n) : term896 n.
Proof. exact (@lem2713916 n (@lem2713913 n h1)). Qed.
Lemma lem2713918 (n : int) : (term897 n) = (term898 n).
Proof. exact (@lem1982755 (real_of_int n) (term193 n) (term297 n)). Qed.
Lemma lem2713919 (n : int) : (term899 n) = (term900 n).
Proof. exact (@lem1982755 (term190 n) (term170 n) (term297 n)). Qed.
Lemma lem2713920 (n : int) : (term901 n) = (term902 n).
Proof. exact (@lem1982763 (term170 n) (term48 n) term184). Qed.
Lemma lem2713921 (n : int) : (term725 n) = (term638 n).
Proof. exact (@lem1982713 term140 (term48 n)). Qed.
Lemma lem2713923 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2713924 : term66 = term210.
Proof. exact (@lem2713923 term67). Qed.
Lemma lem2713926 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2713927 : term140 = term141.
Proof. exact (@lem2713926 term67). Qed.
Lemma lem2713928 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713929 : term639 = term640.
Proof. exact (MK_COMB (@lem2713928) (@lem2713927)). Qed.
Lemma lem2713930 : term641 = term642.
Proof. exact (MK_COMB (@lem2713929) (@lem2713924)). Qed.
Lemma lem2713931 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2713933 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713934 : term257 = term258.
Proof. exact (@lem2713933 (NUMERAL 0) term67). Qed.
Lemma lem2713935 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713936 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713937 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713936 h1) (fun h1 : term258 = True => @lem2713935)). Qed.
Lemma lem2713938 : term258 = True.
Proof. exact (EQ_MP (@lem2713937) (@lem2713935)). Qed.
Lemma lem2713939 : term257 = True.
Proof. exact (TRANS (@lem2713934) (@lem2713938)). Qed.
Lemma lem2713940 : True = term257.
Proof. exact (SYM (@lem2713939)). Qed.
Lemma lem2713941 : term257.
Proof. exact (EQ_MP (@lem2713940) (@lem0)). Qed.
Lemma lem2713942 : term644.
Proof. exact (@lem2713931 (@lem2713941)). Qed.
Lemma lem2713944 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713945 : term257 = term258.
Proof. exact (@lem2713944 (NUMERAL 0) term67). Qed.
Lemma lem2713946 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713947 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713948 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713947 h1) (fun h1 : term258 = True => @lem2713946)). Qed.
Lemma lem2713949 : term258 = True.
Proof. exact (EQ_MP (@lem2713948) (@lem2713946)). Qed.
Lemma lem2713950 : term257 = True.
Proof. exact (TRANS (@lem2713945) (@lem2713949)). Qed.
Lemma lem2713951 : True = term257.
Proof. exact (SYM (@lem2713950)). Qed.
Lemma lem2713952 : term257.
Proof. exact (EQ_MP (@lem2713951) (@lem0)). Qed.
Lemma lem2713953 : term645.
Proof. exact (@lem2713942 (@lem2713952)). Qed.
Lemma lem2713955 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2713956 : term257 = term258.
Proof. exact (@lem2713955 (NUMERAL 0) term67). Qed.
Lemma lem2713957 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2713958 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2713959 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2713958 h1) (fun h1 : term258 = True => @lem2713957)). Qed.
Lemma lem2713960 : term258 = True.
Proof. exact (EQ_MP (@lem2713959) (@lem2713957)). Qed.
Lemma lem2713961 : term257 = True.
Proof. exact (TRANS (@lem2713956) (@lem2713960)). Qed.
Lemma lem2713962 : True = term257.
Proof. exact (SYM (@lem2713961)). Qed.
Lemma lem2713963 : term257.
Proof. exact (EQ_MP (@lem2713962) (@lem0)). Qed.
Lemma lem2713964 : term646.
Proof. exact (@lem2713953 (@lem2713963)). Qed.
Lemma lem2713966 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2713967 : term149 = term150.
Proof. exact (@lem2713966 term67 term67). Qed.
Lemma lem2713968 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713969 : term152 = term67.
Proof. exact (EQ_MP (@lem2713968) (@lem940073)). Qed.
Lemma lem2713970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713971 : term150 = term66.
Proof. exact (MK_COMB (@lem2713970) (@lem2713969)). Qed.
Lemma lem2713972 : term149 = term66.
Proof. exact (TRANS (@lem2713967) (@lem2713971)). Qed.
Lemma lem2713974 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2713975 : term211 = term214.
Proof. exact (@lem2713974 term67 term67). Qed.
Lemma lem2713976 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2713977 : term152 = term67.
Proof. exact (EQ_MP (@lem2713976) (@lem940073)). Qed.
Lemma lem2713978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2713979 : term150 = term66.
Proof. exact (MK_COMB (@lem2713978) (@lem2713977)). Qed.
Lemma lem2713980 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2713981 : term214 = term140.
Proof. exact (MK_COMB (@lem2713980) (@lem2713979)). Qed.
Lemma lem2713982 : term211 = term140.
Proof. exact (TRANS (@lem2713975) (@lem2713981)). Qed.
Lemma lem2713983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2713984 : term647 = term639.
Proof. exact (MK_COMB (@lem2713983) (@lem2713982)). Qed.
Lemma lem2713985 : term648 = term641.
Proof. exact (MK_COMB (@lem2713984) (@lem2713972)). Qed.
Lemma lem2713987 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2713988 : term641 = term32.
Proof. exact (@lem2713987 term67). Qed.
Lemma lem2713989 : term648 = term32.
Proof. exact (TRANS (@lem2713985) (@lem2713988)). Qed.
Lemma lem2713990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2713991 : term650 = term267.
Proof. exact (MK_COMB (@lem2713990) (@lem2713989)). Qed.
Lemma lem2713992 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2713993 : term651 = term269.
Proof. exact (MK_COMB (@lem2713991) (@lem2713992)). Qed.
Lemma lem2713995 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2713996 : term269 = term32.
Proof. exact (@lem2713995 term67). Qed.
Lemma lem2713997 : term651 = term32.
Proof. exact (TRANS (@lem2713993) (@lem2713996)). Qed.
Lemma lem2713999 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714000 : term149 = term150.
Proof. exact (@lem2713999 term67 term67). Qed.
Lemma lem2714001 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714002 : term152 = term67.
Proof. exact (EQ_MP (@lem2714001) (@lem940073)). Qed.
Lemma lem2714003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714004 : term150 = term66.
Proof. exact (MK_COMB (@lem2714003) (@lem2714002)). Qed.
Lemma lem2714005 : term149 = term66.
Proof. exact (TRANS (@lem2714000) (@lem2714004)). Qed.
Lemma lem2714006 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2714007 : term271 = term269.
Proof. exact (MK_COMB (@lem2714006) (@lem2714005)). Qed.
Lemma lem2714009 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714010 : term269 = term32.
Proof. exact (@lem2714009 term67). Qed.
Lemma lem2714011 : term271 = term32.
Proof. exact (TRANS (@lem2714007) (@lem2714010)). Qed.
Lemma lem2714012 : term32 = term271.
Proof. exact (SYM (@lem2714011)). Qed.
Lemma lem2714013 : term651 = term271.
Proof. exact (TRANS (@lem2713997) (@lem2714012)). Qed.
Lemma lem2714014 : term642 = term137.
Proof. exact (@lem2713964 (@lem2714013)). Qed.
Lemma lem2714015 : term641 = term137.
Proof. exact (TRANS (@lem2713930) (@lem2714014)). Qed.
Lemma lem2714017 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2714018 : term137 = term32.
Proof. exact (@lem2714017 term32). Qed.
Lemma lem2714019 : term641 = term32.
Proof. exact (TRANS (@lem2714015) (@lem2714018)). Qed.
Lemma lem2714020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714021 : term652 = term267.
Proof. exact (MK_COMB (@lem2714020) (@lem2714019)). Qed.
Lemma lem2714022 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2714023 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2714021) (@lem2714022 n)). Qed.
Lemma lem2714024 (n : int) : (term725 n) = (term653 n).
Proof. exact (TRANS (@lem2713921 n) (@lem2714023 n)). Qed.
Lemma lem2714025 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2714026 (n : int) : (term725 n) = term32.
Proof. exact (TRANS (@lem2714024 n) (@lem2714025 n)). Qed.
Lemma lem2714027 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714028 (n : int) : (term861 n) = term102.
Proof. exact (MK_COMB (@lem2714027) (@lem2714026 n)). Qed.
Lemma lem2714029 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2714030 (n : int) : (term902 n) = term422.
Proof. exact (MK_COMB (@lem2714028 n) (@lem2714029)). Qed.
Lemma lem2714031 (n : int) : (term901 n) = term422.
Proof. exact (TRANS (@lem2713920 n) (@lem2714030 n)). Qed.
Lemma lem2714032 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2714033 (n : int) : (term901 n) = term184.
Proof. exact (TRANS (@lem2714031 n) (@lem2714032)). Qed.
Lemma lem2714034 (n : int) : (term192 n) = (term192 n).
Proof. exact (eq_refl (term192 n)). Qed.
Lemma lem2714035 (n : int) : (term900 n) = (term903 n).
Proof. exact (MK_COMB (@lem2714034 n) (@lem2714033 n)). Qed.
Lemma lem2714036 (n : int) : (term899 n) = (term903 n).
Proof. exact (TRANS (@lem2713919 n) (@lem2714035 n)). Qed.
Lemma lem2714037 (n : int) : (term194 n) = (term194 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem2714038 (n : int) : (term898 n) = (term904 n).
Proof. exact (MK_COMB (@lem2714037 n) (@lem2714036 n)). Qed.
Lemma lem2714039 (n : int) : (term897 n) = (term904 n).
Proof. exact (TRANS (@lem2713918 n) (@lem2714038 n)). Qed.
Lemma lem2714040 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2714041 (n : int) : (term905 n) = (term906 n).
Proof. exact (MK_COMB (@lem2714040) (@lem2714039 n)). Qed.
Lemma lem2714042 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2714043 (n : int) : (term896 n) = (term907 n).
Proof. exact (MK_COMB (@lem2714041 n) (@lem2714042)). Qed.
Lemma lem2714044 (n : int) (h1 : term540 n) : term907 n.
Proof. exact (EQ_MP (@lem2714043 n) (@lem2713917 n h1)). Qed.
Lemma lem2714046 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2714047 : term661 = term662.
Proof. exact (@lem2714046 term32 term28). Qed.
Lemma lem2714049 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714050 : term28 = term173.
Proof. exact (@lem2714049 term29). Qed.
Lemma lem2714052 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714053 : term32 = term137.
Proof. exact (@lem2714052 (NUMERAL 0)). Qed.
Lemma lem2714054 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2714055 : term582 = term583.
Proof. exact (MK_COMB (@lem2714054) (@lem2714053)). Qed.
Lemma lem2714056 : term662 = term663.
Proof. exact (MK_COMB (@lem2714055) (@lem2714050)). Qed.
Lemma lem2714057 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2714059 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714060 : term257 = term258.
Proof. exact (@lem2714059 (NUMERAL 0) term67). Qed.
Lemma lem2714061 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714062 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714063 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714062 h1) (fun h1 : term258 = True => @lem2714061)). Qed.
Lemma lem2714064 : term258 = True.
Proof. exact (EQ_MP (@lem2714063) (@lem2714061)). Qed.
Lemma lem2714065 : term257 = True.
Proof. exact (TRANS (@lem2714060) (@lem2714064)). Qed.
Lemma lem2714066 : True = term257.
Proof. exact (SYM (@lem2714065)). Qed.
Lemma lem2714067 : term257.
Proof. exact (EQ_MP (@lem2714066) (@lem0)). Qed.
Lemma lem2714068 : term665.
Proof. exact (@lem2714057 (@lem2714067)). Qed.
Lemma lem2714070 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714071 : term257 = term258.
Proof. exact (@lem2714070 (NUMERAL 0) term67). Qed.
Lemma lem2714072 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714073 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714074 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714073 h1) (fun h1 : term258 = True => @lem2714072)). Qed.
Lemma lem2714075 : term258 = True.
Proof. exact (EQ_MP (@lem2714074) (@lem2714072)). Qed.
Lemma lem2714076 : term257 = True.
Proof. exact (TRANS (@lem2714071) (@lem2714075)). Qed.
Lemma lem2714077 : True = term257.
Proof. exact (SYM (@lem2714076)). Qed.
Lemma lem2714078 : term257.
Proof. exact (EQ_MP (@lem2714077) (@lem0)). Qed.
Lemma lem2714079 : term663 = term666.
Proof. exact (@lem2714068 (@lem2714078)). Qed.
Lemma lem2714081 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714082 : term289 = term290.
Proof. exact (@lem2714081 term29 term67). Qed.
Lemma lem2714083 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2714084 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2714085 : term292 = term29.
Proof. exact (EQ_MP (@lem2714084) (@lem2714083)). Qed.
Lemma lem2714086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714087 : term290 = term28.
Proof. exact (MK_COMB (@lem2714086) (@lem2714085)). Qed.
Lemma lem2714088 : term289 = term28.
Proof. exact (TRANS (@lem2714082) (@lem2714087)). Qed.
Lemma lem2714090 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714091 : term269 = term32.
Proof. exact (@lem2714090 term67). Qed.
Lemma lem2714092 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2714093 : term588 = term582.
Proof. exact (MK_COMB (@lem2714092) (@lem2714091)). Qed.
Lemma lem2714094 : term666 = term662.
Proof. exact (MK_COMB (@lem2714093) (@lem2714088)). Qed.
Lemma lem2714096 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714097 : term662 = term667.
Proof. exact (@lem2714096 (NUMERAL 0) term29). Qed.
Lemma lem2714098 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2714099 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2714100 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2714099 h1) (fun h1 : term667 = True => @lem2714098)). Qed.
Lemma lem2714101 : term667 = True.
Proof. exact (EQ_MP (@lem2714100) (@lem2714098)). Qed.
Lemma lem2714102 : term662 = True.
Proof. exact (TRANS (@lem2714097) (@lem2714101)). Qed.
Lemma lem2714103 : term666 = True.
Proof. exact (TRANS (@lem2714094) (@lem2714102)). Qed.
Lemma lem2714104 : term663 = True.
Proof. exact (TRANS (@lem2714079) (@lem2714103)). Qed.
Lemma lem2714105 : term662 = True.
Proof. exact (TRANS (@lem2714056) (@lem2714104)). Qed.
Lemma lem2714106 : term661 = True.
Proof. exact (TRANS (@lem2714047) (@lem2714105)). Qed.
Lemma lem2714107 : True = term661.
Proof. exact (SYM (@lem2714106)). Qed.
Lemma lem2714108 : term661.
Proof. exact (EQ_MP (@lem2714107) (@lem0)). Qed.
Lemma lem2714109 (n : int) (h1 : term540 n) : term908 n.
Proof. exact (conj (@lem2714108) (@lem2714044 n h1)). Qed.
Lemma lem2714111 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2714112 (n : int) : term909 n.
Proof. exact (@lem2714111 term28 (term904 n)). Qed.
Lemma lem2714113 (n : int) (h1 : term540 n) : term910 n.
Proof. exact (@lem2714112 n (@lem2714109 n h1)). Qed.
Lemma lem2714114 (n : int) : (term911 n) = (term912 n).
Proof. exact (@lem1982781 (real_of_int n) term28 (term903 n)). Qed.
Lemma lem2714115 (n : int) : (term913 n) = (term914 n).
Proof. exact (@lem1982781 (term190 n) term28 term184). Qed.
Lemma lem2714117 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714118 : term184 = term187.
Proof. exact (@lem2714117 term29). Qed.
Lemma lem2714120 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714121 : term28 = term173.
Proof. exact (@lem2714120 term29). Qed.
Lemma lem2714122 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714123 : term287 = term675.
Proof. exact (MK_COMB (@lem2714122) (@lem2714121)). Qed.
Lemma lem2714124 : term738 = term739.
Proof. exact (MK_COMB (@lem2714123) (@lem2714118)). Qed.
Lemma lem2714125 : term739 = term740.
Proof. exact (@lem1981613 term28 term184 term66 term66). Qed.
Lemma lem2714127 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714128 : term149 = term150.
Proof. exact (@lem2714127 term67 term67). Qed.
Lemma lem2714129 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714130 : term152 = term67.
Proof. exact (EQ_MP (@lem2714129) (@lem940073)). Qed.
Lemma lem2714131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714132 : term150 = term66.
Proof. exact (MK_COMB (@lem2714131) (@lem2714130)). Qed.
Lemma lem2714133 : term149 = term66.
Proof. exact (TRANS (@lem2714128) (@lem2714132)). Qed.
Lemma lem2714135 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2714136 : term738 = term741.
Proof. exact (@lem2714135 term29 term29). Qed.
Lemma lem2714137 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714138 : term687 = term688.
Proof. exact (EQ_MP (@lem2714137) (@lem940073)). Qed.
Lemma lem2714139 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2714140 : term689 = term690.
Proof. exact (EQ_MP (@lem2714139) (@lem2714138)). Qed.
Lemma lem2714141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714142 : term686 = term691.
Proof. exact (MK_COMB (@lem2714141) (@lem2714140)). Qed.
Lemma lem2714143 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714144 : term741 = term742.
Proof. exact (MK_COMB (@lem2714143) (@lem2714142)). Qed.
Lemma lem2714145 : term738 = term742.
Proof. exact (TRANS (@lem2714136) (@lem2714144)). Qed.
Lemma lem2714146 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2714147 : term743 = term744.
Proof. exact (MK_COMB (@lem2714146) (@lem2714145)). Qed.
Lemma lem2714148 : term740 = term745.
Proof. exact (MK_COMB (@lem2714147) (@lem2714133)). Qed.
Lemma lem2714149 : term739 = term745.
Proof. exact (TRANS (@lem2714125) (@lem2714148)). Qed.
Lemma lem2714150 : term738 = term745.
Proof. exact (TRANS (@lem2714124) (@lem2714149)). Qed.
Lemma lem2714152 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2714153 : term745 = term742.
Proof. exact (@lem2714152 term742). Qed.
Lemma lem2714154 : term738 = term742.
Proof. exact (TRANS (@lem2714150) (@lem2714153)). Qed.
Lemma lem2714155 (n : int) : (term736 n) = (term737 n).
Proof. exact (@lem1982749 term28 term184 (term162 n)). Qed.
Lemma lem2714157 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714158 : term184 = term187.
Proof. exact (@lem2714157 term29). Qed.
Lemma lem2714160 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714161 : term28 = term173.
Proof. exact (@lem2714160 term29). Qed.
Lemma lem2714162 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714163 : term287 = term675.
Proof. exact (MK_COMB (@lem2714162) (@lem2714161)). Qed.
Lemma lem2714164 : term738 = term739.
Proof. exact (MK_COMB (@lem2714163) (@lem2714158)). Qed.
Lemma lem2714165 : term739 = term740.
Proof. exact (@lem1981613 term28 term184 term66 term66). Qed.
Lemma lem2714167 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714168 : term149 = term150.
Proof. exact (@lem2714167 term67 term67). Qed.
Lemma lem2714169 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714170 : term152 = term67.
Proof. exact (EQ_MP (@lem2714169) (@lem940073)). Qed.
Lemma lem2714171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714172 : term150 = term66.
Proof. exact (MK_COMB (@lem2714171) (@lem2714170)). Qed.
Lemma lem2714173 : term149 = term66.
Proof. exact (TRANS (@lem2714168) (@lem2714172)). Qed.
Lemma lem2714175 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2714176 : term738 = term741.
Proof. exact (@lem2714175 term29 term29). Qed.
Lemma lem2714177 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714178 : term687 = term688.
Proof. exact (EQ_MP (@lem2714177) (@lem940073)). Qed.
Lemma lem2714179 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2714180 : term689 = term690.
Proof. exact (EQ_MP (@lem2714179) (@lem2714178)). Qed.
Lemma lem2714181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714182 : term686 = term691.
Proof. exact (MK_COMB (@lem2714181) (@lem2714180)). Qed.
Lemma lem2714183 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714184 : term741 = term742.
Proof. exact (MK_COMB (@lem2714183) (@lem2714182)). Qed.
Lemma lem2714185 : term738 = term742.
Proof. exact (TRANS (@lem2714176) (@lem2714184)). Qed.
Lemma lem2714186 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2714187 : term743 = term744.
Proof. exact (MK_COMB (@lem2714186) (@lem2714185)). Qed.
Lemma lem2714188 : term740 = term745.
Proof. exact (MK_COMB (@lem2714187) (@lem2714173)). Qed.
Lemma lem2714189 : term739 = term745.
Proof. exact (TRANS (@lem2714165) (@lem2714188)). Qed.
Lemma lem2714190 : term738 = term745.
Proof. exact (TRANS (@lem2714164) (@lem2714189)). Qed.
Lemma lem2714192 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2714193 : term745 = term742.
Proof. exact (@lem2714192 term742). Qed.
Lemma lem2714194 : term738 = term742.
Proof. exact (TRANS (@lem2714190) (@lem2714193)). Qed.
Lemma lem2714195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714196 : term746 = term747.
Proof. exact (MK_COMB (@lem2714195) (@lem2714194)). Qed.
Lemma lem2714197 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2714198 (n : int) : (term737 n) = (term748 n).
Proof. exact (MK_COMB (@lem2714196) (@lem2714197 n)). Qed.
Lemma lem2714199 (n : int) : (term736 n) = (term748 n).
Proof. exact (TRANS (@lem2714155 n) (@lem2714198 n)). Qed.
Lemma lem2714200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714201 (n : int) : (term874 n) = (term875 n).
Proof. exact (MK_COMB (@lem2714200) (@lem2714199 n)). Qed.
Lemma lem2714202 (n : int) : (term914 n) = (term915 n).
Proof. exact (MK_COMB (@lem2714201 n) (@lem2714154)). Qed.
Lemma lem2714203 (n : int) : (term913 n) = (term915 n).
Proof. exact (TRANS (@lem2714115 n) (@lem2714202 n)). Qed.
Lemma lem2714206 (n : int) : (term749 n) = (term749 n).
Proof. exact (eq_refl (term749 n)). Qed.
Lemma lem2714207 (n : int) : (term912 n) = (term916 n).
Proof. exact (MK_COMB (@lem2714206 n) (@lem2714203 n)). Qed.
Lemma lem2714208 (n : int) : (term911 n) = (term916 n).
Proof. exact (TRANS (@lem2714114 n) (@lem2714207 n)). Qed.
Lemma lem2714209 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2714210 (n : int) : (term917 n) = (term918 n).
Proof. exact (MK_COMB (@lem2714209) (@lem2714208 n)). Qed.
Lemma lem2714211 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2714212 (n : int) : (term910 n) = (term919 n).
Proof. exact (MK_COMB (@lem2714210 n) (@lem2714211)). Qed.
Lemma lem2714213 (n : int) (h1 : term540 n) : term919 n.
Proof. exact (EQ_MP (@lem2714212 n) (@lem2714113 n h1)). Qed.
Lemma lem2714214 (n : int) (h1 : term540 n) : term920 n.
Proof. exact (conj (@lem2714213 n h1) (@lem2713825 n h1)). Qed.
Lemma lem2714216 (x : real) (y : real) : term755 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2714217 (n : int) : term921 n.
Proof. exact (@lem2714216 (term916 n) (term707 n)). Qed.
Lemma lem2714218 (n : int) (h1 : term540 n) : term922 n.
Proof. exact (@lem2714217 n (@lem2714214 n h1)). Qed.
Lemma lem2714219 (n : int) : (term923 n) = (term924 n).
Proof. exact (@lem1982753 (term760 n) (term704 n) (term915 n) (term700 n)). Qed.
Lemma lem2714220 (n : int) : (term761 n) = (term762 n).
Proof. exact (@lem1982711 term28 term184 (real_of_int n)). Qed.
Lemma lem2714222 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714223 : term184 = term187.
Proof. exact (@lem2714222 term29). Qed.
Lemma lem2714225 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714226 : term28 = term173.
Proof. exact (@lem2714225 term29). Qed.
Lemma lem2714227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714228 : term157 = term373.
Proof. exact (MK_COMB (@lem2714227) (@lem2714226)). Qed.
Lemma lem2714229 : term763 = term764.
Proof. exact (MK_COMB (@lem2714228) (@lem2714223)). Qed.
Lemma lem2714230 : term765.
Proof. exact (@lem1981473 term28 term66 term184 term66 term32 term66). Qed.
Lemma lem2714232 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714233 : term257 = term258.
Proof. exact (@lem2714232 (NUMERAL 0) term67). Qed.
Lemma lem2714234 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714235 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714236 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714235 h1) (fun h1 : term258 = True => @lem2714234)). Qed.
Lemma lem2714237 : term258 = True.
Proof. exact (EQ_MP (@lem2714236) (@lem2714234)). Qed.
Lemma lem2714238 : term257 = True.
Proof. exact (TRANS (@lem2714233) (@lem2714237)). Qed.
Lemma lem2714239 : True = term257.
Proof. exact (SYM (@lem2714238)). Qed.
Lemma lem2714240 : term257.
Proof. exact (EQ_MP (@lem2714239) (@lem0)). Qed.
Lemma lem2714241 : term766.
Proof. exact (@lem2714230 (@lem2714240)). Qed.
Lemma lem2714243 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714244 : term257 = term258.
Proof. exact (@lem2714243 (NUMERAL 0) term67). Qed.
Lemma lem2714245 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714246 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714247 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714246 h1) (fun h1 : term258 = True => @lem2714245)). Qed.
Lemma lem2714248 : term258 = True.
Proof. exact (EQ_MP (@lem2714247) (@lem2714245)). Qed.
Lemma lem2714249 : term257 = True.
Proof. exact (TRANS (@lem2714244) (@lem2714248)). Qed.
Lemma lem2714250 : True = term257.
Proof. exact (SYM (@lem2714249)). Qed.
Lemma lem2714251 : term257.
Proof. exact (EQ_MP (@lem2714250) (@lem0)). Qed.
Lemma lem2714252 : term767.
Proof. exact (@lem2714241 (@lem2714251)). Qed.
Lemma lem2714254 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714255 : term257 = term258.
Proof. exact (@lem2714254 (NUMERAL 0) term67). Qed.
Lemma lem2714256 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714257 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714258 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714257 h1) (fun h1 : term258 = True => @lem2714256)). Qed.
Lemma lem2714259 : term258 = True.
Proof. exact (EQ_MP (@lem2714258) (@lem2714256)). Qed.
Lemma lem2714260 : term257 = True.
Proof. exact (TRANS (@lem2714255) (@lem2714259)). Qed.
Lemma lem2714261 : True = term257.
Proof. exact (SYM (@lem2714260)). Qed.
Lemma lem2714262 : term257.
Proof. exact (EQ_MP (@lem2714261) (@lem0)). Qed.
Lemma lem2714263 : term768.
Proof. exact (@lem2714252 (@lem2714262)). Qed.
Lemma lem2714265 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714266 : term439 = term440.
Proof. exact (@lem2714265 term29 term67). Qed.
Lemma lem2714267 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2714268 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2714269 : term292 = term29.
Proof. exact (EQ_MP (@lem2714268) (@lem2714267)). Qed.
Lemma lem2714270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714271 : term290 = term28.
Proof. exact (MK_COMB (@lem2714270) (@lem2714269)). Qed.
Lemma lem2714272 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714273 : term440 = term184.
Proof. exact (MK_COMB (@lem2714272) (@lem2714271)). Qed.
Lemma lem2714274 : term439 = term184.
Proof. exact (TRANS (@lem2714266) (@lem2714273)). Qed.
Lemma lem2714276 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714277 : term289 = term290.
Proof. exact (@lem2714276 term29 term67). Qed.
Lemma lem2714278 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2714279 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2714280 : term292 = term29.
Proof. exact (EQ_MP (@lem2714279) (@lem2714278)). Qed.
Lemma lem2714281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714282 : term290 = term28.
Proof. exact (MK_COMB (@lem2714281) (@lem2714280)). Qed.
Lemma lem2714283 : term289 = term28.
Proof. exact (TRANS (@lem2714277) (@lem2714282)). Qed.
Lemma lem2714284 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714285 : term380 = term157.
Proof. exact (MK_COMB (@lem2714284) (@lem2714283)). Qed.
Lemma lem2714286 : term769 = term763.
Proof. exact (MK_COMB (@lem2714285) (@lem2714274)). Qed.
Lemma lem2714288 (m : nat) : (term265 m) = term32.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2714289 : term763 = term32.
Proof. exact (@lem2714288 term29). Qed.
Lemma lem2714290 : term769 = term32.
Proof. exact (TRANS (@lem2714286) (@lem2714289)). Qed.
Lemma lem2714291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714292 : term770 = term267.
Proof. exact (MK_COMB (@lem2714291) (@lem2714290)). Qed.
Lemma lem2714293 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2714294 : term771 = term269.
Proof. exact (MK_COMB (@lem2714292) (@lem2714293)). Qed.
Lemma lem2714296 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714297 : term269 = term32.
Proof. exact (@lem2714296 term67). Qed.
Lemma lem2714298 : term771 = term32.
Proof. exact (TRANS (@lem2714294) (@lem2714297)). Qed.
Lemma lem2714300 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714301 : term149 = term150.
Proof. exact (@lem2714300 term67 term67). Qed.
Lemma lem2714302 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714303 : term152 = term67.
Proof. exact (EQ_MP (@lem2714302) (@lem940073)). Qed.
Lemma lem2714304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714305 : term150 = term66.
Proof. exact (MK_COMB (@lem2714304) (@lem2714303)). Qed.
Lemma lem2714306 : term149 = term66.
Proof. exact (TRANS (@lem2714301) (@lem2714305)). Qed.
Lemma lem2714307 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2714308 : term271 = term269.
Proof. exact (MK_COMB (@lem2714307) (@lem2714306)). Qed.
Lemma lem2714310 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714311 : term269 = term32.
Proof. exact (@lem2714310 term67). Qed.
Lemma lem2714312 : term271 = term32.
Proof. exact (TRANS (@lem2714308) (@lem2714311)). Qed.
Lemma lem2714313 : term32 = term271.
Proof. exact (SYM (@lem2714312)). Qed.
Lemma lem2714314 : term771 = term271.
Proof. exact (TRANS (@lem2714298) (@lem2714313)). Qed.
Lemma lem2714315 : term764 = term137.
Proof. exact (@lem2714263 (@lem2714314)). Qed.
Lemma lem2714316 : term763 = term137.
Proof. exact (TRANS (@lem2714229) (@lem2714315)). Qed.
Lemma lem2714318 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2714319 : term137 = term32.
Proof. exact (@lem2714318 term32). Qed.
Lemma lem2714320 : term763 = term32.
Proof. exact (TRANS (@lem2714316) (@lem2714319)). Qed.
Lemma lem2714321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714322 : term772 = term267.
Proof. exact (MK_COMB (@lem2714321) (@lem2714320)). Qed.
Lemma lem2714323 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2714324 (n : int) : (term762 n) = (term773 n).
Proof. exact (MK_COMB (@lem2714322) (@lem2714323 n)). Qed.
Lemma lem2714325 (n : int) : (term761 n) = (term773 n).
Proof. exact (TRANS (@lem2714220 n) (@lem2714324 n)). Qed.
Lemma lem2714326 (n : int) : (term773 n) = term32.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2714327 (n : int) : (term761 n) = term32.
Proof. exact (TRANS (@lem2714325 n) (@lem2714326 n)). Qed.
Lemma lem2714328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714329 (n : int) : (term774 n) = term102.
Proof. exact (MK_COMB (@lem2714328) (@lem2714327 n)). Qed.
Lemma lem2714330 (n : int) : (term925 n) = (term926 n).
Proof. exact (@lem1982753 (term748 n) (term697 n) term742 term184). Qed.
Lemma lem2714331 (n : int) : (term777 n) = (term778 n).
Proof. exact (@lem1982711 term742 term691 (term162 n)). Qed.
Lemma lem2714333 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714334 : term691 = term694.
Proof. exact (@lem2714333 term690). Qed.
Lemma lem2714336 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714337 : term742 = term745.
Proof. exact (@lem2714336 term690). Qed.
Lemma lem2714338 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714339 : term779 = term780.
Proof. exact (MK_COMB (@lem2714338) (@lem2714337)). Qed.
Lemma lem2714340 : term781 = term782.
Proof. exact (MK_COMB (@lem2714339) (@lem2714334)). Qed.
Lemma lem2714341 : term783.
Proof. exact (@lem1981473 term742 term66 term691 term66 term32 term66). Qed.
Lemma lem2714343 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714344 : term257 = term258.
Proof. exact (@lem2714343 (NUMERAL 0) term67). Qed.
Lemma lem2714345 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714346 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714347 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714346 h1) (fun h1 : term258 = True => @lem2714345)). Qed.
Lemma lem2714348 : term258 = True.
Proof. exact (EQ_MP (@lem2714347) (@lem2714345)). Qed.
Lemma lem2714349 : term257 = True.
Proof. exact (TRANS (@lem2714344) (@lem2714348)). Qed.
Lemma lem2714350 : True = term257.
Proof. exact (SYM (@lem2714349)). Qed.
Lemma lem2714351 : term257.
Proof. exact (EQ_MP (@lem2714350) (@lem0)). Qed.
Lemma lem2714352 : term784.
Proof. exact (@lem2714341 (@lem2714351)). Qed.
Lemma lem2714354 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714355 : term257 = term258.
Proof. exact (@lem2714354 (NUMERAL 0) term67). Qed.
Lemma lem2714356 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714357 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714358 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714357 h1) (fun h1 : term258 = True => @lem2714356)). Qed.
Lemma lem2714359 : term258 = True.
Proof. exact (EQ_MP (@lem2714358) (@lem2714356)). Qed.
Lemma lem2714360 : term257 = True.
Proof. exact (TRANS (@lem2714355) (@lem2714359)). Qed.
Lemma lem2714361 : True = term257.
Proof. exact (SYM (@lem2714360)). Qed.
Lemma lem2714362 : term257.
Proof. exact (EQ_MP (@lem2714361) (@lem0)). Qed.
Lemma lem2714363 : term785.
Proof. exact (@lem2714352 (@lem2714362)). Qed.
Lemma lem2714365 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714366 : term257 = term258.
Proof. exact (@lem2714365 (NUMERAL 0) term67). Qed.
Lemma lem2714367 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714368 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714369 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714368 h1) (fun h1 : term258 = True => @lem2714367)). Qed.
Lemma lem2714370 : term258 = True.
Proof. exact (EQ_MP (@lem2714369) (@lem2714367)). Qed.
Lemma lem2714371 : term257 = True.
Proof. exact (TRANS (@lem2714366) (@lem2714370)). Qed.
Lemma lem2714372 : True = term257.
Proof. exact (SYM (@lem2714371)). Qed.
Lemma lem2714373 : term257.
Proof. exact (EQ_MP (@lem2714372) (@lem0)). Qed.
Lemma lem2714374 : term786.
Proof. exact (@lem2714363 (@lem2714373)). Qed.
Lemma lem2714376 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714377 : term787 = term788.
Proof. exact (@lem2714376 term690 term67). Qed.
Lemma lem2714378 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2714379 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2714380 : term790 = term690.
Proof. exact (EQ_MP (@lem2714379) (@lem2714378)). Qed.
Lemma lem2714381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714382 : term788 = term691.
Proof. exact (MK_COMB (@lem2714381) (@lem2714380)). Qed.
Lemma lem2714383 : term787 = term691.
Proof. exact (TRANS (@lem2714377) (@lem2714382)). Qed.
Lemma lem2714385 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714386 : term791 = term792.
Proof. exact (@lem2714385 term690 term67). Qed.
Lemma lem2714387 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2714388 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2714389 : term790 = term690.
Proof. exact (EQ_MP (@lem2714388) (@lem2714387)). Qed.
Lemma lem2714390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714391 : term788 = term691.
Proof. exact (MK_COMB (@lem2714390) (@lem2714389)). Qed.
Lemma lem2714392 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714393 : term792 = term742.
Proof. exact (MK_COMB (@lem2714392) (@lem2714391)). Qed.
Lemma lem2714394 : term791 = term742.
Proof. exact (TRANS (@lem2714386) (@lem2714393)). Qed.
Lemma lem2714395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714396 : term793 = term779.
Proof. exact (MK_COMB (@lem2714395) (@lem2714394)). Qed.
Lemma lem2714397 : term794 = term781.
Proof. exact (MK_COMB (@lem2714396) (@lem2714383)). Qed.
Lemma lem2714399 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2714400 : term781 = term32.
Proof. exact (@lem2714399 term690). Qed.
Lemma lem2714401 : term794 = term32.
Proof. exact (TRANS (@lem2714397) (@lem2714400)). Qed.
Lemma lem2714402 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714403 : term795 = term267.
Proof. exact (MK_COMB (@lem2714402) (@lem2714401)). Qed.
Lemma lem2714404 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2714405 : term796 = term269.
Proof. exact (MK_COMB (@lem2714403) (@lem2714404)). Qed.
Lemma lem2714407 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714408 : term269 = term32.
Proof. exact (@lem2714407 term67). Qed.
Lemma lem2714409 : term796 = term32.
Proof. exact (TRANS (@lem2714405) (@lem2714408)). Qed.
Lemma lem2714411 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714412 : term149 = term150.
Proof. exact (@lem2714411 term67 term67). Qed.
Lemma lem2714413 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714414 : term152 = term67.
Proof. exact (EQ_MP (@lem2714413) (@lem940073)). Qed.
Lemma lem2714415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714416 : term150 = term66.
Proof. exact (MK_COMB (@lem2714415) (@lem2714414)). Qed.
Lemma lem2714417 : term149 = term66.
Proof. exact (TRANS (@lem2714412) (@lem2714416)). Qed.
Lemma lem2714418 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2714419 : term271 = term269.
Proof. exact (MK_COMB (@lem2714418) (@lem2714417)). Qed.
Lemma lem2714421 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714422 : term269 = term32.
Proof. exact (@lem2714421 term67). Qed.
Lemma lem2714423 : term271 = term32.
Proof. exact (TRANS (@lem2714419) (@lem2714422)). Qed.
Lemma lem2714424 : term32 = term271.
Proof. exact (SYM (@lem2714423)). Qed.
Lemma lem2714425 : term796 = term271.
Proof. exact (TRANS (@lem2714409) (@lem2714424)). Qed.
Lemma lem2714426 : term782 = term137.
Proof. exact (@lem2714374 (@lem2714425)). Qed.
Lemma lem2714427 : term781 = term137.
Proof. exact (TRANS (@lem2714340) (@lem2714426)). Qed.
Lemma lem2714429 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2714430 : term137 = term32.
Proof. exact (@lem2714429 term32). Qed.
Lemma lem2714431 : term781 = term32.
Proof. exact (TRANS (@lem2714427) (@lem2714430)). Qed.
Lemma lem2714432 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714433 : term797 = term267.
Proof. exact (MK_COMB (@lem2714432) (@lem2714431)). Qed.
Lemma lem2714434 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2714435 (n : int) : (term778 n) = (term798 n).
Proof. exact (MK_COMB (@lem2714433) (@lem2714434 n)). Qed.
Lemma lem2714436 (n : int) : (term777 n) = (term798 n).
Proof. exact (TRANS (@lem2714331 n) (@lem2714435 n)). Qed.
Lemma lem2714437 (n : int) : (term798 n) = term32.
Proof. exact (@lem1982719 (term162 n)). Qed.
Lemma lem2714438 (n : int) : (term777 n) = term32.
Proof. exact (TRANS (@lem2714436 n) (@lem2714437 n)). Qed.
Lemma lem2714439 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714440 (n : int) : (term799 n) = term102.
Proof. exact (MK_COMB (@lem2714439) (@lem2714438 n)). Qed.
Lemma lem2714442 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714443 : term184 = term187.
Proof. exact (@lem2714442 term29). Qed.
Lemma lem2714445 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714446 : term742 = term745.
Proof. exact (@lem2714445 term690). Qed.
Lemma lem2714447 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714448 : term779 = term780.
Proof. exact (MK_COMB (@lem2714447) (@lem2714446)). Qed.
Lemma lem2714449 : term927 = term928.
Proof. exact (MK_COMB (@lem2714448) (@lem2714443)). Qed.
Lemma lem2714450 : term929.
Proof. exact (@lem1981473 term742 term66 term184 term66 term930 term66). Qed.
Lemma lem2714452 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714453 : term257 = term258.
Proof. exact (@lem2714452 (NUMERAL 0) term67). Qed.
Lemma lem2714454 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714455 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714456 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714455 h1) (fun h1 : term258 = True => @lem2714454)). Qed.
Lemma lem2714457 : term258 = True.
Proof. exact (EQ_MP (@lem2714456) (@lem2714454)). Qed.
Lemma lem2714458 : term257 = True.
Proof. exact (TRANS (@lem2714453) (@lem2714457)). Qed.
Lemma lem2714459 : True = term257.
Proof. exact (SYM (@lem2714458)). Qed.
Lemma lem2714460 : term257.
Proof. exact (EQ_MP (@lem2714459) (@lem0)). Qed.
Lemma lem2714461 : term931.
Proof. exact (@lem2714450 (@lem2714460)). Qed.
Lemma lem2714463 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714464 : term257 = term258.
Proof. exact (@lem2714463 (NUMERAL 0) term67). Qed.
Lemma lem2714465 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714466 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714467 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714466 h1) (fun h1 : term258 = True => @lem2714465)). Qed.
Lemma lem2714468 : term258 = True.
Proof. exact (EQ_MP (@lem2714467) (@lem2714465)). Qed.
Lemma lem2714469 : term257 = True.
Proof. exact (TRANS (@lem2714464) (@lem2714468)). Qed.
Lemma lem2714470 : True = term257.
Proof. exact (SYM (@lem2714469)). Qed.
Lemma lem2714471 : term257.
Proof. exact (EQ_MP (@lem2714470) (@lem0)). Qed.
Lemma lem2714472 : term932.
Proof. exact (@lem2714461 (@lem2714471)). Qed.
Lemma lem2714474 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714475 : term257 = term258.
Proof. exact (@lem2714474 (NUMERAL 0) term67). Qed.
Lemma lem2714476 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714477 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714478 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714477 h1) (fun h1 : term258 = True => @lem2714476)). Qed.
Lemma lem2714479 : term258 = True.
Proof. exact (EQ_MP (@lem2714478) (@lem2714476)). Qed.
Lemma lem2714480 : term257 = True.
Proof. exact (TRANS (@lem2714475) (@lem2714479)). Qed.
Lemma lem2714481 : True = term257.
Proof. exact (SYM (@lem2714480)). Qed.
Lemma lem2714482 : term257.
Proof. exact (EQ_MP (@lem2714481) (@lem0)). Qed.
Lemma lem2714483 : term933.
Proof. exact (@lem2714472 (@lem2714482)). Qed.
Lemma lem2714485 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714486 : term439 = term440.
Proof. exact (@lem2714485 term29 term67). Qed.
Lemma lem2714487 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2714488 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2714489 : term292 = term29.
Proof. exact (EQ_MP (@lem2714488) (@lem2714487)). Qed.
Lemma lem2714490 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714491 : term290 = term28.
Proof. exact (MK_COMB (@lem2714490) (@lem2714489)). Qed.
Lemma lem2714492 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714493 : term440 = term184.
Proof. exact (MK_COMB (@lem2714492) (@lem2714491)). Qed.
Lemma lem2714494 : term439 = term184.
Proof. exact (TRANS (@lem2714486) (@lem2714493)). Qed.
Lemma lem2714496 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714497 : term791 = term792.
Proof. exact (@lem2714496 term690 term67). Qed.
Lemma lem2714498 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2714499 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2714500 : term790 = term690.
Proof. exact (EQ_MP (@lem2714499) (@lem2714498)). Qed.
Lemma lem2714501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714502 : term788 = term691.
Proof. exact (MK_COMB (@lem2714501) (@lem2714500)). Qed.
Lemma lem2714503 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714504 : term792 = term742.
Proof. exact (MK_COMB (@lem2714503) (@lem2714502)). Qed.
Lemma lem2714505 : term791 = term742.
Proof. exact (TRANS (@lem2714497) (@lem2714504)). Qed.
Lemma lem2714506 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714507 : term793 = term779.
Proof. exact (MK_COMB (@lem2714506) (@lem2714505)). Qed.
Lemma lem2714508 : term934 = term927.
Proof. exact (MK_COMB (@lem2714507) (@lem2714494)). Qed.
Lemma lem2714509 : term927 = term935.
Proof. exact (@lem1367763 term690 term29). Qed.
Lemma lem2714510 : term936 = term937.
Proof. exact (@lem707079). Qed.
Lemma lem2714511 : (term936 = term937) = (term938 = term939).
Proof. exact (@lem1006570 term688 term181 term937). Qed.
Lemma lem2714512 : term938 = term939.
Proof. exact (EQ_MP (@lem2714511) (@lem2714510)). Qed.
Lemma lem2714513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714514 : term940 = term941.
Proof. exact (MK_COMB (@lem2714513) (@lem2714512)). Qed.
Lemma lem2714515 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714516 : term935 = term930.
Proof. exact (MK_COMB (@lem2714515) (@lem2714514)). Qed.
Lemma lem2714517 : term927 = term930.
Proof. exact (TRANS (@lem2714509) (@lem2714516)). Qed.
Lemma lem2714518 : term934 = term930.
Proof. exact (TRANS (@lem2714508) (@lem2714517)). Qed.
Lemma lem2714519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714520 : term942 = term943.
Proof. exact (MK_COMB (@lem2714519) (@lem2714518)). Qed.
Lemma lem2714521 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2714522 : term944 = term945.
Proof. exact (MK_COMB (@lem2714520) (@lem2714521)). Qed.
Lemma lem2714524 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714525 : term945 = term946.
Proof. exact (@lem2714524 term939 term67). Qed.
Lemma lem2714526 : term947 = term937.
Proof. exact (@lem996237 term937). Qed.
Lemma lem2714527 : (term947 = term937) = (term948 = term939).
Proof. exact (@lem1007663 term937 (BIT1 0) term937). Qed.
Lemma lem2714528 : term948 = term939.
Proof. exact (EQ_MP (@lem2714527) (@lem2714526)). Qed.
Lemma lem2714529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714530 : term949 = term941.
Proof. exact (MK_COMB (@lem2714529) (@lem2714528)). Qed.
Lemma lem2714531 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714532 : term946 = term930.
Proof. exact (MK_COMB (@lem2714531) (@lem2714530)). Qed.
Lemma lem2714533 : term945 = term930.
Proof. exact (TRANS (@lem2714525) (@lem2714532)). Qed.
Lemma lem2714534 : term944 = term930.
Proof. exact (TRANS (@lem2714522) (@lem2714533)). Qed.
Lemma lem2714536 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714537 : term149 = term150.
Proof. exact (@lem2714536 term67 term67). Qed.
Lemma lem2714538 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714539 : term152 = term67.
Proof. exact (EQ_MP (@lem2714538) (@lem940073)). Qed.
Lemma lem2714540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714541 : term150 = term66.
Proof. exact (MK_COMB (@lem2714540) (@lem2714539)). Qed.
Lemma lem2714542 : term149 = term66.
Proof. exact (TRANS (@lem2714537) (@lem2714541)). Qed.
Lemma lem2714543 : term943 = term943.
Proof. exact (eq_refl term943). Qed.
Lemma lem2714544 : term950 = term945.
Proof. exact (MK_COMB (@lem2714543) (@lem2714542)). Qed.
Lemma lem2714546 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714547 : term945 = term946.
Proof. exact (@lem2714546 term939 term67). Qed.
Lemma lem2714548 : term947 = term937.
Proof. exact (@lem996237 term937). Qed.
Lemma lem2714549 : (term947 = term937) = (term948 = term939).
Proof. exact (@lem1007663 term937 (BIT1 0) term937). Qed.
Lemma lem2714550 : term948 = term939.
Proof. exact (EQ_MP (@lem2714549) (@lem2714548)). Qed.
Lemma lem2714551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714552 : term949 = term941.
Proof. exact (MK_COMB (@lem2714551) (@lem2714550)). Qed.
Lemma lem2714553 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714554 : term946 = term930.
Proof. exact (MK_COMB (@lem2714553) (@lem2714552)). Qed.
Lemma lem2714555 : term945 = term930.
Proof. exact (TRANS (@lem2714547) (@lem2714554)). Qed.
Lemma lem2714556 : term950 = term930.
Proof. exact (TRANS (@lem2714544) (@lem2714555)). Qed.
Lemma lem2714557 : term930 = term950.
Proof. exact (SYM (@lem2714556)). Qed.
Lemma lem2714558 : term944 = term950.
Proof. exact (TRANS (@lem2714534) (@lem2714557)). Qed.
Lemma lem2714559 : term928 = term951.
Proof. exact (@lem2714483 (@lem2714558)). Qed.
Lemma lem2714560 : term927 = term951.
Proof. exact (TRANS (@lem2714449) (@lem2714559)). Qed.
Lemma lem2714562 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2714563 : term951 = term930.
Proof. exact (@lem2714562 term930). Qed.
Lemma lem2714564 : term927 = term930.
Proof. exact (TRANS (@lem2714560) (@lem2714563)). Qed.
Lemma lem2714565 (n : int) : (term926 n) = term952.
Proof. exact (MK_COMB (@lem2714440 n) (@lem2714564)). Qed.
Lemma lem2714566 (n : int) : (term925 n) = term952.
Proof. exact (TRANS (@lem2714330 n) (@lem2714565 n)). Qed.
Lemma lem2714567 : term952 = term930.
Proof. exact (@lem1982721 term930). Qed.
Lemma lem2714568 (n : int) : (term925 n) = term930.
Proof. exact (TRANS (@lem2714566 n) (@lem2714567)). Qed.
Lemma lem2714569 (n : int) : (term924 n) = term952.
Proof. exact (MK_COMB (@lem2714329 n) (@lem2714568 n)). Qed.
Lemma lem2714570 (n : int) : (term923 n) = term952.
Proof. exact (TRANS (@lem2714219 n) (@lem2714569 n)). Qed.
Lemma lem2714571 : term952 = term930.
Proof. exact (@lem1982721 term930). Qed.
Lemma lem2714572 (n : int) : (term923 n) = term930.
Proof. exact (TRANS (@lem2714570 n) (@lem2714571)). Qed.
Lemma lem2714573 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2714574 (n : int) : (term953 n) = term954.
Proof. exact (MK_COMB (@lem2714573) (@lem2714572 n)). Qed.
Lemma lem2714575 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2714576 (n : int) : (term922 n) = term955.
Proof. exact (MK_COMB (@lem2714574 n) (@lem2714575)). Qed.
Lemma lem2714577 (n : int) (h1 : term540 n) : term955.
Proof. exact (EQ_MP (@lem2714576 n) (@lem2714218 n h1)). Qed.
Lemma lem2714579 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2714580 : term955 = term956.
Proof. exact (@lem2714579 term32 term930). Qed.
Lemma lem2714582 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714583 : term930 = term951.
Proof. exact (@lem2714582 term939). Qed.
Lemma lem2714585 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714586 : term32 = term137.
Proof. exact (@lem2714585 (NUMERAL 0)). Qed.
Lemma lem2714587 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2714588 : term55 = term804.
Proof. exact (MK_COMB (@lem2714587) (@lem2714586)). Qed.
Lemma lem2714589 : term956 = term957.
Proof. exact (MK_COMB (@lem2714588) (@lem2714583)). Qed.
Lemma lem2714590 : term958.
Proof. exact (@lem1980026 term32 term66 term930 term66). Qed.
Lemma lem2714592 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714593 : term257 = term258.
Proof. exact (@lem2714592 (NUMERAL 0) term67). Qed.
Lemma lem2714594 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714595 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714596 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714595 h1) (fun h1 : term258 = True => @lem2714594)). Qed.
Lemma lem2714597 : term258 = True.
Proof. exact (EQ_MP (@lem2714596) (@lem2714594)). Qed.
Lemma lem2714598 : term257 = True.
Proof. exact (TRANS (@lem2714593) (@lem2714597)). Qed.
Lemma lem2714599 : True = term257.
Proof. exact (SYM (@lem2714598)). Qed.
Lemma lem2714600 : term257.
Proof. exact (EQ_MP (@lem2714599) (@lem0)). Qed.
Lemma lem2714601 : term959.
Proof. exact (@lem2714590 (@lem2714600)). Qed.
Lemma lem2714603 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714604 : term257 = term258.
Proof. exact (@lem2714603 (NUMERAL 0) term67). Qed.
Lemma lem2714605 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714606 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714607 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714606 h1) (fun h1 : term258 = True => @lem2714605)). Qed.
Lemma lem2714608 : term258 = True.
Proof. exact (EQ_MP (@lem2714607) (@lem2714605)). Qed.
Lemma lem2714609 : term257 = True.
Proof. exact (TRANS (@lem2714604) (@lem2714608)). Qed.
Lemma lem2714610 : True = term257.
Proof. exact (SYM (@lem2714609)). Qed.
Lemma lem2714611 : term257.
Proof. exact (EQ_MP (@lem2714610) (@lem0)). Qed.
Lemma lem2714612 : term957 = term960.
Proof. exact (@lem2714601 (@lem2714611)). Qed.
Lemma lem2714614 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714615 : term945 = term946.
Proof. exact (@lem2714614 term939 term67). Qed.
Lemma lem2714616 : term947 = term937.
Proof. exact (@lem996237 term937). Qed.
Lemma lem2714617 : (term947 = term937) = (term948 = term939).
Proof. exact (@lem1007663 term937 (BIT1 0) term937). Qed.
Lemma lem2714618 : term948 = term939.
Proof. exact (EQ_MP (@lem2714617) (@lem2714616)). Qed.
Lemma lem2714619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714620 : term949 = term941.
Proof. exact (MK_COMB (@lem2714619) (@lem2714618)). Qed.
Lemma lem2714621 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714622 : term946 = term930.
Proof. exact (MK_COMB (@lem2714621) (@lem2714620)). Qed.
Lemma lem2714623 : term945 = term930.
Proof. exact (TRANS (@lem2714615) (@lem2714622)). Qed.
Lemma lem2714625 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714626 : term269 = term32.
Proof. exact (@lem2714625 term67). Qed.
Lemma lem2714627 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2714628 : term809 = term55.
Proof. exact (MK_COMB (@lem2714627) (@lem2714626)). Qed.
Lemma lem2714629 : term960 = term956.
Proof. exact (MK_COMB (@lem2714628) (@lem2714623)). Qed.
Lemma lem2714631 (m : nat) (n : nat) : (term810 m n) = (term811 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2714632 : term956 = term961.
Proof. exact (@lem2714631 (NUMERAL 0) term939). Qed.
Lemma lem2714633 : term962 = term937.
Proof. exact (@lem913059). Qed.
Lemma lem2714634 (h1 : term962 = term937) : (term939 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 term963 0 term937 h1). Qed.
Lemma lem2714635 : (term962 = term937) = ((term939 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term962 = term937 => @lem2714634 h1) (fun h1 : (term939 = (NUMERAL 0)) = False => @lem2714633)). Qed.
Lemma lem2714636 : (term939 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2714635) (@lem2714633)). Qed.
Lemma lem2714637 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2714638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2714639 : term813 = (and True).
Proof. exact (MK_COMB (@lem2714638) (@lem2714637)). Qed.
Lemma lem2714640 : term961 = (True /\ False).
Proof. exact (MK_COMB (@lem2714639) (@lem2714636)). Qed.
Lemma lem2714642 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2714643 : term961 = False.
Proof. exact (TRANS (@lem2714640) (@lem2714642)). Qed.
Lemma lem2714644 : term956 = False.
Proof. exact (TRANS (@lem2714632) (@lem2714643)). Qed.
Lemma lem2714645 : term960 = False.
Proof. exact (TRANS (@lem2714629) (@lem2714644)). Qed.
Lemma lem2714646 : term957 = False.
Proof. exact (TRANS (@lem2714612) (@lem2714645)). Qed.
Lemma lem2714647 : term956 = False.
Proof. exact (TRANS (@lem2714589) (@lem2714646)). Qed.
Lemma lem2714648 : term955 = False.
Proof. exact (TRANS (@lem2714580) (@lem2714647)). Qed.
Lemma lem2714649 (n : int) (h1 : term540 n) : False.
Proof. exact (EQ_MP (@lem2714648) (@lem2714577 n h1)). Qed.
Lemma lem2714650 (n : int) (h1 : term542 n) : term542 n.
Proof. exact (h1). Qed.
Lemma lem2714652 (n : int) (h1 : term542 n) : term425.
Proof. exact (proj1 (@lem2714650 n h1)). Qed.
Lemma lem2714662 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2714663 : term425 = term814.
Proof. exact (@lem2714662 term32 term184). Qed.
Lemma lem2714665 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714666 : term184 = term187.
Proof. exact (@lem2714665 term29). Qed.
Lemma lem2714668 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714669 : term32 = term137.
Proof. exact (@lem2714668 (NUMERAL 0)). Qed.
Lemma lem2714670 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2714671 : term582 = term583.
Proof. exact (MK_COMB (@lem2714670) (@lem2714669)). Qed.
Lemma lem2714672 : term814 = term815.
Proof. exact (MK_COMB (@lem2714671) (@lem2714666)). Qed.
Lemma lem2714673 : term816.
Proof. exact (@lem1980255 term32 term66 term184 term66). Qed.
Lemma lem2714675 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714676 : term257 = term258.
Proof. exact (@lem2714675 (NUMERAL 0) term67). Qed.
Lemma lem2714677 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714678 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714679 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714678 h1) (fun h1 : term258 = True => @lem2714677)). Qed.
Lemma lem2714680 : term258 = True.
Proof. exact (EQ_MP (@lem2714679) (@lem2714677)). Qed.
Lemma lem2714681 : term257 = True.
Proof. exact (TRANS (@lem2714676) (@lem2714680)). Qed.
Lemma lem2714682 : True = term257.
Proof. exact (SYM (@lem2714681)). Qed.
Lemma lem2714683 : term257.
Proof. exact (EQ_MP (@lem2714682) (@lem0)). Qed.
Lemma lem2714684 : term817.
Proof. exact (@lem2714673 (@lem2714683)). Qed.
Lemma lem2714686 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714687 : term257 = term258.
Proof. exact (@lem2714686 (NUMERAL 0) term67). Qed.
Lemma lem2714688 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714689 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714690 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714689 h1) (fun h1 : term258 = True => @lem2714688)). Qed.
Lemma lem2714691 : term258 = True.
Proof. exact (EQ_MP (@lem2714690) (@lem2714688)). Qed.
Lemma lem2714692 : term257 = True.
Proof. exact (TRANS (@lem2714687) (@lem2714691)). Qed.
Lemma lem2714693 : True = term257.
Proof. exact (SYM (@lem2714692)). Qed.
Lemma lem2714694 : term257.
Proof. exact (EQ_MP (@lem2714693) (@lem0)). Qed.
Lemma lem2714695 : term815 = term818.
Proof. exact (@lem2714684 (@lem2714694)). Qed.
Lemma lem2714697 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2714698 : term439 = term440.
Proof. exact (@lem2714697 term29 term67). Qed.
Lemma lem2714699 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2714700 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2714701 : term292 = term29.
Proof. exact (EQ_MP (@lem2714700) (@lem2714699)). Qed.
Lemma lem2714702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714703 : term290 = term28.
Proof. exact (MK_COMB (@lem2714702) (@lem2714701)). Qed.
Lemma lem2714704 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2714705 : term440 = term184.
Proof. exact (MK_COMB (@lem2714704) (@lem2714703)). Qed.
Lemma lem2714706 : term439 = term184.
Proof. exact (TRANS (@lem2714698) (@lem2714705)). Qed.
Lemma lem2714708 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714709 : term269 = term32.
Proof. exact (@lem2714708 term67). Qed.
Lemma lem2714710 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2714711 : term588 = term582.
Proof. exact (MK_COMB (@lem2714710) (@lem2714709)). Qed.
Lemma lem2714712 : term818 = term814.
Proof. exact (MK_COMB (@lem2714711) (@lem2714706)). Qed.
Lemma lem2714714 (m : nat) (n : nat) : (term819 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2714715 : term814 = False.
Proof. exact (@lem2714714 (NUMERAL 0) term29). Qed.
Lemma lem2714716 : term818 = False.
Proof. exact (TRANS (@lem2714712) (@lem2714715)). Qed.
Lemma lem2714717 : term815 = False.
Proof. exact (TRANS (@lem2714695) (@lem2714716)). Qed.
Lemma lem2714718 : term814 = False.
Proof. exact (TRANS (@lem2714672) (@lem2714717)). Qed.
Lemma lem2714719 : term425 = False.
Proof. exact (TRANS (@lem2714663) (@lem2714718)). Qed.
Lemma lem2714720 (n : int) (h1 : term542 n) : False.
Proof. exact (EQ_MP (@lem2714719) (@lem2714652 n h1)). Qed.
Lemma lem2714721 (n : int) (h1 : term544 n) : False.
Proof. exact (or_elim (@lem2713291 n h1) (fun h0 : term540 n => @lem2714649 n h0) (fun h0 : term542 n => @lem2714720 n h0)). Qed.
Lemma lem2714722 (n : int) (h1 : term546 n) : False.
Proof. exact (or_elim (@lem2713226 n h1) (fun h0 : term888 n => @lem2713290 n h0) (fun h0 : term544 n => @lem2714721 n h0)). Qed.
Lemma lem2714723 (n : int) (h1 : term570 n) : term570 n.
Proof. exact (h1). Qed.
Lemma lem2714724 (n : int) (h1 : term964 n) : term964 n.
Proof. exact (h1). Qed.
Lemma lem2714726 (n : int) (h1 : term964 n) : term28 = term32.
Proof. exact (proj1 (@lem2714724 n h1)). Qed.
Lemma lem2714730 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714731 : term32 = term137.
Proof. exact (@lem2714730 (NUMERAL 0)). Qed.
Lemma lem2714733 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714734 : term28 = term173.
Proof. exact (@lem2714733 term29). Qed.
Lemma lem2714735 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2714736 : term31 = term576.
Proof. exact (MK_COMB (@lem2714735) (@lem2714734)). Qed.
Lemma lem2714737 : (term28 = term32) = (term173 = term137).
Proof. exact (MK_COMB (@lem2714736) (@lem2714731)). Qed.
Lemma lem2714738 : term577.
Proof. exact (@lem1980277 term28 term66 term32 term66). Qed.
Lemma lem2714740 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714741 : term257 = term258.
Proof. exact (@lem2714740 (NUMERAL 0) term67). Qed.
Lemma lem2714742 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714743 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714744 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714743 h1) (fun h1 : term258 = True => @lem2714742)). Qed.
Lemma lem2714745 : term258 = True.
Proof. exact (EQ_MP (@lem2714744) (@lem2714742)). Qed.
Lemma lem2714746 : term257 = True.
Proof. exact (TRANS (@lem2714741) (@lem2714745)). Qed.
Lemma lem2714747 : True = term257.
Proof. exact (SYM (@lem2714746)). Qed.
Lemma lem2714748 : term257.
Proof. exact (EQ_MP (@lem2714747) (@lem0)). Qed.
Lemma lem2714749 : term578.
Proof. exact (@lem2714738 (@lem2714748)). Qed.
Lemma lem2714751 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714752 : term257 = term258.
Proof. exact (@lem2714751 (NUMERAL 0) term67). Qed.
Lemma lem2714753 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714754 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714755 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714754 h1) (fun h1 : term258 = True => @lem2714753)). Qed.
Lemma lem2714756 : term258 = True.
Proof. exact (EQ_MP (@lem2714755) (@lem2714753)). Qed.
Lemma lem2714757 : term257 = True.
Proof. exact (TRANS (@lem2714752) (@lem2714756)). Qed.
Lemma lem2714758 : True = term257.
Proof. exact (SYM (@lem2714757)). Qed.
Lemma lem2714759 : term257.
Proof. exact (EQ_MP (@lem2714758) (@lem0)). Qed.
Lemma lem2714760 : (term173 = term137) = (term289 = term269).
Proof. exact (@lem2714749 (@lem2714759)). Qed.
Lemma lem2714762 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714763 : term269 = term32.
Proof. exact (@lem2714762 term67). Qed.
Lemma lem2714765 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714766 : term289 = term290.
Proof. exact (@lem2714765 term29 term67). Qed.
Lemma lem2714767 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2714768 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2714769 : term292 = term29.
Proof. exact (EQ_MP (@lem2714768) (@lem2714767)). Qed.
Lemma lem2714770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714771 : term290 = term28.
Proof. exact (MK_COMB (@lem2714770) (@lem2714769)). Qed.
Lemma lem2714772 : term289 = term28.
Proof. exact (TRANS (@lem2714766) (@lem2714771)). Qed.
Lemma lem2714773 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2714774 : term579 = term31.
Proof. exact (MK_COMB (@lem2714773) (@lem2714772)). Qed.
Lemma lem2714775 : (term289 = term269) = (term28 = term32).
Proof. exact (MK_COMB (@lem2714774) (@lem2714763)). Qed.
Lemma lem2714777 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem2714778 : (term28 = term32) = (term29 = (NUMERAL 0)).
Proof. exact (@lem2714777 term29 (NUMERAL 0)). Qed.
Lemma lem2714779 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2714780 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2714781 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2714780 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2714779)). Qed.
Lemma lem2714782 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2714781) (@lem2714779)). Qed.
Lemma lem2714783 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2714778) (@lem2714782)). Qed.
Lemma lem2714784 : (term289 = term269) = False.
Proof. exact (TRANS (@lem2714775) (@lem2714783)). Qed.
Lemma lem2714785 : (term173 = term137) = False.
Proof. exact (TRANS (@lem2714760) (@lem2714784)). Qed.
Lemma lem2714786 : (term28 = term32) = False.
Proof. exact (TRANS (@lem2714737) (@lem2714785)). Qed.
Lemma lem2714787 (n : int) (h1 : term964 n) : False.
Proof. exact (EQ_MP (@lem2714786) (@lem2714726 n h1)). Qed.
Lemma lem2714788 (n : int) (h1 : term568 n) : term568 n.
Proof. exact (h1). Qed.
Lemma lem2714789 (n : int) (h1 : term564 n) : term564 n.
Proof. exact (h1). Qed.
Lemma lem2714790 (n : int) (h1 : term564 n) : term563 n.
Proof. exact (proj2 (@lem2714789 n h1)). Qed.
Lemma lem2714792 (n : int) (h1 : term564 n) : term320 n.
Proof. exact (proj2 (@lem2714790 n h1)). Qed.
Lemma lem2714793 (n : int) (h1 : term564 n) : term402 n.
Proof. exact (proj1 (@lem2714790 n h1)). Qed.
Lemma lem2714794 (n : int) (h1 : term564 n) : term400 n.
Proof. exact (proj2 (@lem2714793 n h1)). Qed.
Lemma lem2714795 (n : int) (h1 : term564 n) : (term195 n) = term32.
Proof. exact (proj1 (@lem2714793 n h1)). Qed.
Lemma lem2714796 (n : int) (h1 : term564 n) : term398 n.
Proof. exact (proj2 (@lem2714794 n h1)). Qed.
Lemma lem2714798 (n : int) (h1 : term564 n) : term300 n.
Proof. exact (proj2 (@lem2714792 n h1)). Qed.
Lemma lem2714801 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2714802 : term581 = term257.
Proof. exact (@lem2714801 term32 term66). Qed.
Lemma lem2714804 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714805 : term66 = term210.
Proof. exact (@lem2714804 term67). Qed.
Lemma lem2714807 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714808 : term32 = term137.
Proof. exact (@lem2714807 (NUMERAL 0)). Qed.
Lemma lem2714809 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2714810 : term582 = term583.
Proof. exact (MK_COMB (@lem2714809) (@lem2714808)). Qed.
Lemma lem2714811 : term257 = term584.
Proof. exact (MK_COMB (@lem2714810) (@lem2714805)). Qed.
Lemma lem2714812 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2714814 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714815 : term257 = term258.
Proof. exact (@lem2714814 (NUMERAL 0) term67). Qed.
Lemma lem2714816 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714817 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714818 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714817 h1) (fun h1 : term258 = True => @lem2714816)). Qed.
Lemma lem2714819 : term258 = True.
Proof. exact (EQ_MP (@lem2714818) (@lem2714816)). Qed.
Lemma lem2714820 : term257 = True.
Proof. exact (TRANS (@lem2714815) (@lem2714819)). Qed.
Lemma lem2714821 : True = term257.
Proof. exact (SYM (@lem2714820)). Qed.
Lemma lem2714822 : term257.
Proof. exact (EQ_MP (@lem2714821) (@lem0)). Qed.
Lemma lem2714823 : term586.
Proof. exact (@lem2714812 (@lem2714822)). Qed.
Lemma lem2714825 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714826 : term257 = term258.
Proof. exact (@lem2714825 (NUMERAL 0) term67). Qed.
Lemma lem2714827 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714828 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714829 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714828 h1) (fun h1 : term258 = True => @lem2714827)). Qed.
Lemma lem2714830 : term258 = True.
Proof. exact (EQ_MP (@lem2714829) (@lem2714827)). Qed.
Lemma lem2714831 : term257 = True.
Proof. exact (TRANS (@lem2714826) (@lem2714830)). Qed.
Lemma lem2714832 : True = term257.
Proof. exact (SYM (@lem2714831)). Qed.
Lemma lem2714833 : term257.
Proof. exact (EQ_MP (@lem2714832) (@lem0)). Qed.
Lemma lem2714834 : term584 = term587.
Proof. exact (@lem2714823 (@lem2714833)). Qed.
Lemma lem2714836 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714837 : term149 = term150.
Proof. exact (@lem2714836 term67 term67). Qed.
Lemma lem2714838 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714839 : term152 = term67.
Proof. exact (EQ_MP (@lem2714838) (@lem940073)). Qed.
Lemma lem2714840 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714841 : term150 = term66.
Proof. exact (MK_COMB (@lem2714840) (@lem2714839)). Qed.
Lemma lem2714842 : term149 = term66.
Proof. exact (TRANS (@lem2714837) (@lem2714841)). Qed.
Lemma lem2714844 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2714845 : term269 = term32.
Proof. exact (@lem2714844 term67). Qed.
Lemma lem2714846 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2714847 : term588 = term582.
Proof. exact (MK_COMB (@lem2714846) (@lem2714845)). Qed.
Lemma lem2714848 : term587 = term257.
Proof. exact (MK_COMB (@lem2714847) (@lem2714842)). Qed.
Lemma lem2714850 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2714851 : term257 = term258.
Proof. exact (@lem2714850 (NUMERAL 0) term67). Qed.
Lemma lem2714852 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2714853 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2714854 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2714853 h1) (fun h1 : term258 = True => @lem2714852)). Qed.
Lemma lem2714855 : term258 = True.
Proof. exact (EQ_MP (@lem2714854) (@lem2714852)). Qed.
Lemma lem2714856 : term257 = True.
Proof. exact (TRANS (@lem2714851) (@lem2714855)). Qed.
Lemma lem2714857 : term587 = True.
Proof. exact (TRANS (@lem2714848) (@lem2714856)). Qed.
Lemma lem2714858 : term584 = True.
Proof. exact (TRANS (@lem2714834) (@lem2714857)). Qed.
Lemma lem2714859 : term257 = True.
Proof. exact (TRANS (@lem2714811) (@lem2714858)). Qed.
Lemma lem2714860 : term581 = True.
Proof. exact (TRANS (@lem2714802) (@lem2714859)). Qed.
Lemma lem2714861 : True = term581.
Proof. exact (SYM (@lem2714860)). Qed.
Lemma lem2714862 : term581.
Proof. exact (EQ_MP (@lem2714861) (@lem0)). Qed.
Lemma lem2714863 (n : int) (h1 : term564 n) : term965 n.
Proof. exact (conj (@lem2714862) (@lem2714796 n h1)). Qed.
Lemma lem2714865 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2714866 (n : int) : term966 n.
Proof. exact (@lem2714865 term66 (term388 n)). Qed.
Lemma lem2714867 (n : int) (h1 : term564 n) : term967 n.
Proof. exact (@lem2714866 n (@lem2714863 n h1)). Qed.
Lemma lem2714868 (n : int) : (term968 n) = (term388 n).
Proof. exact (@lem1982733 (term388 n)). Qed.
Lemma lem2714869 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2714870 (n : int) : (term969 n) = (term397 n).
Proof. exact (MK_COMB (@lem2714869) (@lem2714868 n)). Qed.
Lemma lem2714871 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2714872 (n : int) : (term967 n) = (term398 n).
Proof. exact (MK_COMB (@lem2714870 n) (@lem2714871)). Qed.
Lemma lem2714873 (n : int) (h1 : term564 n) : term398 n.
Proof. exact (EQ_MP (@lem2714872 n) (@lem2714867 n h1)). Qed.
Lemma lem2714875 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2714876 (n : int) : term596 n.
Proof. exact (@lem2714875 (term195 n)). Qed.
Lemma lem2714877 (n : int) (h1 : term564 n) : term597 n.
Proof. exact (@lem2714876 n (@lem2714795 n h1)). Qed.
Lemma lem2714878 (n : int) (h1 : term564 n) : term598 n.
Proof. exact (@lem2714877 n h1 term140). Qed.
Lemma lem2714879 (n : int) : (term598 n) = ((term599 n) = term32).
Proof. exact (eq_refl (term598 n)). Qed.
Lemma lem2714880 (n : int) (h1 : term564 n) : (term599 n) = term32.
Proof. exact (EQ_MP (@lem2714879 n) (@lem2714878 n h1)). Qed.
Lemma lem2714881 (n : int) : (term599 n) = (term600 n).
Proof. exact (@lem1982781 (real_of_int n) term140 (term193 n)). Qed.
Lemma lem2714882 (n : int) : (term601 n) = (term602 n).
Proof. exact (@lem1982781 (term190 n) term140 (term170 n)). Qed.
Lemma lem2714883 (n : int) : (term603 n) = (term604 n).
Proof. exact (@lem1982749 term140 term140 (term48 n)). Qed.
Lemma lem2714885 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714886 : term140 = term141.
Proof. exact (@lem2714885 term67). Qed.
Lemma lem2714888 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714889 : term140 = term141.
Proof. exact (@lem2714888 term67). Qed.
Lemma lem2714890 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714891 : term142 = term143.
Proof. exact (MK_COMB (@lem2714890) (@lem2714889)). Qed.
Lemma lem2714892 : term605 = term606.
Proof. exact (MK_COMB (@lem2714891) (@lem2714886)). Qed.
Lemma lem2714893 : term606 = term607.
Proof. exact (@lem1981613 term140 term140 term66 term66). Qed.
Lemma lem2714895 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714896 : term149 = term150.
Proof. exact (@lem2714895 term67 term67). Qed.
Lemma lem2714897 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714898 : term152 = term67.
Proof. exact (EQ_MP (@lem2714897) (@lem940073)). Qed.
Lemma lem2714899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714900 : term150 = term66.
Proof. exact (MK_COMB (@lem2714899) (@lem2714898)). Qed.
Lemma lem2714901 : term149 = term66.
Proof. exact (TRANS (@lem2714896) (@lem2714900)). Qed.
Lemma lem2714903 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2714904 : term605 = term150.
Proof. exact (@lem2714903 term67 term67). Qed.
Lemma lem2714905 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714906 : term152 = term67.
Proof. exact (EQ_MP (@lem2714905) (@lem940073)). Qed.
Lemma lem2714907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714908 : term150 = term66.
Proof. exact (MK_COMB (@lem2714907) (@lem2714906)). Qed.
Lemma lem2714909 : term605 = term66.
Proof. exact (TRANS (@lem2714904) (@lem2714908)). Qed.
Lemma lem2714910 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2714911 : term609 = term610.
Proof. exact (MK_COMB (@lem2714910) (@lem2714909)). Qed.
Lemma lem2714912 : term607 = term210.
Proof. exact (MK_COMB (@lem2714911) (@lem2714901)). Qed.
Lemma lem2714913 : term606 = term210.
Proof. exact (TRANS (@lem2714893) (@lem2714912)). Qed.
Lemma lem2714914 : term605 = term210.
Proof. exact (TRANS (@lem2714892) (@lem2714913)). Qed.
Lemma lem2714916 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2714917 : term210 = term66.
Proof. exact (@lem2714916 term66). Qed.
Lemma lem2714918 : term605 = term66.
Proof. exact (TRANS (@lem2714914) (@lem2714917)). Qed.
Lemma lem2714919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714920 : term611 = term385.
Proof. exact (MK_COMB (@lem2714919) (@lem2714918)). Qed.
Lemma lem2714921 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2714922 (n : int) : (term604 n) = (term612 n).
Proof. exact (MK_COMB (@lem2714920) (@lem2714921 n)). Qed.
Lemma lem2714923 (n : int) : (term603 n) = (term612 n).
Proof. exact (TRANS (@lem2714883 n) (@lem2714922 n)). Qed.
Lemma lem2714924 (n : int) : (term612 n) = (term48 n).
Proof. exact (@lem1982709 (term48 n)). Qed.
Lemma lem2714925 (n : int) : (term603 n) = (term48 n).
Proof. exact (TRANS (@lem2714923 n) (@lem2714924 n)). Qed.
Lemma lem2714926 (n : int) : (term613 n) = (term614 n).
Proof. exact (@lem1982749 term140 term184 (term162 n)). Qed.
Lemma lem2714928 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714929 : term184 = term187.
Proof. exact (@lem2714928 term29). Qed.
Lemma lem2714931 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714932 : term140 = term141.
Proof. exact (@lem2714931 term67). Qed.
Lemma lem2714933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714934 : term142 = term143.
Proof. exact (MK_COMB (@lem2714933) (@lem2714932)). Qed.
Lemma lem2714935 : term615 = term616.
Proof. exact (MK_COMB (@lem2714934) (@lem2714929)). Qed.
Lemma lem2714936 : term616 = term617.
Proof. exact (@lem1981613 term140 term184 term66 term66). Qed.
Lemma lem2714938 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2714939 : term149 = term150.
Proof. exact (@lem2714938 term67 term67). Qed.
Lemma lem2714940 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2714941 : term152 = term67.
Proof. exact (EQ_MP (@lem2714940) (@lem940073)). Qed.
Lemma lem2714942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714943 : term150 = term66.
Proof. exact (MK_COMB (@lem2714942) (@lem2714941)). Qed.
Lemma lem2714944 : term149 = term66.
Proof. exact (TRANS (@lem2714939) (@lem2714943)). Qed.
Lemma lem2714946 (m : nat) (n : nat) : (term608 m n) = (term148 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2714947 : term615 = term183.
Proof. exact (@lem2714946 term67 term29). Qed.
Lemma lem2714948 : term180 = term181.
Proof. exact (@lem996238 term181). Qed.
Lemma lem2714949 : (term180 = term181) = (term182 = term29).
Proof. exact (@lem1007663 (BIT1 0) term181 term181). Qed.
Lemma lem2714950 : term182 = term29.
Proof. exact (EQ_MP (@lem2714949) (@lem2714948)). Qed.
Lemma lem2714951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2714952 : term183 = term28.
Proof. exact (MK_COMB (@lem2714951) (@lem2714950)). Qed.
Lemma lem2714953 : term615 = term28.
Proof. exact (TRANS (@lem2714947) (@lem2714952)). Qed.
Lemma lem2714954 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2714955 : term618 = term619.
Proof. exact (MK_COMB (@lem2714954) (@lem2714953)). Qed.
Lemma lem2714956 : term617 = term173.
Proof. exact (MK_COMB (@lem2714955) (@lem2714944)). Qed.
Lemma lem2714957 : term616 = term173.
Proof. exact (TRANS (@lem2714936) (@lem2714956)). Qed.
Lemma lem2714958 : term615 = term173.
Proof. exact (TRANS (@lem2714935) (@lem2714957)). Qed.
Lemma lem2714960 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2714961 : term173 = term28.
Proof. exact (@lem2714960 term28). Qed.
Lemma lem2714962 : term615 = term28.
Proof. exact (TRANS (@lem2714958) (@lem2714961)). Qed.
Lemma lem2714963 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2714964 : term620 = term287.
Proof. exact (MK_COMB (@lem2714963) (@lem2714962)). Qed.
Lemma lem2714965 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2714966 (n : int) : (term614 n) = (term161 n).
Proof. exact (MK_COMB (@lem2714964) (@lem2714965 n)). Qed.
Lemma lem2714967 (n : int) : (term613 n) = (term161 n).
Proof. exact (TRANS (@lem2714926 n) (@lem2714966 n)). Qed.
Lemma lem2714968 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714969 (n : int) : (term621 n) = (term163 n).
Proof. exact (MK_COMB (@lem2714968) (@lem2714967 n)). Qed.
Lemma lem2714970 (n : int) : (term602 n) = (term164 n).
Proof. exact (MK_COMB (@lem2714969 n) (@lem2714925 n)). Qed.
Lemma lem2714971 (n : int) : (term601 n) = (term164 n).
Proof. exact (TRANS (@lem2714882 n) (@lem2714970 n)). Qed.
Lemma lem2714974 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2714975 (n : int) : (term600 n) = (term623 n).
Proof. exact (MK_COMB (@lem2714974 n) (@lem2714971 n)). Qed.
Lemma lem2714976 (n : int) : (term599 n) = (term623 n).
Proof. exact (TRANS (@lem2714881 n) (@lem2714975 n)). Qed.
Lemma lem2714977 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2714978 (n : int) : (term624 n) = (term625 n).
Proof. exact (MK_COMB (@lem2714977) (@lem2714976 n)). Qed.
Lemma lem2714979 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2714980 (n : int) : ((term599 n) = term32) = ((term623 n) = term32).
Proof. exact (MK_COMB (@lem2714978 n) (@lem2714979)). Qed.
Lemma lem2714981 (n : int) (h1 : term564 n) : (term623 n) = term32.
Proof. exact (EQ_MP (@lem2714980 n) (@lem2714880 n h1)). Qed.
Lemma lem2714982 (n : int) (h1 : term564 n) : term970 n.
Proof. exact (conj (@lem2714981 n h1) (@lem2714873 n h1)). Qed.
Lemma lem2714984 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2714985 (n : int) : term971 n.
Proof. exact (@lem2714984 (term623 n) (term388 n)). Qed.
Lemma lem2714986 (n : int) (h1 : term564 n) : term972 n.
Proof. exact (@lem2714985 n (@lem2714982 n h1)). Qed.
Lemma lem2714987 (n : int) : (term973 n) = (term974 n).
Proof. exact (@lem1982755 (term632 n) (term164 n) (term388 n)). Qed.
Lemma lem2714988 (n : int) : (term975 n) = (term976 n).
Proof. exact (@lem1982755 (term161 n) (term48 n) (term388 n)). Qed.
Lemma lem2714989 (n : int) : (term977 n) = (term978 n).
Proof. exact (@lem1982763 (term48 n) (term170 n) term66). Qed.
Lemma lem2714990 (n : int) : (term637 n) = (term638 n).
Proof. exact (@lem1982715 term140 (term48 n)). Qed.
Lemma lem2714992 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2714993 : term66 = term210.
Proof. exact (@lem2714992 term67). Qed.
Lemma lem2714995 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2714996 : term140 = term141.
Proof. exact (@lem2714995 term67). Qed.
Lemma lem2714997 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2714998 : term639 = term640.
Proof. exact (MK_COMB (@lem2714997) (@lem2714996)). Qed.
Lemma lem2714999 : term641 = term642.
Proof. exact (MK_COMB (@lem2714998) (@lem2714993)). Qed.
Lemma lem2715000 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2715002 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715003 : term257 = term258.
Proof. exact (@lem2715002 (NUMERAL 0) term67). Qed.
Lemma lem2715004 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715005 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715006 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715005 h1) (fun h1 : term258 = True => @lem2715004)). Qed.
Lemma lem2715007 : term258 = True.
Proof. exact (EQ_MP (@lem2715006) (@lem2715004)). Qed.
Lemma lem2715008 : term257 = True.
Proof. exact (TRANS (@lem2715003) (@lem2715007)). Qed.
Lemma lem2715009 : True = term257.
Proof. exact (SYM (@lem2715008)). Qed.
Lemma lem2715010 : term257.
Proof. exact (EQ_MP (@lem2715009) (@lem0)). Qed.
Lemma lem2715011 : term644.
Proof. exact (@lem2715000 (@lem2715010)). Qed.
Lemma lem2715013 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715014 : term257 = term258.
Proof. exact (@lem2715013 (NUMERAL 0) term67). Qed.
Lemma lem2715015 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715016 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715017 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715016 h1) (fun h1 : term258 = True => @lem2715015)). Qed.
Lemma lem2715018 : term258 = True.
Proof. exact (EQ_MP (@lem2715017) (@lem2715015)). Qed.
Lemma lem2715019 : term257 = True.
Proof. exact (TRANS (@lem2715014) (@lem2715018)). Qed.
Lemma lem2715020 : True = term257.
Proof. exact (SYM (@lem2715019)). Qed.
Lemma lem2715021 : term257.
Proof. exact (EQ_MP (@lem2715020) (@lem0)). Qed.
Lemma lem2715022 : term645.
Proof. exact (@lem2715011 (@lem2715021)). Qed.
Lemma lem2715024 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715025 : term257 = term258.
Proof. exact (@lem2715024 (NUMERAL 0) term67). Qed.
Lemma lem2715026 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715027 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715028 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715027 h1) (fun h1 : term258 = True => @lem2715026)). Qed.
Lemma lem2715029 : term258 = True.
Proof. exact (EQ_MP (@lem2715028) (@lem2715026)). Qed.
Lemma lem2715030 : term257 = True.
Proof. exact (TRANS (@lem2715025) (@lem2715029)). Qed.
Lemma lem2715031 : True = term257.
Proof. exact (SYM (@lem2715030)). Qed.
Lemma lem2715032 : term257.
Proof. exact (EQ_MP (@lem2715031) (@lem0)). Qed.
Lemma lem2715033 : term646.
Proof. exact (@lem2715022 (@lem2715032)). Qed.
Lemma lem2715035 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715036 : term149 = term150.
Proof. exact (@lem2715035 term67 term67). Qed.
Lemma lem2715037 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715038 : term152 = term67.
Proof. exact (EQ_MP (@lem2715037) (@lem940073)). Qed.
Lemma lem2715039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715040 : term150 = term66.
Proof. exact (MK_COMB (@lem2715039) (@lem2715038)). Qed.
Lemma lem2715041 : term149 = term66.
Proof. exact (TRANS (@lem2715036) (@lem2715040)). Qed.
Lemma lem2715043 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2715044 : term211 = term214.
Proof. exact (@lem2715043 term67 term67). Qed.
Lemma lem2715045 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715046 : term152 = term67.
Proof. exact (EQ_MP (@lem2715045) (@lem940073)). Qed.
Lemma lem2715047 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715048 : term150 = term66.
Proof. exact (MK_COMB (@lem2715047) (@lem2715046)). Qed.
Lemma lem2715049 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715050 : term214 = term140.
Proof. exact (MK_COMB (@lem2715049) (@lem2715048)). Qed.
Lemma lem2715051 : term211 = term140.
Proof. exact (TRANS (@lem2715044) (@lem2715050)). Qed.
Lemma lem2715052 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715053 : term647 = term639.
Proof. exact (MK_COMB (@lem2715052) (@lem2715051)). Qed.
Lemma lem2715054 : term648 = term641.
Proof. exact (MK_COMB (@lem2715053) (@lem2715041)). Qed.
Lemma lem2715056 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2715057 : term641 = term32.
Proof. exact (@lem2715056 term67). Qed.
Lemma lem2715058 : term648 = term32.
Proof. exact (TRANS (@lem2715054) (@lem2715057)). Qed.
Lemma lem2715059 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715060 : term650 = term267.
Proof. exact (MK_COMB (@lem2715059) (@lem2715058)). Qed.
Lemma lem2715061 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2715062 : term651 = term269.
Proof. exact (MK_COMB (@lem2715060) (@lem2715061)). Qed.
Lemma lem2715064 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715065 : term269 = term32.
Proof. exact (@lem2715064 term67). Qed.
Lemma lem2715066 : term651 = term32.
Proof. exact (TRANS (@lem2715062) (@lem2715065)). Qed.
Lemma lem2715068 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715069 : term149 = term150.
Proof. exact (@lem2715068 term67 term67). Qed.
Lemma lem2715070 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715071 : term152 = term67.
Proof. exact (EQ_MP (@lem2715070) (@lem940073)). Qed.
Lemma lem2715072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715073 : term150 = term66.
Proof. exact (MK_COMB (@lem2715072) (@lem2715071)). Qed.
Lemma lem2715074 : term149 = term66.
Proof. exact (TRANS (@lem2715069) (@lem2715073)). Qed.
Lemma lem2715075 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2715076 : term271 = term269.
Proof. exact (MK_COMB (@lem2715075) (@lem2715074)). Qed.
Lemma lem2715078 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715079 : term269 = term32.
Proof. exact (@lem2715078 term67). Qed.
Lemma lem2715080 : term271 = term32.
Proof. exact (TRANS (@lem2715076) (@lem2715079)). Qed.
Lemma lem2715081 : term32 = term271.
Proof. exact (SYM (@lem2715080)). Qed.
Lemma lem2715082 : term651 = term271.
Proof. exact (TRANS (@lem2715066) (@lem2715081)). Qed.
Lemma lem2715083 : term642 = term137.
Proof. exact (@lem2715033 (@lem2715082)). Qed.
Lemma lem2715084 : term641 = term137.
Proof. exact (TRANS (@lem2714999) (@lem2715083)). Qed.
Lemma lem2715086 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2715087 : term137 = term32.
Proof. exact (@lem2715086 term32). Qed.
Lemma lem2715088 : term641 = term32.
Proof. exact (TRANS (@lem2715084) (@lem2715087)). Qed.
Lemma lem2715089 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715090 : term652 = term267.
Proof. exact (MK_COMB (@lem2715089) (@lem2715088)). Qed.
Lemma lem2715091 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2715092 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2715090) (@lem2715091 n)). Qed.
Lemma lem2715093 (n : int) : (term637 n) = (term653 n).
Proof. exact (TRANS (@lem2714990 n) (@lem2715092 n)). Qed.
Lemma lem2715094 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2715095 (n : int) : (term637 n) = term32.
Proof. exact (TRANS (@lem2715093 n) (@lem2715094 n)). Qed.
Lemma lem2715096 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715097 (n : int) : (term654 n) = term102.
Proof. exact (MK_COMB (@lem2715096) (@lem2715095 n)). Qed.
Lemma lem2715098 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2715099 (n : int) : (term978 n) = term103.
Proof. exact (MK_COMB (@lem2715097 n) (@lem2715098)). Qed.
Lemma lem2715100 (n : int) : (term977 n) = term103.
Proof. exact (TRANS (@lem2714989 n) (@lem2715099 n)). Qed.
Lemma lem2715101 : term103 = term66.
Proof. exact (@lem1982721 term66). Qed.
Lemma lem2715102 (n : int) : (term977 n) = term66.
Proof. exact (TRANS (@lem2715100 n) (@lem2715101)). Qed.
Lemma lem2715103 (n : int) : (term163 n) = (term163 n).
Proof. exact (eq_refl (term163 n)). Qed.
Lemma lem2715104 (n : int) : (term976 n) = (term979 n).
Proof. exact (MK_COMB (@lem2715103 n) (@lem2715102 n)). Qed.
Lemma lem2715105 (n : int) : (term975 n) = (term979 n).
Proof. exact (TRANS (@lem2714988 n) (@lem2715104 n)). Qed.
Lemma lem2715106 (n : int) : (term622 n) = (term622 n).
Proof. exact (eq_refl (term622 n)). Qed.
Lemma lem2715107 (n : int) : (term974 n) = (term980 n).
Proof. exact (MK_COMB (@lem2715106 n) (@lem2715105 n)). Qed.
Lemma lem2715108 (n : int) : (term973 n) = (term980 n).
Proof. exact (TRANS (@lem2714987 n) (@lem2715107 n)). Qed.
Lemma lem2715109 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2715110 (n : int) : (term981 n) = (term982 n).
Proof. exact (MK_COMB (@lem2715109) (@lem2715108 n)). Qed.
Lemma lem2715111 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2715112 (n : int) : (term972 n) = (term983 n).
Proof. exact (MK_COMB (@lem2715110 n) (@lem2715111)). Qed.
Lemma lem2715113 (n : int) (h1 : term564 n) : term983 n.
Proof. exact (EQ_MP (@lem2715112 n) (@lem2714986 n h1)). Qed.
Lemma lem2715115 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2715116 : term661 = term662.
Proof. exact (@lem2715115 term32 term28). Qed.
Lemma lem2715118 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715119 : term28 = term173.
Proof. exact (@lem2715118 term29). Qed.
Lemma lem2715121 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715122 : term32 = term137.
Proof. exact (@lem2715121 (NUMERAL 0)). Qed.
Lemma lem2715123 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2715124 : term582 = term583.
Proof. exact (MK_COMB (@lem2715123) (@lem2715122)). Qed.
Lemma lem2715125 : term662 = term663.
Proof. exact (MK_COMB (@lem2715124) (@lem2715119)). Qed.
Lemma lem2715126 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2715128 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715129 : term257 = term258.
Proof. exact (@lem2715128 (NUMERAL 0) term67). Qed.
Lemma lem2715130 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715131 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715132 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715131 h1) (fun h1 : term258 = True => @lem2715130)). Qed.
Lemma lem2715133 : term258 = True.
Proof. exact (EQ_MP (@lem2715132) (@lem2715130)). Qed.
Lemma lem2715134 : term257 = True.
Proof. exact (TRANS (@lem2715129) (@lem2715133)). Qed.
Lemma lem2715135 : True = term257.
Proof. exact (SYM (@lem2715134)). Qed.
Lemma lem2715136 : term257.
Proof. exact (EQ_MP (@lem2715135) (@lem0)). Qed.
Lemma lem2715137 : term665.
Proof. exact (@lem2715126 (@lem2715136)). Qed.
Lemma lem2715139 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715140 : term257 = term258.
Proof. exact (@lem2715139 (NUMERAL 0) term67). Qed.
Lemma lem2715141 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715142 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715143 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715142 h1) (fun h1 : term258 = True => @lem2715141)). Qed.
Lemma lem2715144 : term258 = True.
Proof. exact (EQ_MP (@lem2715143) (@lem2715141)). Qed.
Lemma lem2715145 : term257 = True.
Proof. exact (TRANS (@lem2715140) (@lem2715144)). Qed.
Lemma lem2715146 : True = term257.
Proof. exact (SYM (@lem2715145)). Qed.
Lemma lem2715147 : term257.
Proof. exact (EQ_MP (@lem2715146) (@lem0)). Qed.
Lemma lem2715148 : term663 = term666.
Proof. exact (@lem2715137 (@lem2715147)). Qed.
Lemma lem2715150 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715151 : term289 = term290.
Proof. exact (@lem2715150 term29 term67). Qed.
Lemma lem2715152 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715153 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715154 : term292 = term29.
Proof. exact (EQ_MP (@lem2715153) (@lem2715152)). Qed.
Lemma lem2715155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715156 : term290 = term28.
Proof. exact (MK_COMB (@lem2715155) (@lem2715154)). Qed.
Lemma lem2715157 : term289 = term28.
Proof. exact (TRANS (@lem2715151) (@lem2715156)). Qed.
Lemma lem2715159 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715160 : term269 = term32.
Proof. exact (@lem2715159 term67). Qed.
Lemma lem2715161 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2715162 : term588 = term582.
Proof. exact (MK_COMB (@lem2715161) (@lem2715160)). Qed.
Lemma lem2715163 : term666 = term662.
Proof. exact (MK_COMB (@lem2715162) (@lem2715157)). Qed.
Lemma lem2715165 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715166 : term662 = term667.
Proof. exact (@lem2715165 (NUMERAL 0) term29). Qed.
Lemma lem2715167 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2715168 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2715169 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2715168 h1) (fun h1 : term667 = True => @lem2715167)). Qed.
Lemma lem2715170 : term667 = True.
Proof. exact (EQ_MP (@lem2715169) (@lem2715167)). Qed.
Lemma lem2715171 : term662 = True.
Proof. exact (TRANS (@lem2715166) (@lem2715170)). Qed.
Lemma lem2715172 : term666 = True.
Proof. exact (TRANS (@lem2715163) (@lem2715171)). Qed.
Lemma lem2715173 : term663 = True.
Proof. exact (TRANS (@lem2715148) (@lem2715172)). Qed.
Lemma lem2715174 : term662 = True.
Proof. exact (TRANS (@lem2715125) (@lem2715173)). Qed.
Lemma lem2715175 : term661 = True.
Proof. exact (TRANS (@lem2715116) (@lem2715174)). Qed.
Lemma lem2715176 : True = term661.
Proof. exact (SYM (@lem2715175)). Qed.
Lemma lem2715177 : term661.
Proof. exact (EQ_MP (@lem2715176) (@lem0)). Qed.
Lemma lem2715178 (n : int) (h1 : term564 n) : term984 n.
Proof. exact (conj (@lem2715177) (@lem2715113 n h1)). Qed.
Lemma lem2715180 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2715181 (n : int) : term985 n.
Proof. exact (@lem2715180 term28 (term980 n)). Qed.
Lemma lem2715182 (n : int) (h1 : term564 n) : term986 n.
Proof. exact (@lem2715181 n (@lem2715178 n h1)). Qed.
Lemma lem2715183 (n : int) : (term987 n) = (term988 n).
Proof. exact (@lem1982781 (term632 n) term28 (term979 n)). Qed.
Lemma lem2715184 (n : int) : (term989 n) = (term990 n).
Proof. exact (@lem1982781 (term161 n) term28 term66). Qed.
Lemma lem2715186 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715187 : term66 = term210.
Proof. exact (@lem2715186 term67). Qed.
Lemma lem2715189 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715190 : term28 = term173.
Proof. exact (@lem2715189 term29). Qed.
Lemma lem2715191 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715192 : term287 = term675.
Proof. exact (MK_COMB (@lem2715191) (@lem2715190)). Qed.
Lemma lem2715193 : term289 = term991.
Proof. exact (MK_COMB (@lem2715192) (@lem2715187)). Qed.
Lemma lem2715194 : term991 = term992.
Proof. exact (@lem1981613 term28 term66 term66 term66). Qed.
Lemma lem2715196 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715197 : term149 = term150.
Proof. exact (@lem2715196 term67 term67). Qed.
Lemma lem2715198 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715199 : term152 = term67.
Proof. exact (EQ_MP (@lem2715198) (@lem940073)). Qed.
Lemma lem2715200 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715201 : term150 = term66.
Proof. exact (MK_COMB (@lem2715200) (@lem2715199)). Qed.
Lemma lem2715202 : term149 = term66.
Proof. exact (TRANS (@lem2715197) (@lem2715201)). Qed.
Lemma lem2715204 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715205 : term289 = term290.
Proof. exact (@lem2715204 term29 term67). Qed.
Lemma lem2715206 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715207 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715208 : term292 = term29.
Proof. exact (EQ_MP (@lem2715207) (@lem2715206)). Qed.
Lemma lem2715209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715210 : term290 = term28.
Proof. exact (MK_COMB (@lem2715209) (@lem2715208)). Qed.
Lemma lem2715211 : term289 = term28.
Proof. exact (TRANS (@lem2715205) (@lem2715210)). Qed.
Lemma lem2715212 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2715213 : term993 = term619.
Proof. exact (MK_COMB (@lem2715212) (@lem2715211)). Qed.
Lemma lem2715214 : term992 = term173.
Proof. exact (MK_COMB (@lem2715213) (@lem2715202)). Qed.
Lemma lem2715215 : term991 = term173.
Proof. exact (TRANS (@lem2715194) (@lem2715214)). Qed.
Lemma lem2715216 : term289 = term173.
Proof. exact (TRANS (@lem2715193) (@lem2715215)). Qed.
Lemma lem2715218 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2715219 : term173 = term28.
Proof. exact (@lem2715218 term28). Qed.
Lemma lem2715220 : term289 = term28.
Proof. exact (TRANS (@lem2715216) (@lem2715219)). Qed.
Lemma lem2715221 (n : int) : (term681 n) = (term682 n).
Proof. exact (@lem1982749 term28 term28 (term162 n)). Qed.
Lemma lem2715223 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715224 : term28 = term173.
Proof. exact (@lem2715223 term29). Qed.
Lemma lem2715226 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715227 : term28 = term173.
Proof. exact (@lem2715226 term29). Qed.
Lemma lem2715228 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715229 : term287 = term675.
Proof. exact (MK_COMB (@lem2715228) (@lem2715227)). Qed.
Lemma lem2715230 : term683 = term684.
Proof. exact (MK_COMB (@lem2715229) (@lem2715224)). Qed.
Lemma lem2715231 : term684 = term685.
Proof. exact (@lem1981613 term28 term28 term66 term66). Qed.
Lemma lem2715233 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715234 : term149 = term150.
Proof. exact (@lem2715233 term67 term67). Qed.
Lemma lem2715235 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715236 : term152 = term67.
Proof. exact (EQ_MP (@lem2715235) (@lem940073)). Qed.
Lemma lem2715237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715238 : term150 = term66.
Proof. exact (MK_COMB (@lem2715237) (@lem2715236)). Qed.
Lemma lem2715239 : term149 = term66.
Proof. exact (TRANS (@lem2715234) (@lem2715238)). Qed.
Lemma lem2715241 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715242 : term683 = term686.
Proof. exact (@lem2715241 term29 term29). Qed.
Lemma lem2715243 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715244 : term687 = term688.
Proof. exact (EQ_MP (@lem2715243) (@lem940073)). Qed.
Lemma lem2715245 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2715246 : term689 = term690.
Proof. exact (EQ_MP (@lem2715245) (@lem2715244)). Qed.
Lemma lem2715247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715248 : term686 = term691.
Proof. exact (MK_COMB (@lem2715247) (@lem2715246)). Qed.
Lemma lem2715249 : term683 = term691.
Proof. exact (TRANS (@lem2715242) (@lem2715248)). Qed.
Lemma lem2715250 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2715251 : term692 = term693.
Proof. exact (MK_COMB (@lem2715250) (@lem2715249)). Qed.
Lemma lem2715252 : term685 = term694.
Proof. exact (MK_COMB (@lem2715251) (@lem2715239)). Qed.
Lemma lem2715253 : term684 = term694.
Proof. exact (TRANS (@lem2715231) (@lem2715252)). Qed.
Lemma lem2715254 : term683 = term694.
Proof. exact (TRANS (@lem2715230) (@lem2715253)). Qed.
Lemma lem2715256 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2715257 : term694 = term691.
Proof. exact (@lem2715256 term691). Qed.
Lemma lem2715258 : term683 = term691.
Proof. exact (TRANS (@lem2715254) (@lem2715257)). Qed.
Lemma lem2715259 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715260 : term695 = term696.
Proof. exact (MK_COMB (@lem2715259) (@lem2715258)). Qed.
Lemma lem2715261 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2715262 (n : int) : (term682 n) = (term697 n).
Proof. exact (MK_COMB (@lem2715260) (@lem2715261 n)). Qed.
Lemma lem2715263 (n : int) : (term681 n) = (term697 n).
Proof. exact (TRANS (@lem2715221 n) (@lem2715262 n)). Qed.
Lemma lem2715264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715265 (n : int) : (term698 n) = (term699 n).
Proof. exact (MK_COMB (@lem2715264) (@lem2715263 n)). Qed.
Lemma lem2715266 (n : int) : (term990 n) = (term994 n).
Proof. exact (MK_COMB (@lem2715265 n) (@lem2715220)). Qed.
Lemma lem2715267 (n : int) : (term989 n) = (term994 n).
Proof. exact (TRANS (@lem2715184 n) (@lem2715266 n)). Qed.
Lemma lem2715268 (n : int) : (term701 n) = (term702 n).
Proof. exact (@lem1982749 term28 term140 (real_of_int n)). Qed.
Lemma lem2715270 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715271 : term140 = term141.
Proof. exact (@lem2715270 term67). Qed.
Lemma lem2715273 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715274 : term28 = term173.
Proof. exact (@lem2715273 term29). Qed.
Lemma lem2715275 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715276 : term287 = term675.
Proof. exact (MK_COMB (@lem2715275) (@lem2715274)). Qed.
Lemma lem2715277 : term676 = term677.
Proof. exact (MK_COMB (@lem2715276) (@lem2715271)). Qed.
Lemma lem2715278 : term677 = term678.
Proof. exact (@lem1981613 term28 term140 term66 term66). Qed.
Lemma lem2715280 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715281 : term149 = term150.
Proof. exact (@lem2715280 term67 term67). Qed.
Lemma lem2715282 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715283 : term152 = term67.
Proof. exact (EQ_MP (@lem2715282) (@lem940073)). Qed.
Lemma lem2715284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715285 : term150 = term66.
Proof. exact (MK_COMB (@lem2715284) (@lem2715283)). Qed.
Lemma lem2715286 : term149 = term66.
Proof. exact (TRANS (@lem2715281) (@lem2715285)). Qed.
Lemma lem2715288 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2715289 : term676 = term440.
Proof. exact (@lem2715288 term29 term67). Qed.
Lemma lem2715290 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715291 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715292 : term292 = term29.
Proof. exact (EQ_MP (@lem2715291) (@lem2715290)). Qed.
Lemma lem2715293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715294 : term290 = term28.
Proof. exact (MK_COMB (@lem2715293) (@lem2715292)). Qed.
Lemma lem2715295 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715296 : term440 = term184.
Proof. exact (MK_COMB (@lem2715295) (@lem2715294)). Qed.
Lemma lem2715297 : term676 = term184.
Proof. exact (TRANS (@lem2715289) (@lem2715296)). Qed.
Lemma lem2715298 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2715299 : term680 = term186.
Proof. exact (MK_COMB (@lem2715298) (@lem2715297)). Qed.
Lemma lem2715300 : term678 = term187.
Proof. exact (MK_COMB (@lem2715299) (@lem2715286)). Qed.
Lemma lem2715301 : term677 = term187.
Proof. exact (TRANS (@lem2715278) (@lem2715300)). Qed.
Lemma lem2715302 : term676 = term187.
Proof. exact (TRANS (@lem2715277) (@lem2715301)). Qed.
Lemma lem2715304 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2715305 : term187 = term184.
Proof. exact (@lem2715304 term184). Qed.
Lemma lem2715306 : term676 = term184.
Proof. exact (TRANS (@lem2715302) (@lem2715305)). Qed.
Lemma lem2715307 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715308 : term703 = term189.
Proof. exact (MK_COMB (@lem2715307) (@lem2715306)). Qed.
Lemma lem2715309 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2715310 (n : int) : (term702 n) = (term704 n).
Proof. exact (MK_COMB (@lem2715308) (@lem2715309 n)). Qed.
Lemma lem2715311 (n : int) : (term701 n) = (term704 n).
Proof. exact (TRANS (@lem2715268 n) (@lem2715310 n)). Qed.
Lemma lem2715312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715313 (n : int) : (term705 n) = (term706 n).
Proof. exact (MK_COMB (@lem2715312) (@lem2715311 n)). Qed.
Lemma lem2715314 (n : int) : (term988 n) = (term995 n).
Proof. exact (MK_COMB (@lem2715313 n) (@lem2715267 n)). Qed.
Lemma lem2715315 (n : int) : (term987 n) = (term995 n).
Proof. exact (TRANS (@lem2715183 n) (@lem2715314 n)). Qed.
Lemma lem2715316 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2715317 (n : int) : (term996 n) = (term997 n).
Proof. exact (MK_COMB (@lem2715316) (@lem2715315 n)). Qed.
Lemma lem2715318 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2715319 (n : int) : (term986 n) = (term998 n).
Proof. exact (MK_COMB (@lem2715317 n) (@lem2715318)). Qed.
Lemma lem2715320 (n : int) (h1 : term564 n) : term998 n.
Proof. exact (EQ_MP (@lem2715319 n) (@lem2715182 n h1)). Qed.
Lemma lem2715322 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2715323 : term581 = term257.
Proof. exact (@lem2715322 term32 term66). Qed.
Lemma lem2715325 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715326 : term66 = term210.
Proof. exact (@lem2715325 term67). Qed.
Lemma lem2715328 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715329 : term32 = term137.
Proof. exact (@lem2715328 (NUMERAL 0)). Qed.
Lemma lem2715330 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2715331 : term582 = term583.
Proof. exact (MK_COMB (@lem2715330) (@lem2715329)). Qed.
Lemma lem2715332 : term257 = term584.
Proof. exact (MK_COMB (@lem2715331) (@lem2715326)). Qed.
Lemma lem2715333 : term585.
Proof. exact (@lem1980255 term32 term66 term66 term66). Qed.
Lemma lem2715335 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715336 : term257 = term258.
Proof. exact (@lem2715335 (NUMERAL 0) term67). Qed.
Lemma lem2715337 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715338 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715339 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715338 h1) (fun h1 : term258 = True => @lem2715337)). Qed.
Lemma lem2715340 : term258 = True.
Proof. exact (EQ_MP (@lem2715339) (@lem2715337)). Qed.
Lemma lem2715341 : term257 = True.
Proof. exact (TRANS (@lem2715336) (@lem2715340)). Qed.
Lemma lem2715342 : True = term257.
Proof. exact (SYM (@lem2715341)). Qed.
Lemma lem2715343 : term257.
Proof. exact (EQ_MP (@lem2715342) (@lem0)). Qed.
Lemma lem2715344 : term586.
Proof. exact (@lem2715333 (@lem2715343)). Qed.
Lemma lem2715346 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715347 : term257 = term258.
Proof. exact (@lem2715346 (NUMERAL 0) term67). Qed.
Lemma lem2715348 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715349 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715350 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715349 h1) (fun h1 : term258 = True => @lem2715348)). Qed.
Lemma lem2715351 : term258 = True.
Proof. exact (EQ_MP (@lem2715350) (@lem2715348)). Qed.
Lemma lem2715352 : term257 = True.
Proof. exact (TRANS (@lem2715347) (@lem2715351)). Qed.
Lemma lem2715353 : True = term257.
Proof. exact (SYM (@lem2715352)). Qed.
Lemma lem2715354 : term257.
Proof. exact (EQ_MP (@lem2715353) (@lem0)). Qed.
Lemma lem2715355 : term584 = term587.
Proof. exact (@lem2715344 (@lem2715354)). Qed.
Lemma lem2715357 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715358 : term149 = term150.
Proof. exact (@lem2715357 term67 term67). Qed.
Lemma lem2715359 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715360 : term152 = term67.
Proof. exact (EQ_MP (@lem2715359) (@lem940073)). Qed.
Lemma lem2715361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715362 : term150 = term66.
Proof. exact (MK_COMB (@lem2715361) (@lem2715360)). Qed.
Lemma lem2715363 : term149 = term66.
Proof. exact (TRANS (@lem2715358) (@lem2715362)). Qed.
Lemma lem2715365 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715366 : term269 = term32.
Proof. exact (@lem2715365 term67). Qed.
Lemma lem2715367 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2715368 : term588 = term582.
Proof. exact (MK_COMB (@lem2715367) (@lem2715366)). Qed.
Lemma lem2715369 : term587 = term257.
Proof. exact (MK_COMB (@lem2715368) (@lem2715363)). Qed.
Lemma lem2715371 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715372 : term257 = term258.
Proof. exact (@lem2715371 (NUMERAL 0) term67). Qed.
Lemma lem2715373 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715374 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715375 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715374 h1) (fun h1 : term258 = True => @lem2715373)). Qed.
Lemma lem2715376 : term258 = True.
Proof. exact (EQ_MP (@lem2715375) (@lem2715373)). Qed.
Lemma lem2715377 : term257 = True.
Proof. exact (TRANS (@lem2715372) (@lem2715376)). Qed.
Lemma lem2715378 : term587 = True.
Proof. exact (TRANS (@lem2715369) (@lem2715377)). Qed.
Lemma lem2715379 : term584 = True.
Proof. exact (TRANS (@lem2715355) (@lem2715378)). Qed.
Lemma lem2715380 : term257 = True.
Proof. exact (TRANS (@lem2715332) (@lem2715379)). Qed.
Lemma lem2715381 : term581 = True.
Proof. exact (TRANS (@lem2715323) (@lem2715380)). Qed.
Lemma lem2715382 : True = term581.
Proof. exact (SYM (@lem2715381)). Qed.
Lemma lem2715383 : term581.
Proof. exact (EQ_MP (@lem2715382) (@lem0)). Qed.
Lemma lem2715384 (n : int) (h1 : term564 n) : term889 n.
Proof. exact (conj (@lem2715383) (@lem2714798 n h1)). Qed.
Lemma lem2715386 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2715387 (n : int) : term890 n.
Proof. exact (@lem2715386 term66 (term297 n)). Qed.
Lemma lem2715388 (n : int) (h1 : term564 n) : term891 n.
Proof. exact (@lem2715387 n (@lem2715384 n h1)). Qed.
Lemma lem2715389 (n : int) : (term892 n) = (term297 n).
Proof. exact (@lem1982733 (term297 n)). Qed.
Lemma lem2715390 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2715391 (n : int) : (term893 n) = (term299 n).
Proof. exact (MK_COMB (@lem2715390) (@lem2715389 n)). Qed.
Lemma lem2715392 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2715393 (n : int) : (term891 n) = (term300 n).
Proof. exact (MK_COMB (@lem2715391 n) (@lem2715392)). Qed.
Lemma lem2715394 (n : int) (h1 : term564 n) : term300 n.
Proof. exact (EQ_MP (@lem2715393 n) (@lem2715388 n h1)). Qed.
Lemma lem2715396 (y : real) : term595 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2715397 (n : int) : term596 n.
Proof. exact (@lem2715396 (term195 n)). Qed.
Lemma lem2715398 (n : int) (h1 : term564 n) : term597 n.
Proof. exact (@lem2715397 n (@lem2714795 n h1)). Qed.
Lemma lem2715399 (n : int) (h1 : term564 n) : term715 n.
Proof. exact (@lem2715398 n h1 term66). Qed.
Lemma lem2715400 (n : int) : (term715 n) = ((term716 n) = term32).
Proof. exact (eq_refl (term715 n)). Qed.
Lemma lem2715401 (n : int) (h1 : term564 n) : (term716 n) = term32.
Proof. exact (EQ_MP (@lem2715400 n) (@lem2715399 n h1)). Qed.
Lemma lem2715402 (n : int) : (term716 n) = (term195 n).
Proof. exact (@lem1982733 (term195 n)). Qed.
Lemma lem2715403 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2715404 (n : int) : (term717 n) = (term197 n).
Proof. exact (MK_COMB (@lem2715403) (@lem2715402 n)). Qed.
Lemma lem2715405 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2715406 (n : int) : ((term716 n) = term32) = ((term195 n) = term32).
Proof. exact (MK_COMB (@lem2715404 n) (@lem2715405)). Qed.
Lemma lem2715407 (n : int) (h1 : term564 n) : (term195 n) = term32.
Proof. exact (EQ_MP (@lem2715406 n) (@lem2715401 n h1)). Qed.
Lemma lem2715408 (n : int) (h1 : term564 n) : term894 n.
Proof. exact (conj (@lem2715407 n h1) (@lem2715394 n h1)). Qed.
Lemma lem2715410 (x : real) (y : real) : term627 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2715411 (n : int) : term895 n.
Proof. exact (@lem2715410 (term195 n) (term297 n)). Qed.
Lemma lem2715412 (n : int) (h1 : term564 n) : term896 n.
Proof. exact (@lem2715411 n (@lem2715408 n h1)). Qed.
Lemma lem2715413 (n : int) : (term897 n) = (term898 n).
Proof. exact (@lem1982755 (real_of_int n) (term193 n) (term297 n)). Qed.
Lemma lem2715414 (n : int) : (term899 n) = (term900 n).
Proof. exact (@lem1982755 (term190 n) (term170 n) (term297 n)). Qed.
Lemma lem2715415 (n : int) : (term901 n) = (term902 n).
Proof. exact (@lem1982763 (term170 n) (term48 n) term184). Qed.
Lemma lem2715416 (n : int) : (term725 n) = (term638 n).
Proof. exact (@lem1982713 term140 (term48 n)). Qed.
Lemma lem2715418 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715419 : term66 = term210.
Proof. exact (@lem2715418 term67). Qed.
Lemma lem2715421 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715422 : term140 = term141.
Proof. exact (@lem2715421 term67). Qed.
Lemma lem2715423 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715424 : term639 = term640.
Proof. exact (MK_COMB (@lem2715423) (@lem2715422)). Qed.
Lemma lem2715425 : term641 = term642.
Proof. exact (MK_COMB (@lem2715424) (@lem2715419)). Qed.
Lemma lem2715426 : term643.
Proof. exact (@lem1981473 term140 term66 term66 term66 term32 term66). Qed.
Lemma lem2715428 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715429 : term257 = term258.
Proof. exact (@lem2715428 (NUMERAL 0) term67). Qed.
Lemma lem2715430 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715431 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715432 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715431 h1) (fun h1 : term258 = True => @lem2715430)). Qed.
Lemma lem2715433 : term258 = True.
Proof. exact (EQ_MP (@lem2715432) (@lem2715430)). Qed.
Lemma lem2715434 : term257 = True.
Proof. exact (TRANS (@lem2715429) (@lem2715433)). Qed.
Lemma lem2715435 : True = term257.
Proof. exact (SYM (@lem2715434)). Qed.
Lemma lem2715436 : term257.
Proof. exact (EQ_MP (@lem2715435) (@lem0)). Qed.
Lemma lem2715437 : term644.
Proof. exact (@lem2715426 (@lem2715436)). Qed.
Lemma lem2715439 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715440 : term257 = term258.
Proof. exact (@lem2715439 (NUMERAL 0) term67). Qed.
Lemma lem2715441 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715442 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715443 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715442 h1) (fun h1 : term258 = True => @lem2715441)). Qed.
Lemma lem2715444 : term258 = True.
Proof. exact (EQ_MP (@lem2715443) (@lem2715441)). Qed.
Lemma lem2715445 : term257 = True.
Proof. exact (TRANS (@lem2715440) (@lem2715444)). Qed.
Lemma lem2715446 : True = term257.
Proof. exact (SYM (@lem2715445)). Qed.
Lemma lem2715447 : term257.
Proof. exact (EQ_MP (@lem2715446) (@lem0)). Qed.
Lemma lem2715448 : term645.
Proof. exact (@lem2715437 (@lem2715447)). Qed.
Lemma lem2715450 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715451 : term257 = term258.
Proof. exact (@lem2715450 (NUMERAL 0) term67). Qed.
Lemma lem2715452 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715453 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715454 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715453 h1) (fun h1 : term258 = True => @lem2715452)). Qed.
Lemma lem2715455 : term258 = True.
Proof. exact (EQ_MP (@lem2715454) (@lem2715452)). Qed.
Lemma lem2715456 : term257 = True.
Proof. exact (TRANS (@lem2715451) (@lem2715455)). Qed.
Lemma lem2715457 : True = term257.
Proof. exact (SYM (@lem2715456)). Qed.
Lemma lem2715458 : term257.
Proof. exact (EQ_MP (@lem2715457) (@lem0)). Qed.
Lemma lem2715459 : term646.
Proof. exact (@lem2715448 (@lem2715458)). Qed.
Lemma lem2715461 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715462 : term149 = term150.
Proof. exact (@lem2715461 term67 term67). Qed.
Lemma lem2715463 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715464 : term152 = term67.
Proof. exact (EQ_MP (@lem2715463) (@lem940073)). Qed.
Lemma lem2715465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715466 : term150 = term66.
Proof. exact (MK_COMB (@lem2715465) (@lem2715464)). Qed.
Lemma lem2715467 : term149 = term66.
Proof. exact (TRANS (@lem2715462) (@lem2715466)). Qed.
Lemma lem2715469 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2715470 : term211 = term214.
Proof. exact (@lem2715469 term67 term67). Qed.
Lemma lem2715471 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715472 : term152 = term67.
Proof. exact (EQ_MP (@lem2715471) (@lem940073)). Qed.
Lemma lem2715473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715474 : term150 = term66.
Proof. exact (MK_COMB (@lem2715473) (@lem2715472)). Qed.
Lemma lem2715475 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715476 : term214 = term140.
Proof. exact (MK_COMB (@lem2715475) (@lem2715474)). Qed.
Lemma lem2715477 : term211 = term140.
Proof. exact (TRANS (@lem2715470) (@lem2715476)). Qed.
Lemma lem2715478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715479 : term647 = term639.
Proof. exact (MK_COMB (@lem2715478) (@lem2715477)). Qed.
Lemma lem2715480 : term648 = term641.
Proof. exact (MK_COMB (@lem2715479) (@lem2715467)). Qed.
Lemma lem2715482 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2715483 : term641 = term32.
Proof. exact (@lem2715482 term67). Qed.
Lemma lem2715484 : term648 = term32.
Proof. exact (TRANS (@lem2715480) (@lem2715483)). Qed.
Lemma lem2715485 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715486 : term650 = term267.
Proof. exact (MK_COMB (@lem2715485) (@lem2715484)). Qed.
Lemma lem2715487 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2715488 : term651 = term269.
Proof. exact (MK_COMB (@lem2715486) (@lem2715487)). Qed.
Lemma lem2715490 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715491 : term269 = term32.
Proof. exact (@lem2715490 term67). Qed.
Lemma lem2715492 : term651 = term32.
Proof. exact (TRANS (@lem2715488) (@lem2715491)). Qed.
Lemma lem2715494 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715495 : term149 = term150.
Proof. exact (@lem2715494 term67 term67). Qed.
Lemma lem2715496 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715497 : term152 = term67.
Proof. exact (EQ_MP (@lem2715496) (@lem940073)). Qed.
Lemma lem2715498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715499 : term150 = term66.
Proof. exact (MK_COMB (@lem2715498) (@lem2715497)). Qed.
Lemma lem2715500 : term149 = term66.
Proof. exact (TRANS (@lem2715495) (@lem2715499)). Qed.
Lemma lem2715501 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2715502 : term271 = term269.
Proof. exact (MK_COMB (@lem2715501) (@lem2715500)). Qed.
Lemma lem2715504 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715505 : term269 = term32.
Proof. exact (@lem2715504 term67). Qed.
Lemma lem2715506 : term271 = term32.
Proof. exact (TRANS (@lem2715502) (@lem2715505)). Qed.
Lemma lem2715507 : term32 = term271.
Proof. exact (SYM (@lem2715506)). Qed.
Lemma lem2715508 : term651 = term271.
Proof. exact (TRANS (@lem2715492) (@lem2715507)). Qed.
Lemma lem2715509 : term642 = term137.
Proof. exact (@lem2715459 (@lem2715508)). Qed.
Lemma lem2715510 : term641 = term137.
Proof. exact (TRANS (@lem2715425) (@lem2715509)). Qed.
Lemma lem2715512 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2715513 : term137 = term32.
Proof. exact (@lem2715512 term32). Qed.
Lemma lem2715514 : term641 = term32.
Proof. exact (TRANS (@lem2715510) (@lem2715513)). Qed.
Lemma lem2715515 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715516 : term652 = term267.
Proof. exact (MK_COMB (@lem2715515) (@lem2715514)). Qed.
Lemma lem2715517 (n : int) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2715518 (n : int) : (term638 n) = (term653 n).
Proof. exact (MK_COMB (@lem2715516) (@lem2715517 n)). Qed.
Lemma lem2715519 (n : int) : (term725 n) = (term653 n).
Proof. exact (TRANS (@lem2715416 n) (@lem2715518 n)). Qed.
Lemma lem2715520 (n : int) : (term653 n) = term32.
Proof. exact (@lem1982719 (term48 n)). Qed.
Lemma lem2715521 (n : int) : (term725 n) = term32.
Proof. exact (TRANS (@lem2715519 n) (@lem2715520 n)). Qed.
Lemma lem2715522 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715523 (n : int) : (term861 n) = term102.
Proof. exact (MK_COMB (@lem2715522) (@lem2715521 n)). Qed.
Lemma lem2715524 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2715525 (n : int) : (term902 n) = term422.
Proof. exact (MK_COMB (@lem2715523 n) (@lem2715524)). Qed.
Lemma lem2715526 (n : int) : (term901 n) = term422.
Proof. exact (TRANS (@lem2715415 n) (@lem2715525 n)). Qed.
Lemma lem2715527 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2715528 (n : int) : (term901 n) = term184.
Proof. exact (TRANS (@lem2715526 n) (@lem2715527)). Qed.
Lemma lem2715529 (n : int) : (term192 n) = (term192 n).
Proof. exact (eq_refl (term192 n)). Qed.
Lemma lem2715530 (n : int) : (term900 n) = (term903 n).
Proof. exact (MK_COMB (@lem2715529 n) (@lem2715528 n)). Qed.
Lemma lem2715531 (n : int) : (term899 n) = (term903 n).
Proof. exact (TRANS (@lem2715414 n) (@lem2715530 n)). Qed.
Lemma lem2715532 (n : int) : (term194 n) = (term194 n).
Proof. exact (eq_refl (term194 n)). Qed.
Lemma lem2715533 (n : int) : (term898 n) = (term904 n).
Proof. exact (MK_COMB (@lem2715532 n) (@lem2715531 n)). Qed.
Lemma lem2715534 (n : int) : (term897 n) = (term904 n).
Proof. exact (TRANS (@lem2715413 n) (@lem2715533 n)). Qed.
Lemma lem2715535 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2715536 (n : int) : (term905 n) = (term906 n).
Proof. exact (MK_COMB (@lem2715535) (@lem2715534 n)). Qed.
Lemma lem2715537 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2715538 (n : int) : (term896 n) = (term907 n).
Proof. exact (MK_COMB (@lem2715536 n) (@lem2715537)). Qed.
Lemma lem2715539 (n : int) (h1 : term564 n) : term907 n.
Proof. exact (EQ_MP (@lem2715538 n) (@lem2715412 n h1)). Qed.
Lemma lem2715541 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2715542 : term661 = term662.
Proof. exact (@lem2715541 term32 term28). Qed.
Lemma lem2715544 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715545 : term28 = term173.
Proof. exact (@lem2715544 term29). Qed.
Lemma lem2715547 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715548 : term32 = term137.
Proof. exact (@lem2715547 (NUMERAL 0)). Qed.
Lemma lem2715549 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2715550 : term582 = term583.
Proof. exact (MK_COMB (@lem2715549) (@lem2715548)). Qed.
Lemma lem2715551 : term662 = term663.
Proof. exact (MK_COMB (@lem2715550) (@lem2715545)). Qed.
Lemma lem2715552 : term664.
Proof. exact (@lem1980255 term32 term66 term28 term66). Qed.
Lemma lem2715554 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715555 : term257 = term258.
Proof. exact (@lem2715554 (NUMERAL 0) term67). Qed.
Lemma lem2715556 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715557 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715558 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715557 h1) (fun h1 : term258 = True => @lem2715556)). Qed.
Lemma lem2715559 : term258 = True.
Proof. exact (EQ_MP (@lem2715558) (@lem2715556)). Qed.
Lemma lem2715560 : term257 = True.
Proof. exact (TRANS (@lem2715555) (@lem2715559)). Qed.
Lemma lem2715561 : True = term257.
Proof. exact (SYM (@lem2715560)). Qed.
Lemma lem2715562 : term257.
Proof. exact (EQ_MP (@lem2715561) (@lem0)). Qed.
Lemma lem2715563 : term665.
Proof. exact (@lem2715552 (@lem2715562)). Qed.
Lemma lem2715565 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715566 : term257 = term258.
Proof. exact (@lem2715565 (NUMERAL 0) term67). Qed.
Lemma lem2715567 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715568 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715569 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715568 h1) (fun h1 : term258 = True => @lem2715567)). Qed.
Lemma lem2715570 : term258 = True.
Proof. exact (EQ_MP (@lem2715569) (@lem2715567)). Qed.
Lemma lem2715571 : term257 = True.
Proof. exact (TRANS (@lem2715566) (@lem2715570)). Qed.
Lemma lem2715572 : True = term257.
Proof. exact (SYM (@lem2715571)). Qed.
Lemma lem2715573 : term257.
Proof. exact (EQ_MP (@lem2715572) (@lem0)). Qed.
Lemma lem2715574 : term663 = term666.
Proof. exact (@lem2715563 (@lem2715573)). Qed.
Lemma lem2715576 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715577 : term289 = term290.
Proof. exact (@lem2715576 term29 term67). Qed.
Lemma lem2715578 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715579 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715580 : term292 = term29.
Proof. exact (EQ_MP (@lem2715579) (@lem2715578)). Qed.
Lemma lem2715581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715582 : term290 = term28.
Proof. exact (MK_COMB (@lem2715581) (@lem2715580)). Qed.
Lemma lem2715583 : term289 = term28.
Proof. exact (TRANS (@lem2715577) (@lem2715582)). Qed.
Lemma lem2715585 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715586 : term269 = term32.
Proof. exact (@lem2715585 term67). Qed.
Lemma lem2715587 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2715588 : term588 = term582.
Proof. exact (MK_COMB (@lem2715587) (@lem2715586)). Qed.
Lemma lem2715589 : term666 = term662.
Proof. exact (MK_COMB (@lem2715588) (@lem2715583)). Qed.
Lemma lem2715591 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715592 : term662 = term667.
Proof. exact (@lem2715591 (NUMERAL 0) term29). Qed.
Lemma lem2715593 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2715594 (h1 : term580 = term181) : term667 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2715595 : (term580 = term181) = (term667 = True).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2715594 h1) (fun h1 : term667 = True => @lem2715593)). Qed.
Lemma lem2715596 : term667 = True.
Proof. exact (EQ_MP (@lem2715595) (@lem2715593)). Qed.
Lemma lem2715597 : term662 = True.
Proof. exact (TRANS (@lem2715592) (@lem2715596)). Qed.
Lemma lem2715598 : term666 = True.
Proof. exact (TRANS (@lem2715589) (@lem2715597)). Qed.
Lemma lem2715599 : term663 = True.
Proof. exact (TRANS (@lem2715574) (@lem2715598)). Qed.
Lemma lem2715600 : term662 = True.
Proof. exact (TRANS (@lem2715551) (@lem2715599)). Qed.
Lemma lem2715601 : term661 = True.
Proof. exact (TRANS (@lem2715542) (@lem2715600)). Qed.
Lemma lem2715602 : True = term661.
Proof. exact (SYM (@lem2715601)). Qed.
Lemma lem2715603 : term661.
Proof. exact (EQ_MP (@lem2715602) (@lem0)). Qed.
Lemma lem2715604 (n : int) (h1 : term564 n) : term908 n.
Proof. exact (conj (@lem2715603) (@lem2715539 n h1)). Qed.
Lemma lem2715606 (x : real) (y : real) : term590 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2715607 (n : int) : term909 n.
Proof. exact (@lem2715606 term28 (term904 n)). Qed.
Lemma lem2715608 (n : int) (h1 : term564 n) : term910 n.
Proof. exact (@lem2715607 n (@lem2715604 n h1)). Qed.
Lemma lem2715609 (n : int) : (term911 n) = (term912 n).
Proof. exact (@lem1982781 (real_of_int n) term28 (term903 n)). Qed.
Lemma lem2715610 (n : int) : (term913 n) = (term914 n).
Proof. exact (@lem1982781 (term190 n) term28 term184). Qed.
Lemma lem2715612 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715613 : term184 = term187.
Proof. exact (@lem2715612 term29). Qed.
Lemma lem2715615 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715616 : term28 = term173.
Proof. exact (@lem2715615 term29). Qed.
Lemma lem2715617 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715618 : term287 = term675.
Proof. exact (MK_COMB (@lem2715617) (@lem2715616)). Qed.
Lemma lem2715619 : term738 = term739.
Proof. exact (MK_COMB (@lem2715618) (@lem2715613)). Qed.
Lemma lem2715620 : term739 = term740.
Proof. exact (@lem1981613 term28 term184 term66 term66). Qed.
Lemma lem2715622 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715623 : term149 = term150.
Proof. exact (@lem2715622 term67 term67). Qed.
Lemma lem2715624 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715625 : term152 = term67.
Proof. exact (EQ_MP (@lem2715624) (@lem940073)). Qed.
Lemma lem2715626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715627 : term150 = term66.
Proof. exact (MK_COMB (@lem2715626) (@lem2715625)). Qed.
Lemma lem2715628 : term149 = term66.
Proof. exact (TRANS (@lem2715623) (@lem2715627)). Qed.
Lemma lem2715630 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2715631 : term738 = term741.
Proof. exact (@lem2715630 term29 term29). Qed.
Lemma lem2715632 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715633 : term687 = term688.
Proof. exact (EQ_MP (@lem2715632) (@lem940073)). Qed.
Lemma lem2715634 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2715635 : term689 = term690.
Proof. exact (EQ_MP (@lem2715634) (@lem2715633)). Qed.
Lemma lem2715636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715637 : term686 = term691.
Proof. exact (MK_COMB (@lem2715636) (@lem2715635)). Qed.
Lemma lem2715638 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715639 : term741 = term742.
Proof. exact (MK_COMB (@lem2715638) (@lem2715637)). Qed.
Lemma lem2715640 : term738 = term742.
Proof. exact (TRANS (@lem2715631) (@lem2715639)). Qed.
Lemma lem2715641 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2715642 : term743 = term744.
Proof. exact (MK_COMB (@lem2715641) (@lem2715640)). Qed.
Lemma lem2715643 : term740 = term745.
Proof. exact (MK_COMB (@lem2715642) (@lem2715628)). Qed.
Lemma lem2715644 : term739 = term745.
Proof. exact (TRANS (@lem2715620) (@lem2715643)). Qed.
Lemma lem2715645 : term738 = term745.
Proof. exact (TRANS (@lem2715619) (@lem2715644)). Qed.
Lemma lem2715647 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2715648 : term745 = term742.
Proof. exact (@lem2715647 term742). Qed.
Lemma lem2715649 : term738 = term742.
Proof. exact (TRANS (@lem2715645) (@lem2715648)). Qed.
Lemma lem2715650 (n : int) : (term736 n) = (term737 n).
Proof. exact (@lem1982749 term28 term184 (term162 n)). Qed.
Lemma lem2715652 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715653 : term184 = term187.
Proof. exact (@lem2715652 term29). Qed.
Lemma lem2715655 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715656 : term28 = term173.
Proof. exact (@lem2715655 term29). Qed.
Lemma lem2715657 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715658 : term287 = term675.
Proof. exact (MK_COMB (@lem2715657) (@lem2715656)). Qed.
Lemma lem2715659 : term738 = term739.
Proof. exact (MK_COMB (@lem2715658) (@lem2715653)). Qed.
Lemma lem2715660 : term739 = term740.
Proof. exact (@lem1981613 term28 term184 term66 term66). Qed.
Lemma lem2715662 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715663 : term149 = term150.
Proof. exact (@lem2715662 term67 term67). Qed.
Lemma lem2715664 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715665 : term152 = term67.
Proof. exact (EQ_MP (@lem2715664) (@lem940073)). Qed.
Lemma lem2715666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715667 : term150 = term66.
Proof. exact (MK_COMB (@lem2715666) (@lem2715665)). Qed.
Lemma lem2715668 : term149 = term66.
Proof. exact (TRANS (@lem2715663) (@lem2715667)). Qed.
Lemma lem2715670 (m : nat) (n : nat) : (term679 m n) = (term178 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem2715671 : term738 = term741.
Proof. exact (@lem2715670 term29 term29). Qed.
Lemma lem2715672 : (term151 = (BIT1 0)) = (term687 = term688).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715673 : term687 = term688.
Proof. exact (EQ_MP (@lem2715672) (@lem940073)). Qed.
Lemma lem2715674 : (term687 = term688) = (term689 = term690).
Proof. exact (@lem1008952 term181 term688). Qed.
Lemma lem2715675 : term689 = term690.
Proof. exact (EQ_MP (@lem2715674) (@lem2715673)). Qed.
Lemma lem2715676 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715677 : term686 = term691.
Proof. exact (MK_COMB (@lem2715676) (@lem2715675)). Qed.
Lemma lem2715678 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715679 : term741 = term742.
Proof. exact (MK_COMB (@lem2715678) (@lem2715677)). Qed.
Lemma lem2715680 : term738 = term742.
Proof. exact (TRANS (@lem2715671) (@lem2715679)). Qed.
Lemma lem2715681 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2715682 : term743 = term744.
Proof. exact (MK_COMB (@lem2715681) (@lem2715680)). Qed.
Lemma lem2715683 : term740 = term745.
Proof. exact (MK_COMB (@lem2715682) (@lem2715668)). Qed.
Lemma lem2715684 : term739 = term745.
Proof. exact (TRANS (@lem2715660) (@lem2715683)). Qed.
Lemma lem2715685 : term738 = term745.
Proof. exact (TRANS (@lem2715659) (@lem2715684)). Qed.
Lemma lem2715687 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2715688 : term745 = term742.
Proof. exact (@lem2715687 term742). Qed.
Lemma lem2715689 : term738 = term742.
Proof. exact (TRANS (@lem2715685) (@lem2715688)). Qed.
Lemma lem2715690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715691 : term746 = term747.
Proof. exact (MK_COMB (@lem2715690) (@lem2715689)). Qed.
Lemma lem2715692 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2715693 (n : int) : (term737 n) = (term748 n).
Proof. exact (MK_COMB (@lem2715691) (@lem2715692 n)). Qed.
Lemma lem2715694 (n : int) : (term736 n) = (term748 n).
Proof. exact (TRANS (@lem2715650 n) (@lem2715693 n)). Qed.
Lemma lem2715695 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715696 (n : int) : (term874 n) = (term875 n).
Proof. exact (MK_COMB (@lem2715695) (@lem2715694 n)). Qed.
Lemma lem2715697 (n : int) : (term914 n) = (term915 n).
Proof. exact (MK_COMB (@lem2715696 n) (@lem2715649)). Qed.
Lemma lem2715698 (n : int) : (term913 n) = (term915 n).
Proof. exact (TRANS (@lem2715610 n) (@lem2715697 n)). Qed.
Lemma lem2715701 (n : int) : (term749 n) = (term749 n).
Proof. exact (eq_refl (term749 n)). Qed.
Lemma lem2715702 (n : int) : (term912 n) = (term916 n).
Proof. exact (MK_COMB (@lem2715701 n) (@lem2715698 n)). Qed.
Lemma lem2715703 (n : int) : (term911 n) = (term916 n).
Proof. exact (TRANS (@lem2715609 n) (@lem2715702 n)). Qed.
Lemma lem2715704 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2715705 (n : int) : (term917 n) = (term918 n).
Proof. exact (MK_COMB (@lem2715704) (@lem2715703 n)). Qed.
Lemma lem2715706 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2715707 (n : int) : (term910 n) = (term919 n).
Proof. exact (MK_COMB (@lem2715705 n) (@lem2715706)). Qed.
Lemma lem2715708 (n : int) (h1 : term564 n) : term919 n.
Proof. exact (EQ_MP (@lem2715707 n) (@lem2715608 n h1)). Qed.
Lemma lem2715709 (n : int) (h1 : term564 n) : term999 n.
Proof. exact (conj (@lem2715708 n h1) (@lem2715320 n h1)). Qed.
Lemma lem2715711 (x : real) (y : real) : term755 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2715712 (n : int) : term1000 n.
Proof. exact (@lem2715711 (term916 n) (term995 n)). Qed.
Lemma lem2715713 (n : int) (h1 : term564 n) : term1001 n.
Proof. exact (@lem2715712 n (@lem2715709 n h1)). Qed.
Lemma lem2715714 (n : int) : (term1002 n) = (term1003 n).
Proof. exact (@lem1982753 (term760 n) (term704 n) (term915 n) (term994 n)). Qed.
Lemma lem2715715 (n : int) : (term761 n) = (term762 n).
Proof. exact (@lem1982711 term28 term184 (real_of_int n)). Qed.
Lemma lem2715717 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715718 : term184 = term187.
Proof. exact (@lem2715717 term29). Qed.
Lemma lem2715720 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715721 : term28 = term173.
Proof. exact (@lem2715720 term29). Qed.
Lemma lem2715722 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715723 : term157 = term373.
Proof. exact (MK_COMB (@lem2715722) (@lem2715721)). Qed.
Lemma lem2715724 : term763 = term764.
Proof. exact (MK_COMB (@lem2715723) (@lem2715718)). Qed.
Lemma lem2715725 : term765.
Proof. exact (@lem1981473 term28 term66 term184 term66 term32 term66). Qed.
Lemma lem2715727 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715728 : term257 = term258.
Proof. exact (@lem2715727 (NUMERAL 0) term67). Qed.
Lemma lem2715729 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715730 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715731 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715730 h1) (fun h1 : term258 = True => @lem2715729)). Qed.
Lemma lem2715732 : term258 = True.
Proof. exact (EQ_MP (@lem2715731) (@lem2715729)). Qed.
Lemma lem2715733 : term257 = True.
Proof. exact (TRANS (@lem2715728) (@lem2715732)). Qed.
Lemma lem2715734 : True = term257.
Proof. exact (SYM (@lem2715733)). Qed.
Lemma lem2715735 : term257.
Proof. exact (EQ_MP (@lem2715734) (@lem0)). Qed.
Lemma lem2715736 : term766.
Proof. exact (@lem2715725 (@lem2715735)). Qed.
Lemma lem2715738 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715739 : term257 = term258.
Proof. exact (@lem2715738 (NUMERAL 0) term67). Qed.
Lemma lem2715740 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715741 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715742 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715741 h1) (fun h1 : term258 = True => @lem2715740)). Qed.
Lemma lem2715743 : term258 = True.
Proof. exact (EQ_MP (@lem2715742) (@lem2715740)). Qed.
Lemma lem2715744 : term257 = True.
Proof. exact (TRANS (@lem2715739) (@lem2715743)). Qed.
Lemma lem2715745 : True = term257.
Proof. exact (SYM (@lem2715744)). Qed.
Lemma lem2715746 : term257.
Proof. exact (EQ_MP (@lem2715745) (@lem0)). Qed.
Lemma lem2715747 : term767.
Proof. exact (@lem2715736 (@lem2715746)). Qed.
Lemma lem2715749 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715750 : term257 = term258.
Proof. exact (@lem2715749 (NUMERAL 0) term67). Qed.
Lemma lem2715751 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715752 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715753 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715752 h1) (fun h1 : term258 = True => @lem2715751)). Qed.
Lemma lem2715754 : term258 = True.
Proof. exact (EQ_MP (@lem2715753) (@lem2715751)). Qed.
Lemma lem2715755 : term257 = True.
Proof. exact (TRANS (@lem2715750) (@lem2715754)). Qed.
Lemma lem2715756 : True = term257.
Proof. exact (SYM (@lem2715755)). Qed.
Lemma lem2715757 : term257.
Proof. exact (EQ_MP (@lem2715756) (@lem0)). Qed.
Lemma lem2715758 : term768.
Proof. exact (@lem2715747 (@lem2715757)). Qed.
Lemma lem2715760 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2715761 : term439 = term440.
Proof. exact (@lem2715760 term29 term67). Qed.
Lemma lem2715762 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715763 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715764 : term292 = term29.
Proof. exact (EQ_MP (@lem2715763) (@lem2715762)). Qed.
Lemma lem2715765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715766 : term290 = term28.
Proof. exact (MK_COMB (@lem2715765) (@lem2715764)). Qed.
Lemma lem2715767 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715768 : term440 = term184.
Proof. exact (MK_COMB (@lem2715767) (@lem2715766)). Qed.
Lemma lem2715769 : term439 = term184.
Proof. exact (TRANS (@lem2715761) (@lem2715768)). Qed.
Lemma lem2715771 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715772 : term289 = term290.
Proof. exact (@lem2715771 term29 term67). Qed.
Lemma lem2715773 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715774 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715775 : term292 = term29.
Proof. exact (EQ_MP (@lem2715774) (@lem2715773)). Qed.
Lemma lem2715776 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715777 : term290 = term28.
Proof. exact (MK_COMB (@lem2715776) (@lem2715775)). Qed.
Lemma lem2715778 : term289 = term28.
Proof. exact (TRANS (@lem2715772) (@lem2715777)). Qed.
Lemma lem2715779 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715780 : term380 = term157.
Proof. exact (MK_COMB (@lem2715779) (@lem2715778)). Qed.
Lemma lem2715781 : term769 = term763.
Proof. exact (MK_COMB (@lem2715780) (@lem2715769)). Qed.
Lemma lem2715783 (m : nat) : (term265 m) = term32.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2715784 : term763 = term32.
Proof. exact (@lem2715783 term29). Qed.
Lemma lem2715785 : term769 = term32.
Proof. exact (TRANS (@lem2715781) (@lem2715784)). Qed.
Lemma lem2715786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715787 : term770 = term267.
Proof. exact (MK_COMB (@lem2715786) (@lem2715785)). Qed.
Lemma lem2715788 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2715789 : term771 = term269.
Proof. exact (MK_COMB (@lem2715787) (@lem2715788)). Qed.
Lemma lem2715791 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715792 : term269 = term32.
Proof. exact (@lem2715791 term67). Qed.
Lemma lem2715793 : term771 = term32.
Proof. exact (TRANS (@lem2715789) (@lem2715792)). Qed.
Lemma lem2715795 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715796 : term149 = term150.
Proof. exact (@lem2715795 term67 term67). Qed.
Lemma lem2715797 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715798 : term152 = term67.
Proof. exact (EQ_MP (@lem2715797) (@lem940073)). Qed.
Lemma lem2715799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715800 : term150 = term66.
Proof. exact (MK_COMB (@lem2715799) (@lem2715798)). Qed.
Lemma lem2715801 : term149 = term66.
Proof. exact (TRANS (@lem2715796) (@lem2715800)). Qed.
Lemma lem2715802 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2715803 : term271 = term269.
Proof. exact (MK_COMB (@lem2715802) (@lem2715801)). Qed.
Lemma lem2715805 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715806 : term269 = term32.
Proof. exact (@lem2715805 term67). Qed.
Lemma lem2715807 : term271 = term32.
Proof. exact (TRANS (@lem2715803) (@lem2715806)). Qed.
Lemma lem2715808 : term32 = term271.
Proof. exact (SYM (@lem2715807)). Qed.
Lemma lem2715809 : term771 = term271.
Proof. exact (TRANS (@lem2715793) (@lem2715808)). Qed.
Lemma lem2715810 : term764 = term137.
Proof. exact (@lem2715758 (@lem2715809)). Qed.
Lemma lem2715811 : term763 = term137.
Proof. exact (TRANS (@lem2715724) (@lem2715810)). Qed.
Lemma lem2715813 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2715814 : term137 = term32.
Proof. exact (@lem2715813 term32). Qed.
Lemma lem2715815 : term763 = term32.
Proof. exact (TRANS (@lem2715811) (@lem2715814)). Qed.
Lemma lem2715816 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715817 : term772 = term267.
Proof. exact (MK_COMB (@lem2715816) (@lem2715815)). Qed.
Lemma lem2715818 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2715819 (n : int) : (term762 n) = (term773 n).
Proof. exact (MK_COMB (@lem2715817) (@lem2715818 n)). Qed.
Lemma lem2715820 (n : int) : (term761 n) = (term773 n).
Proof. exact (TRANS (@lem2715715 n) (@lem2715819 n)). Qed.
Lemma lem2715821 (n : int) : (term773 n) = term32.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2715822 (n : int) : (term761 n) = term32.
Proof. exact (TRANS (@lem2715820 n) (@lem2715821 n)). Qed.
Lemma lem2715823 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715824 (n : int) : (term774 n) = term102.
Proof. exact (MK_COMB (@lem2715823) (@lem2715822 n)). Qed.
Lemma lem2715825 (n : int) : (term1004 n) = (term1005 n).
Proof. exact (@lem1982753 (term748 n) (term697 n) term742 term28). Qed.
Lemma lem2715826 (n : int) : (term777 n) = (term778 n).
Proof. exact (@lem1982711 term742 term691 (term162 n)). Qed.
Lemma lem2715828 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715829 : term691 = term694.
Proof. exact (@lem2715828 term690). Qed.
Lemma lem2715831 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715832 : term742 = term745.
Proof. exact (@lem2715831 term690). Qed.
Lemma lem2715833 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715834 : term779 = term780.
Proof. exact (MK_COMB (@lem2715833) (@lem2715832)). Qed.
Lemma lem2715835 : term781 = term782.
Proof. exact (MK_COMB (@lem2715834) (@lem2715829)). Qed.
Lemma lem2715836 : term783.
Proof. exact (@lem1981473 term742 term66 term691 term66 term32 term66). Qed.
Lemma lem2715838 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715839 : term257 = term258.
Proof. exact (@lem2715838 (NUMERAL 0) term67). Qed.
Lemma lem2715840 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715841 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715842 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715841 h1) (fun h1 : term258 = True => @lem2715840)). Qed.
Lemma lem2715843 : term258 = True.
Proof. exact (EQ_MP (@lem2715842) (@lem2715840)). Qed.
Lemma lem2715844 : term257 = True.
Proof. exact (TRANS (@lem2715839) (@lem2715843)). Qed.
Lemma lem2715845 : True = term257.
Proof. exact (SYM (@lem2715844)). Qed.
Lemma lem2715846 : term257.
Proof. exact (EQ_MP (@lem2715845) (@lem0)). Qed.
Lemma lem2715847 : term784.
Proof. exact (@lem2715836 (@lem2715846)). Qed.
Lemma lem2715849 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715850 : term257 = term258.
Proof. exact (@lem2715849 (NUMERAL 0) term67). Qed.
Lemma lem2715851 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715852 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715853 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715852 h1) (fun h1 : term258 = True => @lem2715851)). Qed.
Lemma lem2715854 : term258 = True.
Proof. exact (EQ_MP (@lem2715853) (@lem2715851)). Qed.
Lemma lem2715855 : term257 = True.
Proof. exact (TRANS (@lem2715850) (@lem2715854)). Qed.
Lemma lem2715856 : True = term257.
Proof. exact (SYM (@lem2715855)). Qed.
Lemma lem2715857 : term257.
Proof. exact (EQ_MP (@lem2715856) (@lem0)). Qed.
Lemma lem2715858 : term785.
Proof. exact (@lem2715847 (@lem2715857)). Qed.
Lemma lem2715860 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715861 : term257 = term258.
Proof. exact (@lem2715860 (NUMERAL 0) term67). Qed.
Lemma lem2715862 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715863 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715864 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715863 h1) (fun h1 : term258 = True => @lem2715862)). Qed.
Lemma lem2715865 : term258 = True.
Proof. exact (EQ_MP (@lem2715864) (@lem2715862)). Qed.
Lemma lem2715866 : term257 = True.
Proof. exact (TRANS (@lem2715861) (@lem2715865)). Qed.
Lemma lem2715867 : True = term257.
Proof. exact (SYM (@lem2715866)). Qed.
Lemma lem2715868 : term257.
Proof. exact (EQ_MP (@lem2715867) (@lem0)). Qed.
Lemma lem2715869 : term786.
Proof. exact (@lem2715858 (@lem2715868)). Qed.
Lemma lem2715871 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715872 : term787 = term788.
Proof. exact (@lem2715871 term690 term67). Qed.
Lemma lem2715873 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2715874 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2715875 : term790 = term690.
Proof. exact (EQ_MP (@lem2715874) (@lem2715873)). Qed.
Lemma lem2715876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715877 : term788 = term691.
Proof. exact (MK_COMB (@lem2715876) (@lem2715875)). Qed.
Lemma lem2715878 : term787 = term691.
Proof. exact (TRANS (@lem2715872) (@lem2715877)). Qed.
Lemma lem2715880 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2715881 : term791 = term792.
Proof. exact (@lem2715880 term690 term67). Qed.
Lemma lem2715882 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2715883 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2715884 : term790 = term690.
Proof. exact (EQ_MP (@lem2715883) (@lem2715882)). Qed.
Lemma lem2715885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715886 : term788 = term691.
Proof. exact (MK_COMB (@lem2715885) (@lem2715884)). Qed.
Lemma lem2715887 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715888 : term792 = term742.
Proof. exact (MK_COMB (@lem2715887) (@lem2715886)). Qed.
Lemma lem2715889 : term791 = term742.
Proof. exact (TRANS (@lem2715881) (@lem2715888)). Qed.
Lemma lem2715890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715891 : term793 = term779.
Proof. exact (MK_COMB (@lem2715890) (@lem2715889)). Qed.
Lemma lem2715892 : term794 = term781.
Proof. exact (MK_COMB (@lem2715891) (@lem2715878)). Qed.
Lemma lem2715894 (m : nat) : (term649 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2715895 : term781 = term32.
Proof. exact (@lem2715894 term690). Qed.
Lemma lem2715896 : term794 = term32.
Proof. exact (TRANS (@lem2715892) (@lem2715895)). Qed.
Lemma lem2715897 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715898 : term795 = term267.
Proof. exact (MK_COMB (@lem2715897) (@lem2715896)). Qed.
Lemma lem2715899 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2715900 : term796 = term269.
Proof. exact (MK_COMB (@lem2715898) (@lem2715899)). Qed.
Lemma lem2715902 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715903 : term269 = term32.
Proof. exact (@lem2715902 term67). Qed.
Lemma lem2715904 : term796 = term32.
Proof. exact (TRANS (@lem2715900) (@lem2715903)). Qed.
Lemma lem2715906 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715907 : term149 = term150.
Proof. exact (@lem2715906 term67 term67). Qed.
Lemma lem2715908 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2715909 : term152 = term67.
Proof. exact (EQ_MP (@lem2715908) (@lem940073)). Qed.
Lemma lem2715910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715911 : term150 = term66.
Proof. exact (MK_COMB (@lem2715910) (@lem2715909)). Qed.
Lemma lem2715912 : term149 = term66.
Proof. exact (TRANS (@lem2715907) (@lem2715911)). Qed.
Lemma lem2715913 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2715914 : term271 = term269.
Proof. exact (MK_COMB (@lem2715913) (@lem2715912)). Qed.
Lemma lem2715916 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2715917 : term269 = term32.
Proof. exact (@lem2715916 term67). Qed.
Lemma lem2715918 : term271 = term32.
Proof. exact (TRANS (@lem2715914) (@lem2715917)). Qed.
Lemma lem2715919 : term32 = term271.
Proof. exact (SYM (@lem2715918)). Qed.
Lemma lem2715920 : term796 = term271.
Proof. exact (TRANS (@lem2715904) (@lem2715919)). Qed.
Lemma lem2715921 : term782 = term137.
Proof. exact (@lem2715869 (@lem2715920)). Qed.
Lemma lem2715922 : term781 = term137.
Proof. exact (TRANS (@lem2715835) (@lem2715921)). Qed.
Lemma lem2715924 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2715925 : term137 = term32.
Proof. exact (@lem2715924 term32). Qed.
Lemma lem2715926 : term781 = term32.
Proof. exact (TRANS (@lem2715922) (@lem2715925)). Qed.
Lemma lem2715927 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2715928 : term797 = term267.
Proof. exact (MK_COMB (@lem2715927) (@lem2715926)). Qed.
Lemma lem2715929 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2715930 (n : int) : (term778 n) = (term798 n).
Proof. exact (MK_COMB (@lem2715928) (@lem2715929 n)). Qed.
Lemma lem2715931 (n : int) : (term777 n) = (term798 n).
Proof. exact (TRANS (@lem2715826 n) (@lem2715930 n)). Qed.
Lemma lem2715932 (n : int) : (term798 n) = term32.
Proof. exact (@lem1982719 (term162 n)). Qed.
Lemma lem2715933 (n : int) : (term777 n) = term32.
Proof. exact (TRANS (@lem2715931 n) (@lem2715932 n)). Qed.
Lemma lem2715934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715935 (n : int) : (term799 n) = term102.
Proof. exact (MK_COMB (@lem2715934) (@lem2715933 n)). Qed.
Lemma lem2715937 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2715938 : term28 = term173.
Proof. exact (@lem2715937 term29). Qed.
Lemma lem2715940 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2715941 : term742 = term745.
Proof. exact (@lem2715940 term690). Qed.
Lemma lem2715942 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2715943 : term779 = term780.
Proof. exact (MK_COMB (@lem2715942) (@lem2715941)). Qed.
Lemma lem2715944 : term1006 = term1007.
Proof. exact (MK_COMB (@lem2715943) (@lem2715938)). Qed.
Lemma lem2715945 : term1008.
Proof. exact (@lem1981473 term742 term66 term28 term66 term184 term66). Qed.
Lemma lem2715947 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715948 : term257 = term258.
Proof. exact (@lem2715947 (NUMERAL 0) term67). Qed.
Lemma lem2715949 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715950 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715951 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715950 h1) (fun h1 : term258 = True => @lem2715949)). Qed.
Lemma lem2715952 : term258 = True.
Proof. exact (EQ_MP (@lem2715951) (@lem2715949)). Qed.
Lemma lem2715953 : term257 = True.
Proof. exact (TRANS (@lem2715948) (@lem2715952)). Qed.
Lemma lem2715954 : True = term257.
Proof. exact (SYM (@lem2715953)). Qed.
Lemma lem2715955 : term257.
Proof. exact (EQ_MP (@lem2715954) (@lem0)). Qed.
Lemma lem2715956 : term1009.
Proof. exact (@lem2715945 (@lem2715955)). Qed.
Lemma lem2715958 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715959 : term257 = term258.
Proof. exact (@lem2715958 (NUMERAL 0) term67). Qed.
Lemma lem2715960 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715961 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715962 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715961 h1) (fun h1 : term258 = True => @lem2715960)). Qed.
Lemma lem2715963 : term258 = True.
Proof. exact (EQ_MP (@lem2715962) (@lem2715960)). Qed.
Lemma lem2715964 : term257 = True.
Proof. exact (TRANS (@lem2715959) (@lem2715963)). Qed.
Lemma lem2715965 : True = term257.
Proof. exact (SYM (@lem2715964)). Qed.
Lemma lem2715966 : term257.
Proof. exact (EQ_MP (@lem2715965) (@lem0)). Qed.
Lemma lem2715967 : term1010.
Proof. exact (@lem2715956 (@lem2715966)). Qed.
Lemma lem2715969 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2715970 : term257 = term258.
Proof. exact (@lem2715969 (NUMERAL 0) term67). Qed.
Lemma lem2715971 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2715972 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2715973 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2715972 h1) (fun h1 : term258 = True => @lem2715971)). Qed.
Lemma lem2715974 : term258 = True.
Proof. exact (EQ_MP (@lem2715973) (@lem2715971)). Qed.
Lemma lem2715975 : term257 = True.
Proof. exact (TRANS (@lem2715970) (@lem2715974)). Qed.
Lemma lem2715976 : True = term257.
Proof. exact (SYM (@lem2715975)). Qed.
Lemma lem2715977 : term257.
Proof. exact (EQ_MP (@lem2715976) (@lem0)). Qed.
Lemma lem2715978 : term1011.
Proof. exact (@lem2715967 (@lem2715977)). Qed.
Lemma lem2715980 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2715981 : term289 = term290.
Proof. exact (@lem2715980 term29 term67). Qed.
Lemma lem2715982 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2715983 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2715984 : term292 = term29.
Proof. exact (EQ_MP (@lem2715983) (@lem2715982)). Qed.
Lemma lem2715985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715986 : term290 = term28.
Proof. exact (MK_COMB (@lem2715985) (@lem2715984)). Qed.
Lemma lem2715987 : term289 = term28.
Proof. exact (TRANS (@lem2715981) (@lem2715986)). Qed.
Lemma lem2715989 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2715990 : term791 = term792.
Proof. exact (@lem2715989 term690 term67). Qed.
Lemma lem2715991 : term789 = term688.
Proof. exact (@lem996237 term688). Qed.
Lemma lem2715992 : (term789 = term688) = (term790 = term690).
Proof. exact (@lem1007663 term688 (BIT1 0) term688). Qed.
Lemma lem2715993 : term790 = term690.
Proof. exact (EQ_MP (@lem2715992) (@lem2715991)). Qed.
Lemma lem2715994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2715995 : term788 = term691.
Proof. exact (MK_COMB (@lem2715994) (@lem2715993)). Qed.
Lemma lem2715996 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2715997 : term792 = term742.
Proof. exact (MK_COMB (@lem2715996) (@lem2715995)). Qed.
Lemma lem2715998 : term791 = term742.
Proof. exact (TRANS (@lem2715990) (@lem2715997)). Qed.
Lemma lem2715999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2716000 : term793 = term779.
Proof. exact (MK_COMB (@lem2715999) (@lem2715998)). Qed.
Lemma lem2716001 : term1012 = term1006.
Proof. exact (MK_COMB (@lem2716000) (@lem2715987)). Qed.
Lemma lem2716004 : term1013 = term184.
Proof. exact (@lem1367767 term29 term29). Qed.
Lemma lem2716005 : term1014 = term688.
Proof. exact (@lem706951). Qed.
Lemma lem2716006 : (term1014 = term688) = (term1015 = term690).
Proof. exact (@lem1006570 term181 term181 term688). Qed.
Lemma lem2716007 : term1015 = term690.
Proof. exact (EQ_MP (@lem2716006) (@lem2716005)). Qed.
Lemma lem2716008 : term690 = term1015.
Proof. exact (SYM (@lem2716007)). Qed.
Lemma lem2716009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716010 : term691 = term1016.
Proof. exact (MK_COMB (@lem2716009) (@lem2716008)). Qed.
Lemma lem2716011 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2716012 : term742 = term1017.
Proof. exact (MK_COMB (@lem2716011) (@lem2716010)). Qed.
Lemma lem2716013 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2716014 : term779 = term1018.
Proof. exact (MK_COMB (@lem2716013) (@lem2716012)). Qed.
Lemma lem2716015 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2716016 : term1006 = term1013.
Proof. exact (MK_COMB (@lem2716014) (@lem2716015)). Qed.
Lemma lem2716017 : term1006 = term184.
Proof. exact (TRANS (@lem2716016) (@lem2716004)). Qed.
Lemma lem2716018 : term1012 = term184.
Proof. exact (TRANS (@lem2716001) (@lem2716017)). Qed.
Lemma lem2716019 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2716020 : term1019 = term189.
Proof. exact (MK_COMB (@lem2716019) (@lem2716018)). Qed.
Lemma lem2716021 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem2716022 : term1020 = term439.
Proof. exact (MK_COMB (@lem2716020) (@lem2716021)). Qed.
Lemma lem2716024 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2716025 : term439 = term440.
Proof. exact (@lem2716024 term29 term67). Qed.
Lemma lem2716026 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2716027 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2716028 : term292 = term29.
Proof. exact (EQ_MP (@lem2716027) (@lem2716026)). Qed.
Lemma lem2716029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716030 : term290 = term28.
Proof. exact (MK_COMB (@lem2716029) (@lem2716028)). Qed.
Lemma lem2716031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2716032 : term440 = term184.
Proof. exact (MK_COMB (@lem2716031) (@lem2716030)). Qed.
Lemma lem2716033 : term439 = term184.
Proof. exact (TRANS (@lem2716025) (@lem2716032)). Qed.
Lemma lem2716034 : term1020 = term184.
Proof. exact (TRANS (@lem2716022) (@lem2716033)). Qed.
Lemma lem2716036 (m : nat) (n : nat) : (term147 m n) = (term148 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2716037 : term149 = term150.
Proof. exact (@lem2716036 term67 term67). Qed.
Lemma lem2716038 : (term151 = (BIT1 0)) = (term152 = term67).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2716039 : term152 = term67.
Proof. exact (EQ_MP (@lem2716038) (@lem940073)). Qed.
Lemma lem2716040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716041 : term150 = term66.
Proof. exact (MK_COMB (@lem2716040) (@lem2716039)). Qed.
Lemma lem2716042 : term149 = term66.
Proof. exact (TRANS (@lem2716037) (@lem2716041)). Qed.
Lemma lem2716043 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem2716044 : term1021 = term439.
Proof. exact (MK_COMB (@lem2716043) (@lem2716042)). Qed.
Lemma lem2716046 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2716047 : term439 = term440.
Proof. exact (@lem2716046 term29 term67). Qed.
Lemma lem2716048 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2716049 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2716050 : term292 = term29.
Proof. exact (EQ_MP (@lem2716049) (@lem2716048)). Qed.
Lemma lem2716051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716052 : term290 = term28.
Proof. exact (MK_COMB (@lem2716051) (@lem2716050)). Qed.
Lemma lem2716053 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2716054 : term440 = term184.
Proof. exact (MK_COMB (@lem2716053) (@lem2716052)). Qed.
Lemma lem2716055 : term439 = term184.
Proof. exact (TRANS (@lem2716047) (@lem2716054)). Qed.
Lemma lem2716056 : term1021 = term184.
Proof. exact (TRANS (@lem2716044) (@lem2716055)). Qed.
Lemma lem2716057 : term184 = term1021.
Proof. exact (SYM (@lem2716056)). Qed.
Lemma lem2716058 : term1020 = term1021.
Proof. exact (TRANS (@lem2716034) (@lem2716057)). Qed.
Lemma lem2716059 : term1007 = term187.
Proof. exact (@lem2715978 (@lem2716058)). Qed.
Lemma lem2716060 : term1006 = term187.
Proof. exact (TRANS (@lem2715944) (@lem2716059)). Qed.
Lemma lem2716062 (x : real) : (term156 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2716063 : term187 = term184.
Proof. exact (@lem2716062 term184). Qed.
Lemma lem2716064 : term1006 = term184.
Proof. exact (TRANS (@lem2716060) (@lem2716063)). Qed.
Lemma lem2716065 (n : int) : (term1005 n) = term422.
Proof. exact (MK_COMB (@lem2715935 n) (@lem2716064)). Qed.
Lemma lem2716066 (n : int) : (term1004 n) = term422.
Proof. exact (TRANS (@lem2715825 n) (@lem2716065 n)). Qed.
Lemma lem2716067 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2716068 (n : int) : (term1004 n) = term184.
Proof. exact (TRANS (@lem2716066 n) (@lem2716067)). Qed.
Lemma lem2716069 (n : int) : (term1003 n) = term422.
Proof. exact (MK_COMB (@lem2715824 n) (@lem2716068 n)). Qed.
Lemma lem2716070 (n : int) : (term1002 n) = term422.
Proof. exact (TRANS (@lem2715714 n) (@lem2716069 n)). Qed.
Lemma lem2716071 : term422 = term184.
Proof. exact (@lem1982721 term184). Qed.
Lemma lem2716072 (n : int) : (term1002 n) = term184.
Proof. exact (TRANS (@lem2716070 n) (@lem2716071)). Qed.
Lemma lem2716073 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2716074 (n : int) : (term1022 n) = term801.
Proof. exact (MK_COMB (@lem2716073) (@lem2716072 n)). Qed.
Lemma lem2716075 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem2716076 (n : int) : (term1001 n) = term802.
Proof. exact (MK_COMB (@lem2716074 n) (@lem2716075)). Qed.
Lemma lem2716077 (n : int) (h1 : term564 n) : term802.
Proof. exact (EQ_MP (@lem2716076 n) (@lem2715713 n h1)). Qed.
Lemma lem2716079 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2716080 : term802 = term803.
Proof. exact (@lem2716079 term32 term184). Qed.
Lemma lem2716082 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2716083 : term184 = term187.
Proof. exact (@lem2716082 term29). Qed.
Lemma lem2716085 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2716086 : term32 = term137.
Proof. exact (@lem2716085 (NUMERAL 0)). Qed.
Lemma lem2716087 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716088 : term55 = term804.
Proof. exact (MK_COMB (@lem2716087) (@lem2716086)). Qed.
Lemma lem2716089 : term803 = term805.
Proof. exact (MK_COMB (@lem2716088) (@lem2716083)). Qed.
Lemma lem2716090 : term806.
Proof. exact (@lem1980026 term32 term66 term184 term66). Qed.
Lemma lem2716092 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2716093 : term257 = term258.
Proof. exact (@lem2716092 (NUMERAL 0) term67). Qed.
Lemma lem2716094 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2716095 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2716096 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2716095 h1) (fun h1 : term258 = True => @lem2716094)). Qed.
Lemma lem2716097 : term258 = True.
Proof. exact (EQ_MP (@lem2716096) (@lem2716094)). Qed.
Lemma lem2716098 : term257 = True.
Proof. exact (TRANS (@lem2716093) (@lem2716097)). Qed.
Lemma lem2716099 : True = term257.
Proof. exact (SYM (@lem2716098)). Qed.
Lemma lem2716100 : term257.
Proof. exact (EQ_MP (@lem2716099) (@lem0)). Qed.
Lemma lem2716101 : term807.
Proof. exact (@lem2716090 (@lem2716100)). Qed.
Lemma lem2716103 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2716104 : term257 = term258.
Proof. exact (@lem2716103 (NUMERAL 0) term67). Qed.
Lemma lem2716105 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2716106 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2716107 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2716106 h1) (fun h1 : term258 = True => @lem2716105)). Qed.
Lemma lem2716108 : term258 = True.
Proof. exact (EQ_MP (@lem2716107) (@lem2716105)). Qed.
Lemma lem2716109 : term257 = True.
Proof. exact (TRANS (@lem2716104) (@lem2716108)). Qed.
Lemma lem2716110 : True = term257.
Proof. exact (SYM (@lem2716109)). Qed.
Lemma lem2716111 : term257.
Proof. exact (EQ_MP (@lem2716110) (@lem0)). Qed.
Lemma lem2716112 : term805 = term808.
Proof. exact (@lem2716101 (@lem2716111)). Qed.
Lemma lem2716114 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2716115 : term439 = term440.
Proof. exact (@lem2716114 term29 term67). Qed.
Lemma lem2716116 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2716117 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2716118 : term292 = term29.
Proof. exact (EQ_MP (@lem2716117) (@lem2716116)). Qed.
Lemma lem2716119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716120 : term290 = term28.
Proof. exact (MK_COMB (@lem2716119) (@lem2716118)). Qed.
Lemma lem2716121 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2716122 : term440 = term184.
Proof. exact (MK_COMB (@lem2716121) (@lem2716120)). Qed.
Lemma lem2716123 : term439 = term184.
Proof. exact (TRANS (@lem2716115) (@lem2716122)). Qed.
Lemma lem2716125 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2716126 : term269 = term32.
Proof. exact (@lem2716125 term67). Qed.
Lemma lem2716127 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716128 : term809 = term55.
Proof. exact (MK_COMB (@lem2716127) (@lem2716126)). Qed.
Lemma lem2716129 : term808 = term803.
Proof. exact (MK_COMB (@lem2716128) (@lem2716123)). Qed.
Lemma lem2716131 (m : nat) (n : nat) : (term810 m n) = (term811 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2716132 : term803 = term812.
Proof. exact (@lem2716131 (NUMERAL 0) term29). Qed.
Lemma lem2716133 : term580 = term181.
Proof. exact (@lem912803). Qed.
Lemma lem2716134 (h1 : term580 = term181) : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term181 h1). Qed.
Lemma lem2716135 : (term580 = term181) = ((term29 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term580 = term181 => @lem2716134 h1) (fun h1 : (term29 = (NUMERAL 0)) = False => @lem2716133)). Qed.
Lemma lem2716136 : (term29 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2716135) (@lem2716133)). Qed.
Lemma lem2716137 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2716138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716139 : term813 = (and True).
Proof. exact (MK_COMB (@lem2716138) (@lem2716137)). Qed.
Lemma lem2716140 : term812 = (True /\ False).
Proof. exact (MK_COMB (@lem2716139) (@lem2716136)). Qed.
Lemma lem2716142 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2716143 : term812 = False.
Proof. exact (TRANS (@lem2716140) (@lem2716142)). Qed.
Lemma lem2716144 : term803 = False.
Proof. exact (TRANS (@lem2716132) (@lem2716143)). Qed.
Lemma lem2716145 : term808 = False.
Proof. exact (TRANS (@lem2716129) (@lem2716144)). Qed.
Lemma lem2716146 : term805 = False.
Proof. exact (TRANS (@lem2716112) (@lem2716145)). Qed.
Lemma lem2716147 : term803 = False.
Proof. exact (TRANS (@lem2716089) (@lem2716146)). Qed.
Lemma lem2716148 : term802 = False.
Proof. exact (TRANS (@lem2716080) (@lem2716147)). Qed.
Lemma lem2716149 (n : int) (h1 : term564 n) : False.
Proof. exact (EQ_MP (@lem2716148) (@lem2716077 n h1)). Qed.
Lemma lem2716150 (n : int) (h1 : term566 n) : term566 n.
Proof. exact (h1). Qed.
Lemma lem2716152 (n : int) (h1 : term566 n) : term425.
Proof. exact (proj1 (@lem2716150 n h1)). Qed.
Lemma lem2716162 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2716163 : term425 = term814.
Proof. exact (@lem2716162 term32 term184). Qed.
Lemma lem2716165 (x : nat) : (term138 x) = (term139 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2716166 : term184 = term187.
Proof. exact (@lem2716165 term29). Qed.
Lemma lem2716168 (x : nat) : (real_of_num x) = (term136 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2716169 : term32 = term137.
Proof. exact (@lem2716168 (NUMERAL 0)). Qed.
Lemma lem2716170 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2716171 : term582 = term583.
Proof. exact (MK_COMB (@lem2716170) (@lem2716169)). Qed.
Lemma lem2716172 : term814 = term815.
Proof. exact (MK_COMB (@lem2716171) (@lem2716166)). Qed.
Lemma lem2716173 : term816.
Proof. exact (@lem1980255 term32 term66 term184 term66). Qed.
Lemma lem2716175 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2716176 : term257 = term258.
Proof. exact (@lem2716175 (NUMERAL 0) term67). Qed.
Lemma lem2716177 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2716178 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2716179 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2716178 h1) (fun h1 : term258 = True => @lem2716177)). Qed.
Lemma lem2716180 : term258 = True.
Proof. exact (EQ_MP (@lem2716179) (@lem2716177)). Qed.
Lemma lem2716181 : term257 = True.
Proof. exact (TRANS (@lem2716176) (@lem2716180)). Qed.
Lemma lem2716182 : True = term257.
Proof. exact (SYM (@lem2716181)). Qed.
Lemma lem2716183 : term257.
Proof. exact (EQ_MP (@lem2716182) (@lem0)). Qed.
Lemma lem2716184 : term817.
Proof. exact (@lem2716173 (@lem2716183)). Qed.
Lemma lem2716186 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2716187 : term257 = term258.
Proof. exact (@lem2716186 (NUMERAL 0) term67). Qed.
Lemma lem2716188 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2716189 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2716190 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2716189 h1) (fun h1 : term258 = True => @lem2716188)). Qed.
Lemma lem2716191 : term258 = True.
Proof. exact (EQ_MP (@lem2716190) (@lem2716188)). Qed.
Lemma lem2716192 : term257 = True.
Proof. exact (TRANS (@lem2716187) (@lem2716191)). Qed.
Lemma lem2716193 : True = term257.
Proof. exact (SYM (@lem2716192)). Qed.
Lemma lem2716194 : term257.
Proof. exact (EQ_MP (@lem2716193) (@lem0)). Qed.
Lemma lem2716195 : term815 = term818.
Proof. exact (@lem2716184 (@lem2716194)). Qed.
Lemma lem2716197 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2716198 : term439 = term440.
Proof. exact (@lem2716197 term29 term67). Qed.
Lemma lem2716199 : term291 = term181.
Proof. exact (@lem996237 term181). Qed.
Lemma lem2716200 : (term291 = term181) = (term292 = term29).
Proof. exact (@lem1007663 term181 (BIT1 0) term181). Qed.
Lemma lem2716201 : term292 = term29.
Proof. exact (EQ_MP (@lem2716200) (@lem2716199)). Qed.
Lemma lem2716202 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716203 : term290 = term28.
Proof. exact (MK_COMB (@lem2716202) (@lem2716201)). Qed.
Lemma lem2716204 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2716205 : term440 = term184.
Proof. exact (MK_COMB (@lem2716204) (@lem2716203)). Qed.
Lemma lem2716206 : term439 = term184.
Proof. exact (TRANS (@lem2716198) (@lem2716205)). Qed.
Lemma lem2716208 (x : nat) : (term270 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2716209 : term269 = term32.
Proof. exact (@lem2716208 term67). Qed.
Lemma lem2716210 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2716211 : term588 = term582.
Proof. exact (MK_COMB (@lem2716210) (@lem2716209)). Qed.
Lemma lem2716212 : term818 = term814.
Proof. exact (MK_COMB (@lem2716211) (@lem2716206)). Qed.
Lemma lem2716214 (m : nat) (n : nat) : (term819 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem2716215 : term814 = False.
Proof. exact (@lem2716214 (NUMERAL 0) term29). Qed.
Lemma lem2716216 : term818 = False.
Proof. exact (TRANS (@lem2716212) (@lem2716215)). Qed.
Lemma lem2716217 : term815 = False.
Proof. exact (TRANS (@lem2716195) (@lem2716216)). Qed.
Lemma lem2716218 : term814 = False.
Proof. exact (TRANS (@lem2716172) (@lem2716217)). Qed.
Lemma lem2716219 : term425 = False.
Proof. exact (TRANS (@lem2716163) (@lem2716218)). Qed.
Lemma lem2716220 (n : int) (h1 : term566 n) : False.
Proof. exact (EQ_MP (@lem2716219) (@lem2716152 n h1)). Qed.
Lemma lem2716221 (n : int) (h1 : term568 n) : False.
Proof. exact (or_elim (@lem2714788 n h1) (fun h0 : term564 n => @lem2716149 n h0) (fun h0 : term566 n => @lem2716220 n h0)). Qed.
Lemma lem2716222 (n : int) (h1 : term570 n) : False.
Proof. exact (or_elim (@lem2714723 n h1) (fun h0 : term964 n => @lem2714787 n h0) (fun h0 : term568 n => @lem2716221 n h0)). Qed.
Lemma lem2716223 (n : int) (h1 : term572 n) : False.
Proof. exact (or_elim (@lem2713225 n h1) (fun h0 : term546 n => @lem2714722 n h0) (fun h0 : term570 n => @lem2716222 n h0)). Qed.
Lemma lem2716224 (n : int) (h1 : term574 n) : False.
Proof. exact (or_elim (@lem2710574 n h1) (fun h0 : term516 n => @lem2713224 n h0) (fun h0 : term572 n => @lem2716223 n h0)). Qed.
Lemma lem2716225 (n : int) (h1 : term341 n) : term341 n.
Proof. exact (h1). Qed.
Lemma lem2716226 (n : int) (h1 : term341 n) : term574 n.
Proof. exact (EQ_MP (@lem2710573 n) (@lem2716225 n h1)). Qed.
Lemma lem2716227 (n : int) (h1 : term341 n) : (term574 n) = False.
Proof. exact (prop_ext (fun h2 : term574 n => @lem2716224 n h2) (fun h2 : False => @lem2716226 n h1)). Qed.
Lemma lem2716228 (n : int) (h1 : term341 n) : False.
Proof. exact (EQ_MP (@lem2716227 n h1) (@lem2716226 n h1)). Qed.
Lemma lem2716229 (n : int) (h1 : term133 n) : term133 n.
Proof. exact (h1). Qed.
Lemma lem2716230 (n : int) (h1 : term133 n) : term341 n.
Proof. exact (EQ_MP (@lem2709465 n) (@lem2716229 n h1)). Qed.
Lemma lem2716231 (n : int) (h1 : term133 n) : (term341 n) = False.
Proof. exact (prop_ext (fun h2 : term341 n => @lem2716228 n h2) (fun h2 : False => @lem2716230 n h1)). Qed.
Lemma lem2716232 (n : int) (h1 : term133 n) : False.
Proof. exact (EQ_MP (@lem2716231 n h1) (@lem2716230 n h1)). Qed.
Lemma lem2716233 (n : int) : term1023 n.
Proof. exact (fun h0 : term133 n => @lem2716232 n h0). Qed.
Lemma lem2716234 (n : int) : term1024 n.
Proof. exact (@lem1386578 (term1025 n)). Qed.
Lemma lem2716237 (n : int) : term1025 n.
Proof. exact (@lem2716234 n (@lem2716233 n)). Qed.
Lemma lem2716238 (n : int) : (term131 n) = (term23 n).
Proof. exact (SYM (@lem2708543 n)). Qed.
Lemma lem2716239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2716240 (n : int) : (term1025 n) = (term5 n).
Proof. exact (MK_COMB (@lem2716239) (@lem2716238 n)). Qed.
Lemma lem2716241 (n : int) : term5 n.
Proof. exact (EQ_MP (@lem2716240 n) (@lem2716237 n)). Qed.
Lemma lem2716242 (n : int) : term6 n.
Proof. exact (EQ_MP (@lem2708276 n) (@lem2716241 n)). Qed.
Lemma lem2716243 (n : int) : (term6 n) = ((term6 n) = True).
Proof. exact (@lem7 (term6 n)). Qed.
Lemma lem2716244 (n : int) : (term6 n) = True.
Proof. exact (EQ_MP (@lem2716243 n) (@lem2716242 n)). Qed.
Lemma lem2716245 (n : int) : True = (term6 n).
Proof. exact (SYM (@lem2716244 n)). Qed.
Lemma lem2716246 (n : int) : term6 n.
Proof. exact (EQ_MP (@lem2716245 n) (@lem0)). Qed.
Lemma lem2716247 (n : int) : term24 n.
Proof. exact (@lem2716246 n (@lem2708275 n)). Qed.
Lemma lem2716252 : term1026.
Proof. exact (fun n : int => @lem2716247 n). Qed.
