Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_POS_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_POS_spec.
Require Import NSUM_EQ_0_IFF_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6954283 (n : nat) : (term0 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem6954285 (n : nat) : (term1 n) = (term1 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem6954286 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem6954285 n) (@lem6954283 n)). Qed.
Lemma lem6954291 (n : nat) : (term4 n) = (term4 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem6954292 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem6954291 n) (@lem6954286 n)). Qed.
Lemma lem6954293 (n : nat) : ((term7 n) = (term8 n)) = (term5 n).
Proof. exact (@lem17500 (term7 n) (term8 n)). Qed.
Lemma lem6954349 (n : nat) : ((term7 n) = (term8 n)) = (term6 n).
Proof. exact (TRANS (@lem6954293 n) (@lem6954292 n)). Qed.
Lemma lem6954351 (m : nat) (n : nat) : (Peano.lt m n) = (term9 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6954352 (n : nat) : (term7 n) = (term10 n).
Proof. exact (@lem6954351 (NUMERAL 0) n). Qed.
Lemma lem6954353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954354 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem6954353) (@lem6954352 n)). Qed.
Lemma lem6954356 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6954357 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term13).
Proof. exact (@lem6954356 n (NUMERAL 0)). Qed.
Lemma lem6954360 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6954361 (n : nat) : (term8 n) = (term14 n).
Proof. exact (MK_COMB (@lem6954360) (@lem6954357 n)). Qed.
Lemma lem6954362 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem6954354 n) (@lem6954361 n)). Qed.
Lemma lem6954363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954364 (n : nat) : (term4 n) = (term17 n).
Proof. exact (MK_COMB (@lem6954363) (@lem6954362 n)). Qed.
Lemma lem6954366 (m : nat) (n : nat) : (Peano.lt m n) = (term9 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6954367 (n : nat) : (term7 n) = (term10 n).
Proof. exact (@lem6954366 (NUMERAL 0) n). Qed.
Lemma lem6954368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6954369 (n : nat) : (term18 n) = (term19 n).
Proof. exact (MK_COMB (@lem6954368) (@lem6954367 n)). Qed.
Lemma lem6954370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954371 (n : nat) : (term1 n) = (term20 n).
Proof. exact (MK_COMB (@lem6954370) (@lem6954369 n)). Qed.
Lemma lem6954373 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6954374 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term13).
Proof. exact (@lem6954373 n (NUMERAL 0)). Qed.
Lemma lem6954377 (n : nat) : (term3 n) = (term21 n).
Proof. exact (MK_COMB (@lem6954371 n) (@lem6954374 n)). Qed.
Lemma lem6954378 (n : nat) : (term6 n) = (term22 n).
Proof. exact (MK_COMB (@lem6954364 n) (@lem6954377 n)). Qed.
Lemma lem6954379 (n : nat) : ((term7 n) = (term8 n)) = (term22 n).
Proof. exact (TRANS (@lem6954349 n) (@lem6954378 n)). Qed.
Lemma lem6954380 (n : nat) : term23 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem6954381 (n : nat) : (term23 n) = (term24 n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem6954382 (n : nat) : term24 n.
Proof. exact (EQ_MP (@lem6954381 n) (@lem6954380 n)). Qed.
Lemma lem6954383 (_92655 : int) : (term25 _92655) = (term26 _92655).
Proof. exact (@lem2318604 (term26 _92655)). Qed.
Lemma lem6954401 (_92655 : int) : (term27 _92655) = (_92655 = term13).
Proof. exact (@lem16933 (_92655 = term13)). Qed.
Lemma lem6954403 (_92655 : int) : (term28 _92655) = (term28 _92655).
Proof. exact (eq_refl (term28 _92655)). Qed.
Lemma lem6954404 (_92655 : int) : (term29 _92655) = (term30 _92655).
Proof. exact (MK_COMB (@lem6954403 _92655) (@lem6954401 _92655)). Qed.
Lemma lem6954405 (_92655 : int) : (term31 _92655) = (term29 _92655).
Proof. exact (@lem17045 (term32 _92655) (term33 _92655)). Qed.
Lemma lem6954406 (_92655 : int) : (term31 _92655) = (term30 _92655).
Proof. exact (TRANS (@lem6954405 _92655) (@lem6954404 _92655)). Qed.
Lemma lem6954409 (_92655 : int) : (term34 _92655) = (term32 _92655).
Proof. exact (@lem16933 (term32 _92655)). Qed.
Lemma lem6954410 (_92655 : int) : (term33 _92655) = (term33 _92655).
Proof. exact (eq_refl (term33 _92655)). Qed.
Lemma lem6954411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954412 (_92655 : int) : (term35 _92655) = (term36 _92655).
Proof. exact (MK_COMB (@lem6954411) (@lem6954409 _92655)). Qed.
Lemma lem6954413 (_92655 : int) : (term37 _92655) = (term38 _92655).
Proof. exact (MK_COMB (@lem6954412 _92655) (@lem6954410 _92655)). Qed.
Lemma lem6954414 (_92655 : int) : (term39 _92655) = (term37 _92655).
Proof. exact (@lem17045 (term40 _92655) (_92655 = term13)). Qed.
Lemma lem6954415 (_92655 : int) : (term39 _92655) = (term38 _92655).
Proof. exact (TRANS (@lem6954414 _92655) (@lem6954413 _92655)). Qed.
Lemma lem6954416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954417 (_92655 : int) : (term41 _92655) = (term42 _92655).
Proof. exact (MK_COMB (@lem6954416) (@lem6954406 _92655)). Qed.
Lemma lem6954418 (_92655 : int) : (term43 _92655) = (term44 _92655).
Proof. exact (MK_COMB (@lem6954417 _92655) (@lem6954415 _92655)). Qed.
Lemma lem6954419 (_92655 : int) : (term45 _92655) = (term43 _92655).
Proof. exact (@lem17160 (term46 _92655) (term47 _92655)). Qed.
Lemma lem6954420 (_92655 : int) : (term45 _92655) = (term44 _92655).
Proof. exact (TRANS (@lem6954419 _92655) (@lem6954418 _92655)). Qed.
Lemma lem6954422 (_92655 : int) : (term48 _92655) = (term48 _92655).
Proof. exact (eq_refl (term48 _92655)). Qed.
Lemma lem6954423 (_92655 : int) : (term49 _92655) = (term50 _92655).
Proof. exact (MK_COMB (@lem6954422 _92655) (@lem6954420 _92655)). Qed.
Lemma lem6954424 (_92655 : int) : (term51 _92655) = (term49 _92655).
Proof. exact (@lem17362 (term52 _92655) (term53 _92655)). Qed.
Lemma lem6954448 (_92655 : int) : (term51 _92655) = (term50 _92655).
Proof. exact (TRANS (@lem6954424 _92655) (@lem6954423 _92655)). Qed.
Lemma lem6954451 (x : int) (y : int) : (int_le x y) = (term54 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6954452 (_92655 : int) : (term52 _92655) = (term55 _92655).
Proof. exact (@lem6954451 term13 _92655). Qed.
Lemma lem6954454 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954455 : term57 = term58.
Proof. exact (@lem6954454 (NUMERAL 0)). Qed.
Lemma lem6954456 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6954457 : term59 = term60.
Proof. exact (MK_COMB (@lem6954456) (@lem6954455)). Qed.
Lemma lem6954458 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6954459 (_92655 : int) : (term55 _92655) = (term61 _92655).
Proof. exact (MK_COMB (@lem6954457) (@lem6954458 _92655)). Qed.
Lemma lem6954461 (_92655 : int) : (term52 _92655) = (term61 _92655).
Proof. exact (TRANS (@lem6954452 _92655) (@lem6954459 _92655)). Qed.
Lemma lem6954463 (y : int) (x : int) : (term62 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem6954464 (_92655 : int) : (term40 _92655) = (term63 _92655).
Proof. exact (@lem6954463 _92655 term13). Qed.
Lemma lem6954466 (x : int) (y : int) : (int_le x y) = (term54 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6954467 (_92655 : int) : (term63 _92655) = (term64 _92655).
Proof. exact (@lem6954466 _92655 term13). Qed.
Lemma lem6954469 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954470 : term57 = term58.
Proof. exact (@lem6954469 (NUMERAL 0)). Qed.
Lemma lem6954471 (_92655 : int) : (term65 _92655) = (term65 _92655).
Proof. exact (eq_refl (term65 _92655)). Qed.
Lemma lem6954472 (_92655 : int) : (term64 _92655) = (term66 _92655).
Proof. exact (MK_COMB (@lem6954471 _92655) (@lem6954470)). Qed.
Lemma lem6954473 (_92655 : int) : (term63 _92655) = (term66 _92655).
Proof. exact (TRANS (@lem6954467 _92655) (@lem6954472 _92655)). Qed.
Lemma lem6954474 (_92655 : int) : (term40 _92655) = (term66 _92655).
Proof. exact (TRANS (@lem6954464 _92655) (@lem6954473 _92655)). Qed.
Lemma lem6954477 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6954478 (_92655 : int) : (_92655 = term13) = ((real_of_int _92655) = term57).
Proof. exact (@lem6954477 _92655 term13). Qed.
Lemma lem6954482 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954483 : term57 = term58.
Proof. exact (@lem6954482 (NUMERAL 0)). Qed.
Lemma lem6954484 (_92655 : int) : (term67 _92655) = (term67 _92655).
Proof. exact (eq_refl (term67 _92655)). Qed.
Lemma lem6954485 (_92655 : int) : ((real_of_int _92655) = term57) = ((real_of_int _92655) = term58).
Proof. exact (MK_COMB (@lem6954484 _92655) (@lem6954483)). Qed.
Lemma lem6954487 (_92655 : int) : (_92655 = term13) = ((real_of_int _92655) = term58).
Proof. exact (TRANS (@lem6954478 _92655) (@lem6954485 _92655)). Qed.
Lemma lem6954488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954489 (_92655 : int) : (term28 _92655) = (term68 _92655).
Proof. exact (MK_COMB (@lem6954488) (@lem6954474 _92655)). Qed.
Lemma lem6954490 (_92655 : int) : (term30 _92655) = (term69 _92655).
Proof. exact (MK_COMB (@lem6954489 _92655) (@lem6954487 _92655)). Qed.
Lemma lem6954492 (x : int) (y : int) : (int_lt x y) = (term70 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem6954493 (_92655 : int) : (term32 _92655) = (term71 _92655).
Proof. exact (@lem6954492 term13 _92655). Qed.
Lemma lem6954495 (x : int) (y : int) : (int_le x y) = (term54 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6954496 (_92655 : int) : (term71 _92655) = (term72 _92655).
Proof. exact (@lem6954495 term73 _92655). Qed.
Lemma lem6954498 (x : int) (y : int) : (term74 x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6954499 : term76 = term77.
Proof. exact (@lem6954498 term13 term78). Qed.
Lemma lem6954501 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954502 : term57 = term58.
Proof. exact (@lem6954501 (NUMERAL 0)). Qed.
Lemma lem6954503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6954504 : term79 = term80.
Proof. exact (MK_COMB (@lem6954503) (@lem6954502)). Qed.
Lemma lem6954506 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954507 : term81 = term82.
Proof. exact (@lem6954506 term83). Qed.
Lemma lem6954508 : term77 = term84.
Proof. exact (MK_COMB (@lem6954504) (@lem6954507)). Qed.
Lemma lem6954509 : term76 = term84.
Proof. exact (TRANS (@lem6954499) (@lem6954508)). Qed.
Lemma lem6954510 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6954511 : term85 = term86.
Proof. exact (MK_COMB (@lem6954510) (@lem6954509)). Qed.
Lemma lem6954512 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6954513 (_92655 : int) : (term72 _92655) = (term87 _92655).
Proof. exact (MK_COMB (@lem6954511) (@lem6954512 _92655)). Qed.
Lemma lem6954514 (_92655 : int) : (term71 _92655) = (term87 _92655).
Proof. exact (TRANS (@lem6954496 _92655) (@lem6954513 _92655)). Qed.
Lemma lem6954515 (_92655 : int) : (term32 _92655) = (term87 _92655).
Proof. exact (TRANS (@lem6954493 _92655) (@lem6954514 _92655)). Qed.
Lemma lem6954517 (y : int) (x : int) : (term88 x y) = (term89 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6954518 (_92655 : int) : (term33 _92655) = (term90 _92655).
Proof. exact (@lem6954517 term13 _92655). Qed.
Lemma lem6954520 (x : int) (y : int) : (int_le x y) = (term54 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6954521 (_92655 : int) : (term91 _92655) = (term92 _92655).
Proof. exact (@lem6954520 (term93 _92655) term13). Qed.
Lemma lem6954523 (x : int) (y : int) : (term74 x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6954524 (_92655 : int) : (term94 _92655) = (term95 _92655).
Proof. exact (@lem6954523 _92655 term78). Qed.
Lemma lem6954526 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954527 : term81 = term82.
Proof. exact (@lem6954526 term83). Qed.
Lemma lem6954528 (_92655 : int) : (term96 _92655) = (term96 _92655).
Proof. exact (eq_refl (term96 _92655)). Qed.
Lemma lem6954529 (_92655 : int) : (term95 _92655) = (term97 _92655).
Proof. exact (MK_COMB (@lem6954528 _92655) (@lem6954527)). Qed.
Lemma lem6954530 (_92655 : int) : (term94 _92655) = (term97 _92655).
Proof. exact (TRANS (@lem6954524 _92655) (@lem6954529 _92655)). Qed.
Lemma lem6954531 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6954532 (_92655 : int) : (term98 _92655) = (term99 _92655).
Proof. exact (MK_COMB (@lem6954531) (@lem6954530 _92655)). Qed.
Lemma lem6954534 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954535 : term57 = term58.
Proof. exact (@lem6954534 (NUMERAL 0)). Qed.
Lemma lem6954536 (_92655 : int) : (term92 _92655) = (term100 _92655).
Proof. exact (MK_COMB (@lem6954532 _92655) (@lem6954535)). Qed.
Lemma lem6954537 (_92655 : int) : (term91 _92655) = (term100 _92655).
Proof. exact (TRANS (@lem6954521 _92655) (@lem6954536 _92655)). Qed.
Lemma lem6954538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954539 (_92655 : int) : (term101 _92655) = (term102 _92655).
Proof. exact (MK_COMB (@lem6954538) (@lem6954537 _92655)). Qed.
Lemma lem6954541 (x : int) (y : int) : (int_le x y) = (term54 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6954542 (_92655 : int) : (term71 _92655) = (term72 _92655).
Proof. exact (@lem6954541 term73 _92655). Qed.
Lemma lem6954544 (x : int) (y : int) : (term74 x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6954545 : term76 = term77.
Proof. exact (@lem6954544 term13 term78). Qed.
Lemma lem6954547 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954548 : term57 = term58.
Proof. exact (@lem6954547 (NUMERAL 0)). Qed.
Lemma lem6954549 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6954550 : term79 = term80.
Proof. exact (MK_COMB (@lem6954549) (@lem6954548)). Qed.
Lemma lem6954552 (n : nat) : (term56 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6954553 : term81 = term82.
Proof. exact (@lem6954552 term83). Qed.
Lemma lem6954554 : term77 = term84.
Proof. exact (MK_COMB (@lem6954550) (@lem6954553)). Qed.
Lemma lem6954555 : term76 = term84.
Proof. exact (TRANS (@lem6954545) (@lem6954554)). Qed.
Lemma lem6954556 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6954557 : term85 = term86.
Proof. exact (MK_COMB (@lem6954556) (@lem6954555)). Qed.
Lemma lem6954558 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6954559 (_92655 : int) : (term72 _92655) = (term87 _92655).
Proof. exact (MK_COMB (@lem6954557) (@lem6954558 _92655)). Qed.
Lemma lem6954560 (_92655 : int) : (term71 _92655) = (term87 _92655).
Proof. exact (TRANS (@lem6954542 _92655) (@lem6954559 _92655)). Qed.
Lemma lem6954561 (_92655 : int) : (term90 _92655) = (term103 _92655).
Proof. exact (MK_COMB (@lem6954539 _92655) (@lem6954560 _92655)). Qed.
Lemma lem6954562 (_92655 : int) : (term33 _92655) = (term103 _92655).
Proof. exact (TRANS (@lem6954518 _92655) (@lem6954561 _92655)). Qed.
Lemma lem6954563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954564 (_92655 : int) : (term36 _92655) = (term104 _92655).
Proof. exact (MK_COMB (@lem6954563) (@lem6954515 _92655)). Qed.
Lemma lem6954565 (_92655 : int) : (term38 _92655) = (term105 _92655).
Proof. exact (MK_COMB (@lem6954564 _92655) (@lem6954562 _92655)). Qed.
Lemma lem6954566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954567 (_92655 : int) : (term42 _92655) = (term106 _92655).
Proof. exact (MK_COMB (@lem6954566) (@lem6954490 _92655)). Qed.
Lemma lem6954568 (_92655 : int) : (term44 _92655) = (term107 _92655).
Proof. exact (MK_COMB (@lem6954567 _92655) (@lem6954565 _92655)). Qed.
Lemma lem6954569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954570 (_92655 : int) : (term48 _92655) = (term108 _92655).
Proof. exact (MK_COMB (@lem6954569) (@lem6954461 _92655)). Qed.
Lemma lem6954571 (_92655 : int) : (term50 _92655) = (term109 _92655).
Proof. exact (MK_COMB (@lem6954570 _92655) (@lem6954568 _92655)). Qed.
Lemma lem6954572 (_92655 : int) : (term51 _92655) = (term109 _92655).
Proof. exact (TRANS (@lem6954448 _92655) (@lem6954571 _92655)). Qed.
Lemma lem6954576 (t : Prop) : (term110 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6954632 (_92655 : int) : (term111 _92655) = (term109 _92655).
Proof. exact (@lem6954576 (term109 _92655)). Qed.
Lemma lem6954633 (_92655 : int) : (term61 _92655) = (term112 _92655).
Proof. exact (@lem1988287 (real_of_int _92655) term58). Qed.
Lemma lem6954639 (_92655 : int) : (term113 _92655) = (term114 _92655).
Proof. exact (@lem1982792 (real_of_int _92655) term58). Qed.
Lemma lem6954641 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6954642 : term58 = term116.
Proof. exact (@lem6954641 (NUMERAL 0)). Qed.
Lemma lem6954644 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6954645 : term119 = term120.
Proof. exact (@lem6954644 term83). Qed.
Lemma lem6954646 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6954647 : term121 = term122.
Proof. exact (MK_COMB (@lem6954646) (@lem6954645)). Qed.
Lemma lem6954648 : term123 = term124.
Proof. exact (MK_COMB (@lem6954647) (@lem6954642)). Qed.
Lemma lem6954649 : term124 = term125.
Proof. exact (@lem1981613 term119 term58 term82 term82). Qed.
Lemma lem6954651 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6954652 : term128 = term129.
Proof. exact (@lem6954651 term83 term83). Qed.
Lemma lem6954653 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954654 : term131 = term83.
Proof. exact (EQ_MP (@lem6954653) (@lem940073)). Qed.
Lemma lem6954655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954656 : term129 = term82.
Proof. exact (MK_COMB (@lem6954655) (@lem6954654)). Qed.
Lemma lem6954657 : term128 = term82.
Proof. exact (TRANS (@lem6954652) (@lem6954656)). Qed.
Lemma lem6954659 (x : nat) : (term132 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6954660 : term123 = term58.
Proof. exact (@lem6954659 term83). Qed.
Lemma lem6954661 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6954662 : term133 = term134.
Proof. exact (MK_COMB (@lem6954661) (@lem6954660)). Qed.
Lemma lem6954663 : term125 = term116.
Proof. exact (MK_COMB (@lem6954662) (@lem6954657)). Qed.
Lemma lem6954664 : term124 = term116.
Proof. exact (TRANS (@lem6954649) (@lem6954663)). Qed.
Lemma lem6954665 : term123 = term116.
Proof. exact (TRANS (@lem6954648) (@lem6954664)). Qed.
Lemma lem6954667 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6954668 : term116 = term58.
Proof. exact (@lem6954667 term58). Qed.
Lemma lem6954669 : term123 = term58.
Proof. exact (TRANS (@lem6954665) (@lem6954668)). Qed.
Lemma lem6954670 (_92655 : int) : (term96 _92655) = (term96 _92655).
Proof. exact (eq_refl (term96 _92655)). Qed.
Lemma lem6954671 (_92655 : int) : (term114 _92655) = (term136 _92655).
Proof. exact (MK_COMB (@lem6954670 _92655) (@lem6954669)). Qed.
Lemma lem6954672 (_92655 : int) : (term136 _92655) = (real_of_int _92655).
Proof. exact (@lem1982723 (real_of_int _92655)). Qed.
Lemma lem6954673 (_92655 : int) : (term114 _92655) = (real_of_int _92655).
Proof. exact (TRANS (@lem6954671 _92655) (@lem6954672 _92655)). Qed.
Lemma lem6954675 (_92655 : int) : (term113 _92655) = (real_of_int _92655).
Proof. exact (TRANS (@lem6954639 _92655) (@lem6954673 _92655)). Qed.
Lemma lem6954676 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6954677 (_92655 : int) : (term137 _92655) = (term138 _92655).
Proof. exact (MK_COMB (@lem6954676) (@lem6954675 _92655)). Qed.
Lemma lem6954678 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6954679 (_92655 : int) : (term112 _92655) = (term139 _92655).
Proof. exact (MK_COMB (@lem6954677 _92655) (@lem6954678)). Qed.
Lemma lem6954680 (_92655 : int) : (term61 _92655) = (term139 _92655).
Proof. exact (TRANS (@lem6954633 _92655) (@lem6954679 _92655)). Qed.
Lemma lem6954681 (_92655 : int) : (term66 _92655) = (term140 _92655).
Proof. exact (@lem1988287 term58 (real_of_int _92655)). Qed.
Lemma lem6954687 (_92655 : int) : (term141 _92655) = (term142 _92655).
Proof. exact (@lem1982792 term58 (real_of_int _92655)). Qed.
Lemma lem6954692 (_92655 : int) : (term142 _92655) = (term143 _92655).
Proof. exact (@lem1982721 (term143 _92655)). Qed.
Lemma lem6954694 (_92655 : int) : (term141 _92655) = (term143 _92655).
Proof. exact (TRANS (@lem6954687 _92655) (@lem6954692 _92655)). Qed.
Lemma lem6954695 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6954696 (_92655 : int) : (term144 _92655) = (term145 _92655).
Proof. exact (MK_COMB (@lem6954695) (@lem6954694 _92655)). Qed.
Lemma lem6954697 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6954698 (_92655 : int) : (term140 _92655) = (term146 _92655).
Proof. exact (MK_COMB (@lem6954696 _92655) (@lem6954697)). Qed.
Lemma lem6954699 (_92655 : int) : (term66 _92655) = (term146 _92655).
Proof. exact (TRANS (@lem6954681 _92655) (@lem6954698 _92655)). Qed.
Lemma lem6954700 (_92655 : int) : ((real_of_int _92655) = term58) = ((term113 _92655) = term58).
Proof. exact (@lem1988293 (real_of_int _92655) term58). Qed.
Lemma lem6954706 (_92655 : int) : (term113 _92655) = (term114 _92655).
Proof. exact (@lem1982792 (real_of_int _92655) term58). Qed.
Lemma lem6954708 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6954709 : term58 = term116.
Proof. exact (@lem6954708 (NUMERAL 0)). Qed.
Lemma lem6954711 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6954712 : term119 = term120.
Proof. exact (@lem6954711 term83). Qed.
Lemma lem6954713 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6954714 : term121 = term122.
Proof. exact (MK_COMB (@lem6954713) (@lem6954712)). Qed.
Lemma lem6954715 : term123 = term124.
Proof. exact (MK_COMB (@lem6954714) (@lem6954709)). Qed.
Lemma lem6954716 : term124 = term125.
Proof. exact (@lem1981613 term119 term58 term82 term82). Qed.
Lemma lem6954718 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6954719 : term128 = term129.
Proof. exact (@lem6954718 term83 term83). Qed.
Lemma lem6954720 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954721 : term131 = term83.
Proof. exact (EQ_MP (@lem6954720) (@lem940073)). Qed.
Lemma lem6954722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954723 : term129 = term82.
Proof. exact (MK_COMB (@lem6954722) (@lem6954721)). Qed.
Lemma lem6954724 : term128 = term82.
Proof. exact (TRANS (@lem6954719) (@lem6954723)). Qed.
Lemma lem6954726 (x : nat) : (term132 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6954727 : term123 = term58.
Proof. exact (@lem6954726 term83). Qed.
Lemma lem6954728 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6954729 : term133 = term134.
Proof. exact (MK_COMB (@lem6954728) (@lem6954727)). Qed.
Lemma lem6954730 : term125 = term116.
Proof. exact (MK_COMB (@lem6954729) (@lem6954724)). Qed.
Lemma lem6954731 : term124 = term116.
Proof. exact (TRANS (@lem6954716) (@lem6954730)). Qed.
Lemma lem6954732 : term123 = term116.
Proof. exact (TRANS (@lem6954715) (@lem6954731)). Qed.
Lemma lem6954734 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6954735 : term116 = term58.
Proof. exact (@lem6954734 term58). Qed.
Lemma lem6954736 : term123 = term58.
Proof. exact (TRANS (@lem6954732) (@lem6954735)). Qed.
Lemma lem6954737 (_92655 : int) : (term96 _92655) = (term96 _92655).
Proof. exact (eq_refl (term96 _92655)). Qed.
Lemma lem6954738 (_92655 : int) : (term114 _92655) = (term136 _92655).
Proof. exact (MK_COMB (@lem6954737 _92655) (@lem6954736)). Qed.
Lemma lem6954739 (_92655 : int) : (term136 _92655) = (real_of_int _92655).
Proof. exact (@lem1982723 (real_of_int _92655)). Qed.
Lemma lem6954740 (_92655 : int) : (term114 _92655) = (real_of_int _92655).
Proof. exact (TRANS (@lem6954738 _92655) (@lem6954739 _92655)). Qed.
Lemma lem6954742 (_92655 : int) : (term113 _92655) = (real_of_int _92655).
Proof. exact (TRANS (@lem6954706 _92655) (@lem6954740 _92655)). Qed.
Lemma lem6954743 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6954744 (_92655 : int) : (term147 _92655) = (term67 _92655).
Proof. exact (MK_COMB (@lem6954743) (@lem6954742 _92655)). Qed.
Lemma lem6954745 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6954746 (_92655 : int) : ((term113 _92655) = term58) = ((real_of_int _92655) = term58).
Proof. exact (MK_COMB (@lem6954744 _92655) (@lem6954745)). Qed.
Lemma lem6954747 (_92655 : int) : ((real_of_int _92655) = term58) = ((real_of_int _92655) = term58).
Proof. exact (TRANS (@lem6954700 _92655) (@lem6954746 _92655)). Qed.
Lemma lem6954748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954749 (_92655 : int) : (term68 _92655) = (term148 _92655).
Proof. exact (MK_COMB (@lem6954748) (@lem6954699 _92655)). Qed.
Lemma lem6954750 (_92655 : int) : (term69 _92655) = (term149 _92655).
Proof. exact (MK_COMB (@lem6954749 _92655) (@lem6954747 _92655)). Qed.
Lemma lem6954751 (_92655 : int) : (term87 _92655) = (term150 _92655).
Proof. exact (@lem1988287 (real_of_int _92655) term84). Qed.
Lemma lem6954758 : term84 = term82.
Proof. exact (@lem1982721 term82). Qed.
Lemma lem6954761 (_92655 : int) : (term151 _92655) = (term151 _92655).
Proof. exact (eq_refl (term151 _92655)). Qed.
Lemma lem6954762 (_92655 : int) : (term152 _92655) = (term153 _92655).
Proof. exact (MK_COMB (@lem6954761 _92655) (@lem6954758)). Qed.
Lemma lem6954763 (_92655 : int) : (term153 _92655) = (term154 _92655).
Proof. exact (@lem1982792 (real_of_int _92655) term82). Qed.
Lemma lem6954765 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6954766 : term82 = term155.
Proof. exact (@lem6954765 term83). Qed.
Lemma lem6954768 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6954769 : term119 = term120.
Proof. exact (@lem6954768 term83). Qed.
Lemma lem6954770 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6954771 : term121 = term122.
Proof. exact (MK_COMB (@lem6954770) (@lem6954769)). Qed.
Lemma lem6954772 : term156 = term157.
Proof. exact (MK_COMB (@lem6954771) (@lem6954766)). Qed.
Lemma lem6954773 : term157 = term158.
Proof. exact (@lem1981613 term119 term82 term82 term82). Qed.
Lemma lem6954775 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6954776 : term128 = term129.
Proof. exact (@lem6954775 term83 term83). Qed.
Lemma lem6954777 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954778 : term131 = term83.
Proof. exact (EQ_MP (@lem6954777) (@lem940073)). Qed.
Lemma lem6954779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954780 : term129 = term82.
Proof. exact (MK_COMB (@lem6954779) (@lem6954778)). Qed.
Lemma lem6954781 : term128 = term82.
Proof. exact (TRANS (@lem6954776) (@lem6954780)). Qed.
Lemma lem6954783 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6954784 : term156 = term161.
Proof. exact (@lem6954783 term83 term83). Qed.
Lemma lem6954785 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954786 : term131 = term83.
Proof. exact (EQ_MP (@lem6954785) (@lem940073)). Qed.
Lemma lem6954787 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954788 : term129 = term82.
Proof. exact (MK_COMB (@lem6954787) (@lem6954786)). Qed.
Lemma lem6954789 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6954790 : term161 = term119.
Proof. exact (MK_COMB (@lem6954789) (@lem6954788)). Qed.
Lemma lem6954791 : term156 = term119.
Proof. exact (TRANS (@lem6954784) (@lem6954790)). Qed.
Lemma lem6954792 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6954793 : term162 = term163.
Proof. exact (MK_COMB (@lem6954792) (@lem6954791)). Qed.
Lemma lem6954794 : term158 = term120.
Proof. exact (MK_COMB (@lem6954793) (@lem6954781)). Qed.
Lemma lem6954795 : term157 = term120.
Proof. exact (TRANS (@lem6954773) (@lem6954794)). Qed.
Lemma lem6954796 : term156 = term120.
Proof. exact (TRANS (@lem6954772) (@lem6954795)). Qed.
Lemma lem6954798 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6954799 : term120 = term119.
Proof. exact (@lem6954798 term119). Qed.
Lemma lem6954800 : term156 = term119.
Proof. exact (TRANS (@lem6954796) (@lem6954799)). Qed.
Lemma lem6954801 (_92655 : int) : (term96 _92655) = (term96 _92655).
Proof. exact (eq_refl (term96 _92655)). Qed.
Lemma lem6954804 (_92655 : int) : (term154 _92655) = (term164 _92655).
Proof. exact (MK_COMB (@lem6954801 _92655) (@lem6954800)). Qed.
Lemma lem6954805 (_92655 : int) : (term153 _92655) = (term164 _92655).
Proof. exact (TRANS (@lem6954763 _92655) (@lem6954804 _92655)). Qed.
Lemma lem6954806 (_92655 : int) : (term152 _92655) = (term164 _92655).
Proof. exact (TRANS (@lem6954762 _92655) (@lem6954805 _92655)). Qed.
Lemma lem6954807 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6954808 (_92655 : int) : (term165 _92655) = (term166 _92655).
Proof. exact (MK_COMB (@lem6954807) (@lem6954806 _92655)). Qed.
Lemma lem6954809 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6954810 (_92655 : int) : (term150 _92655) = (term167 _92655).
Proof. exact (MK_COMB (@lem6954808 _92655) (@lem6954809)). Qed.
Lemma lem6954811 (_92655 : int) : (term87 _92655) = (term167 _92655).
Proof. exact (TRANS (@lem6954751 _92655) (@lem6954810 _92655)). Qed.
Lemma lem6954812 (_92655 : int) : (term100 _92655) = (term168 _92655).
Proof. exact (@lem1988287 term58 (term97 _92655)). Qed.
Lemma lem6954824 (_92655 : int) : (term169 _92655) = (term170 _92655).
Proof. exact (@lem1982792 term58 (term97 _92655)). Qed.
Lemma lem6954825 (_92655 : int) : (term171 _92655) = (term172 _92655).
Proof. exact (@lem1982781 (real_of_int _92655) term119 term82). Qed.
Lemma lem6954827 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6954828 : term82 = term155.
Proof. exact (@lem6954827 term83). Qed.
Lemma lem6954830 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6954831 : term119 = term120.
Proof. exact (@lem6954830 term83). Qed.
Lemma lem6954832 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6954833 : term121 = term122.
Proof. exact (MK_COMB (@lem6954832) (@lem6954831)). Qed.
Lemma lem6954834 : term156 = term157.
Proof. exact (MK_COMB (@lem6954833) (@lem6954828)). Qed.
Lemma lem6954835 : term157 = term158.
Proof. exact (@lem1981613 term119 term82 term82 term82). Qed.
Lemma lem6954837 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6954838 : term128 = term129.
Proof. exact (@lem6954837 term83 term83). Qed.
Lemma lem6954839 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954840 : term131 = term83.
Proof. exact (EQ_MP (@lem6954839) (@lem940073)). Qed.
Lemma lem6954841 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954842 : term129 = term82.
Proof. exact (MK_COMB (@lem6954841) (@lem6954840)). Qed.
Lemma lem6954843 : term128 = term82.
Proof. exact (TRANS (@lem6954838) (@lem6954842)). Qed.
Lemma lem6954845 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6954846 : term156 = term161.
Proof. exact (@lem6954845 term83 term83). Qed.
Lemma lem6954847 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954848 : term131 = term83.
Proof. exact (EQ_MP (@lem6954847) (@lem940073)). Qed.
Lemma lem6954849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954850 : term129 = term82.
Proof. exact (MK_COMB (@lem6954849) (@lem6954848)). Qed.
Lemma lem6954851 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6954852 : term161 = term119.
Proof. exact (MK_COMB (@lem6954851) (@lem6954850)). Qed.
Lemma lem6954853 : term156 = term119.
Proof. exact (TRANS (@lem6954846) (@lem6954852)). Qed.
Lemma lem6954854 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6954855 : term162 = term163.
Proof. exact (MK_COMB (@lem6954854) (@lem6954853)). Qed.
Lemma lem6954856 : term158 = term120.
Proof. exact (MK_COMB (@lem6954855) (@lem6954843)). Qed.
Lemma lem6954857 : term157 = term120.
Proof. exact (TRANS (@lem6954835) (@lem6954856)). Qed.
Lemma lem6954858 : term156 = term120.
Proof. exact (TRANS (@lem6954834) (@lem6954857)). Qed.
Lemma lem6954860 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6954861 : term120 = term119.
Proof. exact (@lem6954860 term119). Qed.
Lemma lem6954862 : term156 = term119.
Proof. exact (TRANS (@lem6954858) (@lem6954861)). Qed.
Lemma lem6954865 (_92655 : int) : (term173 _92655) = (term173 _92655).
Proof. exact (eq_refl (term173 _92655)). Qed.
Lemma lem6954866 (_92655 : int) : (term172 _92655) = (term174 _92655).
Proof. exact (MK_COMB (@lem6954865 _92655) (@lem6954862)). Qed.
Lemma lem6954867 (_92655 : int) : (term171 _92655) = (term174 _92655).
Proof. exact (TRANS (@lem6954825 _92655) (@lem6954866 _92655)). Qed.
Lemma lem6954868 : term80 = term80.
Proof. exact (eq_refl term80). Qed.
Lemma lem6954869 (_92655 : int) : (term170 _92655) = (term175 _92655).
Proof. exact (MK_COMB (@lem6954868) (@lem6954867 _92655)). Qed.
Lemma lem6954870 (_92655 : int) : (term175 _92655) = (term174 _92655).
Proof. exact (@lem1982721 (term174 _92655)). Qed.
Lemma lem6954871 (_92655 : int) : (term170 _92655) = (term174 _92655).
Proof. exact (TRANS (@lem6954869 _92655) (@lem6954870 _92655)). Qed.
Lemma lem6954873 (_92655 : int) : (term169 _92655) = (term174 _92655).
Proof. exact (TRANS (@lem6954824 _92655) (@lem6954871 _92655)). Qed.
Lemma lem6954874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6954875 (_92655 : int) : (term176 _92655) = (term177 _92655).
Proof. exact (MK_COMB (@lem6954874) (@lem6954873 _92655)). Qed.
Lemma lem6954876 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6954877 (_92655 : int) : (term168 _92655) = (term178 _92655).
Proof. exact (MK_COMB (@lem6954875 _92655) (@lem6954876)). Qed.
Lemma lem6954878 (_92655 : int) : (term100 _92655) = (term178 _92655).
Proof. exact (TRANS (@lem6954812 _92655) (@lem6954877 _92655)). Qed.
Lemma lem6954879 (_92655 : int) : (term87 _92655) = (term150 _92655).
Proof. exact (@lem1988287 (real_of_int _92655) term84). Qed.
Lemma lem6954886 : term84 = term82.
Proof. exact (@lem1982721 term82). Qed.
Lemma lem6954889 (_92655 : int) : (term151 _92655) = (term151 _92655).
Proof. exact (eq_refl (term151 _92655)). Qed.
Lemma lem6954890 (_92655 : int) : (term152 _92655) = (term153 _92655).
Proof. exact (MK_COMB (@lem6954889 _92655) (@lem6954886)). Qed.
Lemma lem6954891 (_92655 : int) : (term153 _92655) = (term154 _92655).
Proof. exact (@lem1982792 (real_of_int _92655) term82). Qed.
Lemma lem6954893 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6954894 : term82 = term155.
Proof. exact (@lem6954893 term83). Qed.
Lemma lem6954896 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6954897 : term119 = term120.
Proof. exact (@lem6954896 term83). Qed.
Lemma lem6954898 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6954899 : term121 = term122.
Proof. exact (MK_COMB (@lem6954898) (@lem6954897)). Qed.
Lemma lem6954900 : term156 = term157.
Proof. exact (MK_COMB (@lem6954899) (@lem6954894)). Qed.
Lemma lem6954901 : term157 = term158.
Proof. exact (@lem1981613 term119 term82 term82 term82). Qed.
Lemma lem6954903 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6954904 : term128 = term129.
Proof. exact (@lem6954903 term83 term83). Qed.
Lemma lem6954905 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954906 : term131 = term83.
Proof. exact (EQ_MP (@lem6954905) (@lem940073)). Qed.
Lemma lem6954907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954908 : term129 = term82.
Proof. exact (MK_COMB (@lem6954907) (@lem6954906)). Qed.
Lemma lem6954909 : term128 = term82.
Proof. exact (TRANS (@lem6954904) (@lem6954908)). Qed.
Lemma lem6954911 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6954912 : term156 = term161.
Proof. exact (@lem6954911 term83 term83). Qed.
Lemma lem6954913 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6954914 : term131 = term83.
Proof. exact (EQ_MP (@lem6954913) (@lem940073)). Qed.
Lemma lem6954915 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6954916 : term129 = term82.
Proof. exact (MK_COMB (@lem6954915) (@lem6954914)). Qed.
Lemma lem6954917 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6954918 : term161 = term119.
Proof. exact (MK_COMB (@lem6954917) (@lem6954916)). Qed.
Lemma lem6954919 : term156 = term119.
Proof. exact (TRANS (@lem6954912) (@lem6954918)). Qed.
Lemma lem6954920 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6954921 : term162 = term163.
Proof. exact (MK_COMB (@lem6954920) (@lem6954919)). Qed.
Lemma lem6954922 : term158 = term120.
Proof. exact (MK_COMB (@lem6954921) (@lem6954909)). Qed.
Lemma lem6954923 : term157 = term120.
Proof. exact (TRANS (@lem6954901) (@lem6954922)). Qed.
Lemma lem6954924 : term156 = term120.
Proof. exact (TRANS (@lem6954900) (@lem6954923)). Qed.
Lemma lem6954926 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6954927 : term120 = term119.
Proof. exact (@lem6954926 term119). Qed.
Lemma lem6954928 : term156 = term119.
Proof. exact (TRANS (@lem6954924) (@lem6954927)). Qed.
Lemma lem6954929 (_92655 : int) : (term96 _92655) = (term96 _92655).
Proof. exact (eq_refl (term96 _92655)). Qed.
Lemma lem6954932 (_92655 : int) : (term154 _92655) = (term164 _92655).
Proof. exact (MK_COMB (@lem6954929 _92655) (@lem6954928)). Qed.
Lemma lem6954933 (_92655 : int) : (term153 _92655) = (term164 _92655).
Proof. exact (TRANS (@lem6954891 _92655) (@lem6954932 _92655)). Qed.
Lemma lem6954934 (_92655 : int) : (term152 _92655) = (term164 _92655).
Proof. exact (TRANS (@lem6954890 _92655) (@lem6954933 _92655)). Qed.
Lemma lem6954935 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6954936 (_92655 : int) : (term165 _92655) = (term166 _92655).
Proof. exact (MK_COMB (@lem6954935) (@lem6954934 _92655)). Qed.
Lemma lem6954937 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6954938 (_92655 : int) : (term150 _92655) = (term167 _92655).
Proof. exact (MK_COMB (@lem6954936 _92655) (@lem6954937)). Qed.
Lemma lem6954939 (_92655 : int) : (term87 _92655) = (term167 _92655).
Proof. exact (TRANS (@lem6954879 _92655) (@lem6954938 _92655)). Qed.
Lemma lem6954940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954941 (_92655 : int) : (term102 _92655) = (term179 _92655).
Proof. exact (MK_COMB (@lem6954940) (@lem6954878 _92655)). Qed.
Lemma lem6954942 (_92655 : int) : (term103 _92655) = (term180 _92655).
Proof. exact (MK_COMB (@lem6954941 _92655) (@lem6954939 _92655)). Qed.
Lemma lem6954943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954944 (_92655 : int) : (term104 _92655) = (term181 _92655).
Proof. exact (MK_COMB (@lem6954943) (@lem6954811 _92655)). Qed.
Lemma lem6954945 (_92655 : int) : (term105 _92655) = (term182 _92655).
Proof. exact (MK_COMB (@lem6954944 _92655) (@lem6954942 _92655)). Qed.
Lemma lem6954946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954947 (_92655 : int) : (term106 _92655) = (term183 _92655).
Proof. exact (MK_COMB (@lem6954946) (@lem6954750 _92655)). Qed.
Lemma lem6954948 (_92655 : int) : (term107 _92655) = (term184 _92655).
Proof. exact (MK_COMB (@lem6954947 _92655) (@lem6954945 _92655)). Qed.
Lemma lem6954949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6954950 (_92655 : int) : (term108 _92655) = (term185 _92655).
Proof. exact (MK_COMB (@lem6954949) (@lem6954680 _92655)). Qed.
Lemma lem6954951 (_92655 : int) : (term109 _92655) = (term186 _92655).
Proof. exact (MK_COMB (@lem6954950 _92655) (@lem6954948 _92655)). Qed.
Lemma lem6954958 (_92655 : int) : (term111 _92655) = (term186 _92655).
Proof. exact (TRANS (@lem6954632 _92655) (@lem6954951 _92655)). Qed.
Lemma lem6954976 (_92655 : int) : (term184 _92655) = (term187 _92655).
Proof. exact (@lem19158 (term167 _92655) (term149 _92655) (term180 _92655)). Qed.
Lemma lem6954977 (_92655 : int) : (term188 _92655) = (term189 _92655).
Proof. exact (@lem19158 (term178 _92655) (term149 _92655) (term167 _92655)). Qed.
Lemma lem6954984 (_92655 : int) : (term190 _92655) = (term191 _92655).
Proof. exact (@lem19367 (term146 _92655) ((real_of_int _92655) = term58) (term167 _92655)). Qed.
Lemma lem6954991 (_92655 : int) : (term192 _92655) = (term193 _92655).
Proof. exact (@lem19367 (term146 _92655) ((real_of_int _92655) = term58) (term178 _92655)). Qed.
Lemma lem6954992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6954993 (_92655 : int) : (term194 _92655) = (term195 _92655).
Proof. exact (MK_COMB (@lem6954992) (@lem6954991 _92655)). Qed.
Lemma lem6954994 (_92655 : int) : (term189 _92655) = (term196 _92655).
Proof. exact (MK_COMB (@lem6954993 _92655) (@lem6954984 _92655)). Qed.
Lemma lem6954995 (_92655 : int) : (term188 _92655) = (term196 _92655).
Proof. exact (TRANS (@lem6954977 _92655) (@lem6954994 _92655)). Qed.
Lemma lem6955002 (_92655 : int) : (term190 _92655) = (term191 _92655).
Proof. exact (@lem19367 (term146 _92655) ((real_of_int _92655) = term58) (term167 _92655)). Qed.
Lemma lem6955003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6955004 (_92655 : int) : (term197 _92655) = (term198 _92655).
Proof. exact (MK_COMB (@lem6955003) (@lem6955002 _92655)). Qed.
Lemma lem6955005 (_92655 : int) : (term187 _92655) = (term199 _92655).
Proof. exact (MK_COMB (@lem6955004 _92655) (@lem6954995 _92655)). Qed.
Lemma lem6955007 (_92655 : int) : (term184 _92655) = (term199 _92655).
Proof. exact (TRANS (@lem6954976 _92655) (@lem6955005 _92655)). Qed.
Lemma lem6955010 (_92655 : int) : (term185 _92655) = (term185 _92655).
Proof. exact (eq_refl (term185 _92655)). Qed.
Lemma lem6955011 (_92655 : int) : (term186 _92655) = (term200 _92655).
Proof. exact (MK_COMB (@lem6955010 _92655) (@lem6955007 _92655)). Qed.
Lemma lem6955012 (_92655 : int) : (term200 _92655) = (term201 _92655).
Proof. exact (@lem19158 (term191 _92655) (term139 _92655) (term196 _92655)). Qed.
Lemma lem6955013 (_92655 : int) : (term202 _92655) = (term203 _92655).
Proof. exact (@lem19158 (term193 _92655) (term139 _92655) (term191 _92655)). Qed.
Lemma lem6955020 (_92655 : int) : (term204 _92655) = (term205 _92655).
Proof. exact (@lem19158 (term206 _92655) (term139 _92655) (term207 _92655)). Qed.
Lemma lem6955027 (_92655 : int) : (term208 _92655) = (term209 _92655).
Proof. exact (@lem19158 (term210 _92655) (term139 _92655) (term211 _92655)). Qed.
Lemma lem6955028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6955029 (_92655 : int) : (term212 _92655) = (term213 _92655).
Proof. exact (MK_COMB (@lem6955028) (@lem6955027 _92655)). Qed.
Lemma lem6955030 (_92655 : int) : (term203 _92655) = (term214 _92655).
Proof. exact (MK_COMB (@lem6955029 _92655) (@lem6955020 _92655)). Qed.
Lemma lem6955031 (_92655 : int) : (term202 _92655) = (term214 _92655).
Proof. exact (TRANS (@lem6955013 _92655) (@lem6955030 _92655)). Qed.
Lemma lem6955038 (_92655 : int) : (term204 _92655) = (term205 _92655).
Proof. exact (@lem19158 (term206 _92655) (term139 _92655) (term207 _92655)). Qed.
Lemma lem6955039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6955040 (_92655 : int) : (term215 _92655) = (term216 _92655).
Proof. exact (MK_COMB (@lem6955039) (@lem6955038 _92655)). Qed.
Lemma lem6955041 (_92655 : int) : (term201 _92655) = (term217 _92655).
Proof. exact (MK_COMB (@lem6955040 _92655) (@lem6955031 _92655)). Qed.
Lemma lem6955042 (_92655 : int) : (term200 _92655) = (term217 _92655).
Proof. exact (TRANS (@lem6955012 _92655) (@lem6955041 _92655)). Qed.
Lemma lem6955043 (_92655 : int) : (term186 _92655) = (term217 _92655).
Proof. exact (TRANS (@lem6955011 _92655) (@lem6955042 _92655)). Qed.
Lemma lem6955044 (_92655 : int) : (term111 _92655) = (term217 _92655).
Proof. exact (TRANS (@lem6954958 _92655) (@lem6955043 _92655)). Qed.
Lemma lem6955078 (_92655 : int) (h1 : term217 _92655) : term217 _92655.
Proof. exact (h1). Qed.
Lemma lem6955079 (_92655 : int) (h1 : term205 _92655) : term205 _92655.
Proof. exact (h1). Qed.
Lemma lem6955080 (_92655 : int) (h1 : term218 _92655) : term218 _92655.
Proof. exact (h1). Qed.
Lemma lem6955081 (_92655 : int) (h1 : term218 _92655) : term206 _92655.
Proof. exact (proj2 (@lem6955080 _92655 h1)). Qed.
Lemma lem6955083 (_92655 : int) (h1 : term218 _92655) : term167 _92655.
Proof. exact (proj2 (@lem6955081 _92655 h1)). Qed.
Lemma lem6955084 (_92655 : int) (h1 : term218 _92655) : term146 _92655.
Proof. exact (proj1 (@lem6955081 _92655 h1)). Qed.
Lemma lem6955086 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6955087 : term219 = term220.
Proof. exact (@lem6955086 term58 term82). Qed.
Lemma lem6955089 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955090 : term82 = term155.
Proof. exact (@lem6955089 term83). Qed.
Lemma lem6955092 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955093 : term58 = term116.
Proof. exact (@lem6955092 (NUMERAL 0)). Qed.
Lemma lem6955094 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955095 : term221 = term222.
Proof. exact (MK_COMB (@lem6955094) (@lem6955093)). Qed.
Lemma lem6955096 : term220 = term223.
Proof. exact (MK_COMB (@lem6955095) (@lem6955090)). Qed.
Lemma lem6955097 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6955099 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955100 : term220 = term226.
Proof. exact (@lem6955099 (NUMERAL 0) term83). Qed.
Lemma lem6955101 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955102 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955103 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955102 h1) (fun h1 : term226 = True => @lem6955101)). Qed.
Lemma lem6955104 : term226 = True.
Proof. exact (EQ_MP (@lem6955103) (@lem6955101)). Qed.
Lemma lem6955105 : term220 = True.
Proof. exact (TRANS (@lem6955100) (@lem6955104)). Qed.
Lemma lem6955106 : True = term220.
Proof. exact (SYM (@lem6955105)). Qed.
Lemma lem6955107 : term220.
Proof. exact (EQ_MP (@lem6955106) (@lem0)). Qed.
Lemma lem6955108 : term228.
Proof. exact (@lem6955097 (@lem6955107)). Qed.
Lemma lem6955110 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955111 : term220 = term226.
Proof. exact (@lem6955110 (NUMERAL 0) term83). Qed.
Lemma lem6955112 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955113 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955114 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955113 h1) (fun h1 : term226 = True => @lem6955112)). Qed.
Lemma lem6955115 : term226 = True.
Proof. exact (EQ_MP (@lem6955114) (@lem6955112)). Qed.
Lemma lem6955116 : term220 = True.
Proof. exact (TRANS (@lem6955111) (@lem6955115)). Qed.
Lemma lem6955117 : True = term220.
Proof. exact (SYM (@lem6955116)). Qed.
Lemma lem6955118 : term220.
Proof. exact (EQ_MP (@lem6955117) (@lem0)). Qed.
Lemma lem6955119 : term223 = term229.
Proof. exact (@lem6955108 (@lem6955118)). Qed.
Lemma lem6955121 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955122 : term128 = term129.
Proof. exact (@lem6955121 term83 term83). Qed.
Lemma lem6955123 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955124 : term131 = term83.
Proof. exact (EQ_MP (@lem6955123) (@lem940073)). Qed.
Lemma lem6955125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955126 : term129 = term82.
Proof. exact (MK_COMB (@lem6955125) (@lem6955124)). Qed.
Lemma lem6955127 : term128 = term82.
Proof. exact (TRANS (@lem6955122) (@lem6955126)). Qed.
Lemma lem6955129 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955130 : term231 = term58.
Proof. exact (@lem6955129 term83). Qed.
Lemma lem6955131 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955132 : term232 = term221.
Proof. exact (MK_COMB (@lem6955131) (@lem6955130)). Qed.
Lemma lem6955133 : term229 = term220.
Proof. exact (MK_COMB (@lem6955132) (@lem6955127)). Qed.
Lemma lem6955135 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955136 : term220 = term226.
Proof. exact (@lem6955135 (NUMERAL 0) term83). Qed.
Lemma lem6955137 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955138 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955139 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955138 h1) (fun h1 : term226 = True => @lem6955137)). Qed.
Lemma lem6955140 : term226 = True.
Proof. exact (EQ_MP (@lem6955139) (@lem6955137)). Qed.
Lemma lem6955141 : term220 = True.
Proof. exact (TRANS (@lem6955136) (@lem6955140)). Qed.
Lemma lem6955142 : term229 = True.
Proof. exact (TRANS (@lem6955133) (@lem6955141)). Qed.
Lemma lem6955143 : term223 = True.
Proof. exact (TRANS (@lem6955119) (@lem6955142)). Qed.
Lemma lem6955144 : term220 = True.
Proof. exact (TRANS (@lem6955096) (@lem6955143)). Qed.
Lemma lem6955145 : term219 = True.
Proof. exact (TRANS (@lem6955087) (@lem6955144)). Qed.
Lemma lem6955146 : True = term219.
Proof. exact (SYM (@lem6955145)). Qed.
Lemma lem6955147 : term219.
Proof. exact (EQ_MP (@lem6955146) (@lem0)). Qed.
Lemma lem6955148 (_92655 : int) (h1 : term218 _92655) : term233 _92655.
Proof. exact (conj (@lem6955147) (@lem6955083 _92655 h1)). Qed.
Lemma lem6955150 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6955151 (_92655 : int) : term235 _92655.
Proof. exact (@lem6955150 term82 (term164 _92655)). Qed.
Lemma lem6955152 (_92655 : int) (h1 : term218 _92655) : term236 _92655.
Proof. exact (@lem6955151 _92655 (@lem6955148 _92655 h1)). Qed.
Lemma lem6955153 (_92655 : int) : (term237 _92655) = (term164 _92655).
Proof. exact (@lem1982733 (term164 _92655)). Qed.
Lemma lem6955154 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955155 (_92655 : int) : (term238 _92655) = (term166 _92655).
Proof. exact (MK_COMB (@lem6955154) (@lem6955153 _92655)). Qed.
Lemma lem6955156 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955157 (_92655 : int) : (term236 _92655) = (term167 _92655).
Proof. exact (MK_COMB (@lem6955155 _92655) (@lem6955156)). Qed.
Lemma lem6955158 (_92655 : int) (h1 : term218 _92655) : term167 _92655.
Proof. exact (EQ_MP (@lem6955157 _92655) (@lem6955152 _92655 h1)). Qed.
Lemma lem6955160 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6955161 : term219 = term220.
Proof. exact (@lem6955160 term58 term82). Qed.
Lemma lem6955163 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955164 : term82 = term155.
Proof. exact (@lem6955163 term83). Qed.
Lemma lem6955166 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955167 : term58 = term116.
Proof. exact (@lem6955166 (NUMERAL 0)). Qed.
Lemma lem6955168 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955169 : term221 = term222.
Proof. exact (MK_COMB (@lem6955168) (@lem6955167)). Qed.
Lemma lem6955170 : term220 = term223.
Proof. exact (MK_COMB (@lem6955169) (@lem6955164)). Qed.
Lemma lem6955171 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6955173 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955174 : term220 = term226.
Proof. exact (@lem6955173 (NUMERAL 0) term83). Qed.
Lemma lem6955175 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955176 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955177 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955176 h1) (fun h1 : term226 = True => @lem6955175)). Qed.
Lemma lem6955178 : term226 = True.
Proof. exact (EQ_MP (@lem6955177) (@lem6955175)). Qed.
Lemma lem6955179 : term220 = True.
Proof. exact (TRANS (@lem6955174) (@lem6955178)). Qed.
Lemma lem6955180 : True = term220.
Proof. exact (SYM (@lem6955179)). Qed.
Lemma lem6955181 : term220.
Proof. exact (EQ_MP (@lem6955180) (@lem0)). Qed.
Lemma lem6955182 : term228.
Proof. exact (@lem6955171 (@lem6955181)). Qed.
Lemma lem6955184 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955185 : term220 = term226.
Proof. exact (@lem6955184 (NUMERAL 0) term83). Qed.
Lemma lem6955186 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955187 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955188 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955187 h1) (fun h1 : term226 = True => @lem6955186)). Qed.
Lemma lem6955189 : term226 = True.
Proof. exact (EQ_MP (@lem6955188) (@lem6955186)). Qed.
Lemma lem6955190 : term220 = True.
Proof. exact (TRANS (@lem6955185) (@lem6955189)). Qed.
Lemma lem6955191 : True = term220.
Proof. exact (SYM (@lem6955190)). Qed.
Lemma lem6955192 : term220.
Proof. exact (EQ_MP (@lem6955191) (@lem0)). Qed.
Lemma lem6955193 : term223 = term229.
Proof. exact (@lem6955182 (@lem6955192)). Qed.
Lemma lem6955195 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955196 : term128 = term129.
Proof. exact (@lem6955195 term83 term83). Qed.
Lemma lem6955197 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955198 : term131 = term83.
Proof. exact (EQ_MP (@lem6955197) (@lem940073)). Qed.
Lemma lem6955199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955200 : term129 = term82.
Proof. exact (MK_COMB (@lem6955199) (@lem6955198)). Qed.
Lemma lem6955201 : term128 = term82.
Proof. exact (TRANS (@lem6955196) (@lem6955200)). Qed.
Lemma lem6955203 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955204 : term231 = term58.
Proof. exact (@lem6955203 term83). Qed.
Lemma lem6955205 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955206 : term232 = term221.
Proof. exact (MK_COMB (@lem6955205) (@lem6955204)). Qed.
Lemma lem6955207 : term229 = term220.
Proof. exact (MK_COMB (@lem6955206) (@lem6955201)). Qed.
Lemma lem6955209 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955210 : term220 = term226.
Proof. exact (@lem6955209 (NUMERAL 0) term83). Qed.
Lemma lem6955211 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955212 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955213 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955212 h1) (fun h1 : term226 = True => @lem6955211)). Qed.
Lemma lem6955214 : term226 = True.
Proof. exact (EQ_MP (@lem6955213) (@lem6955211)). Qed.
Lemma lem6955215 : term220 = True.
Proof. exact (TRANS (@lem6955210) (@lem6955214)). Qed.
Lemma lem6955216 : term229 = True.
Proof. exact (TRANS (@lem6955207) (@lem6955215)). Qed.
Lemma lem6955217 : term223 = True.
Proof. exact (TRANS (@lem6955193) (@lem6955216)). Qed.
Lemma lem6955218 : term220 = True.
Proof. exact (TRANS (@lem6955170) (@lem6955217)). Qed.
Lemma lem6955219 : term219 = True.
Proof. exact (TRANS (@lem6955161) (@lem6955218)). Qed.
Lemma lem6955220 : True = term219.
Proof. exact (SYM (@lem6955219)). Qed.
Lemma lem6955221 : term219.
Proof. exact (EQ_MP (@lem6955220) (@lem0)). Qed.
Lemma lem6955222 (_92655 : int) (h1 : term218 _92655) : term239 _92655.
Proof. exact (conj (@lem6955221) (@lem6955084 _92655 h1)). Qed.
Lemma lem6955224 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6955225 (_92655 : int) : term240 _92655.
Proof. exact (@lem6955224 term82 (term143 _92655)). Qed.
Lemma lem6955226 (_92655 : int) (h1 : term218 _92655) : term241 _92655.
Proof. exact (@lem6955225 _92655 (@lem6955222 _92655 h1)). Qed.
Lemma lem6955227 (_92655 : int) : (term242 _92655) = (term143 _92655).
Proof. exact (@lem1982733 (term143 _92655)). Qed.
Lemma lem6955228 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955229 (_92655 : int) : (term243 _92655) = (term145 _92655).
Proof. exact (MK_COMB (@lem6955228) (@lem6955227 _92655)). Qed.
Lemma lem6955230 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955231 (_92655 : int) : (term241 _92655) = (term146 _92655).
Proof. exact (MK_COMB (@lem6955229 _92655) (@lem6955230)). Qed.
Lemma lem6955232 (_92655 : int) (h1 : term218 _92655) : term146 _92655.
Proof. exact (EQ_MP (@lem6955231 _92655) (@lem6955226 _92655 h1)). Qed.
Lemma lem6955233 (_92655 : int) (h1 : term218 _92655) : term206 _92655.
Proof. exact (conj (@lem6955232 _92655 h1) (@lem6955158 _92655 h1)). Qed.
Lemma lem6955235 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6955236 (_92655 : int) : term245 _92655.
Proof. exact (@lem6955235 (term143 _92655) (term164 _92655)). Qed.
Lemma lem6955237 (_92655 : int) (h1 : term218 _92655) : term246 _92655.
Proof. exact (@lem6955236 _92655 (@lem6955233 _92655 h1)). Qed.
Lemma lem6955238 (_92655 : int) : (term247 _92655) = (term248 _92655).
Proof. exact (@lem1982763 (term143 _92655) (real_of_int _92655) term119). Qed.
Lemma lem6955239 (_92655 : int) : (term249 _92655) = (term250 _92655).
Proof. exact (@lem1982713 term119 (real_of_int _92655)). Qed.
Lemma lem6955241 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955242 : term82 = term155.
Proof. exact (@lem6955241 term83). Qed.
Lemma lem6955244 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6955245 : term119 = term120.
Proof. exact (@lem6955244 term83). Qed.
Lemma lem6955246 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955247 : term251 = term252.
Proof. exact (MK_COMB (@lem6955246) (@lem6955245)). Qed.
Lemma lem6955248 : term253 = term254.
Proof. exact (MK_COMB (@lem6955247) (@lem6955242)). Qed.
Lemma lem6955249 : term255.
Proof. exact (@lem1981473 term119 term82 term82 term82 term58 term82). Qed.
Lemma lem6955251 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955252 : term220 = term226.
Proof. exact (@lem6955251 (NUMERAL 0) term83). Qed.
Lemma lem6955253 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955254 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955255 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955254 h1) (fun h1 : term226 = True => @lem6955253)). Qed.
Lemma lem6955256 : term226 = True.
Proof. exact (EQ_MP (@lem6955255) (@lem6955253)). Qed.
Lemma lem6955257 : term220 = True.
Proof. exact (TRANS (@lem6955252) (@lem6955256)). Qed.
Lemma lem6955258 : True = term220.
Proof. exact (SYM (@lem6955257)). Qed.
Lemma lem6955259 : term220.
Proof. exact (EQ_MP (@lem6955258) (@lem0)). Qed.
Lemma lem6955260 : term256.
Proof. exact (@lem6955249 (@lem6955259)). Qed.
Lemma lem6955262 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955263 : term220 = term226.
Proof. exact (@lem6955262 (NUMERAL 0) term83). Qed.
Lemma lem6955264 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955265 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955266 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955265 h1) (fun h1 : term226 = True => @lem6955264)). Qed.
Lemma lem6955267 : term226 = True.
Proof. exact (EQ_MP (@lem6955266) (@lem6955264)). Qed.
Lemma lem6955268 : term220 = True.
Proof. exact (TRANS (@lem6955263) (@lem6955267)). Qed.
Lemma lem6955269 : True = term220.
Proof. exact (SYM (@lem6955268)). Qed.
Lemma lem6955270 : term220.
Proof. exact (EQ_MP (@lem6955269) (@lem0)). Qed.
Lemma lem6955271 : term257.
Proof. exact (@lem6955260 (@lem6955270)). Qed.
Lemma lem6955273 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955274 : term220 = term226.
Proof. exact (@lem6955273 (NUMERAL 0) term83). Qed.
Lemma lem6955275 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955276 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955277 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955276 h1) (fun h1 : term226 = True => @lem6955275)). Qed.
Lemma lem6955278 : term226 = True.
Proof. exact (EQ_MP (@lem6955277) (@lem6955275)). Qed.
Lemma lem6955279 : term220 = True.
Proof. exact (TRANS (@lem6955274) (@lem6955278)). Qed.
Lemma lem6955280 : True = term220.
Proof. exact (SYM (@lem6955279)). Qed.
Lemma lem6955281 : term220.
Proof. exact (EQ_MP (@lem6955280) (@lem0)). Qed.
Lemma lem6955282 : term258.
Proof. exact (@lem6955271 (@lem6955281)). Qed.
Lemma lem6955284 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955285 : term128 = term129.
Proof. exact (@lem6955284 term83 term83). Qed.
Lemma lem6955286 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955287 : term131 = term83.
Proof. exact (EQ_MP (@lem6955286) (@lem940073)). Qed.
Lemma lem6955288 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955289 : term129 = term82.
Proof. exact (MK_COMB (@lem6955288) (@lem6955287)). Qed.
Lemma lem6955290 : term128 = term82.
Proof. exact (TRANS (@lem6955285) (@lem6955289)). Qed.
Lemma lem6955292 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6955293 : term156 = term161.
Proof. exact (@lem6955292 term83 term83). Qed.
Lemma lem6955294 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955295 : term131 = term83.
Proof. exact (EQ_MP (@lem6955294) (@lem940073)). Qed.
Lemma lem6955296 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955297 : term129 = term82.
Proof. exact (MK_COMB (@lem6955296) (@lem6955295)). Qed.
Lemma lem6955298 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6955299 : term161 = term119.
Proof. exact (MK_COMB (@lem6955298) (@lem6955297)). Qed.
Lemma lem6955300 : term156 = term119.
Proof. exact (TRANS (@lem6955293) (@lem6955299)). Qed.
Lemma lem6955301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955302 : term259 = term251.
Proof. exact (MK_COMB (@lem6955301) (@lem6955300)). Qed.
Lemma lem6955303 : term260 = term253.
Proof. exact (MK_COMB (@lem6955302) (@lem6955290)). Qed.
Lemma lem6955305 (m : nat) : (term261 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6955306 : term253 = term58.
Proof. exact (@lem6955305 term83). Qed.
Lemma lem6955307 : term260 = term58.
Proof. exact (TRANS (@lem6955303) (@lem6955306)). Qed.
Lemma lem6955308 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6955309 : term262 = term263.
Proof. exact (MK_COMB (@lem6955308) (@lem6955307)). Qed.
Lemma lem6955310 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem6955311 : term264 = term231.
Proof. exact (MK_COMB (@lem6955309) (@lem6955310)). Qed.
Lemma lem6955313 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955314 : term231 = term58.
Proof. exact (@lem6955313 term83). Qed.
Lemma lem6955315 : term264 = term58.
Proof. exact (TRANS (@lem6955311) (@lem6955314)). Qed.
Lemma lem6955317 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955318 : term128 = term129.
Proof. exact (@lem6955317 term83 term83). Qed.
Lemma lem6955319 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955320 : term131 = term83.
Proof. exact (EQ_MP (@lem6955319) (@lem940073)). Qed.
Lemma lem6955321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955322 : term129 = term82.
Proof. exact (MK_COMB (@lem6955321) (@lem6955320)). Qed.
Lemma lem6955323 : term128 = term82.
Proof. exact (TRANS (@lem6955318) (@lem6955322)). Qed.
Lemma lem6955324 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem6955325 : term265 = term231.
Proof. exact (MK_COMB (@lem6955324) (@lem6955323)). Qed.
Lemma lem6955327 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955328 : term231 = term58.
Proof. exact (@lem6955327 term83). Qed.
Lemma lem6955329 : term265 = term58.
Proof. exact (TRANS (@lem6955325) (@lem6955328)). Qed.
Lemma lem6955330 : term58 = term265.
Proof. exact (SYM (@lem6955329)). Qed.
Lemma lem6955331 : term264 = term265.
Proof. exact (TRANS (@lem6955315) (@lem6955330)). Qed.
Lemma lem6955332 : term254 = term116.
Proof. exact (@lem6955282 (@lem6955331)). Qed.
Lemma lem6955333 : term253 = term116.
Proof. exact (TRANS (@lem6955248) (@lem6955332)). Qed.
Lemma lem6955335 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6955336 : term116 = term58.
Proof. exact (@lem6955335 term58). Qed.
Lemma lem6955337 : term253 = term58.
Proof. exact (TRANS (@lem6955333) (@lem6955336)). Qed.
Lemma lem6955338 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6955339 : term266 = term263.
Proof. exact (MK_COMB (@lem6955338) (@lem6955337)). Qed.
Lemma lem6955340 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6955341 (_92655 : int) : (term250 _92655) = (term267 _92655).
Proof. exact (MK_COMB (@lem6955339) (@lem6955340 _92655)). Qed.
Lemma lem6955342 (_92655 : int) : (term249 _92655) = (term267 _92655).
Proof. exact (TRANS (@lem6955239 _92655) (@lem6955341 _92655)). Qed.
Lemma lem6955343 (_92655 : int) : (term267 _92655) = term58.
Proof. exact (@lem1982719 (real_of_int _92655)). Qed.
Lemma lem6955344 (_92655 : int) : (term249 _92655) = term58.
Proof. exact (TRANS (@lem6955342 _92655) (@lem6955343 _92655)). Qed.
Lemma lem6955345 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955346 (_92655 : int) : (term268 _92655) = term80.
Proof. exact (MK_COMB (@lem6955345) (@lem6955344 _92655)). Qed.
Lemma lem6955347 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem6955348 (_92655 : int) : (term248 _92655) = term269.
Proof. exact (MK_COMB (@lem6955346 _92655) (@lem6955347)). Qed.
Lemma lem6955349 (_92655 : int) : (term247 _92655) = term269.
Proof. exact (TRANS (@lem6955238 _92655) (@lem6955348 _92655)). Qed.
Lemma lem6955350 : term269 = term119.
Proof. exact (@lem1982721 term119). Qed.
Lemma lem6955351 (_92655 : int) : (term247 _92655) = term119.
Proof. exact (TRANS (@lem6955349 _92655) (@lem6955350)). Qed.
Lemma lem6955352 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955353 (_92655 : int) : (term270 _92655) = term271.
Proof. exact (MK_COMB (@lem6955352) (@lem6955351 _92655)). Qed.
Lemma lem6955354 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955355 (_92655 : int) : (term246 _92655) = term272.
Proof. exact (MK_COMB (@lem6955353 _92655) (@lem6955354)). Qed.
Lemma lem6955356 (_92655 : int) (h1 : term218 _92655) : term272.
Proof. exact (EQ_MP (@lem6955355 _92655) (@lem6955237 _92655 h1)). Qed.
Lemma lem6955358 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6955359 : term272 = term273.
Proof. exact (@lem6955358 term58 term119). Qed.
Lemma lem6955361 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6955362 : term119 = term120.
Proof. exact (@lem6955361 term83). Qed.
Lemma lem6955364 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955365 : term58 = term116.
Proof. exact (@lem6955364 (NUMERAL 0)). Qed.
Lemma lem6955366 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6955367 : term60 = term274.
Proof. exact (MK_COMB (@lem6955366) (@lem6955365)). Qed.
Lemma lem6955368 : term273 = term275.
Proof. exact (MK_COMB (@lem6955367) (@lem6955362)). Qed.
Lemma lem6955369 : term276.
Proof. exact (@lem1980026 term58 term82 term119 term82). Qed.
Lemma lem6955371 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955372 : term220 = term226.
Proof. exact (@lem6955371 (NUMERAL 0) term83). Qed.
Lemma lem6955373 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955374 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955375 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955374 h1) (fun h1 : term226 = True => @lem6955373)). Qed.
Lemma lem6955376 : term226 = True.
Proof. exact (EQ_MP (@lem6955375) (@lem6955373)). Qed.
Lemma lem6955377 : term220 = True.
Proof. exact (TRANS (@lem6955372) (@lem6955376)). Qed.
Lemma lem6955378 : True = term220.
Proof. exact (SYM (@lem6955377)). Qed.
Lemma lem6955379 : term220.
Proof. exact (EQ_MP (@lem6955378) (@lem0)). Qed.
Lemma lem6955380 : term277.
Proof. exact (@lem6955369 (@lem6955379)). Qed.
Lemma lem6955382 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955383 : term220 = term226.
Proof. exact (@lem6955382 (NUMERAL 0) term83). Qed.
Lemma lem6955384 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955385 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955386 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955385 h1) (fun h1 : term226 = True => @lem6955384)). Qed.
Lemma lem6955387 : term226 = True.
Proof. exact (EQ_MP (@lem6955386) (@lem6955384)). Qed.
Lemma lem6955388 : term220 = True.
Proof. exact (TRANS (@lem6955383) (@lem6955387)). Qed.
Lemma lem6955389 : True = term220.
Proof. exact (SYM (@lem6955388)). Qed.
Lemma lem6955390 : term220.
Proof. exact (EQ_MP (@lem6955389) (@lem0)). Qed.
Lemma lem6955391 : term275 = term278.
Proof. exact (@lem6955380 (@lem6955390)). Qed.
Lemma lem6955393 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6955394 : term156 = term161.
Proof. exact (@lem6955393 term83 term83). Qed.
Lemma lem6955395 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955396 : term131 = term83.
Proof. exact (EQ_MP (@lem6955395) (@lem940073)). Qed.
Lemma lem6955397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955398 : term129 = term82.
Proof. exact (MK_COMB (@lem6955397) (@lem6955396)). Qed.
Lemma lem6955399 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6955400 : term161 = term119.
Proof. exact (MK_COMB (@lem6955399) (@lem6955398)). Qed.
Lemma lem6955401 : term156 = term119.
Proof. exact (TRANS (@lem6955394) (@lem6955400)). Qed.
Lemma lem6955403 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955404 : term231 = term58.
Proof. exact (@lem6955403 term83). Qed.
Lemma lem6955405 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6955406 : term279 = term60.
Proof. exact (MK_COMB (@lem6955405) (@lem6955404)). Qed.
Lemma lem6955407 : term278 = term273.
Proof. exact (MK_COMB (@lem6955406) (@lem6955401)). Qed.
Lemma lem6955409 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6955410 : term273 = term282.
Proof. exact (@lem6955409 (NUMERAL 0) term83). Qed.
Lemma lem6955411 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955412 (h1 : term227 = (BIT1 0)) : (term83 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6955413 : (term227 = (BIT1 0)) = ((term83 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955412 h1) (fun h1 : (term83 = (NUMERAL 0)) = False => @lem6955411)). Qed.
Lemma lem6955414 : (term83 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6955413) (@lem6955411)). Qed.
Lemma lem6955415 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6955416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6955417 : term283 = (and True).
Proof. exact (MK_COMB (@lem6955416) (@lem6955415)). Qed.
Lemma lem6955418 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem6955417) (@lem6955414)). Qed.
Lemma lem6955420 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6955421 : term282 = False.
Proof. exact (TRANS (@lem6955418) (@lem6955420)). Qed.
Lemma lem6955422 : term273 = False.
Proof. exact (TRANS (@lem6955410) (@lem6955421)). Qed.
Lemma lem6955423 : term278 = False.
Proof. exact (TRANS (@lem6955407) (@lem6955422)). Qed.
Lemma lem6955424 : term275 = False.
Proof. exact (TRANS (@lem6955391) (@lem6955423)). Qed.
Lemma lem6955425 : term273 = False.
Proof. exact (TRANS (@lem6955368) (@lem6955424)). Qed.
Lemma lem6955426 : term272 = False.
Proof. exact (TRANS (@lem6955359) (@lem6955425)). Qed.
Lemma lem6955427 (_92655 : int) (h1 : term218 _92655) : False.
Proof. exact (EQ_MP (@lem6955426) (@lem6955356 _92655 h1)). Qed.
Lemma lem6955428 (_92655 : int) (h1 : term284 _92655) : term284 _92655.
Proof. exact (h1). Qed.
Lemma lem6955429 (_92655 : int) (h1 : term284 _92655) : term207 _92655.
Proof. exact (proj2 (@lem6955428 _92655 h1)). Qed.
Lemma lem6955431 (_92655 : int) (h1 : term284 _92655) : term167 _92655.
Proof. exact (proj2 (@lem6955429 _92655 h1)). Qed.
Lemma lem6955432 (_92655 : int) (h1 : term284 _92655) : (real_of_int _92655) = term58.
Proof. exact (proj1 (@lem6955429 _92655 h1)). Qed.
Lemma lem6955434 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6955435 : term219 = term220.
Proof. exact (@lem6955434 term58 term82). Qed.
Lemma lem6955437 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955438 : term82 = term155.
Proof. exact (@lem6955437 term83). Qed.
Lemma lem6955440 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955441 : term58 = term116.
Proof. exact (@lem6955440 (NUMERAL 0)). Qed.
Lemma lem6955442 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955443 : term221 = term222.
Proof. exact (MK_COMB (@lem6955442) (@lem6955441)). Qed.
Lemma lem6955444 : term220 = term223.
Proof. exact (MK_COMB (@lem6955443) (@lem6955438)). Qed.
Lemma lem6955445 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6955447 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955448 : term220 = term226.
Proof. exact (@lem6955447 (NUMERAL 0) term83). Qed.
Lemma lem6955449 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955450 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955451 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955450 h1) (fun h1 : term226 = True => @lem6955449)). Qed.
Lemma lem6955452 : term226 = True.
Proof. exact (EQ_MP (@lem6955451) (@lem6955449)). Qed.
Lemma lem6955453 : term220 = True.
Proof. exact (TRANS (@lem6955448) (@lem6955452)). Qed.
Lemma lem6955454 : True = term220.
Proof. exact (SYM (@lem6955453)). Qed.
Lemma lem6955455 : term220.
Proof. exact (EQ_MP (@lem6955454) (@lem0)). Qed.
Lemma lem6955456 : term228.
Proof. exact (@lem6955445 (@lem6955455)). Qed.
Lemma lem6955458 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955459 : term220 = term226.
Proof. exact (@lem6955458 (NUMERAL 0) term83). Qed.
Lemma lem6955460 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955461 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955462 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955461 h1) (fun h1 : term226 = True => @lem6955460)). Qed.
Lemma lem6955463 : term226 = True.
Proof. exact (EQ_MP (@lem6955462) (@lem6955460)). Qed.
Lemma lem6955464 : term220 = True.
Proof. exact (TRANS (@lem6955459) (@lem6955463)). Qed.
Lemma lem6955465 : True = term220.
Proof. exact (SYM (@lem6955464)). Qed.
Lemma lem6955466 : term220.
Proof. exact (EQ_MP (@lem6955465) (@lem0)). Qed.
Lemma lem6955467 : term223 = term229.
Proof. exact (@lem6955456 (@lem6955466)). Qed.
Lemma lem6955469 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955470 : term128 = term129.
Proof. exact (@lem6955469 term83 term83). Qed.
Lemma lem6955471 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955472 : term131 = term83.
Proof. exact (EQ_MP (@lem6955471) (@lem940073)). Qed.
Lemma lem6955473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955474 : term129 = term82.
Proof. exact (MK_COMB (@lem6955473) (@lem6955472)). Qed.
Lemma lem6955475 : term128 = term82.
Proof. exact (TRANS (@lem6955470) (@lem6955474)). Qed.
Lemma lem6955477 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955478 : term231 = term58.
Proof. exact (@lem6955477 term83). Qed.
Lemma lem6955479 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955480 : term232 = term221.
Proof. exact (MK_COMB (@lem6955479) (@lem6955478)). Qed.
Lemma lem6955481 : term229 = term220.
Proof. exact (MK_COMB (@lem6955480) (@lem6955475)). Qed.
Lemma lem6955483 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955484 : term220 = term226.
Proof. exact (@lem6955483 (NUMERAL 0) term83). Qed.
Lemma lem6955485 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955486 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955487 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955486 h1) (fun h1 : term226 = True => @lem6955485)). Qed.
Lemma lem6955488 : term226 = True.
Proof. exact (EQ_MP (@lem6955487) (@lem6955485)). Qed.
Lemma lem6955489 : term220 = True.
Proof. exact (TRANS (@lem6955484) (@lem6955488)). Qed.
Lemma lem6955490 : term229 = True.
Proof. exact (TRANS (@lem6955481) (@lem6955489)). Qed.
Lemma lem6955491 : term223 = True.
Proof. exact (TRANS (@lem6955467) (@lem6955490)). Qed.
Lemma lem6955492 : term220 = True.
Proof. exact (TRANS (@lem6955444) (@lem6955491)). Qed.
Lemma lem6955493 : term219 = True.
Proof. exact (TRANS (@lem6955435) (@lem6955492)). Qed.
Lemma lem6955494 : True = term219.
Proof. exact (SYM (@lem6955493)). Qed.
Lemma lem6955495 : term219.
Proof. exact (EQ_MP (@lem6955494) (@lem0)). Qed.
Lemma lem6955496 (_92655 : int) (h1 : term284 _92655) : term233 _92655.
Proof. exact (conj (@lem6955495) (@lem6955431 _92655 h1)). Qed.
Lemma lem6955498 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6955499 (_92655 : int) : term235 _92655.
Proof. exact (@lem6955498 term82 (term164 _92655)). Qed.
Lemma lem6955500 (_92655 : int) (h1 : term284 _92655) : term236 _92655.
Proof. exact (@lem6955499 _92655 (@lem6955496 _92655 h1)). Qed.
Lemma lem6955501 (_92655 : int) : (term237 _92655) = (term164 _92655).
Proof. exact (@lem1982733 (term164 _92655)). Qed.
Lemma lem6955502 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955503 (_92655 : int) : (term238 _92655) = (term166 _92655).
Proof. exact (MK_COMB (@lem6955502) (@lem6955501 _92655)). Qed.
Lemma lem6955504 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955505 (_92655 : int) : (term236 _92655) = (term167 _92655).
Proof. exact (MK_COMB (@lem6955503 _92655) (@lem6955504)). Qed.
Lemma lem6955506 (_92655 : int) (h1 : term284 _92655) : term167 _92655.
Proof. exact (EQ_MP (@lem6955505 _92655) (@lem6955500 _92655 h1)). Qed.
Lemma lem6955508 (y : real) : term285 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6955509 (_92655 : int) : term286 _92655.
Proof. exact (@lem6955508 (real_of_int _92655)). Qed.
Lemma lem6955510 (_92655 : int) (h1 : term284 _92655) : term287 _92655.
Proof. exact (@lem6955509 _92655 (@lem6955432 _92655 h1)). Qed.
Lemma lem6955511 (_92655 : int) (h1 : term284 _92655) : term288 _92655.
Proof. exact (@lem6955510 _92655 h1 term119). Qed.
Lemma lem6955512 (_92655 : int) : (term288 _92655) = ((term143 _92655) = term58).
Proof. exact (eq_refl (term288 _92655)). Qed.
Lemma lem6955519 (_92655 : int) (h1 : term284 _92655) : (term143 _92655) = term58.
Proof. exact (EQ_MP (@lem6955512 _92655) (@lem6955511 _92655 h1)). Qed.
Lemma lem6955520 (_92655 : int) (h1 : term284 _92655) : term289 _92655.
Proof. exact (conj (@lem6955519 _92655 h1) (@lem6955506 _92655 h1)). Qed.
Lemma lem6955522 (x : real) (y : real) : term290 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6955523 (_92655 : int) : term291 _92655.
Proof. exact (@lem6955522 (term143 _92655) (term164 _92655)). Qed.
Lemma lem6955524 (_92655 : int) (h1 : term284 _92655) : term246 _92655.
Proof. exact (@lem6955523 _92655 (@lem6955520 _92655 h1)). Qed.
Lemma lem6955525 (_92655 : int) : (term247 _92655) = (term248 _92655).
Proof. exact (@lem1982763 (term143 _92655) (real_of_int _92655) term119). Qed.
Lemma lem6955526 (_92655 : int) : (term249 _92655) = (term250 _92655).
Proof. exact (@lem1982713 term119 (real_of_int _92655)). Qed.
Lemma lem6955528 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955529 : term82 = term155.
Proof. exact (@lem6955528 term83). Qed.
Lemma lem6955531 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6955532 : term119 = term120.
Proof. exact (@lem6955531 term83). Qed.
Lemma lem6955533 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955534 : term251 = term252.
Proof. exact (MK_COMB (@lem6955533) (@lem6955532)). Qed.
Lemma lem6955535 : term253 = term254.
Proof. exact (MK_COMB (@lem6955534) (@lem6955529)). Qed.
Lemma lem6955536 : term255.
Proof. exact (@lem1981473 term119 term82 term82 term82 term58 term82). Qed.
Lemma lem6955538 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955539 : term220 = term226.
Proof. exact (@lem6955538 (NUMERAL 0) term83). Qed.
Lemma lem6955540 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955541 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955542 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955541 h1) (fun h1 : term226 = True => @lem6955540)). Qed.
Lemma lem6955543 : term226 = True.
Proof. exact (EQ_MP (@lem6955542) (@lem6955540)). Qed.
Lemma lem6955544 : term220 = True.
Proof. exact (TRANS (@lem6955539) (@lem6955543)). Qed.
Lemma lem6955545 : True = term220.
Proof. exact (SYM (@lem6955544)). Qed.
Lemma lem6955546 : term220.
Proof. exact (EQ_MP (@lem6955545) (@lem0)). Qed.
Lemma lem6955547 : term256.
Proof. exact (@lem6955536 (@lem6955546)). Qed.
Lemma lem6955549 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955550 : term220 = term226.
Proof. exact (@lem6955549 (NUMERAL 0) term83). Qed.
Lemma lem6955551 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955552 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955553 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955552 h1) (fun h1 : term226 = True => @lem6955551)). Qed.
Lemma lem6955554 : term226 = True.
Proof. exact (EQ_MP (@lem6955553) (@lem6955551)). Qed.
Lemma lem6955555 : term220 = True.
Proof. exact (TRANS (@lem6955550) (@lem6955554)). Qed.
Lemma lem6955556 : True = term220.
Proof. exact (SYM (@lem6955555)). Qed.
Lemma lem6955557 : term220.
Proof. exact (EQ_MP (@lem6955556) (@lem0)). Qed.
Lemma lem6955558 : term257.
Proof. exact (@lem6955547 (@lem6955557)). Qed.
Lemma lem6955560 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955561 : term220 = term226.
Proof. exact (@lem6955560 (NUMERAL 0) term83). Qed.
Lemma lem6955562 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955563 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955564 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955563 h1) (fun h1 : term226 = True => @lem6955562)). Qed.
Lemma lem6955565 : term226 = True.
Proof. exact (EQ_MP (@lem6955564) (@lem6955562)). Qed.
Lemma lem6955566 : term220 = True.
Proof. exact (TRANS (@lem6955561) (@lem6955565)). Qed.
Lemma lem6955567 : True = term220.
Proof. exact (SYM (@lem6955566)). Qed.
Lemma lem6955568 : term220.
Proof. exact (EQ_MP (@lem6955567) (@lem0)). Qed.
Lemma lem6955569 : term258.
Proof. exact (@lem6955558 (@lem6955568)). Qed.
Lemma lem6955571 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955572 : term128 = term129.
Proof. exact (@lem6955571 term83 term83). Qed.
Lemma lem6955573 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955574 : term131 = term83.
Proof. exact (EQ_MP (@lem6955573) (@lem940073)). Qed.
Lemma lem6955575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955576 : term129 = term82.
Proof. exact (MK_COMB (@lem6955575) (@lem6955574)). Qed.
Lemma lem6955577 : term128 = term82.
Proof. exact (TRANS (@lem6955572) (@lem6955576)). Qed.
Lemma lem6955579 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6955580 : term156 = term161.
Proof. exact (@lem6955579 term83 term83). Qed.
Lemma lem6955581 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955582 : term131 = term83.
Proof. exact (EQ_MP (@lem6955581) (@lem940073)). Qed.
Lemma lem6955583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955584 : term129 = term82.
Proof. exact (MK_COMB (@lem6955583) (@lem6955582)). Qed.
Lemma lem6955585 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6955586 : term161 = term119.
Proof. exact (MK_COMB (@lem6955585) (@lem6955584)). Qed.
Lemma lem6955587 : term156 = term119.
Proof. exact (TRANS (@lem6955580) (@lem6955586)). Qed.
Lemma lem6955588 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955589 : term259 = term251.
Proof. exact (MK_COMB (@lem6955588) (@lem6955587)). Qed.
Lemma lem6955590 : term260 = term253.
Proof. exact (MK_COMB (@lem6955589) (@lem6955577)). Qed.
Lemma lem6955592 (m : nat) : (term261 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6955593 : term253 = term58.
Proof. exact (@lem6955592 term83). Qed.
Lemma lem6955594 : term260 = term58.
Proof. exact (TRANS (@lem6955590) (@lem6955593)). Qed.
Lemma lem6955595 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6955596 : term262 = term263.
Proof. exact (MK_COMB (@lem6955595) (@lem6955594)). Qed.
Lemma lem6955597 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem6955598 : term264 = term231.
Proof. exact (MK_COMB (@lem6955596) (@lem6955597)). Qed.
Lemma lem6955600 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955601 : term231 = term58.
Proof. exact (@lem6955600 term83). Qed.
Lemma lem6955602 : term264 = term58.
Proof. exact (TRANS (@lem6955598) (@lem6955601)). Qed.
Lemma lem6955604 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955605 : term128 = term129.
Proof. exact (@lem6955604 term83 term83). Qed.
Lemma lem6955606 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955607 : term131 = term83.
Proof. exact (EQ_MP (@lem6955606) (@lem940073)). Qed.
Lemma lem6955608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955609 : term129 = term82.
Proof. exact (MK_COMB (@lem6955608) (@lem6955607)). Qed.
Lemma lem6955610 : term128 = term82.
Proof. exact (TRANS (@lem6955605) (@lem6955609)). Qed.
Lemma lem6955611 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem6955612 : term265 = term231.
Proof. exact (MK_COMB (@lem6955611) (@lem6955610)). Qed.
Lemma lem6955614 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955615 : term231 = term58.
Proof. exact (@lem6955614 term83). Qed.
Lemma lem6955616 : term265 = term58.
Proof. exact (TRANS (@lem6955612) (@lem6955615)). Qed.
Lemma lem6955617 : term58 = term265.
Proof. exact (SYM (@lem6955616)). Qed.
Lemma lem6955618 : term264 = term265.
Proof. exact (TRANS (@lem6955602) (@lem6955617)). Qed.
Lemma lem6955619 : term254 = term116.
Proof. exact (@lem6955569 (@lem6955618)). Qed.
Lemma lem6955620 : term253 = term116.
Proof. exact (TRANS (@lem6955535) (@lem6955619)). Qed.
Lemma lem6955622 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6955623 : term116 = term58.
Proof. exact (@lem6955622 term58). Qed.
Lemma lem6955624 : term253 = term58.
Proof. exact (TRANS (@lem6955620) (@lem6955623)). Qed.
Lemma lem6955625 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6955626 : term266 = term263.
Proof. exact (MK_COMB (@lem6955625) (@lem6955624)). Qed.
Lemma lem6955627 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6955628 (_92655 : int) : (term250 _92655) = (term267 _92655).
Proof. exact (MK_COMB (@lem6955626) (@lem6955627 _92655)). Qed.
Lemma lem6955629 (_92655 : int) : (term249 _92655) = (term267 _92655).
Proof. exact (TRANS (@lem6955526 _92655) (@lem6955628 _92655)). Qed.
Lemma lem6955630 (_92655 : int) : (term267 _92655) = term58.
Proof. exact (@lem1982719 (real_of_int _92655)). Qed.
Lemma lem6955631 (_92655 : int) : (term249 _92655) = term58.
Proof. exact (TRANS (@lem6955629 _92655) (@lem6955630 _92655)). Qed.
Lemma lem6955632 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955633 (_92655 : int) : (term268 _92655) = term80.
Proof. exact (MK_COMB (@lem6955632) (@lem6955631 _92655)). Qed.
Lemma lem6955634 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem6955635 (_92655 : int) : (term248 _92655) = term269.
Proof. exact (MK_COMB (@lem6955633 _92655) (@lem6955634)). Qed.
Lemma lem6955636 (_92655 : int) : (term247 _92655) = term269.
Proof. exact (TRANS (@lem6955525 _92655) (@lem6955635 _92655)). Qed.
Lemma lem6955637 : term269 = term119.
Proof. exact (@lem1982721 term119). Qed.
Lemma lem6955638 (_92655 : int) : (term247 _92655) = term119.
Proof. exact (TRANS (@lem6955636 _92655) (@lem6955637)). Qed.
Lemma lem6955639 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955640 (_92655 : int) : (term270 _92655) = term271.
Proof. exact (MK_COMB (@lem6955639) (@lem6955638 _92655)). Qed.
Lemma lem6955641 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955642 (_92655 : int) : (term246 _92655) = term272.
Proof. exact (MK_COMB (@lem6955640 _92655) (@lem6955641)). Qed.
Lemma lem6955643 (_92655 : int) (h1 : term284 _92655) : term272.
Proof. exact (EQ_MP (@lem6955642 _92655) (@lem6955524 _92655 h1)). Qed.
Lemma lem6955645 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6955646 : term272 = term273.
Proof. exact (@lem6955645 term58 term119). Qed.
Lemma lem6955648 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6955649 : term119 = term120.
Proof. exact (@lem6955648 term83). Qed.
Lemma lem6955651 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955652 : term58 = term116.
Proof. exact (@lem6955651 (NUMERAL 0)). Qed.
Lemma lem6955653 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6955654 : term60 = term274.
Proof. exact (MK_COMB (@lem6955653) (@lem6955652)). Qed.
Lemma lem6955655 : term273 = term275.
Proof. exact (MK_COMB (@lem6955654) (@lem6955649)). Qed.
Lemma lem6955656 : term276.
Proof. exact (@lem1980026 term58 term82 term119 term82). Qed.
Lemma lem6955658 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955659 : term220 = term226.
Proof. exact (@lem6955658 (NUMERAL 0) term83). Qed.
Lemma lem6955660 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955661 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955662 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955661 h1) (fun h1 : term226 = True => @lem6955660)). Qed.
Lemma lem6955663 : term226 = True.
Proof. exact (EQ_MP (@lem6955662) (@lem6955660)). Qed.
Lemma lem6955664 : term220 = True.
Proof. exact (TRANS (@lem6955659) (@lem6955663)). Qed.
Lemma lem6955665 : True = term220.
Proof. exact (SYM (@lem6955664)). Qed.
Lemma lem6955666 : term220.
Proof. exact (EQ_MP (@lem6955665) (@lem0)). Qed.
Lemma lem6955667 : term277.
Proof. exact (@lem6955656 (@lem6955666)). Qed.
Lemma lem6955669 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955670 : term220 = term226.
Proof. exact (@lem6955669 (NUMERAL 0) term83). Qed.
Lemma lem6955671 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955672 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955673 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955672 h1) (fun h1 : term226 = True => @lem6955671)). Qed.
Lemma lem6955674 : term226 = True.
Proof. exact (EQ_MP (@lem6955673) (@lem6955671)). Qed.
Lemma lem6955675 : term220 = True.
Proof. exact (TRANS (@lem6955670) (@lem6955674)). Qed.
Lemma lem6955676 : True = term220.
Proof. exact (SYM (@lem6955675)). Qed.
Lemma lem6955677 : term220.
Proof. exact (EQ_MP (@lem6955676) (@lem0)). Qed.
Lemma lem6955678 : term275 = term278.
Proof. exact (@lem6955667 (@lem6955677)). Qed.
Lemma lem6955680 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6955681 : term156 = term161.
Proof. exact (@lem6955680 term83 term83). Qed.
Lemma lem6955682 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955683 : term131 = term83.
Proof. exact (EQ_MP (@lem6955682) (@lem940073)). Qed.
Lemma lem6955684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955685 : term129 = term82.
Proof. exact (MK_COMB (@lem6955684) (@lem6955683)). Qed.
Lemma lem6955686 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6955687 : term161 = term119.
Proof. exact (MK_COMB (@lem6955686) (@lem6955685)). Qed.
Lemma lem6955688 : term156 = term119.
Proof. exact (TRANS (@lem6955681) (@lem6955687)). Qed.
Lemma lem6955690 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955691 : term231 = term58.
Proof. exact (@lem6955690 term83). Qed.
Lemma lem6955692 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6955693 : term279 = term60.
Proof. exact (MK_COMB (@lem6955692) (@lem6955691)). Qed.
Lemma lem6955694 : term278 = term273.
Proof. exact (MK_COMB (@lem6955693) (@lem6955688)). Qed.
Lemma lem6955696 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6955697 : term273 = term282.
Proof. exact (@lem6955696 (NUMERAL 0) term83). Qed.
Lemma lem6955698 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955699 (h1 : term227 = (BIT1 0)) : (term83 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6955700 : (term227 = (BIT1 0)) = ((term83 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955699 h1) (fun h1 : (term83 = (NUMERAL 0)) = False => @lem6955698)). Qed.
Lemma lem6955701 : (term83 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6955700) (@lem6955698)). Qed.
Lemma lem6955702 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6955703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6955704 : term283 = (and True).
Proof. exact (MK_COMB (@lem6955703) (@lem6955702)). Qed.
Lemma lem6955705 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem6955704) (@lem6955701)). Qed.
Lemma lem6955707 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6955708 : term282 = False.
Proof. exact (TRANS (@lem6955705) (@lem6955707)). Qed.
Lemma lem6955709 : term273 = False.
Proof. exact (TRANS (@lem6955697) (@lem6955708)). Qed.
Lemma lem6955710 : term278 = False.
Proof. exact (TRANS (@lem6955694) (@lem6955709)). Qed.
Lemma lem6955711 : term275 = False.
Proof. exact (TRANS (@lem6955678) (@lem6955710)). Qed.
Lemma lem6955712 : term273 = False.
Proof. exact (TRANS (@lem6955655) (@lem6955711)). Qed.
Lemma lem6955713 : term272 = False.
Proof. exact (TRANS (@lem6955646) (@lem6955712)). Qed.
Lemma lem6955714 (_92655 : int) (h1 : term284 _92655) : False.
Proof. exact (EQ_MP (@lem6955713) (@lem6955643 _92655 h1)). Qed.
Lemma lem6955715 (_92655 : int) (h1 : term205 _92655) : False.
Proof. exact (or_elim (@lem6955079 _92655 h1) (fun h0 : term218 _92655 => @lem6955427 _92655 h0) (fun h0 : term284 _92655 => @lem6955714 _92655 h0)). Qed.
Lemma lem6955716 (_92655 : int) (h1 : term214 _92655) : term214 _92655.
Proof. exact (h1). Qed.
Lemma lem6955717 (_92655 : int) (h1 : term209 _92655) : term209 _92655.
Proof. exact (h1). Qed.
Lemma lem6955718 (_92655 : int) (h1 : term292 _92655) : term292 _92655.
Proof. exact (h1). Qed.
Lemma lem6955719 (_92655 : int) (h1 : term292 _92655) : term210 _92655.
Proof. exact (proj2 (@lem6955718 _92655 h1)). Qed.
Lemma lem6955720 (_92655 : int) (h1 : term292 _92655) : term139 _92655.
Proof. exact (proj1 (@lem6955718 _92655 h1)). Qed.
Lemma lem6955721 (_92655 : int) (h1 : term292 _92655) : term178 _92655.
Proof. exact (proj2 (@lem6955719 _92655 h1)). Qed.
Lemma lem6955724 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6955725 : term219 = term220.
Proof. exact (@lem6955724 term58 term82). Qed.
Lemma lem6955727 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955728 : term82 = term155.
Proof. exact (@lem6955727 term83). Qed.
Lemma lem6955730 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955731 : term58 = term116.
Proof. exact (@lem6955730 (NUMERAL 0)). Qed.
Lemma lem6955732 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955733 : term221 = term222.
Proof. exact (MK_COMB (@lem6955732) (@lem6955731)). Qed.
Lemma lem6955734 : term220 = term223.
Proof. exact (MK_COMB (@lem6955733) (@lem6955728)). Qed.
Lemma lem6955735 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6955737 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955738 : term220 = term226.
Proof. exact (@lem6955737 (NUMERAL 0) term83). Qed.
Lemma lem6955739 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955740 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955741 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955740 h1) (fun h1 : term226 = True => @lem6955739)). Qed.
Lemma lem6955742 : term226 = True.
Proof. exact (EQ_MP (@lem6955741) (@lem6955739)). Qed.
Lemma lem6955743 : term220 = True.
Proof. exact (TRANS (@lem6955738) (@lem6955742)). Qed.
Lemma lem6955744 : True = term220.
Proof. exact (SYM (@lem6955743)). Qed.
Lemma lem6955745 : term220.
Proof. exact (EQ_MP (@lem6955744) (@lem0)). Qed.
Lemma lem6955746 : term228.
Proof. exact (@lem6955735 (@lem6955745)). Qed.
Lemma lem6955748 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955749 : term220 = term226.
Proof. exact (@lem6955748 (NUMERAL 0) term83). Qed.
Lemma lem6955750 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955751 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955752 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955751 h1) (fun h1 : term226 = True => @lem6955750)). Qed.
Lemma lem6955753 : term226 = True.
Proof. exact (EQ_MP (@lem6955752) (@lem6955750)). Qed.
Lemma lem6955754 : term220 = True.
Proof. exact (TRANS (@lem6955749) (@lem6955753)). Qed.
Lemma lem6955755 : True = term220.
Proof. exact (SYM (@lem6955754)). Qed.
Lemma lem6955756 : term220.
Proof. exact (EQ_MP (@lem6955755) (@lem0)). Qed.
Lemma lem6955757 : term223 = term229.
Proof. exact (@lem6955746 (@lem6955756)). Qed.
Lemma lem6955759 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955760 : term128 = term129.
Proof. exact (@lem6955759 term83 term83). Qed.
Lemma lem6955761 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955762 : term131 = term83.
Proof. exact (EQ_MP (@lem6955761) (@lem940073)). Qed.
Lemma lem6955763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955764 : term129 = term82.
Proof. exact (MK_COMB (@lem6955763) (@lem6955762)). Qed.
Lemma lem6955765 : term128 = term82.
Proof. exact (TRANS (@lem6955760) (@lem6955764)). Qed.
Lemma lem6955767 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955768 : term231 = term58.
Proof. exact (@lem6955767 term83). Qed.
Lemma lem6955769 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955770 : term232 = term221.
Proof. exact (MK_COMB (@lem6955769) (@lem6955768)). Qed.
Lemma lem6955771 : term229 = term220.
Proof. exact (MK_COMB (@lem6955770) (@lem6955765)). Qed.
Lemma lem6955773 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955774 : term220 = term226.
Proof. exact (@lem6955773 (NUMERAL 0) term83). Qed.
Lemma lem6955775 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955776 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955777 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955776 h1) (fun h1 : term226 = True => @lem6955775)). Qed.
Lemma lem6955778 : term226 = True.
Proof. exact (EQ_MP (@lem6955777) (@lem6955775)). Qed.
Lemma lem6955779 : term220 = True.
Proof. exact (TRANS (@lem6955774) (@lem6955778)). Qed.
Lemma lem6955780 : term229 = True.
Proof. exact (TRANS (@lem6955771) (@lem6955779)). Qed.
Lemma lem6955781 : term223 = True.
Proof. exact (TRANS (@lem6955757) (@lem6955780)). Qed.
Lemma lem6955782 : term220 = True.
Proof. exact (TRANS (@lem6955734) (@lem6955781)). Qed.
Lemma lem6955783 : term219 = True.
Proof. exact (TRANS (@lem6955725) (@lem6955782)). Qed.
Lemma lem6955784 : True = term219.
Proof. exact (SYM (@lem6955783)). Qed.
Lemma lem6955785 : term219.
Proof. exact (EQ_MP (@lem6955784) (@lem0)). Qed.
Lemma lem6955786 (_92655 : int) (h1 : term292 _92655) : term293 _92655.
Proof. exact (conj (@lem6955785) (@lem6955720 _92655 h1)). Qed.
Lemma lem6955788 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6955789 (_92655 : int) : term294 _92655.
Proof. exact (@lem6955788 term82 (real_of_int _92655)). Qed.
Lemma lem6955790 (_92655 : int) (h1 : term292 _92655) : term295 _92655.
Proof. exact (@lem6955789 _92655 (@lem6955786 _92655 h1)). Qed.
Lemma lem6955791 (_92655 : int) : (term296 _92655) = (real_of_int _92655).
Proof. exact (@lem1982733 (real_of_int _92655)). Qed.
Lemma lem6955792 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955793 (_92655 : int) : (term297 _92655) = (term138 _92655).
Proof. exact (MK_COMB (@lem6955792) (@lem6955791 _92655)). Qed.
Lemma lem6955794 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955795 (_92655 : int) : (term295 _92655) = (term139 _92655).
Proof. exact (MK_COMB (@lem6955793 _92655) (@lem6955794)). Qed.
Lemma lem6955796 (_92655 : int) (h1 : term292 _92655) : term139 _92655.
Proof. exact (EQ_MP (@lem6955795 _92655) (@lem6955790 _92655 h1)). Qed.
Lemma lem6955798 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6955799 : term219 = term220.
Proof. exact (@lem6955798 term58 term82). Qed.
Lemma lem6955801 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955802 : term82 = term155.
Proof. exact (@lem6955801 term83). Qed.
Lemma lem6955804 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955805 : term58 = term116.
Proof. exact (@lem6955804 (NUMERAL 0)). Qed.
Lemma lem6955806 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955807 : term221 = term222.
Proof. exact (MK_COMB (@lem6955806) (@lem6955805)). Qed.
Lemma lem6955808 : term220 = term223.
Proof. exact (MK_COMB (@lem6955807) (@lem6955802)). Qed.
Lemma lem6955809 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6955811 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955812 : term220 = term226.
Proof. exact (@lem6955811 (NUMERAL 0) term83). Qed.
Lemma lem6955813 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955814 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955815 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955814 h1) (fun h1 : term226 = True => @lem6955813)). Qed.
Lemma lem6955816 : term226 = True.
Proof. exact (EQ_MP (@lem6955815) (@lem6955813)). Qed.
Lemma lem6955817 : term220 = True.
Proof. exact (TRANS (@lem6955812) (@lem6955816)). Qed.
Lemma lem6955818 : True = term220.
Proof. exact (SYM (@lem6955817)). Qed.
Lemma lem6955819 : term220.
Proof. exact (EQ_MP (@lem6955818) (@lem0)). Qed.
Lemma lem6955820 : term228.
Proof. exact (@lem6955809 (@lem6955819)). Qed.
Lemma lem6955822 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955823 : term220 = term226.
Proof. exact (@lem6955822 (NUMERAL 0) term83). Qed.
Lemma lem6955824 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955825 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955826 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955825 h1) (fun h1 : term226 = True => @lem6955824)). Qed.
Lemma lem6955827 : term226 = True.
Proof. exact (EQ_MP (@lem6955826) (@lem6955824)). Qed.
Lemma lem6955828 : term220 = True.
Proof. exact (TRANS (@lem6955823) (@lem6955827)). Qed.
Lemma lem6955829 : True = term220.
Proof. exact (SYM (@lem6955828)). Qed.
Lemma lem6955830 : term220.
Proof. exact (EQ_MP (@lem6955829) (@lem0)). Qed.
Lemma lem6955831 : term223 = term229.
Proof. exact (@lem6955820 (@lem6955830)). Qed.
Lemma lem6955833 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955834 : term128 = term129.
Proof. exact (@lem6955833 term83 term83). Qed.
Lemma lem6955835 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955836 : term131 = term83.
Proof. exact (EQ_MP (@lem6955835) (@lem940073)). Qed.
Lemma lem6955837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955838 : term129 = term82.
Proof. exact (MK_COMB (@lem6955837) (@lem6955836)). Qed.
Lemma lem6955839 : term128 = term82.
Proof. exact (TRANS (@lem6955834) (@lem6955838)). Qed.
Lemma lem6955841 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955842 : term231 = term58.
Proof. exact (@lem6955841 term83). Qed.
Lemma lem6955843 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6955844 : term232 = term221.
Proof. exact (MK_COMB (@lem6955843) (@lem6955842)). Qed.
Lemma lem6955845 : term229 = term220.
Proof. exact (MK_COMB (@lem6955844) (@lem6955839)). Qed.
Lemma lem6955847 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955848 : term220 = term226.
Proof. exact (@lem6955847 (NUMERAL 0) term83). Qed.
Lemma lem6955849 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955850 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955851 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955850 h1) (fun h1 : term226 = True => @lem6955849)). Qed.
Lemma lem6955852 : term226 = True.
Proof. exact (EQ_MP (@lem6955851) (@lem6955849)). Qed.
Lemma lem6955853 : term220 = True.
Proof. exact (TRANS (@lem6955848) (@lem6955852)). Qed.
Lemma lem6955854 : term229 = True.
Proof. exact (TRANS (@lem6955845) (@lem6955853)). Qed.
Lemma lem6955855 : term223 = True.
Proof. exact (TRANS (@lem6955831) (@lem6955854)). Qed.
Lemma lem6955856 : term220 = True.
Proof. exact (TRANS (@lem6955808) (@lem6955855)). Qed.
Lemma lem6955857 : term219 = True.
Proof. exact (TRANS (@lem6955799) (@lem6955856)). Qed.
Lemma lem6955858 : True = term219.
Proof. exact (SYM (@lem6955857)). Qed.
Lemma lem6955859 : term219.
Proof. exact (EQ_MP (@lem6955858) (@lem0)). Qed.
Lemma lem6955860 (_92655 : int) (h1 : term292 _92655) : term298 _92655.
Proof. exact (conj (@lem6955859) (@lem6955721 _92655 h1)). Qed.
Lemma lem6955862 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6955863 (_92655 : int) : term299 _92655.
Proof. exact (@lem6955862 term82 (term174 _92655)). Qed.
Lemma lem6955864 (_92655 : int) (h1 : term292 _92655) : term300 _92655.
Proof. exact (@lem6955863 _92655 (@lem6955860 _92655 h1)). Qed.
Lemma lem6955865 (_92655 : int) : (term301 _92655) = (term174 _92655).
Proof. exact (@lem1982733 (term174 _92655)). Qed.
Lemma lem6955866 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955867 (_92655 : int) : (term302 _92655) = (term177 _92655).
Proof. exact (MK_COMB (@lem6955866) (@lem6955865 _92655)). Qed.
Lemma lem6955868 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955869 (_92655 : int) : (term300 _92655) = (term178 _92655).
Proof. exact (MK_COMB (@lem6955867 _92655) (@lem6955868)). Qed.
Lemma lem6955870 (_92655 : int) (h1 : term292 _92655) : term178 _92655.
Proof. exact (EQ_MP (@lem6955869 _92655) (@lem6955864 _92655 h1)). Qed.
Lemma lem6955871 (_92655 : int) (h1 : term292 _92655) : term303 _92655.
Proof. exact (conj (@lem6955870 _92655 h1) (@lem6955796 _92655 h1)). Qed.
Lemma lem6955873 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6955874 (_92655 : int) : term304 _92655.
Proof. exact (@lem6955873 (term174 _92655) (real_of_int _92655)). Qed.
Lemma lem6955875 (_92655 : int) (h1 : term292 _92655) : term305 _92655.
Proof. exact (@lem6955874 _92655 (@lem6955871 _92655 h1)). Qed.
Lemma lem6955876 (_92655 : int) : (term306 _92655) = (term248 _92655).
Proof. exact (@lem1982759 (term143 _92655) (real_of_int _92655) term119). Qed.
Lemma lem6955877 (_92655 : int) : (term249 _92655) = (term250 _92655).
Proof. exact (@lem1982713 term119 (real_of_int _92655)). Qed.
Lemma lem6955879 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6955880 : term82 = term155.
Proof. exact (@lem6955879 term83). Qed.
Lemma lem6955882 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6955883 : term119 = term120.
Proof. exact (@lem6955882 term83). Qed.
Lemma lem6955884 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955885 : term251 = term252.
Proof. exact (MK_COMB (@lem6955884) (@lem6955883)). Qed.
Lemma lem6955886 : term253 = term254.
Proof. exact (MK_COMB (@lem6955885) (@lem6955880)). Qed.
Lemma lem6955887 : term255.
Proof. exact (@lem1981473 term119 term82 term82 term82 term58 term82). Qed.
Lemma lem6955889 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955890 : term220 = term226.
Proof. exact (@lem6955889 (NUMERAL 0) term83). Qed.
Lemma lem6955891 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955892 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955893 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955892 h1) (fun h1 : term226 = True => @lem6955891)). Qed.
Lemma lem6955894 : term226 = True.
Proof. exact (EQ_MP (@lem6955893) (@lem6955891)). Qed.
Lemma lem6955895 : term220 = True.
Proof. exact (TRANS (@lem6955890) (@lem6955894)). Qed.
Lemma lem6955896 : True = term220.
Proof. exact (SYM (@lem6955895)). Qed.
Lemma lem6955897 : term220.
Proof. exact (EQ_MP (@lem6955896) (@lem0)). Qed.
Lemma lem6955898 : term256.
Proof. exact (@lem6955887 (@lem6955897)). Qed.
Lemma lem6955900 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955901 : term220 = term226.
Proof. exact (@lem6955900 (NUMERAL 0) term83). Qed.
Lemma lem6955902 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955903 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955904 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955903 h1) (fun h1 : term226 = True => @lem6955902)). Qed.
Lemma lem6955905 : term226 = True.
Proof. exact (EQ_MP (@lem6955904) (@lem6955902)). Qed.
Lemma lem6955906 : term220 = True.
Proof. exact (TRANS (@lem6955901) (@lem6955905)). Qed.
Lemma lem6955907 : True = term220.
Proof. exact (SYM (@lem6955906)). Qed.
Lemma lem6955908 : term220.
Proof. exact (EQ_MP (@lem6955907) (@lem0)). Qed.
Lemma lem6955909 : term257.
Proof. exact (@lem6955898 (@lem6955908)). Qed.
Lemma lem6955911 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6955912 : term220 = term226.
Proof. exact (@lem6955911 (NUMERAL 0) term83). Qed.
Lemma lem6955913 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6955914 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6955915 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6955914 h1) (fun h1 : term226 = True => @lem6955913)). Qed.
Lemma lem6955916 : term226 = True.
Proof. exact (EQ_MP (@lem6955915) (@lem6955913)). Qed.
Lemma lem6955917 : term220 = True.
Proof. exact (TRANS (@lem6955912) (@lem6955916)). Qed.
Lemma lem6955918 : True = term220.
Proof. exact (SYM (@lem6955917)). Qed.
Lemma lem6955919 : term220.
Proof. exact (EQ_MP (@lem6955918) (@lem0)). Qed.
Lemma lem6955920 : term258.
Proof. exact (@lem6955909 (@lem6955919)). Qed.
Lemma lem6955922 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955923 : term128 = term129.
Proof. exact (@lem6955922 term83 term83). Qed.
Lemma lem6955924 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955925 : term131 = term83.
Proof. exact (EQ_MP (@lem6955924) (@lem940073)). Qed.
Lemma lem6955926 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955927 : term129 = term82.
Proof. exact (MK_COMB (@lem6955926) (@lem6955925)). Qed.
Lemma lem6955928 : term128 = term82.
Proof. exact (TRANS (@lem6955923) (@lem6955927)). Qed.
Lemma lem6955930 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6955931 : term156 = term161.
Proof. exact (@lem6955930 term83 term83). Qed.
Lemma lem6955932 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955933 : term131 = term83.
Proof. exact (EQ_MP (@lem6955932) (@lem940073)). Qed.
Lemma lem6955934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955935 : term129 = term82.
Proof. exact (MK_COMB (@lem6955934) (@lem6955933)). Qed.
Lemma lem6955936 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6955937 : term161 = term119.
Proof. exact (MK_COMB (@lem6955936) (@lem6955935)). Qed.
Lemma lem6955938 : term156 = term119.
Proof. exact (TRANS (@lem6955931) (@lem6955937)). Qed.
Lemma lem6955939 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955940 : term259 = term251.
Proof. exact (MK_COMB (@lem6955939) (@lem6955938)). Qed.
Lemma lem6955941 : term260 = term253.
Proof. exact (MK_COMB (@lem6955940) (@lem6955928)). Qed.
Lemma lem6955943 (m : nat) : (term261 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6955944 : term253 = term58.
Proof. exact (@lem6955943 term83). Qed.
Lemma lem6955945 : term260 = term58.
Proof. exact (TRANS (@lem6955941) (@lem6955944)). Qed.
Lemma lem6955946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6955947 : term262 = term263.
Proof. exact (MK_COMB (@lem6955946) (@lem6955945)). Qed.
Lemma lem6955948 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem6955949 : term264 = term231.
Proof. exact (MK_COMB (@lem6955947) (@lem6955948)). Qed.
Lemma lem6955951 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955952 : term231 = term58.
Proof. exact (@lem6955951 term83). Qed.
Lemma lem6955953 : term264 = term58.
Proof. exact (TRANS (@lem6955949) (@lem6955952)). Qed.
Lemma lem6955955 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6955956 : term128 = term129.
Proof. exact (@lem6955955 term83 term83). Qed.
Lemma lem6955957 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6955958 : term131 = term83.
Proof. exact (EQ_MP (@lem6955957) (@lem940073)). Qed.
Lemma lem6955959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6955960 : term129 = term82.
Proof. exact (MK_COMB (@lem6955959) (@lem6955958)). Qed.
Lemma lem6955961 : term128 = term82.
Proof. exact (TRANS (@lem6955956) (@lem6955960)). Qed.
Lemma lem6955962 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem6955963 : term265 = term231.
Proof. exact (MK_COMB (@lem6955962) (@lem6955961)). Qed.
Lemma lem6955965 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6955966 : term231 = term58.
Proof. exact (@lem6955965 term83). Qed.
Lemma lem6955967 : term265 = term58.
Proof. exact (TRANS (@lem6955963) (@lem6955966)). Qed.
Lemma lem6955968 : term58 = term265.
Proof. exact (SYM (@lem6955967)). Qed.
Lemma lem6955969 : term264 = term265.
Proof. exact (TRANS (@lem6955953) (@lem6955968)). Qed.
Lemma lem6955970 : term254 = term116.
Proof. exact (@lem6955920 (@lem6955969)). Qed.
Lemma lem6955971 : term253 = term116.
Proof. exact (TRANS (@lem6955886) (@lem6955970)). Qed.
Lemma lem6955973 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6955974 : term116 = term58.
Proof. exact (@lem6955973 term58). Qed.
Lemma lem6955975 : term253 = term58.
Proof. exact (TRANS (@lem6955971) (@lem6955974)). Qed.
Lemma lem6955976 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6955977 : term266 = term263.
Proof. exact (MK_COMB (@lem6955976) (@lem6955975)). Qed.
Lemma lem6955978 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6955979 (_92655 : int) : (term250 _92655) = (term267 _92655).
Proof. exact (MK_COMB (@lem6955977) (@lem6955978 _92655)). Qed.
Lemma lem6955980 (_92655 : int) : (term249 _92655) = (term267 _92655).
Proof. exact (TRANS (@lem6955877 _92655) (@lem6955979 _92655)). Qed.
Lemma lem6955981 (_92655 : int) : (term267 _92655) = term58.
Proof. exact (@lem1982719 (real_of_int _92655)). Qed.
Lemma lem6955982 (_92655 : int) : (term249 _92655) = term58.
Proof. exact (TRANS (@lem6955980 _92655) (@lem6955981 _92655)). Qed.
Lemma lem6955983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6955984 (_92655 : int) : (term268 _92655) = term80.
Proof. exact (MK_COMB (@lem6955983) (@lem6955982 _92655)). Qed.
Lemma lem6955985 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem6955986 (_92655 : int) : (term248 _92655) = term269.
Proof. exact (MK_COMB (@lem6955984 _92655) (@lem6955985)). Qed.
Lemma lem6955987 (_92655 : int) : (term306 _92655) = term269.
Proof. exact (TRANS (@lem6955876 _92655) (@lem6955986 _92655)). Qed.
Lemma lem6955988 : term269 = term119.
Proof. exact (@lem1982721 term119). Qed.
Lemma lem6955989 (_92655 : int) : (term306 _92655) = term119.
Proof. exact (TRANS (@lem6955987 _92655) (@lem6955988)). Qed.
Lemma lem6955990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6955991 (_92655 : int) : (term307 _92655) = term271.
Proof. exact (MK_COMB (@lem6955990) (@lem6955989 _92655)). Qed.
Lemma lem6955992 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6955993 (_92655 : int) : (term305 _92655) = term272.
Proof. exact (MK_COMB (@lem6955991 _92655) (@lem6955992)). Qed.
Lemma lem6955994 (_92655 : int) (h1 : term292 _92655) : term272.
Proof. exact (EQ_MP (@lem6955993 _92655) (@lem6955875 _92655 h1)). Qed.
Lemma lem6955996 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6955997 : term272 = term273.
Proof. exact (@lem6955996 term58 term119). Qed.
Lemma lem6955999 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956000 : term119 = term120.
Proof. exact (@lem6955999 term83). Qed.
Lemma lem6956002 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956003 : term58 = term116.
Proof. exact (@lem6956002 (NUMERAL 0)). Qed.
Lemma lem6956004 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956005 : term60 = term274.
Proof. exact (MK_COMB (@lem6956004) (@lem6956003)). Qed.
Lemma lem6956006 : term273 = term275.
Proof. exact (MK_COMB (@lem6956005) (@lem6956000)). Qed.
Lemma lem6956007 : term276.
Proof. exact (@lem1980026 term58 term82 term119 term82). Qed.
Lemma lem6956009 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956010 : term220 = term226.
Proof. exact (@lem6956009 (NUMERAL 0) term83). Qed.
Lemma lem6956011 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956012 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956013 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956012 h1) (fun h1 : term226 = True => @lem6956011)). Qed.
Lemma lem6956014 : term226 = True.
Proof. exact (EQ_MP (@lem6956013) (@lem6956011)). Qed.
Lemma lem6956015 : term220 = True.
Proof. exact (TRANS (@lem6956010) (@lem6956014)). Qed.
Lemma lem6956016 : True = term220.
Proof. exact (SYM (@lem6956015)). Qed.
Lemma lem6956017 : term220.
Proof. exact (EQ_MP (@lem6956016) (@lem0)). Qed.
Lemma lem6956018 : term277.
Proof. exact (@lem6956007 (@lem6956017)). Qed.
Lemma lem6956020 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956021 : term220 = term226.
Proof. exact (@lem6956020 (NUMERAL 0) term83). Qed.
Lemma lem6956022 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956023 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956024 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956023 h1) (fun h1 : term226 = True => @lem6956022)). Qed.
Lemma lem6956025 : term226 = True.
Proof. exact (EQ_MP (@lem6956024) (@lem6956022)). Qed.
Lemma lem6956026 : term220 = True.
Proof. exact (TRANS (@lem6956021) (@lem6956025)). Qed.
Lemma lem6956027 : True = term220.
Proof. exact (SYM (@lem6956026)). Qed.
Lemma lem6956028 : term220.
Proof. exact (EQ_MP (@lem6956027) (@lem0)). Qed.
Lemma lem6956029 : term275 = term278.
Proof. exact (@lem6956018 (@lem6956028)). Qed.
Lemma lem6956031 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956032 : term156 = term161.
Proof. exact (@lem6956031 term83 term83). Qed.
Lemma lem6956033 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956034 : term131 = term83.
Proof. exact (EQ_MP (@lem6956033) (@lem940073)). Qed.
Lemma lem6956035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956036 : term129 = term82.
Proof. exact (MK_COMB (@lem6956035) (@lem6956034)). Qed.
Lemma lem6956037 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956038 : term161 = term119.
Proof. exact (MK_COMB (@lem6956037) (@lem6956036)). Qed.
Lemma lem6956039 : term156 = term119.
Proof. exact (TRANS (@lem6956032) (@lem6956038)). Qed.
Lemma lem6956041 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956042 : term231 = term58.
Proof. exact (@lem6956041 term83). Qed.
Lemma lem6956043 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956044 : term279 = term60.
Proof. exact (MK_COMB (@lem6956043) (@lem6956042)). Qed.
Lemma lem6956045 : term278 = term273.
Proof. exact (MK_COMB (@lem6956044) (@lem6956039)). Qed.
Lemma lem6956047 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6956048 : term273 = term282.
Proof. exact (@lem6956047 (NUMERAL 0) term83). Qed.
Lemma lem6956049 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956050 (h1 : term227 = (BIT1 0)) : (term83 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6956051 : (term227 = (BIT1 0)) = ((term83 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956050 h1) (fun h1 : (term83 = (NUMERAL 0)) = False => @lem6956049)). Qed.
Lemma lem6956052 : (term83 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6956051) (@lem6956049)). Qed.
Lemma lem6956053 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6956054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6956055 : term283 = (and True).
Proof. exact (MK_COMB (@lem6956054) (@lem6956053)). Qed.
Lemma lem6956056 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem6956055) (@lem6956052)). Qed.
Lemma lem6956058 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6956059 : term282 = False.
Proof. exact (TRANS (@lem6956056) (@lem6956058)). Qed.
Lemma lem6956060 : term273 = False.
Proof. exact (TRANS (@lem6956048) (@lem6956059)). Qed.
Lemma lem6956061 : term278 = False.
Proof. exact (TRANS (@lem6956045) (@lem6956060)). Qed.
Lemma lem6956062 : term275 = False.
Proof. exact (TRANS (@lem6956029) (@lem6956061)). Qed.
Lemma lem6956063 : term273 = False.
Proof. exact (TRANS (@lem6956006) (@lem6956062)). Qed.
Lemma lem6956064 : term272 = False.
Proof. exact (TRANS (@lem6955997) (@lem6956063)). Qed.
Lemma lem6956065 (_92655 : int) (h1 : term292 _92655) : False.
Proof. exact (EQ_MP (@lem6956064) (@lem6955994 _92655 h1)). Qed.
Lemma lem6956066 (_92655 : int) (h1 : term308 _92655) : term308 _92655.
Proof. exact (h1). Qed.
Lemma lem6956067 (_92655 : int) (h1 : term308 _92655) : term211 _92655.
Proof. exact (proj2 (@lem6956066 _92655 h1)). Qed.
Lemma lem6956069 (_92655 : int) (h1 : term308 _92655) : term178 _92655.
Proof. exact (proj2 (@lem6956067 _92655 h1)). Qed.
Lemma lem6956070 (_92655 : int) (h1 : term308 _92655) : (real_of_int _92655) = term58.
Proof. exact (proj1 (@lem6956067 _92655 h1)). Qed.
Lemma lem6956072 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6956073 : term219 = term220.
Proof. exact (@lem6956072 term58 term82). Qed.
Lemma lem6956075 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956076 : term82 = term155.
Proof. exact (@lem6956075 term83). Qed.
Lemma lem6956078 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956079 : term58 = term116.
Proof. exact (@lem6956078 (NUMERAL 0)). Qed.
Lemma lem6956080 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956081 : term221 = term222.
Proof. exact (MK_COMB (@lem6956080) (@lem6956079)). Qed.
Lemma lem6956082 : term220 = term223.
Proof. exact (MK_COMB (@lem6956081) (@lem6956076)). Qed.
Lemma lem6956083 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6956085 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956086 : term220 = term226.
Proof. exact (@lem6956085 (NUMERAL 0) term83). Qed.
Lemma lem6956087 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956088 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956089 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956088 h1) (fun h1 : term226 = True => @lem6956087)). Qed.
Lemma lem6956090 : term226 = True.
Proof. exact (EQ_MP (@lem6956089) (@lem6956087)). Qed.
Lemma lem6956091 : term220 = True.
Proof. exact (TRANS (@lem6956086) (@lem6956090)). Qed.
Lemma lem6956092 : True = term220.
Proof. exact (SYM (@lem6956091)). Qed.
Lemma lem6956093 : term220.
Proof. exact (EQ_MP (@lem6956092) (@lem0)). Qed.
Lemma lem6956094 : term228.
Proof. exact (@lem6956083 (@lem6956093)). Qed.
Lemma lem6956096 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956097 : term220 = term226.
Proof. exact (@lem6956096 (NUMERAL 0) term83). Qed.
Lemma lem6956098 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956099 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956100 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956099 h1) (fun h1 : term226 = True => @lem6956098)). Qed.
Lemma lem6956101 : term226 = True.
Proof. exact (EQ_MP (@lem6956100) (@lem6956098)). Qed.
Lemma lem6956102 : term220 = True.
Proof. exact (TRANS (@lem6956097) (@lem6956101)). Qed.
Lemma lem6956103 : True = term220.
Proof. exact (SYM (@lem6956102)). Qed.
Lemma lem6956104 : term220.
Proof. exact (EQ_MP (@lem6956103) (@lem0)). Qed.
Lemma lem6956105 : term223 = term229.
Proof. exact (@lem6956094 (@lem6956104)). Qed.
Lemma lem6956107 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956108 : term128 = term129.
Proof. exact (@lem6956107 term83 term83). Qed.
Lemma lem6956109 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956110 : term131 = term83.
Proof. exact (EQ_MP (@lem6956109) (@lem940073)). Qed.
Lemma lem6956111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956112 : term129 = term82.
Proof. exact (MK_COMB (@lem6956111) (@lem6956110)). Qed.
Lemma lem6956113 : term128 = term82.
Proof. exact (TRANS (@lem6956108) (@lem6956112)). Qed.
Lemma lem6956115 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956116 : term231 = term58.
Proof. exact (@lem6956115 term83). Qed.
Lemma lem6956117 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956118 : term232 = term221.
Proof. exact (MK_COMB (@lem6956117) (@lem6956116)). Qed.
Lemma lem6956119 : term229 = term220.
Proof. exact (MK_COMB (@lem6956118) (@lem6956113)). Qed.
Lemma lem6956121 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956122 : term220 = term226.
Proof. exact (@lem6956121 (NUMERAL 0) term83). Qed.
Lemma lem6956123 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956124 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956125 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956124 h1) (fun h1 : term226 = True => @lem6956123)). Qed.
Lemma lem6956126 : term226 = True.
Proof. exact (EQ_MP (@lem6956125) (@lem6956123)). Qed.
Lemma lem6956127 : term220 = True.
Proof. exact (TRANS (@lem6956122) (@lem6956126)). Qed.
Lemma lem6956128 : term229 = True.
Proof. exact (TRANS (@lem6956119) (@lem6956127)). Qed.
Lemma lem6956129 : term223 = True.
Proof. exact (TRANS (@lem6956105) (@lem6956128)). Qed.
Lemma lem6956130 : term220 = True.
Proof. exact (TRANS (@lem6956082) (@lem6956129)). Qed.
Lemma lem6956131 : term219 = True.
Proof. exact (TRANS (@lem6956073) (@lem6956130)). Qed.
Lemma lem6956132 : True = term219.
Proof. exact (SYM (@lem6956131)). Qed.
Lemma lem6956133 : term219.
Proof. exact (EQ_MP (@lem6956132) (@lem0)). Qed.
Lemma lem6956134 (_92655 : int) (h1 : term308 _92655) : term298 _92655.
Proof. exact (conj (@lem6956133) (@lem6956069 _92655 h1)). Qed.
Lemma lem6956136 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6956137 (_92655 : int) : term299 _92655.
Proof. exact (@lem6956136 term82 (term174 _92655)). Qed.
Lemma lem6956138 (_92655 : int) (h1 : term308 _92655) : term300 _92655.
Proof. exact (@lem6956137 _92655 (@lem6956134 _92655 h1)). Qed.
Lemma lem6956139 (_92655 : int) : (term301 _92655) = (term174 _92655).
Proof. exact (@lem1982733 (term174 _92655)). Qed.
Lemma lem6956140 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956141 (_92655 : int) : (term302 _92655) = (term177 _92655).
Proof. exact (MK_COMB (@lem6956140) (@lem6956139 _92655)). Qed.
Lemma lem6956142 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956143 (_92655 : int) : (term300 _92655) = (term178 _92655).
Proof. exact (MK_COMB (@lem6956141 _92655) (@lem6956142)). Qed.
Lemma lem6956144 (_92655 : int) (h1 : term308 _92655) : term178 _92655.
Proof. exact (EQ_MP (@lem6956143 _92655) (@lem6956138 _92655 h1)). Qed.
Lemma lem6956146 (y : real) : term285 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6956147 (_92655 : int) : term286 _92655.
Proof. exact (@lem6956146 (real_of_int _92655)). Qed.
Lemma lem6956148 (_92655 : int) (h1 : term308 _92655) : term287 _92655.
Proof. exact (@lem6956147 _92655 (@lem6956070 _92655 h1)). Qed.
Lemma lem6956149 (_92655 : int) (h1 : term308 _92655) : term309 _92655.
Proof. exact (@lem6956148 _92655 h1 term82). Qed.
Lemma lem6956150 (_92655 : int) : (term309 _92655) = ((term296 _92655) = term58).
Proof. exact (eq_refl (term309 _92655)). Qed.
Lemma lem6956151 (_92655 : int) (h1 : term308 _92655) : (term296 _92655) = term58.
Proof. exact (EQ_MP (@lem6956150 _92655) (@lem6956149 _92655 h1)). Qed.
Lemma lem6956152 (_92655 : int) : (term296 _92655) = (real_of_int _92655).
Proof. exact (@lem1982733 (real_of_int _92655)). Qed.
Lemma lem6956153 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6956154 (_92655 : int) : (term310 _92655) = (term67 _92655).
Proof. exact (MK_COMB (@lem6956153) (@lem6956152 _92655)). Qed.
Lemma lem6956155 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956156 (_92655 : int) : ((term296 _92655) = term58) = ((real_of_int _92655) = term58).
Proof. exact (MK_COMB (@lem6956154 _92655) (@lem6956155)). Qed.
Lemma lem6956157 (_92655 : int) (h1 : term308 _92655) : (real_of_int _92655) = term58.
Proof. exact (EQ_MP (@lem6956156 _92655) (@lem6956151 _92655 h1)). Qed.
Lemma lem6956158 (_92655 : int) (h1 : term308 _92655) : term211 _92655.
Proof. exact (conj (@lem6956157 _92655 h1) (@lem6956144 _92655 h1)). Qed.
Lemma lem6956160 (x : real) (y : real) : term290 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6956161 (_92655 : int) : term311 _92655.
Proof. exact (@lem6956160 (real_of_int _92655) (term174 _92655)). Qed.
Lemma lem6956162 (_92655 : int) (h1 : term308 _92655) : term312 _92655.
Proof. exact (@lem6956161 _92655 (@lem6956158 _92655 h1)). Qed.
Lemma lem6956163 (_92655 : int) : (term313 _92655) = (term314 _92655).
Proof. exact (@lem1982763 (real_of_int _92655) (term143 _92655) term119). Qed.
Lemma lem6956164 (_92655 : int) : (term315 _92655) = (term250 _92655).
Proof. exact (@lem1982715 term119 (real_of_int _92655)). Qed.
Lemma lem6956166 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956167 : term82 = term155.
Proof. exact (@lem6956166 term83). Qed.
Lemma lem6956169 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956170 : term119 = term120.
Proof. exact (@lem6956169 term83). Qed.
Lemma lem6956171 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956172 : term251 = term252.
Proof. exact (MK_COMB (@lem6956171) (@lem6956170)). Qed.
Lemma lem6956173 : term253 = term254.
Proof. exact (MK_COMB (@lem6956172) (@lem6956167)). Qed.
Lemma lem6956174 : term255.
Proof. exact (@lem1981473 term119 term82 term82 term82 term58 term82). Qed.
Lemma lem6956176 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956177 : term220 = term226.
Proof. exact (@lem6956176 (NUMERAL 0) term83). Qed.
Lemma lem6956178 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956179 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956180 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956179 h1) (fun h1 : term226 = True => @lem6956178)). Qed.
Lemma lem6956181 : term226 = True.
Proof. exact (EQ_MP (@lem6956180) (@lem6956178)). Qed.
Lemma lem6956182 : term220 = True.
Proof. exact (TRANS (@lem6956177) (@lem6956181)). Qed.
Lemma lem6956183 : True = term220.
Proof. exact (SYM (@lem6956182)). Qed.
Lemma lem6956184 : term220.
Proof. exact (EQ_MP (@lem6956183) (@lem0)). Qed.
Lemma lem6956185 : term256.
Proof. exact (@lem6956174 (@lem6956184)). Qed.
Lemma lem6956187 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956188 : term220 = term226.
Proof. exact (@lem6956187 (NUMERAL 0) term83). Qed.
Lemma lem6956189 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956190 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956191 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956190 h1) (fun h1 : term226 = True => @lem6956189)). Qed.
Lemma lem6956192 : term226 = True.
Proof. exact (EQ_MP (@lem6956191) (@lem6956189)). Qed.
Lemma lem6956193 : term220 = True.
Proof. exact (TRANS (@lem6956188) (@lem6956192)). Qed.
Lemma lem6956194 : True = term220.
Proof. exact (SYM (@lem6956193)). Qed.
Lemma lem6956195 : term220.
Proof. exact (EQ_MP (@lem6956194) (@lem0)). Qed.
Lemma lem6956196 : term257.
Proof. exact (@lem6956185 (@lem6956195)). Qed.
Lemma lem6956198 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956199 : term220 = term226.
Proof. exact (@lem6956198 (NUMERAL 0) term83). Qed.
Lemma lem6956200 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956201 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956202 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956201 h1) (fun h1 : term226 = True => @lem6956200)). Qed.
Lemma lem6956203 : term226 = True.
Proof. exact (EQ_MP (@lem6956202) (@lem6956200)). Qed.
Lemma lem6956204 : term220 = True.
Proof. exact (TRANS (@lem6956199) (@lem6956203)). Qed.
Lemma lem6956205 : True = term220.
Proof. exact (SYM (@lem6956204)). Qed.
Lemma lem6956206 : term220.
Proof. exact (EQ_MP (@lem6956205) (@lem0)). Qed.
Lemma lem6956207 : term258.
Proof. exact (@lem6956196 (@lem6956206)). Qed.
Lemma lem6956209 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956210 : term128 = term129.
Proof. exact (@lem6956209 term83 term83). Qed.
Lemma lem6956211 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956212 : term131 = term83.
Proof. exact (EQ_MP (@lem6956211) (@lem940073)). Qed.
Lemma lem6956213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956214 : term129 = term82.
Proof. exact (MK_COMB (@lem6956213) (@lem6956212)). Qed.
Lemma lem6956215 : term128 = term82.
Proof. exact (TRANS (@lem6956210) (@lem6956214)). Qed.
Lemma lem6956217 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956218 : term156 = term161.
Proof. exact (@lem6956217 term83 term83). Qed.
Lemma lem6956219 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956220 : term131 = term83.
Proof. exact (EQ_MP (@lem6956219) (@lem940073)). Qed.
Lemma lem6956221 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956222 : term129 = term82.
Proof. exact (MK_COMB (@lem6956221) (@lem6956220)). Qed.
Lemma lem6956223 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956224 : term161 = term119.
Proof. exact (MK_COMB (@lem6956223) (@lem6956222)). Qed.
Lemma lem6956225 : term156 = term119.
Proof. exact (TRANS (@lem6956218) (@lem6956224)). Qed.
Lemma lem6956226 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956227 : term259 = term251.
Proof. exact (MK_COMB (@lem6956226) (@lem6956225)). Qed.
Lemma lem6956228 : term260 = term253.
Proof. exact (MK_COMB (@lem6956227) (@lem6956215)). Qed.
Lemma lem6956230 (m : nat) : (term261 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6956231 : term253 = term58.
Proof. exact (@lem6956230 term83). Qed.
Lemma lem6956232 : term260 = term58.
Proof. exact (TRANS (@lem6956228) (@lem6956231)). Qed.
Lemma lem6956233 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6956234 : term262 = term263.
Proof. exact (MK_COMB (@lem6956233) (@lem6956232)). Qed.
Lemma lem6956235 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem6956236 : term264 = term231.
Proof. exact (MK_COMB (@lem6956234) (@lem6956235)). Qed.
Lemma lem6956238 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956239 : term231 = term58.
Proof. exact (@lem6956238 term83). Qed.
Lemma lem6956240 : term264 = term58.
Proof. exact (TRANS (@lem6956236) (@lem6956239)). Qed.
Lemma lem6956242 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956243 : term128 = term129.
Proof. exact (@lem6956242 term83 term83). Qed.
Lemma lem6956244 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956245 : term131 = term83.
Proof. exact (EQ_MP (@lem6956244) (@lem940073)). Qed.
Lemma lem6956246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956247 : term129 = term82.
Proof. exact (MK_COMB (@lem6956246) (@lem6956245)). Qed.
Lemma lem6956248 : term128 = term82.
Proof. exact (TRANS (@lem6956243) (@lem6956247)). Qed.
Lemma lem6956249 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem6956250 : term265 = term231.
Proof. exact (MK_COMB (@lem6956249) (@lem6956248)). Qed.
Lemma lem6956252 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956253 : term231 = term58.
Proof. exact (@lem6956252 term83). Qed.
Lemma lem6956254 : term265 = term58.
Proof. exact (TRANS (@lem6956250) (@lem6956253)). Qed.
Lemma lem6956255 : term58 = term265.
Proof. exact (SYM (@lem6956254)). Qed.
Lemma lem6956256 : term264 = term265.
Proof. exact (TRANS (@lem6956240) (@lem6956255)). Qed.
Lemma lem6956257 : term254 = term116.
Proof. exact (@lem6956207 (@lem6956256)). Qed.
Lemma lem6956258 : term253 = term116.
Proof. exact (TRANS (@lem6956173) (@lem6956257)). Qed.
Lemma lem6956260 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6956261 : term116 = term58.
Proof. exact (@lem6956260 term58). Qed.
Lemma lem6956262 : term253 = term58.
Proof. exact (TRANS (@lem6956258) (@lem6956261)). Qed.
Lemma lem6956263 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6956264 : term266 = term263.
Proof. exact (MK_COMB (@lem6956263) (@lem6956262)). Qed.
Lemma lem6956265 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6956266 (_92655 : int) : (term250 _92655) = (term267 _92655).
Proof. exact (MK_COMB (@lem6956264) (@lem6956265 _92655)). Qed.
Lemma lem6956267 (_92655 : int) : (term315 _92655) = (term267 _92655).
Proof. exact (TRANS (@lem6956164 _92655) (@lem6956266 _92655)). Qed.
Lemma lem6956268 (_92655 : int) : (term267 _92655) = term58.
Proof. exact (@lem1982719 (real_of_int _92655)). Qed.
Lemma lem6956269 (_92655 : int) : (term315 _92655) = term58.
Proof. exact (TRANS (@lem6956267 _92655) (@lem6956268 _92655)). Qed.
Lemma lem6956270 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956271 (_92655 : int) : (term316 _92655) = term80.
Proof. exact (MK_COMB (@lem6956270) (@lem6956269 _92655)). Qed.
Lemma lem6956272 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem6956273 (_92655 : int) : (term314 _92655) = term269.
Proof. exact (MK_COMB (@lem6956271 _92655) (@lem6956272)). Qed.
Lemma lem6956274 (_92655 : int) : (term313 _92655) = term269.
Proof. exact (TRANS (@lem6956163 _92655) (@lem6956273 _92655)). Qed.
Lemma lem6956275 : term269 = term119.
Proof. exact (@lem1982721 term119). Qed.
Lemma lem6956276 (_92655 : int) : (term313 _92655) = term119.
Proof. exact (TRANS (@lem6956274 _92655) (@lem6956275)). Qed.
Lemma lem6956277 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956278 (_92655 : int) : (term317 _92655) = term271.
Proof. exact (MK_COMB (@lem6956277) (@lem6956276 _92655)). Qed.
Lemma lem6956279 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956280 (_92655 : int) : (term312 _92655) = term272.
Proof. exact (MK_COMB (@lem6956278 _92655) (@lem6956279)). Qed.
Lemma lem6956281 (_92655 : int) (h1 : term308 _92655) : term272.
Proof. exact (EQ_MP (@lem6956280 _92655) (@lem6956162 _92655 h1)). Qed.
Lemma lem6956283 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6956284 : term272 = term273.
Proof. exact (@lem6956283 term58 term119). Qed.
Lemma lem6956286 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956287 : term119 = term120.
Proof. exact (@lem6956286 term83). Qed.
Lemma lem6956289 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956290 : term58 = term116.
Proof. exact (@lem6956289 (NUMERAL 0)). Qed.
Lemma lem6956291 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956292 : term60 = term274.
Proof. exact (MK_COMB (@lem6956291) (@lem6956290)). Qed.
Lemma lem6956293 : term273 = term275.
Proof. exact (MK_COMB (@lem6956292) (@lem6956287)). Qed.
Lemma lem6956294 : term276.
Proof. exact (@lem1980026 term58 term82 term119 term82). Qed.
Lemma lem6956296 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956297 : term220 = term226.
Proof. exact (@lem6956296 (NUMERAL 0) term83). Qed.
Lemma lem6956298 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956299 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956300 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956299 h1) (fun h1 : term226 = True => @lem6956298)). Qed.
Lemma lem6956301 : term226 = True.
Proof. exact (EQ_MP (@lem6956300) (@lem6956298)). Qed.
Lemma lem6956302 : term220 = True.
Proof. exact (TRANS (@lem6956297) (@lem6956301)). Qed.
Lemma lem6956303 : True = term220.
Proof. exact (SYM (@lem6956302)). Qed.
Lemma lem6956304 : term220.
Proof. exact (EQ_MP (@lem6956303) (@lem0)). Qed.
Lemma lem6956305 : term277.
Proof. exact (@lem6956294 (@lem6956304)). Qed.
Lemma lem6956307 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956308 : term220 = term226.
Proof. exact (@lem6956307 (NUMERAL 0) term83). Qed.
Lemma lem6956309 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956310 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956311 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956310 h1) (fun h1 : term226 = True => @lem6956309)). Qed.
Lemma lem6956312 : term226 = True.
Proof. exact (EQ_MP (@lem6956311) (@lem6956309)). Qed.
Lemma lem6956313 : term220 = True.
Proof. exact (TRANS (@lem6956308) (@lem6956312)). Qed.
Lemma lem6956314 : True = term220.
Proof. exact (SYM (@lem6956313)). Qed.
Lemma lem6956315 : term220.
Proof. exact (EQ_MP (@lem6956314) (@lem0)). Qed.
Lemma lem6956316 : term275 = term278.
Proof. exact (@lem6956305 (@lem6956315)). Qed.
Lemma lem6956318 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956319 : term156 = term161.
Proof. exact (@lem6956318 term83 term83). Qed.
Lemma lem6956320 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956321 : term131 = term83.
Proof. exact (EQ_MP (@lem6956320) (@lem940073)). Qed.
Lemma lem6956322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956323 : term129 = term82.
Proof. exact (MK_COMB (@lem6956322) (@lem6956321)). Qed.
Lemma lem6956324 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956325 : term161 = term119.
Proof. exact (MK_COMB (@lem6956324) (@lem6956323)). Qed.
Lemma lem6956326 : term156 = term119.
Proof. exact (TRANS (@lem6956319) (@lem6956325)). Qed.
Lemma lem6956328 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956329 : term231 = term58.
Proof. exact (@lem6956328 term83). Qed.
Lemma lem6956330 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956331 : term279 = term60.
Proof. exact (MK_COMB (@lem6956330) (@lem6956329)). Qed.
Lemma lem6956332 : term278 = term273.
Proof. exact (MK_COMB (@lem6956331) (@lem6956326)). Qed.
Lemma lem6956334 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6956335 : term273 = term282.
Proof. exact (@lem6956334 (NUMERAL 0) term83). Qed.
Lemma lem6956336 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956337 (h1 : term227 = (BIT1 0)) : (term83 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6956338 : (term227 = (BIT1 0)) = ((term83 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956337 h1) (fun h1 : (term83 = (NUMERAL 0)) = False => @lem6956336)). Qed.
Lemma lem6956339 : (term83 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6956338) (@lem6956336)). Qed.
Lemma lem6956340 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6956341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6956342 : term283 = (and True).
Proof. exact (MK_COMB (@lem6956341) (@lem6956340)). Qed.
Lemma lem6956343 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem6956342) (@lem6956339)). Qed.
Lemma lem6956345 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6956346 : term282 = False.
Proof. exact (TRANS (@lem6956343) (@lem6956345)). Qed.
Lemma lem6956347 : term273 = False.
Proof. exact (TRANS (@lem6956335) (@lem6956346)). Qed.
Lemma lem6956348 : term278 = False.
Proof. exact (TRANS (@lem6956332) (@lem6956347)). Qed.
Lemma lem6956349 : term275 = False.
Proof. exact (TRANS (@lem6956316) (@lem6956348)). Qed.
Lemma lem6956350 : term273 = False.
Proof. exact (TRANS (@lem6956293) (@lem6956349)). Qed.
Lemma lem6956351 : term272 = False.
Proof. exact (TRANS (@lem6956284) (@lem6956350)). Qed.
Lemma lem6956352 (_92655 : int) (h1 : term308 _92655) : False.
Proof. exact (EQ_MP (@lem6956351) (@lem6956281 _92655 h1)). Qed.
Lemma lem6956353 (_92655 : int) (h1 : term209 _92655) : False.
Proof. exact (or_elim (@lem6955717 _92655 h1) (fun h0 : term292 _92655 => @lem6956065 _92655 h0) (fun h0 : term308 _92655 => @lem6956352 _92655 h0)). Qed.
Lemma lem6956354 (_92655 : int) (h1 : term205 _92655) : term205 _92655.
Proof. exact (h1). Qed.
Lemma lem6956355 (_92655 : int) (h1 : term218 _92655) : term218 _92655.
Proof. exact (h1). Qed.
Lemma lem6956356 (_92655 : int) (h1 : term218 _92655) : term206 _92655.
Proof. exact (proj2 (@lem6956355 _92655 h1)). Qed.
Lemma lem6956358 (_92655 : int) (h1 : term218 _92655) : term167 _92655.
Proof. exact (proj2 (@lem6956356 _92655 h1)). Qed.
Lemma lem6956359 (_92655 : int) (h1 : term218 _92655) : term146 _92655.
Proof. exact (proj1 (@lem6956356 _92655 h1)). Qed.
Lemma lem6956361 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6956362 : term219 = term220.
Proof. exact (@lem6956361 term58 term82). Qed.
Lemma lem6956364 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956365 : term82 = term155.
Proof. exact (@lem6956364 term83). Qed.
Lemma lem6956367 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956368 : term58 = term116.
Proof. exact (@lem6956367 (NUMERAL 0)). Qed.
Lemma lem6956369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956370 : term221 = term222.
Proof. exact (MK_COMB (@lem6956369) (@lem6956368)). Qed.
Lemma lem6956371 : term220 = term223.
Proof. exact (MK_COMB (@lem6956370) (@lem6956365)). Qed.
Lemma lem6956372 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6956374 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956375 : term220 = term226.
Proof. exact (@lem6956374 (NUMERAL 0) term83). Qed.
Lemma lem6956376 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956377 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956378 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956377 h1) (fun h1 : term226 = True => @lem6956376)). Qed.
Lemma lem6956379 : term226 = True.
Proof. exact (EQ_MP (@lem6956378) (@lem6956376)). Qed.
Lemma lem6956380 : term220 = True.
Proof. exact (TRANS (@lem6956375) (@lem6956379)). Qed.
Lemma lem6956381 : True = term220.
Proof. exact (SYM (@lem6956380)). Qed.
Lemma lem6956382 : term220.
Proof. exact (EQ_MP (@lem6956381) (@lem0)). Qed.
Lemma lem6956383 : term228.
Proof. exact (@lem6956372 (@lem6956382)). Qed.
Lemma lem6956385 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956386 : term220 = term226.
Proof. exact (@lem6956385 (NUMERAL 0) term83). Qed.
Lemma lem6956387 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956388 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956389 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956388 h1) (fun h1 : term226 = True => @lem6956387)). Qed.
Lemma lem6956390 : term226 = True.
Proof. exact (EQ_MP (@lem6956389) (@lem6956387)). Qed.
Lemma lem6956391 : term220 = True.
Proof. exact (TRANS (@lem6956386) (@lem6956390)). Qed.
Lemma lem6956392 : True = term220.
Proof. exact (SYM (@lem6956391)). Qed.
Lemma lem6956393 : term220.
Proof. exact (EQ_MP (@lem6956392) (@lem0)). Qed.
Lemma lem6956394 : term223 = term229.
Proof. exact (@lem6956383 (@lem6956393)). Qed.
Lemma lem6956396 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956397 : term128 = term129.
Proof. exact (@lem6956396 term83 term83). Qed.
Lemma lem6956398 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956399 : term131 = term83.
Proof. exact (EQ_MP (@lem6956398) (@lem940073)). Qed.
Lemma lem6956400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956401 : term129 = term82.
Proof. exact (MK_COMB (@lem6956400) (@lem6956399)). Qed.
Lemma lem6956402 : term128 = term82.
Proof. exact (TRANS (@lem6956397) (@lem6956401)). Qed.
Lemma lem6956404 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956405 : term231 = term58.
Proof. exact (@lem6956404 term83). Qed.
Lemma lem6956406 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956407 : term232 = term221.
Proof. exact (MK_COMB (@lem6956406) (@lem6956405)). Qed.
Lemma lem6956408 : term229 = term220.
Proof. exact (MK_COMB (@lem6956407) (@lem6956402)). Qed.
Lemma lem6956410 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956411 : term220 = term226.
Proof. exact (@lem6956410 (NUMERAL 0) term83). Qed.
Lemma lem6956412 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956413 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956414 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956413 h1) (fun h1 : term226 = True => @lem6956412)). Qed.
Lemma lem6956415 : term226 = True.
Proof. exact (EQ_MP (@lem6956414) (@lem6956412)). Qed.
Lemma lem6956416 : term220 = True.
Proof. exact (TRANS (@lem6956411) (@lem6956415)). Qed.
Lemma lem6956417 : term229 = True.
Proof. exact (TRANS (@lem6956408) (@lem6956416)). Qed.
Lemma lem6956418 : term223 = True.
Proof. exact (TRANS (@lem6956394) (@lem6956417)). Qed.
Lemma lem6956419 : term220 = True.
Proof. exact (TRANS (@lem6956371) (@lem6956418)). Qed.
Lemma lem6956420 : term219 = True.
Proof. exact (TRANS (@lem6956362) (@lem6956419)). Qed.
Lemma lem6956421 : True = term219.
Proof. exact (SYM (@lem6956420)). Qed.
Lemma lem6956422 : term219.
Proof. exact (EQ_MP (@lem6956421) (@lem0)). Qed.
Lemma lem6956423 (_92655 : int) (h1 : term218 _92655) : term233 _92655.
Proof. exact (conj (@lem6956422) (@lem6956358 _92655 h1)). Qed.
Lemma lem6956425 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6956426 (_92655 : int) : term235 _92655.
Proof. exact (@lem6956425 term82 (term164 _92655)). Qed.
Lemma lem6956427 (_92655 : int) (h1 : term218 _92655) : term236 _92655.
Proof. exact (@lem6956426 _92655 (@lem6956423 _92655 h1)). Qed.
Lemma lem6956428 (_92655 : int) : (term237 _92655) = (term164 _92655).
Proof. exact (@lem1982733 (term164 _92655)). Qed.
Lemma lem6956429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956430 (_92655 : int) : (term238 _92655) = (term166 _92655).
Proof. exact (MK_COMB (@lem6956429) (@lem6956428 _92655)). Qed.
Lemma lem6956431 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956432 (_92655 : int) : (term236 _92655) = (term167 _92655).
Proof. exact (MK_COMB (@lem6956430 _92655) (@lem6956431)). Qed.
Lemma lem6956433 (_92655 : int) (h1 : term218 _92655) : term167 _92655.
Proof. exact (EQ_MP (@lem6956432 _92655) (@lem6956427 _92655 h1)). Qed.
Lemma lem6956435 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6956436 : term219 = term220.
Proof. exact (@lem6956435 term58 term82). Qed.
Lemma lem6956438 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956439 : term82 = term155.
Proof. exact (@lem6956438 term83). Qed.
Lemma lem6956441 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956442 : term58 = term116.
Proof. exact (@lem6956441 (NUMERAL 0)). Qed.
Lemma lem6956443 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956444 : term221 = term222.
Proof. exact (MK_COMB (@lem6956443) (@lem6956442)). Qed.
Lemma lem6956445 : term220 = term223.
Proof. exact (MK_COMB (@lem6956444) (@lem6956439)). Qed.
Lemma lem6956446 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6956448 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956449 : term220 = term226.
Proof. exact (@lem6956448 (NUMERAL 0) term83). Qed.
Lemma lem6956450 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956451 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956452 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956451 h1) (fun h1 : term226 = True => @lem6956450)). Qed.
Lemma lem6956453 : term226 = True.
Proof. exact (EQ_MP (@lem6956452) (@lem6956450)). Qed.
Lemma lem6956454 : term220 = True.
Proof. exact (TRANS (@lem6956449) (@lem6956453)). Qed.
Lemma lem6956455 : True = term220.
Proof. exact (SYM (@lem6956454)). Qed.
Lemma lem6956456 : term220.
Proof. exact (EQ_MP (@lem6956455) (@lem0)). Qed.
Lemma lem6956457 : term228.
Proof. exact (@lem6956446 (@lem6956456)). Qed.
Lemma lem6956459 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956460 : term220 = term226.
Proof. exact (@lem6956459 (NUMERAL 0) term83). Qed.
Lemma lem6956461 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956462 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956463 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956462 h1) (fun h1 : term226 = True => @lem6956461)). Qed.
Lemma lem6956464 : term226 = True.
Proof. exact (EQ_MP (@lem6956463) (@lem6956461)). Qed.
Lemma lem6956465 : term220 = True.
Proof. exact (TRANS (@lem6956460) (@lem6956464)). Qed.
Lemma lem6956466 : True = term220.
Proof. exact (SYM (@lem6956465)). Qed.
Lemma lem6956467 : term220.
Proof. exact (EQ_MP (@lem6956466) (@lem0)). Qed.
Lemma lem6956468 : term223 = term229.
Proof. exact (@lem6956457 (@lem6956467)). Qed.
Lemma lem6956470 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956471 : term128 = term129.
Proof. exact (@lem6956470 term83 term83). Qed.
Lemma lem6956472 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956473 : term131 = term83.
Proof. exact (EQ_MP (@lem6956472) (@lem940073)). Qed.
Lemma lem6956474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956475 : term129 = term82.
Proof. exact (MK_COMB (@lem6956474) (@lem6956473)). Qed.
Lemma lem6956476 : term128 = term82.
Proof. exact (TRANS (@lem6956471) (@lem6956475)). Qed.
Lemma lem6956478 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956479 : term231 = term58.
Proof. exact (@lem6956478 term83). Qed.
Lemma lem6956480 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956481 : term232 = term221.
Proof. exact (MK_COMB (@lem6956480) (@lem6956479)). Qed.
Lemma lem6956482 : term229 = term220.
Proof. exact (MK_COMB (@lem6956481) (@lem6956476)). Qed.
Lemma lem6956484 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956485 : term220 = term226.
Proof. exact (@lem6956484 (NUMERAL 0) term83). Qed.
Lemma lem6956486 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956487 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956488 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956487 h1) (fun h1 : term226 = True => @lem6956486)). Qed.
Lemma lem6956489 : term226 = True.
Proof. exact (EQ_MP (@lem6956488) (@lem6956486)). Qed.
Lemma lem6956490 : term220 = True.
Proof. exact (TRANS (@lem6956485) (@lem6956489)). Qed.
Lemma lem6956491 : term229 = True.
Proof. exact (TRANS (@lem6956482) (@lem6956490)). Qed.
Lemma lem6956492 : term223 = True.
Proof. exact (TRANS (@lem6956468) (@lem6956491)). Qed.
Lemma lem6956493 : term220 = True.
Proof. exact (TRANS (@lem6956445) (@lem6956492)). Qed.
Lemma lem6956494 : term219 = True.
Proof. exact (TRANS (@lem6956436) (@lem6956493)). Qed.
Lemma lem6956495 : True = term219.
Proof. exact (SYM (@lem6956494)). Qed.
Lemma lem6956496 : term219.
Proof. exact (EQ_MP (@lem6956495) (@lem0)). Qed.
Lemma lem6956497 (_92655 : int) (h1 : term218 _92655) : term239 _92655.
Proof. exact (conj (@lem6956496) (@lem6956359 _92655 h1)). Qed.
Lemma lem6956499 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6956500 (_92655 : int) : term240 _92655.
Proof. exact (@lem6956499 term82 (term143 _92655)). Qed.
Lemma lem6956501 (_92655 : int) (h1 : term218 _92655) : term241 _92655.
Proof. exact (@lem6956500 _92655 (@lem6956497 _92655 h1)). Qed.
Lemma lem6956502 (_92655 : int) : (term242 _92655) = (term143 _92655).
Proof. exact (@lem1982733 (term143 _92655)). Qed.
Lemma lem6956503 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956504 (_92655 : int) : (term243 _92655) = (term145 _92655).
Proof. exact (MK_COMB (@lem6956503) (@lem6956502 _92655)). Qed.
Lemma lem6956505 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956506 (_92655 : int) : (term241 _92655) = (term146 _92655).
Proof. exact (MK_COMB (@lem6956504 _92655) (@lem6956505)). Qed.
Lemma lem6956507 (_92655 : int) (h1 : term218 _92655) : term146 _92655.
Proof. exact (EQ_MP (@lem6956506 _92655) (@lem6956501 _92655 h1)). Qed.
Lemma lem6956508 (_92655 : int) (h1 : term218 _92655) : term206 _92655.
Proof. exact (conj (@lem6956507 _92655 h1) (@lem6956433 _92655 h1)). Qed.
Lemma lem6956510 (x : real) (y : real) : term244 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6956511 (_92655 : int) : term245 _92655.
Proof. exact (@lem6956510 (term143 _92655) (term164 _92655)). Qed.
Lemma lem6956512 (_92655 : int) (h1 : term218 _92655) : term246 _92655.
Proof. exact (@lem6956511 _92655 (@lem6956508 _92655 h1)). Qed.
Lemma lem6956513 (_92655 : int) : (term247 _92655) = (term248 _92655).
Proof. exact (@lem1982763 (term143 _92655) (real_of_int _92655) term119). Qed.
Lemma lem6956514 (_92655 : int) : (term249 _92655) = (term250 _92655).
Proof. exact (@lem1982713 term119 (real_of_int _92655)). Qed.
Lemma lem6956516 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956517 : term82 = term155.
Proof. exact (@lem6956516 term83). Qed.
Lemma lem6956519 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956520 : term119 = term120.
Proof. exact (@lem6956519 term83). Qed.
Lemma lem6956521 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956522 : term251 = term252.
Proof. exact (MK_COMB (@lem6956521) (@lem6956520)). Qed.
Lemma lem6956523 : term253 = term254.
Proof. exact (MK_COMB (@lem6956522) (@lem6956517)). Qed.
Lemma lem6956524 : term255.
Proof. exact (@lem1981473 term119 term82 term82 term82 term58 term82). Qed.
Lemma lem6956526 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956527 : term220 = term226.
Proof. exact (@lem6956526 (NUMERAL 0) term83). Qed.
Lemma lem6956528 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956529 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956530 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956529 h1) (fun h1 : term226 = True => @lem6956528)). Qed.
Lemma lem6956531 : term226 = True.
Proof. exact (EQ_MP (@lem6956530) (@lem6956528)). Qed.
Lemma lem6956532 : term220 = True.
Proof. exact (TRANS (@lem6956527) (@lem6956531)). Qed.
Lemma lem6956533 : True = term220.
Proof. exact (SYM (@lem6956532)). Qed.
Lemma lem6956534 : term220.
Proof. exact (EQ_MP (@lem6956533) (@lem0)). Qed.
Lemma lem6956535 : term256.
Proof. exact (@lem6956524 (@lem6956534)). Qed.
Lemma lem6956537 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956538 : term220 = term226.
Proof. exact (@lem6956537 (NUMERAL 0) term83). Qed.
Lemma lem6956539 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956540 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956541 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956540 h1) (fun h1 : term226 = True => @lem6956539)). Qed.
Lemma lem6956542 : term226 = True.
Proof. exact (EQ_MP (@lem6956541) (@lem6956539)). Qed.
Lemma lem6956543 : term220 = True.
Proof. exact (TRANS (@lem6956538) (@lem6956542)). Qed.
Lemma lem6956544 : True = term220.
Proof. exact (SYM (@lem6956543)). Qed.
Lemma lem6956545 : term220.
Proof. exact (EQ_MP (@lem6956544) (@lem0)). Qed.
Lemma lem6956546 : term257.
Proof. exact (@lem6956535 (@lem6956545)). Qed.
Lemma lem6956548 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956549 : term220 = term226.
Proof. exact (@lem6956548 (NUMERAL 0) term83). Qed.
Lemma lem6956550 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956551 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956552 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956551 h1) (fun h1 : term226 = True => @lem6956550)). Qed.
Lemma lem6956553 : term226 = True.
Proof. exact (EQ_MP (@lem6956552) (@lem6956550)). Qed.
Lemma lem6956554 : term220 = True.
Proof. exact (TRANS (@lem6956549) (@lem6956553)). Qed.
Lemma lem6956555 : True = term220.
Proof. exact (SYM (@lem6956554)). Qed.
Lemma lem6956556 : term220.
Proof. exact (EQ_MP (@lem6956555) (@lem0)). Qed.
Lemma lem6956557 : term258.
Proof. exact (@lem6956546 (@lem6956556)). Qed.
Lemma lem6956559 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956560 : term128 = term129.
Proof. exact (@lem6956559 term83 term83). Qed.
Lemma lem6956561 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956562 : term131 = term83.
Proof. exact (EQ_MP (@lem6956561) (@lem940073)). Qed.
Lemma lem6956563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956564 : term129 = term82.
Proof. exact (MK_COMB (@lem6956563) (@lem6956562)). Qed.
Lemma lem6956565 : term128 = term82.
Proof. exact (TRANS (@lem6956560) (@lem6956564)). Qed.
Lemma lem6956567 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956568 : term156 = term161.
Proof. exact (@lem6956567 term83 term83). Qed.
Lemma lem6956569 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956570 : term131 = term83.
Proof. exact (EQ_MP (@lem6956569) (@lem940073)). Qed.
Lemma lem6956571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956572 : term129 = term82.
Proof. exact (MK_COMB (@lem6956571) (@lem6956570)). Qed.
Lemma lem6956573 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956574 : term161 = term119.
Proof. exact (MK_COMB (@lem6956573) (@lem6956572)). Qed.
Lemma lem6956575 : term156 = term119.
Proof. exact (TRANS (@lem6956568) (@lem6956574)). Qed.
Lemma lem6956576 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956577 : term259 = term251.
Proof. exact (MK_COMB (@lem6956576) (@lem6956575)). Qed.
Lemma lem6956578 : term260 = term253.
Proof. exact (MK_COMB (@lem6956577) (@lem6956565)). Qed.
Lemma lem6956580 (m : nat) : (term261 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6956581 : term253 = term58.
Proof. exact (@lem6956580 term83). Qed.
Lemma lem6956582 : term260 = term58.
Proof. exact (TRANS (@lem6956578) (@lem6956581)). Qed.
Lemma lem6956583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6956584 : term262 = term263.
Proof. exact (MK_COMB (@lem6956583) (@lem6956582)). Qed.
Lemma lem6956585 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem6956586 : term264 = term231.
Proof. exact (MK_COMB (@lem6956584) (@lem6956585)). Qed.
Lemma lem6956588 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956589 : term231 = term58.
Proof. exact (@lem6956588 term83). Qed.
Lemma lem6956590 : term264 = term58.
Proof. exact (TRANS (@lem6956586) (@lem6956589)). Qed.
Lemma lem6956592 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956593 : term128 = term129.
Proof. exact (@lem6956592 term83 term83). Qed.
Lemma lem6956594 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956595 : term131 = term83.
Proof. exact (EQ_MP (@lem6956594) (@lem940073)). Qed.
Lemma lem6956596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956597 : term129 = term82.
Proof. exact (MK_COMB (@lem6956596) (@lem6956595)). Qed.
Lemma lem6956598 : term128 = term82.
Proof. exact (TRANS (@lem6956593) (@lem6956597)). Qed.
Lemma lem6956599 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem6956600 : term265 = term231.
Proof. exact (MK_COMB (@lem6956599) (@lem6956598)). Qed.
Lemma lem6956602 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956603 : term231 = term58.
Proof. exact (@lem6956602 term83). Qed.
Lemma lem6956604 : term265 = term58.
Proof. exact (TRANS (@lem6956600) (@lem6956603)). Qed.
Lemma lem6956605 : term58 = term265.
Proof. exact (SYM (@lem6956604)). Qed.
Lemma lem6956606 : term264 = term265.
Proof. exact (TRANS (@lem6956590) (@lem6956605)). Qed.
Lemma lem6956607 : term254 = term116.
Proof. exact (@lem6956557 (@lem6956606)). Qed.
Lemma lem6956608 : term253 = term116.
Proof. exact (TRANS (@lem6956523) (@lem6956607)). Qed.
Lemma lem6956610 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6956611 : term116 = term58.
Proof. exact (@lem6956610 term58). Qed.
Lemma lem6956612 : term253 = term58.
Proof. exact (TRANS (@lem6956608) (@lem6956611)). Qed.
Lemma lem6956613 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6956614 : term266 = term263.
Proof. exact (MK_COMB (@lem6956613) (@lem6956612)). Qed.
Lemma lem6956615 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6956616 (_92655 : int) : (term250 _92655) = (term267 _92655).
Proof. exact (MK_COMB (@lem6956614) (@lem6956615 _92655)). Qed.
Lemma lem6956617 (_92655 : int) : (term249 _92655) = (term267 _92655).
Proof. exact (TRANS (@lem6956514 _92655) (@lem6956616 _92655)). Qed.
Lemma lem6956618 (_92655 : int) : (term267 _92655) = term58.
Proof. exact (@lem1982719 (real_of_int _92655)). Qed.
Lemma lem6956619 (_92655 : int) : (term249 _92655) = term58.
Proof. exact (TRANS (@lem6956617 _92655) (@lem6956618 _92655)). Qed.
Lemma lem6956620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956621 (_92655 : int) : (term268 _92655) = term80.
Proof. exact (MK_COMB (@lem6956620) (@lem6956619 _92655)). Qed.
Lemma lem6956622 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem6956623 (_92655 : int) : (term248 _92655) = term269.
Proof. exact (MK_COMB (@lem6956621 _92655) (@lem6956622)). Qed.
Lemma lem6956624 (_92655 : int) : (term247 _92655) = term269.
Proof. exact (TRANS (@lem6956513 _92655) (@lem6956623 _92655)). Qed.
Lemma lem6956625 : term269 = term119.
Proof. exact (@lem1982721 term119). Qed.
Lemma lem6956626 (_92655 : int) : (term247 _92655) = term119.
Proof. exact (TRANS (@lem6956624 _92655) (@lem6956625)). Qed.
Lemma lem6956627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956628 (_92655 : int) : (term270 _92655) = term271.
Proof. exact (MK_COMB (@lem6956627) (@lem6956626 _92655)). Qed.
Lemma lem6956629 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956630 (_92655 : int) : (term246 _92655) = term272.
Proof. exact (MK_COMB (@lem6956628 _92655) (@lem6956629)). Qed.
Lemma lem6956631 (_92655 : int) (h1 : term218 _92655) : term272.
Proof. exact (EQ_MP (@lem6956630 _92655) (@lem6956512 _92655 h1)). Qed.
Lemma lem6956633 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6956634 : term272 = term273.
Proof. exact (@lem6956633 term58 term119). Qed.
Lemma lem6956636 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956637 : term119 = term120.
Proof. exact (@lem6956636 term83). Qed.
Lemma lem6956639 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956640 : term58 = term116.
Proof. exact (@lem6956639 (NUMERAL 0)). Qed.
Lemma lem6956641 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956642 : term60 = term274.
Proof. exact (MK_COMB (@lem6956641) (@lem6956640)). Qed.
Lemma lem6956643 : term273 = term275.
Proof. exact (MK_COMB (@lem6956642) (@lem6956637)). Qed.
Lemma lem6956644 : term276.
Proof. exact (@lem1980026 term58 term82 term119 term82). Qed.
Lemma lem6956646 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956647 : term220 = term226.
Proof. exact (@lem6956646 (NUMERAL 0) term83). Qed.
Lemma lem6956648 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956649 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956650 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956649 h1) (fun h1 : term226 = True => @lem6956648)). Qed.
Lemma lem6956651 : term226 = True.
Proof. exact (EQ_MP (@lem6956650) (@lem6956648)). Qed.
Lemma lem6956652 : term220 = True.
Proof. exact (TRANS (@lem6956647) (@lem6956651)). Qed.
Lemma lem6956653 : True = term220.
Proof. exact (SYM (@lem6956652)). Qed.
Lemma lem6956654 : term220.
Proof. exact (EQ_MP (@lem6956653) (@lem0)). Qed.
Lemma lem6956655 : term277.
Proof. exact (@lem6956644 (@lem6956654)). Qed.
Lemma lem6956657 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956658 : term220 = term226.
Proof. exact (@lem6956657 (NUMERAL 0) term83). Qed.
Lemma lem6956659 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956660 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956661 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956660 h1) (fun h1 : term226 = True => @lem6956659)). Qed.
Lemma lem6956662 : term226 = True.
Proof. exact (EQ_MP (@lem6956661) (@lem6956659)). Qed.
Lemma lem6956663 : term220 = True.
Proof. exact (TRANS (@lem6956658) (@lem6956662)). Qed.
Lemma lem6956664 : True = term220.
Proof. exact (SYM (@lem6956663)). Qed.
Lemma lem6956665 : term220.
Proof. exact (EQ_MP (@lem6956664) (@lem0)). Qed.
Lemma lem6956666 : term275 = term278.
Proof. exact (@lem6956655 (@lem6956665)). Qed.
Lemma lem6956668 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956669 : term156 = term161.
Proof. exact (@lem6956668 term83 term83). Qed.
Lemma lem6956670 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956671 : term131 = term83.
Proof. exact (EQ_MP (@lem6956670) (@lem940073)). Qed.
Lemma lem6956672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956673 : term129 = term82.
Proof. exact (MK_COMB (@lem6956672) (@lem6956671)). Qed.
Lemma lem6956674 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956675 : term161 = term119.
Proof. exact (MK_COMB (@lem6956674) (@lem6956673)). Qed.
Lemma lem6956676 : term156 = term119.
Proof. exact (TRANS (@lem6956669) (@lem6956675)). Qed.
Lemma lem6956678 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956679 : term231 = term58.
Proof. exact (@lem6956678 term83). Qed.
Lemma lem6956680 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956681 : term279 = term60.
Proof. exact (MK_COMB (@lem6956680) (@lem6956679)). Qed.
Lemma lem6956682 : term278 = term273.
Proof. exact (MK_COMB (@lem6956681) (@lem6956676)). Qed.
Lemma lem6956684 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6956685 : term273 = term282.
Proof. exact (@lem6956684 (NUMERAL 0) term83). Qed.
Lemma lem6956686 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956687 (h1 : term227 = (BIT1 0)) : (term83 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6956688 : (term227 = (BIT1 0)) = ((term83 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956687 h1) (fun h1 : (term83 = (NUMERAL 0)) = False => @lem6956686)). Qed.
Lemma lem6956689 : (term83 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6956688) (@lem6956686)). Qed.
Lemma lem6956690 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6956691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6956692 : term283 = (and True).
Proof. exact (MK_COMB (@lem6956691) (@lem6956690)). Qed.
Lemma lem6956693 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem6956692) (@lem6956689)). Qed.
Lemma lem6956695 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6956696 : term282 = False.
Proof. exact (TRANS (@lem6956693) (@lem6956695)). Qed.
Lemma lem6956697 : term273 = False.
Proof. exact (TRANS (@lem6956685) (@lem6956696)). Qed.
Lemma lem6956698 : term278 = False.
Proof. exact (TRANS (@lem6956682) (@lem6956697)). Qed.
Lemma lem6956699 : term275 = False.
Proof. exact (TRANS (@lem6956666) (@lem6956698)). Qed.
Lemma lem6956700 : term273 = False.
Proof. exact (TRANS (@lem6956643) (@lem6956699)). Qed.
Lemma lem6956701 : term272 = False.
Proof. exact (TRANS (@lem6956634) (@lem6956700)). Qed.
Lemma lem6956702 (_92655 : int) (h1 : term218 _92655) : False.
Proof. exact (EQ_MP (@lem6956701) (@lem6956631 _92655 h1)). Qed.
Lemma lem6956703 (_92655 : int) (h1 : term284 _92655) : term284 _92655.
Proof. exact (h1). Qed.
Lemma lem6956704 (_92655 : int) (h1 : term284 _92655) : term207 _92655.
Proof. exact (proj2 (@lem6956703 _92655 h1)). Qed.
Lemma lem6956706 (_92655 : int) (h1 : term284 _92655) : term167 _92655.
Proof. exact (proj2 (@lem6956704 _92655 h1)). Qed.
Lemma lem6956707 (_92655 : int) (h1 : term284 _92655) : (real_of_int _92655) = term58.
Proof. exact (proj1 (@lem6956704 _92655 h1)). Qed.
Lemma lem6956709 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6956710 : term219 = term220.
Proof. exact (@lem6956709 term58 term82). Qed.
Lemma lem6956712 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956713 : term82 = term155.
Proof. exact (@lem6956712 term83). Qed.
Lemma lem6956715 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956716 : term58 = term116.
Proof. exact (@lem6956715 (NUMERAL 0)). Qed.
Lemma lem6956717 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956718 : term221 = term222.
Proof. exact (MK_COMB (@lem6956717) (@lem6956716)). Qed.
Lemma lem6956719 : term220 = term223.
Proof. exact (MK_COMB (@lem6956718) (@lem6956713)). Qed.
Lemma lem6956720 : term224.
Proof. exact (@lem1980255 term58 term82 term82 term82). Qed.
Lemma lem6956722 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956723 : term220 = term226.
Proof. exact (@lem6956722 (NUMERAL 0) term83). Qed.
Lemma lem6956724 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956725 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956726 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956725 h1) (fun h1 : term226 = True => @lem6956724)). Qed.
Lemma lem6956727 : term226 = True.
Proof. exact (EQ_MP (@lem6956726) (@lem6956724)). Qed.
Lemma lem6956728 : term220 = True.
Proof. exact (TRANS (@lem6956723) (@lem6956727)). Qed.
Lemma lem6956729 : True = term220.
Proof. exact (SYM (@lem6956728)). Qed.
Lemma lem6956730 : term220.
Proof. exact (EQ_MP (@lem6956729) (@lem0)). Qed.
Lemma lem6956731 : term228.
Proof. exact (@lem6956720 (@lem6956730)). Qed.
Lemma lem6956733 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956734 : term220 = term226.
Proof. exact (@lem6956733 (NUMERAL 0) term83). Qed.
Lemma lem6956735 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956736 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956737 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956736 h1) (fun h1 : term226 = True => @lem6956735)). Qed.
Lemma lem6956738 : term226 = True.
Proof. exact (EQ_MP (@lem6956737) (@lem6956735)). Qed.
Lemma lem6956739 : term220 = True.
Proof. exact (TRANS (@lem6956734) (@lem6956738)). Qed.
Lemma lem6956740 : True = term220.
Proof. exact (SYM (@lem6956739)). Qed.
Lemma lem6956741 : term220.
Proof. exact (EQ_MP (@lem6956740) (@lem0)). Qed.
Lemma lem6956742 : term223 = term229.
Proof. exact (@lem6956731 (@lem6956741)). Qed.
Lemma lem6956744 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956745 : term128 = term129.
Proof. exact (@lem6956744 term83 term83). Qed.
Lemma lem6956746 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956747 : term131 = term83.
Proof. exact (EQ_MP (@lem6956746) (@lem940073)). Qed.
Lemma lem6956748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956749 : term129 = term82.
Proof. exact (MK_COMB (@lem6956748) (@lem6956747)). Qed.
Lemma lem6956750 : term128 = term82.
Proof. exact (TRANS (@lem6956745) (@lem6956749)). Qed.
Lemma lem6956752 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956753 : term231 = term58.
Proof. exact (@lem6956752 term83). Qed.
Lemma lem6956754 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6956755 : term232 = term221.
Proof. exact (MK_COMB (@lem6956754) (@lem6956753)). Qed.
Lemma lem6956756 : term229 = term220.
Proof. exact (MK_COMB (@lem6956755) (@lem6956750)). Qed.
Lemma lem6956758 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956759 : term220 = term226.
Proof. exact (@lem6956758 (NUMERAL 0) term83). Qed.
Lemma lem6956760 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956761 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956762 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956761 h1) (fun h1 : term226 = True => @lem6956760)). Qed.
Lemma lem6956763 : term226 = True.
Proof. exact (EQ_MP (@lem6956762) (@lem6956760)). Qed.
Lemma lem6956764 : term220 = True.
Proof. exact (TRANS (@lem6956759) (@lem6956763)). Qed.
Lemma lem6956765 : term229 = True.
Proof. exact (TRANS (@lem6956756) (@lem6956764)). Qed.
Lemma lem6956766 : term223 = True.
Proof. exact (TRANS (@lem6956742) (@lem6956765)). Qed.
Lemma lem6956767 : term220 = True.
Proof. exact (TRANS (@lem6956719) (@lem6956766)). Qed.
Lemma lem6956768 : term219 = True.
Proof. exact (TRANS (@lem6956710) (@lem6956767)). Qed.
Lemma lem6956769 : True = term219.
Proof. exact (SYM (@lem6956768)). Qed.
Lemma lem6956770 : term219.
Proof. exact (EQ_MP (@lem6956769) (@lem0)). Qed.
Lemma lem6956771 (_92655 : int) (h1 : term284 _92655) : term233 _92655.
Proof. exact (conj (@lem6956770) (@lem6956706 _92655 h1)). Qed.
Lemma lem6956773 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6956774 (_92655 : int) : term235 _92655.
Proof. exact (@lem6956773 term82 (term164 _92655)). Qed.
Lemma lem6956775 (_92655 : int) (h1 : term284 _92655) : term236 _92655.
Proof. exact (@lem6956774 _92655 (@lem6956771 _92655 h1)). Qed.
Lemma lem6956776 (_92655 : int) : (term237 _92655) = (term164 _92655).
Proof. exact (@lem1982733 (term164 _92655)). Qed.
Lemma lem6956777 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956778 (_92655 : int) : (term238 _92655) = (term166 _92655).
Proof. exact (MK_COMB (@lem6956777) (@lem6956776 _92655)). Qed.
Lemma lem6956779 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956780 (_92655 : int) : (term236 _92655) = (term167 _92655).
Proof. exact (MK_COMB (@lem6956778 _92655) (@lem6956779)). Qed.
Lemma lem6956781 (_92655 : int) (h1 : term284 _92655) : term167 _92655.
Proof. exact (EQ_MP (@lem6956780 _92655) (@lem6956775 _92655 h1)). Qed.
Lemma lem6956783 (y : real) : term285 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6956784 (_92655 : int) : term286 _92655.
Proof. exact (@lem6956783 (real_of_int _92655)). Qed.
Lemma lem6956785 (_92655 : int) (h1 : term284 _92655) : term287 _92655.
Proof. exact (@lem6956784 _92655 (@lem6956707 _92655 h1)). Qed.
Lemma lem6956786 (_92655 : int) (h1 : term284 _92655) : term288 _92655.
Proof. exact (@lem6956785 _92655 h1 term119). Qed.
Lemma lem6956787 (_92655 : int) : (term288 _92655) = ((term143 _92655) = term58).
Proof. exact (eq_refl (term288 _92655)). Qed.
Lemma lem6956794 (_92655 : int) (h1 : term284 _92655) : (term143 _92655) = term58.
Proof. exact (EQ_MP (@lem6956787 _92655) (@lem6956786 _92655 h1)). Qed.
Lemma lem6956795 (_92655 : int) (h1 : term284 _92655) : term289 _92655.
Proof. exact (conj (@lem6956794 _92655 h1) (@lem6956781 _92655 h1)). Qed.
Lemma lem6956797 (x : real) (y : real) : term290 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6956798 (_92655 : int) : term291 _92655.
Proof. exact (@lem6956797 (term143 _92655) (term164 _92655)). Qed.
Lemma lem6956799 (_92655 : int) (h1 : term284 _92655) : term246 _92655.
Proof. exact (@lem6956798 _92655 (@lem6956795 _92655 h1)). Qed.
Lemma lem6956800 (_92655 : int) : (term247 _92655) = (term248 _92655).
Proof. exact (@lem1982763 (term143 _92655) (real_of_int _92655) term119). Qed.
Lemma lem6956801 (_92655 : int) : (term249 _92655) = (term250 _92655).
Proof. exact (@lem1982713 term119 (real_of_int _92655)). Qed.
Lemma lem6956803 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956804 : term82 = term155.
Proof. exact (@lem6956803 term83). Qed.
Lemma lem6956806 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956807 : term119 = term120.
Proof. exact (@lem6956806 term83). Qed.
Lemma lem6956808 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956809 : term251 = term252.
Proof. exact (MK_COMB (@lem6956808) (@lem6956807)). Qed.
Lemma lem6956810 : term253 = term254.
Proof. exact (MK_COMB (@lem6956809) (@lem6956804)). Qed.
Lemma lem6956811 : term255.
Proof. exact (@lem1981473 term119 term82 term82 term82 term58 term82). Qed.
Lemma lem6956813 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956814 : term220 = term226.
Proof. exact (@lem6956813 (NUMERAL 0) term83). Qed.
Lemma lem6956815 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956816 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956817 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956816 h1) (fun h1 : term226 = True => @lem6956815)). Qed.
Lemma lem6956818 : term226 = True.
Proof. exact (EQ_MP (@lem6956817) (@lem6956815)). Qed.
Lemma lem6956819 : term220 = True.
Proof. exact (TRANS (@lem6956814) (@lem6956818)). Qed.
Lemma lem6956820 : True = term220.
Proof. exact (SYM (@lem6956819)). Qed.
Lemma lem6956821 : term220.
Proof. exact (EQ_MP (@lem6956820) (@lem0)). Qed.
Lemma lem6956822 : term256.
Proof. exact (@lem6956811 (@lem6956821)). Qed.
Lemma lem6956824 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956825 : term220 = term226.
Proof. exact (@lem6956824 (NUMERAL 0) term83). Qed.
Lemma lem6956826 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956827 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956828 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956827 h1) (fun h1 : term226 = True => @lem6956826)). Qed.
Lemma lem6956829 : term226 = True.
Proof. exact (EQ_MP (@lem6956828) (@lem6956826)). Qed.
Lemma lem6956830 : term220 = True.
Proof. exact (TRANS (@lem6956825) (@lem6956829)). Qed.
Lemma lem6956831 : True = term220.
Proof. exact (SYM (@lem6956830)). Qed.
Lemma lem6956832 : term220.
Proof. exact (EQ_MP (@lem6956831) (@lem0)). Qed.
Lemma lem6956833 : term257.
Proof. exact (@lem6956822 (@lem6956832)). Qed.
Lemma lem6956835 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956836 : term220 = term226.
Proof. exact (@lem6956835 (NUMERAL 0) term83). Qed.
Lemma lem6956837 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956838 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956839 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956838 h1) (fun h1 : term226 = True => @lem6956837)). Qed.
Lemma lem6956840 : term226 = True.
Proof. exact (EQ_MP (@lem6956839) (@lem6956837)). Qed.
Lemma lem6956841 : term220 = True.
Proof. exact (TRANS (@lem6956836) (@lem6956840)). Qed.
Lemma lem6956842 : True = term220.
Proof. exact (SYM (@lem6956841)). Qed.
Lemma lem6956843 : term220.
Proof. exact (EQ_MP (@lem6956842) (@lem0)). Qed.
Lemma lem6956844 : term258.
Proof. exact (@lem6956833 (@lem6956843)). Qed.
Lemma lem6956846 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956847 : term128 = term129.
Proof. exact (@lem6956846 term83 term83). Qed.
Lemma lem6956848 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956849 : term131 = term83.
Proof. exact (EQ_MP (@lem6956848) (@lem940073)). Qed.
Lemma lem6956850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956851 : term129 = term82.
Proof. exact (MK_COMB (@lem6956850) (@lem6956849)). Qed.
Lemma lem6956852 : term128 = term82.
Proof. exact (TRANS (@lem6956847) (@lem6956851)). Qed.
Lemma lem6956854 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956855 : term156 = term161.
Proof. exact (@lem6956854 term83 term83). Qed.
Lemma lem6956856 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956857 : term131 = term83.
Proof. exact (EQ_MP (@lem6956856) (@lem940073)). Qed.
Lemma lem6956858 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956859 : term129 = term82.
Proof. exact (MK_COMB (@lem6956858) (@lem6956857)). Qed.
Lemma lem6956860 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956861 : term161 = term119.
Proof. exact (MK_COMB (@lem6956860) (@lem6956859)). Qed.
Lemma lem6956862 : term156 = term119.
Proof. exact (TRANS (@lem6956855) (@lem6956861)). Qed.
Lemma lem6956863 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956864 : term259 = term251.
Proof. exact (MK_COMB (@lem6956863) (@lem6956862)). Qed.
Lemma lem6956865 : term260 = term253.
Proof. exact (MK_COMB (@lem6956864) (@lem6956852)). Qed.
Lemma lem6956867 (m : nat) : (term261 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6956868 : term253 = term58.
Proof. exact (@lem6956867 term83). Qed.
Lemma lem6956869 : term260 = term58.
Proof. exact (TRANS (@lem6956865) (@lem6956868)). Qed.
Lemma lem6956870 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6956871 : term262 = term263.
Proof. exact (MK_COMB (@lem6956870) (@lem6956869)). Qed.
Lemma lem6956872 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem6956873 : term264 = term231.
Proof. exact (MK_COMB (@lem6956871) (@lem6956872)). Qed.
Lemma lem6956875 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956876 : term231 = term58.
Proof. exact (@lem6956875 term83). Qed.
Lemma lem6956877 : term264 = term58.
Proof. exact (TRANS (@lem6956873) (@lem6956876)). Qed.
Lemma lem6956879 (m : nat) (n : nat) : (term126 m n) = (term127 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6956880 : term128 = term129.
Proof. exact (@lem6956879 term83 term83). Qed.
Lemma lem6956881 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956882 : term131 = term83.
Proof. exact (EQ_MP (@lem6956881) (@lem940073)). Qed.
Lemma lem6956883 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956884 : term129 = term82.
Proof. exact (MK_COMB (@lem6956883) (@lem6956882)). Qed.
Lemma lem6956885 : term128 = term82.
Proof. exact (TRANS (@lem6956880) (@lem6956884)). Qed.
Lemma lem6956886 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem6956887 : term265 = term231.
Proof. exact (MK_COMB (@lem6956886) (@lem6956885)). Qed.
Lemma lem6956889 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956890 : term231 = term58.
Proof. exact (@lem6956889 term83). Qed.
Lemma lem6956891 : term265 = term58.
Proof. exact (TRANS (@lem6956887) (@lem6956890)). Qed.
Lemma lem6956892 : term58 = term265.
Proof. exact (SYM (@lem6956891)). Qed.
Lemma lem6956893 : term264 = term265.
Proof. exact (TRANS (@lem6956877) (@lem6956892)). Qed.
Lemma lem6956894 : term254 = term116.
Proof. exact (@lem6956844 (@lem6956893)). Qed.
Lemma lem6956895 : term253 = term116.
Proof. exact (TRANS (@lem6956810) (@lem6956894)). Qed.
Lemma lem6956897 (x : real) : (term135 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6956898 : term116 = term58.
Proof. exact (@lem6956897 term58). Qed.
Lemma lem6956899 : term253 = term58.
Proof. exact (TRANS (@lem6956895) (@lem6956898)). Qed.
Lemma lem6956900 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6956901 : term266 = term263.
Proof. exact (MK_COMB (@lem6956900) (@lem6956899)). Qed.
Lemma lem6956902 (_92655 : int) : (real_of_int _92655) = (real_of_int _92655).
Proof. exact (eq_refl (real_of_int _92655)). Qed.
Lemma lem6956903 (_92655 : int) : (term250 _92655) = (term267 _92655).
Proof. exact (MK_COMB (@lem6956901) (@lem6956902 _92655)). Qed.
Lemma lem6956904 (_92655 : int) : (term249 _92655) = (term267 _92655).
Proof. exact (TRANS (@lem6956801 _92655) (@lem6956903 _92655)). Qed.
Lemma lem6956905 (_92655 : int) : (term267 _92655) = term58.
Proof. exact (@lem1982719 (real_of_int _92655)). Qed.
Lemma lem6956906 (_92655 : int) : (term249 _92655) = term58.
Proof. exact (TRANS (@lem6956904 _92655) (@lem6956905 _92655)). Qed.
Lemma lem6956907 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6956908 (_92655 : int) : (term268 _92655) = term80.
Proof. exact (MK_COMB (@lem6956907) (@lem6956906 _92655)). Qed.
Lemma lem6956909 : term119 = term119.
Proof. exact (eq_refl term119). Qed.
Lemma lem6956910 (_92655 : int) : (term248 _92655) = term269.
Proof. exact (MK_COMB (@lem6956908 _92655) (@lem6956909)). Qed.
Lemma lem6956911 (_92655 : int) : (term247 _92655) = term269.
Proof. exact (TRANS (@lem6956800 _92655) (@lem6956910 _92655)). Qed.
Lemma lem6956912 : term269 = term119.
Proof. exact (@lem1982721 term119). Qed.
Lemma lem6956913 (_92655 : int) : (term247 _92655) = term119.
Proof. exact (TRANS (@lem6956911 _92655) (@lem6956912)). Qed.
Lemma lem6956914 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6956915 (_92655 : int) : (term270 _92655) = term271.
Proof. exact (MK_COMB (@lem6956914) (@lem6956913 _92655)). Qed.
Lemma lem6956916 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem6956917 (_92655 : int) : (term246 _92655) = term272.
Proof. exact (MK_COMB (@lem6956915 _92655) (@lem6956916)). Qed.
Lemma lem6956918 (_92655 : int) (h1 : term284 _92655) : term272.
Proof. exact (EQ_MP (@lem6956917 _92655) (@lem6956799 _92655 h1)). Qed.
Lemma lem6956920 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6956921 : term272 = term273.
Proof. exact (@lem6956920 term58 term119). Qed.
Lemma lem6956923 (x : nat) : (term117 x) = (term118 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6956924 : term119 = term120.
Proof. exact (@lem6956923 term83). Qed.
Lemma lem6956926 (x : nat) : (real_of_num x) = (term115 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6956927 : term58 = term116.
Proof. exact (@lem6956926 (NUMERAL 0)). Qed.
Lemma lem6956928 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956929 : term60 = term274.
Proof. exact (MK_COMB (@lem6956928) (@lem6956927)). Qed.
Lemma lem6956930 : term273 = term275.
Proof. exact (MK_COMB (@lem6956929) (@lem6956924)). Qed.
Lemma lem6956931 : term276.
Proof. exact (@lem1980026 term58 term82 term119 term82). Qed.
Lemma lem6956933 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956934 : term220 = term226.
Proof. exact (@lem6956933 (NUMERAL 0) term83). Qed.
Lemma lem6956935 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956936 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956937 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956936 h1) (fun h1 : term226 = True => @lem6956935)). Qed.
Lemma lem6956938 : term226 = True.
Proof. exact (EQ_MP (@lem6956937) (@lem6956935)). Qed.
Lemma lem6956939 : term220 = True.
Proof. exact (TRANS (@lem6956934) (@lem6956938)). Qed.
Lemma lem6956940 : True = term220.
Proof. exact (SYM (@lem6956939)). Qed.
Lemma lem6956941 : term220.
Proof. exact (EQ_MP (@lem6956940) (@lem0)). Qed.
Lemma lem6956942 : term277.
Proof. exact (@lem6956931 (@lem6956941)). Qed.
Lemma lem6956944 (m : nat) (n : nat) : (term225 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6956945 : term220 = term226.
Proof. exact (@lem6956944 (NUMERAL 0) term83). Qed.
Lemma lem6956946 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956947 (h1 : term227 = (BIT1 0)) : term226 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6956948 : (term227 = (BIT1 0)) = (term226 = True).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956947 h1) (fun h1 : term226 = True => @lem6956946)). Qed.
Lemma lem6956949 : term226 = True.
Proof. exact (EQ_MP (@lem6956948) (@lem6956946)). Qed.
Lemma lem6956950 : term220 = True.
Proof. exact (TRANS (@lem6956945) (@lem6956949)). Qed.
Lemma lem6956951 : True = term220.
Proof. exact (SYM (@lem6956950)). Qed.
Lemma lem6956952 : term220.
Proof. exact (EQ_MP (@lem6956951) (@lem0)). Qed.
Lemma lem6956953 : term275 = term278.
Proof. exact (@lem6956942 (@lem6956952)). Qed.
Lemma lem6956955 (m : nat) (n : nat) : (term159 m n) = (term160 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6956956 : term156 = term161.
Proof. exact (@lem6956955 term83 term83). Qed.
Lemma lem6956957 : (term130 = (BIT1 0)) = (term131 = term83).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6956958 : term131 = term83.
Proof. exact (EQ_MP (@lem6956957) (@lem940073)). Qed.
Lemma lem6956959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6956960 : term129 = term82.
Proof. exact (MK_COMB (@lem6956959) (@lem6956958)). Qed.
Lemma lem6956961 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6956962 : term161 = term119.
Proof. exact (MK_COMB (@lem6956961) (@lem6956960)). Qed.
Lemma lem6956963 : term156 = term119.
Proof. exact (TRANS (@lem6956956) (@lem6956962)). Qed.
Lemma lem6956965 (x : nat) : (term230 x) = term58.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6956966 : term231 = term58.
Proof. exact (@lem6956965 term83). Qed.
Lemma lem6956967 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6956968 : term279 = term60.
Proof. exact (MK_COMB (@lem6956967) (@lem6956966)). Qed.
Lemma lem6956969 : term278 = term273.
Proof. exact (MK_COMB (@lem6956968) (@lem6956963)). Qed.
Lemma lem6956971 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6956972 : term273 = term282.
Proof. exact (@lem6956971 (NUMERAL 0) term83). Qed.
Lemma lem6956973 : term227 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6956974 (h1 : term227 = (BIT1 0)) : (term83 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6956975 : (term227 = (BIT1 0)) = ((term83 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term227 = (BIT1 0) => @lem6956974 h1) (fun h1 : (term83 = (NUMERAL 0)) = False => @lem6956973)). Qed.
Lemma lem6956976 : (term83 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6956975) (@lem6956973)). Qed.
Lemma lem6956977 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6956978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6956979 : term283 = (and True).
Proof. exact (MK_COMB (@lem6956978) (@lem6956977)). Qed.
Lemma lem6956980 : term282 = (True /\ False).
Proof. exact (MK_COMB (@lem6956979) (@lem6956976)). Qed.
Lemma lem6956982 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6956983 : term282 = False.
Proof. exact (TRANS (@lem6956980) (@lem6956982)). Qed.
Lemma lem6956984 : term273 = False.
Proof. exact (TRANS (@lem6956972) (@lem6956983)). Qed.
Lemma lem6956985 : term278 = False.
Proof. exact (TRANS (@lem6956969) (@lem6956984)). Qed.
Lemma lem6956986 : term275 = False.
Proof. exact (TRANS (@lem6956953) (@lem6956985)). Qed.
Lemma lem6956987 : term273 = False.
Proof. exact (TRANS (@lem6956930) (@lem6956986)). Qed.
Lemma lem6956988 : term272 = False.
Proof. exact (TRANS (@lem6956921) (@lem6956987)). Qed.
Lemma lem6956989 (_92655 : int) (h1 : term284 _92655) : False.
Proof. exact (EQ_MP (@lem6956988) (@lem6956918 _92655 h1)). Qed.
Lemma lem6956990 (_92655 : int) (h1 : term205 _92655) : False.
Proof. exact (or_elim (@lem6956354 _92655 h1) (fun h0 : term218 _92655 => @lem6956702 _92655 h0) (fun h0 : term284 _92655 => @lem6956989 _92655 h0)). Qed.
Lemma lem6956991 (_92655 : int) (h1 : term214 _92655) : False.
Proof. exact (or_elim (@lem6955716 _92655 h1) (fun h0 : term209 _92655 => @lem6956353 _92655 h0) (fun h0 : term205 _92655 => @lem6956990 _92655 h0)). Qed.
Lemma lem6956992 (_92655 : int) (h1 : term217 _92655) : False.
Proof. exact (or_elim (@lem6955078 _92655 h1) (fun h0 : term205 _92655 => @lem6955715 _92655 h0) (fun h0 : term214 _92655 => @lem6956991 _92655 h0)). Qed.
Lemma lem6956994 (_92655 : int) (h1 : term217 _92655) : term217 _92655.
Proof. exact (h1). Qed.
Lemma lem6956995 (_92655 : int) (h1 : term217 _92655) : (term217 _92655) = False.
Proof. exact (prop_ext (fun h2 : term217 _92655 => @lem6956992 _92655 h1) (fun h2 : False => @lem6956994 _92655 h1)). Qed.
Lemma lem6956996 (_92655 : int) (h1 : term217 _92655) : False.
Proof. exact (EQ_MP (@lem6956995 _92655 h1) (@lem6956994 _92655 h1)). Qed.
Lemma lem6956997 (_92655 : int) (h1 : term111 _92655) : term111 _92655.
Proof. exact (h1). Qed.
Lemma lem6956998 (_92655 : int) (h1 : term111 _92655) : term217 _92655.
Proof. exact (EQ_MP (@lem6955044 _92655) (@lem6956997 _92655 h1)). Qed.
Lemma lem6956999 (_92655 : int) (h1 : term111 _92655) : (term217 _92655) = False.
Proof. exact (prop_ext (fun h2 : term217 _92655 => @lem6956996 _92655 h2) (fun h2 : False => @lem6956998 _92655 h1)). Qed.
Lemma lem6957000 (_92655 : int) (h1 : term111 _92655) : False.
Proof. exact (EQ_MP (@lem6956999 _92655 h1) (@lem6956998 _92655 h1)). Qed.
Lemma lem6957001 (_92655 : int) : term318 _92655.
Proof. exact (fun h0 : term111 _92655 => @lem6957000 _92655 h0). Qed.
Lemma lem6957002 (_92655 : int) : term319 _92655.
Proof. exact (@lem1386578 (term320 _92655)). Qed.
Lemma lem6957005 (_92655 : int) : term320 _92655.
Proof. exact (@lem6957002 _92655 (@lem6957001 _92655)). Qed.
Lemma lem6957006 (_92655 : int) : (term109 _92655) = (term51 _92655).
Proof. exact (SYM (@lem6954572 _92655)). Qed.
Lemma lem6957007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6957008 (_92655 : int) : (term320 _92655) = (term25 _92655).
Proof. exact (MK_COMB (@lem6957007) (@lem6957006 _92655)). Qed.
Lemma lem6957009 (_92655 : int) : term25 _92655.
Proof. exact (EQ_MP (@lem6957008 _92655) (@lem6957005 _92655)). Qed.
Lemma lem6957010 (_92655 : int) : term26 _92655.
Proof. exact (EQ_MP (@lem6954383 _92655) (@lem6957009 _92655)). Qed.
Lemma lem6957011 (n : nat) : term321 n.
Proof. exact (@lem6957010 (int_of_num n)). Qed.
Lemma lem6957012 (n : nat) : term22 n.
Proof. exact (@lem6957011 n (@lem6954382 n)). Qed.
Lemma lem6957013 (n : nat) : (term22 n) = ((term7 n) = (term8 n)).
Proof. exact (SYM (@lem6954379 n)). Qed.
Lemma lem6957015 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) : term322 _127305 f s.
Proof. exact (@lem6954254 _127305 f s). Qed.
Lemma lem6957016 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : (term322 _127305 f s) = (term323 _127305 s f).
Proof. exact (eq_refl (term322 _127305 f s)). Qed.
Lemma lem6957017 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term323 _127305 s f.
Proof. exact (EQ_MP (@lem6957016 _127305 s f) (@lem6957015 _127305 f s)). Qed.
Lemma lem6957018 {_127305 : Type'} (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : @FINITE _127305 s.
Proof. exact (h1). Qed.
Lemma lem6957019 {_127305 : Type'} (f : _127305 -> nat) (s : _127305 -> Prop) (h1 : @FINITE _127305 s) : ((@nsum _127305 s f) = (NUMERAL 0)) = (term324 _127305 s f).
Proof. exact (@lem6957017 _127305 s f (@lem6957018 _127305 s h1)). Qed.
Lemma lem6957036 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term325 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6957037 (p : Prop) (q : Prop) (p' : Prop) : term326 p q p'.
Proof. exact (fun q' : Prop => @lem6957036 p q p' q'). Qed.
Lemma lem6957038 (p : Prop) (q : Prop) : term327 p q.
Proof. exact (fun p' : Prop => @lem6957037 p q p'). Qed.
Lemma lem6957039 {A : Type'} (s : A -> Prop) (f : A -> nat) : term328 A s f.
Proof. exact (@lem6957038 (term329 A s f) (term330 A s f)). Qed.
Lemma lem6957040 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) : term331 A s f p'.
Proof. exact (@lem6957039 A s f p'). Qed.
Lemma lem6957041 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) : (term331 A s f p') = (term332 A s f p').
Proof. exact (eq_refl (term331 A s f p')). Qed.
Lemma lem6957042 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) : term332 A s f p'.
Proof. exact (EQ_MP (@lem6957041 A s f p') (@lem6957040 A s f p')). Qed.
Lemma lem6957043 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term333 A s f p' q'.
Proof. exact (@lem6957042 A s f p' q'). Qed.
Lemma lem6957044 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : (term333 A s f p' q') = (term334 A s f p' q').
Proof. exact (eq_refl (term333 A s f p' q')). Qed.
Lemma lem6957045 {A : Type'} (s : A -> Prop) (f : A -> nat) (p' : Prop) (q' : Prop) : term334 A s f p' q'.
Proof. exact (EQ_MP (@lem6957044 A s f p' q') (@lem6957043 A s f p' q')). Qed.
Lemma lem6957055 (n : nat) : (term7 n) = (term8 n).
Proof. exact (EQ_MP (@lem6957013 n) (@lem6957012 n)). Qed.
Lemma lem6957056 {A : Type'} (f : A -> nat) (x : A) : (term335 A f x) = (term336 A f x).
Proof. exact (@lem6957055 (f x)). Qed.
Lemma lem6957059 {A : Type'} (x : A) (s : A -> Prop) : (term337 A x s) = (term337 A x s).
Proof. exact (eq_refl (term337 A x s)). Qed.
Lemma lem6957060 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term338 A s f x) = (term339 A s f x).
Proof. exact (MK_COMB (@lem6957059 A x s) (@lem6957056 A f x)). Qed.
Lemma lem6957065 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term340 A s f) = (term341 A s f).
Proof. exact (fun_ext (fun x : A => @lem6957060 A s f x)). Qed.
Lemma lem6957070 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6957071 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term342 A s f) = (term343 A s f).
Proof. exact (MK_COMB (@lem6957070 A) (@lem6957065 A s f)). Qed.
Lemma lem6957080 {A : Type'} (s : A -> Prop) : (term344 A s) = (term344 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem6957081 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term329 A s f) = (term345 A s f).
Proof. exact (MK_COMB (@lem6957080 A s) (@lem6957071 A s f)). Qed.
Lemma lem6957092 {A : Type'} (s : A -> Prop) (f : A -> nat) (q' : Prop) : term346 A s f q'.
Proof. exact (@lem6957045 A s f (term345 A s f) q'). Qed.
Lemma lem6957093 {A : Type'} (s : A -> Prop) (f : A -> nat) (q' : Prop) : term347 A s f q'.
Proof. exact (@lem6957092 A s f q' (@lem6957081 A s f)). Qed.
Lemma lem6957094 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : term345 A s f.
Proof. exact (h1). Qed.
Lemma lem6957098 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem6957094 A s f h1)). Qed.
Lemma lem6957099 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6957102 (n : nat) : (term7 n) = (term8 n).
Proof. exact (EQ_MP (@lem6957013 n) (@lem6957012 n)). Qed.
Lemma lem6957103 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term330 A s f) = (term348 A s f).
Proof. exact (@lem6957102 (@nsum A s f)). Qed.
Lemma lem6957105 {_127305 : Type'} (s : _127305 -> Prop) (f : _127305 -> nat) : term323 _127305 s f.
Proof. exact (fun h0 : @FINITE _127305 s => @lem6957019 _127305 f s h0). Qed.
Lemma lem6957106 {A : Type'} (s : A -> Prop) (f : A -> nat) : term323 A s f.
Proof. exact (@lem6957105 A s f). Qed.
Lemma lem6957108 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6957099 A s) (@lem6957098 A s f h1)). Qed.
Lemma lem6957109 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : True = (@FINITE A s).
Proof. exact (SYM (@lem6957108 A s f h1)). Qed.
Lemma lem6957110 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : @FINITE A s.
Proof. exact (EQ_MP (@lem6957109 A s f h1) (@lem0)). Qed.
Lemma lem6957111 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : ((@nsum A s f) = (NUMERAL 0)) = (term324 A s f).
Proof. exact (@lem6957106 A s f (@lem6957110 A s f h1)). Qed.
Lemma lem6957143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6957144 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : (term348 A s f) = (term349 A s f).
Proof. exact (MK_COMB (@lem6957143) (@lem6957111 A s f h1)). Qed.
Lemma lem6957176 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : (term330 A s f) = (term349 A s f).
Proof. exact (TRANS (@lem6957103 A s f) (@lem6957144 A s f h1)). Qed.
Lemma lem6957177 {A : Type'} (s : A -> Prop) (f : A -> nat) : term350 A s f.
Proof. exact (fun h0 : term345 A s f => @lem6957176 A s f h0). Qed.
Lemma lem6957178 {A : Type'} (s : A -> Prop) (f : A -> nat) : term351 A s f.
Proof. exact (@lem6957093 A s f (term349 A s f)). Qed.
Lemma lem6957179 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term352 A s f) = (term353 A s f).
Proof. exact (@lem6957178 A s f (@lem6957177 A s f)). Qed.
Lemma lem6957289 {A : Type'} (f : A -> nat) : (term354 A f) = (term355 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6957179 A s f)). Qed.
Lemma lem6957399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6957400 {A : Type'} (f : A -> nat) : (term356 A f) = (term357 A f).
Proof. exact (MK_COMB (@lem6957399 A) (@lem6957289 A f)). Qed.
Lemma lem6957514 {A : Type'} : (term358 A) = (term359 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6957400 A f)). Qed.
Lemma lem6957628 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6957629 {A : Type'} : (term360 A) = (term361 A).
Proof. exact (MK_COMB (@lem6957628 A) (@lem6957514 A)). Qed.
Lemma lem6957747 {A : Type'} : (term361 A) = (term360 A).
Proof. exact (SYM (@lem6957629 A)). Qed.
Lemma lem6957749 (p : Prop) : p = (term362 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6957750 {A : Type'} : (term361 A) = (term363 A).
Proof. exact (@lem6957749 (term361 A)). Qed.
Lemma lem6957751 {A : Type'} : (term363 A) = (term361 A).
Proof. exact (SYM (@lem6957750 A)). Qed.
Lemma lem6957752 {A : Type'} (h1 : term364 A) : term364 A.
Proof. exact (h1). Qed.
Lemma lem6957755 {A : Type'} (h1 : term363 A) : term363 A.
Proof. exact (h1). Qed.
Lemma lem6957756 {A : Type'} : term365 A.
Proof. exact (fun h0 : term363 A => @lem6957755 A h0). Qed.
Lemma lem6957757 {A : Type'} (h1 : term365 A) : term365 A.
Proof. exact (h1). Qed.
Lemma lem6957758 {A : Type'} (h1 : term363 A) : term363 A.
Proof. exact (h1). Qed.
Lemma lem6957759 {A : Type'} (h1 : term363 A) (h2 : term365 A) : term363 A.
Proof. exact (@lem6957757 A h2 (@lem6957758 A h1)). Qed.
Lemma lem6957760 {A : Type'} (h1 : term363 A) : term366 A.
Proof. exact (fun h0 : term365 A => @lem6957759 A h1 h0). Qed.
Lemma lem6957761 {A : Type'} (h1 : term365 A) : term365 A.
Proof. exact (h1). Qed.
Lemma lem6957762 {A : Type'} (h1 : term363 A) (h2 : term365 A) : term363 A.
Proof. exact (@lem6957760 A h1 (@lem6957761 A h2)). Qed.
Lemma lem6957763 {A : Type'} (h1 : term365 A) : term365 A.
Proof. exact (fun h0 : term363 A => @lem6957762 A h0 h1). Qed.
Lemma lem6957764 {A : Type'} : term367 A.
Proof. exact (fun h0 : term365 A => @lem6957763 A h0). Qed.
Lemma lem6957767 {A : Type'} : term365 A.
Proof. exact (@lem6957764 A (@lem6957756 A)). Qed.
Lemma lem6957768 {A : Type'} : term365 A.
Proof. exact (@lem6957767 A). Qed.
Lemma lem6957770 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6957771 {A : Type'} : (term363 A) = (term368 A).
Proof. exact (@lem6957770 (term364 A)). Qed.
Lemma lem6957773 (t : Prop) : (term110 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6957774 {A : Type'} : (term368 A) = (term361 A).
Proof. exact (@lem6957773 (term361 A)). Qed.
Lemma lem6957847 {A : Type'} : (term363 A) = (term361 A).
Proof. exact (TRANS (@lem6957771 A) (@lem6957774 A)). Qed.
Lemma lem6957852 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term369 A s f x) = (term369 A s f x).
Proof. exact (eq_refl (term369 A s f x)). Qed.
Lemma lem6957853 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term370 A s f) = (term370 A s f).
Proof. exact (fun_ext (fun x : A => @lem6957852 A s f x)). Qed.
Lemma lem6957854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6957855 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term324 A s f) = (term324 A s f).
Proof. exact (MK_COMB (@lem6957854 A) (@lem6957853 A s f)). Qed.
Lemma lem6957856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6957857 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term349 A s f) = (term349 A s f).
Proof. exact (MK_COMB (@lem6957856) (@lem6957855 A s f)). Qed.
Lemma lem6957864 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term339 A s f x) = (term339 A s f x).
Proof. exact (eq_refl (term339 A s f x)). Qed.
Lemma lem6957865 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term341 A s f) = (term341 A s f).
Proof. exact (fun_ext (fun x : A => @lem6957864 A s f x)). Qed.
Lemma lem6957866 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6957867 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term343 A s f) = (term343 A s f).
Proof. exact (MK_COMB (@lem6957866 A) (@lem6957865 A s f)). Qed.
Lemma lem6957870 {A : Type'} (s : A -> Prop) : (term344 A s) = (term344 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem6957871 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term345 A s f) = (term345 A s f).
Proof. exact (MK_COMB (@lem6957870 A s) (@lem6957867 A s f)). Qed.
Lemma lem6957872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6957873 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term371 A s f) = (term371 A s f).
Proof. exact (MK_COMB (@lem6957872) (@lem6957871 A s f)). Qed.
Lemma lem6957874 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term353 A s f) = (term353 A s f).
Proof. exact (MK_COMB (@lem6957873 A s f) (@lem6957857 A s f)). Qed.
Lemma lem6957875 {A : Type'} (f : A -> nat) : (term355 A f) = (term355 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6957874 A s f)). Qed.
Lemma lem6957876 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6957877 {A : Type'} (f : A -> nat) : (term357 A f) = (term357 A f).
Proof. exact (MK_COMB (@lem6957876 A) (@lem6957875 A f)). Qed.
Lemma lem6957878 {A : Type'} : (term359 A) = (term359 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6957877 A f)). Qed.
Lemma lem6957879 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6957880 {A : Type'} : (term361 A) = (term361 A).
Proof. exact (MK_COMB (@lem6957879 A) (@lem6957878 A)). Qed.
Lemma lem6957915 {A : Type'} : (term363 A) = (term361 A).
Proof. exact (TRANS (@lem6957847 A) (@lem6957880 A)). Qed.
Lemma lem6957916 {A : Type'} : (term361 A) = (term363 A).
Proof. exact (SYM (@lem6957915 A)). Qed.
Lemma lem6957917 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : term345 A s f.
Proof. exact (h1). Qed.
Lemma lem6957918 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term324 A s f.
Proof. exact (h1). Qed.
Lemma lem6957924 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term339 A s f x) = (term339 A s f x).
Proof. exact (eq_refl (term339 A s f x)). Qed.
Lemma lem6957925 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term341 A s f) = (term341 A s f).
Proof. exact (fun_ext (fun x : A => @lem6957924 A s f x)). Qed.
Lemma lem6957926 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6957927 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term343 A s f) = (term343 A s f).
Proof. exact (MK_COMB (@lem6957926 A) (@lem6957925 A s f)). Qed.
Lemma lem6957929 {A : Type'} (s : A -> Prop) : (term344 A s) = (term344 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem6957930 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term345 A s f) = (term345 A s f).
Proof. exact (MK_COMB (@lem6957929 A s) (@lem6957927 A s f)). Qed.
Lemma lem6957981 {A : Type'} (P : Prop) (Q : A -> Prop) : (term372 A P Q) = (term373 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6957982 {A : Type'} (P : Prop) (Q : A -> Prop) : (term372 A P Q) = (term373 A P Q).
Proof. exact (@lem6957981 A P Q). Qed.
Lemma lem6957983 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term374 A s f) = (term375 A s f).
Proof. exact (@lem6957982 A (@FINITE A s) (term341 A s f)). Qed.
Lemma lem6957984 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term376 A s f x) = (term339 A s f x).
Proof. exact (eq_refl (term376 A s f x)). Qed.
Lemma lem6957985 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term377 A s f) = (term341 A s f).
Proof. exact (fun_ext (fun x : A => @lem6957984 A s f x)). Qed.
Lemma lem6957986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6957987 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term378 A s f) = (term343 A s f).
Proof. exact (MK_COMB (@lem6957986 A) (@lem6957985 A s f)). Qed.
Lemma lem6957988 {A : Type'} (s : A -> Prop) : (term344 A s) = (term344 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem6957989 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term374 A s f) = (term345 A s f).
Proof. exact (MK_COMB (@lem6957988 A s) (@lem6957987 A s f)). Qed.
Lemma lem6957990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6957991 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term379 A s f) = (term380 A s f).
Proof. exact (MK_COMB (@lem6957990) (@lem6957989 A s f)). Qed.
Lemma lem6957992 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term376 A s f x) = (term339 A s f x).
Proof. exact (eq_refl (term376 A s f x)). Qed.
Lemma lem6957993 {A : Type'} (s : A -> Prop) : (term344 A s) = (term344 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem6957994 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term381 A s f x) = (term382 A s f x).
Proof. exact (MK_COMB (@lem6957993 A s) (@lem6957992 A s f x)). Qed.
Lemma lem6957995 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term383 A s f) = (term384 A s f).
Proof. exact (fun_ext (fun x : A => @lem6957994 A s f x)). Qed.
Lemma lem6957996 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6957997 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term375 A s f) = (term385 A s f).
Proof. exact (MK_COMB (@lem6957996 A) (@lem6957995 A s f)). Qed.
Lemma lem6957998 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((term374 A s f) = (term375 A s f)) = ((term345 A s f) = (term385 A s f)).
Proof. exact (MK_COMB (@lem6957991 A s f) (@lem6957997 A s f)). Qed.
Lemma lem6958000 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term345 A s f) = (term385 A s f).
Proof. exact (EQ_MP (@lem6957998 A s f) (@lem6957983 A s f)). Qed.
Lemma lem6958001 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term345 A s f) = (term385 A s f).
Proof. exact (TRANS (@lem6957930 A s f) (@lem6958000 A s f)). Qed.
Lemma lem6958002 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : term385 A s f.
Proof. exact (EQ_MP (@lem6958001 A s f) (@lem6957917 A s f h1)). Qed.
Lemma lem6958009 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term369 A s f x) = (term386 A s f x).
Proof. exact (@lem17265 (@IN A x s) ((f x) = (NUMERAL 0))). Qed.
Lemma lem6958010 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term370 A s f) = (term387 A s f).
Proof. exact (fun_ext (fun x : A => @lem6958009 A s f x)). Qed.
Lemma lem6958011 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958064 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term324 A s f) = (term388 A s f).
Proof. exact (MK_COMB (@lem6958011 A) (@lem6958010 A s f)). Qed.
Lemma lem6958065 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term388 A s f.
Proof. exact (EQ_MP (@lem6958064 A s f) (@lem6957918 A s f h1)). Qed.
Lemma lem6958085 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term386 A s f x) = (term386 A s f x).
Proof. exact (eq_refl (term386 A s f x)). Qed.
Lemma lem6958086 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term387 A s f) = (term387 A s f).
Proof. exact (fun_ext (fun x : A => @lem6958085 A s f x)). Qed.
Lemma lem6958087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958088 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term388 A s f) = (term388 A s f).
Proof. exact (MK_COMB (@lem6958087 A) (@lem6958086 A s f)). Qed.
Lemma lem6958089 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term388 A s f.
Proof. exact (EQ_MP (@lem6958088 A s f) (@lem6958065 A s f h1)). Qed.
Lemma lem6958115 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : term382 A s f x.
Proof. exact (h1). Qed.
Lemma lem6958116 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : term339 A s f x.
Proof. exact (proj2 (@lem6958115 A s f x h1)). Qed.
Lemma lem6958127 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) : (term386 A s f x) = (term386 A s f x).
Proof. exact (eq_refl (term386 A s f x)). Qed.
Lemma lem6958128 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term387 A s f) = (term387 A s f).
Proof. exact (fun_ext (fun x : A => @lem6958127 A s f x)). Qed.
Lemma lem6958129 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6958131 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term388 A s f) = (term388 A s f).
Proof. exact (MK_COMB (@lem6958129 A) (@lem6958128 A s f)). Qed.
Lemma lem6958132 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term388 A s f.
Proof. exact (EQ_MP (@lem6958131 A s f) (@lem6958089 A s f h1)). Qed.
Lemma lem6958145 {A : Type'} (_92657 : A) (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term389 A s f _92657.
Proof. exact (@lem6958132 A s f h1 _92657). Qed.
Lemma lem6958146 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92657 : A) : (term389 A s f _92657) = (term386 A s f _92657).
Proof. exact (eq_refl (term389 A s f _92657)). Qed.
Lemma lem6958153 {A : Type'} (_92657 : A) (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term386 A s f _92657.
Proof. exact (EQ_MP (@lem6958146 A s f _92657) (@lem6958145 A _92657 s f h1)). Qed.
Lemma lem6958159 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : term336 A f x.
Proof. exact (proj2 (@lem6958116 A s f x h1)). Qed.
Lemma lem6958214 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : @IN A x s.
Proof. exact (proj1 (@lem6958116 A s f x h1)). Qed.
Lemma lem6958215 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : term390 A x s.
Proof. exact (fun h0 : term391 A x s => @lem6958214 A s f x h1). Qed.
Lemma lem6958217 (p : Prop) : (term392 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6958218 {A : Type'} (x : A) (s : A -> Prop) : (term390 A x s) = (@IN A x s).
Proof. exact (@lem6958217 (@IN A x s)). Qed.
Lemma lem6958219 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : @IN A x s.
Proof. exact (EQ_MP (@lem6958218 A x s) (@lem6958215 A s f x h1)). Qed.
Lemma lem6958225 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6958226 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : (term386 A s f _92657) = (term393 A f _92657 s).
Proof. exact (@lem6958225 ((f _92657) = (NUMERAL 0)) (term391 A _92657 s)). Qed.
Lemma lem6958234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6958235 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : (term394 A s f _92657) = (term395 A f _92657 s).
Proof. exact (MK_COMB (@lem6958234) (@lem6958226 A f _92657 s)). Qed.
Lemma lem6958243 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : (term393 A f _92657 s) = (term393 A f _92657 s).
Proof. exact (eq_refl (term393 A f _92657 s)). Qed.
Lemma lem6958244 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : ((term386 A s f _92657) = (term393 A f _92657 s)) = ((term393 A f _92657 s) = (term393 A f _92657 s)).
Proof. exact (MK_COMB (@lem6958235 A f _92657 s) (@lem6958243 A f _92657 s)). Qed.
Lemma lem6958246 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6958247 (x : Prop) : (x = x) = True.
Proof. exact (@lem6958246 Prop x). Qed.
Lemma lem6958248 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : ((term393 A f _92657 s) = (term393 A f _92657 s)) = True.
Proof. exact (@lem6958247 (term393 A f _92657 s)). Qed.
Lemma lem6958249 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : ((term386 A s f _92657) = (term393 A f _92657 s)) = True.
Proof. exact (TRANS (@lem6958244 A f _92657 s) (@lem6958248 A f _92657 s)). Qed.
Lemma lem6958250 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : True = ((term386 A s f _92657) = (term393 A f _92657 s)).
Proof. exact (SYM (@lem6958249 A f _92657 s)). Qed.
Lemma lem6958251 {A : Type'} (f : A -> nat) (_92657 : A) (s : A -> Prop) : (term386 A s f _92657) = (term393 A f _92657 s).
Proof. exact (EQ_MP (@lem6958250 A f _92657 s) (@lem0)). Qed.
Lemma lem6958252 {A : Type'} (_92657 : A) (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term393 A f _92657 s.
Proof. exact (EQ_MP (@lem6958251 A f _92657 s) (@lem6958153 A _92657 s f h1)). Qed.
Lemma lem6958254 (b : Prop) (a : Prop) : (a \/ b) = (term396 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6958255 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92657 : A) : (term393 A f _92657 s) = (term397 A s f _92657).
Proof. exact (@lem6958254 (term391 A _92657 s) ((f _92657) = (NUMERAL 0))). Qed.
Lemma lem6958257 (a : Prop) : (term110 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6958258 {A : Type'} (_92657 : A) (s : A -> Prop) : (term398 A _92657 s) = (@IN A _92657 s).
Proof. exact (@lem6958257 (@IN A _92657 s)). Qed.
Lemma lem6958259 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6958260 {A : Type'} (_92657 : A) (s : A -> Prop) : (term399 A _92657 s) = (term400 A _92657 s).
Proof. exact (MK_COMB (@lem6958259) (@lem6958258 A _92657 s)). Qed.
Lemma lem6958261 {A : Type'} (f : A -> nat) (_92657 : A) : ((f _92657) = (NUMERAL 0)) = ((f _92657) = (NUMERAL 0)).
Proof. exact (eq_refl ((f _92657) = (NUMERAL 0))). Qed.
Lemma lem6958262 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92657 : A) : (term397 A s f _92657) = (term369 A s f _92657).
Proof. exact (MK_COMB (@lem6958260 A _92657 s) (@lem6958261 A f _92657)). Qed.
Lemma lem6958263 {A : Type'} (s : A -> Prop) (f : A -> nat) (_92657 : A) : (term393 A f _92657 s) = (term369 A s f _92657).
Proof. exact (TRANS (@lem6958255 A s f _92657) (@lem6958262 A s f _92657)). Qed.
Lemma lem6958266 {A : Type'} (_92657 : A) (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term369 A s f _92657.
Proof. exact (EQ_MP (@lem6958263 A s f _92657) (@lem6958252 A _92657 s f h1)). Qed.
Lemma lem6958267 {A : Type'} (_92657 : A) (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term369 A s f _92657.
Proof. exact (@lem6958266 A _92657 s f h1). Qed.
Lemma lem6958268 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) : term369 A s f x.
Proof. exact (@lem6958267 A x s f h1). Qed.
Lemma lem6958271 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : (f x) = (NUMERAL 0).
Proof. exact (@lem6958268 A x s f h1 (@lem6958219 A s f x h2)). Qed.
Lemma lem6958272 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : term401 A f x.
Proof. exact (fun h0 : term336 A f x => @lem6958271 A s f x h1 h2). Qed.
Lemma lem6958274 (p : Prop) : (term392 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6958275 {A : Type'} (f : A -> nat) (x : A) : (term401 A f x) = ((f x) = (NUMERAL 0)).
Proof. exact (@lem6958274 ((f x) = (NUMERAL 0))). Qed.
Lemma lem6958276 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : (f x) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6958275 A f x) (@lem6958272 A s f x h1 h2)). Qed.
Lemma lem6958279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6958281 {A : Type'} (f : A -> nat) (x : A) : (term336 A f x) = (term402 A f x).
Proof. exact (@lem6958279 ((f x) = (NUMERAL 0))). Qed.
Lemma lem6958284 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term382 A s f x) : term402 A f x.
Proof. exact (EQ_MP (@lem6958281 A f x) (@lem6958159 A s f x h1)). Qed.
Lemma lem6958287 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : False.
Proof. exact (@lem6958284 A s f x h2 (@lem6958276 A s f x h1 h2)). Qed.
Lemma lem6958288 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : term403.
Proof. exact (fun h0 : ~ False => @lem6958287 A s f x h1 h2). Qed.
Lemma lem6958290 (p : Prop) : (term392 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6958291 : term403 = False.
Proof. exact (@lem6958290 False). Qed.
Lemma lem6958292 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : False.
Proof. exact (EQ_MP (@lem6958291) (@lem6958288 A s f x h1 h2)). Qed.
Lemma lem6958293 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : (term382 A s f x) = False.
Proof. exact (prop_ext (fun h3 : term382 A s f x => @lem6958292 A s f x h1 h2) (fun h3 : False => @lem6958115 A s f x h2)). Qed.
Lemma lem6958294 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (h1 : term324 A s f) (h2 : term382 A s f x) : False.
Proof. exact (EQ_MP (@lem6958293 A s f x h1 h2) (@lem6958115 A s f x h2)). Qed.
Lemma lem6958295 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term324 A s f) (h2 : term345 A s f) : False.
Proof. exact (ex_elim (@lem6958002 A s f h2) (fun x : A => fun h0 : term384 A s f x => @lem6958294 A s f x h1 h0)). Qed.
Lemma lem6958296 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : term404 A s f.
Proof. exact (fun h0 : term324 A s f => @lem6958295 A s f h0 h1). Qed.
Lemma lem6958297 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term404 A s f) = (term349 A s f).
Proof. exact (@lem69 (term324 A s f)). Qed.
Lemma lem6958298 {A : Type'} (s : A -> Prop) (f : A -> nat) (h1 : term345 A s f) : term349 A s f.
Proof. exact (EQ_MP (@lem6958297 A s f) (@lem6958296 A s f h1)). Qed.
Lemma lem6958299 {A : Type'} (s : A -> Prop) (f : A -> nat) : term353 A s f.
Proof. exact (fun h0 : term345 A s f => @lem6958298 A s f h0). Qed.
Lemma lem6958304 {A : Type'} (f : A -> nat) : term357 A f.
Proof. exact (fun s : A -> Prop => @lem6958299 A s f). Qed.
Lemma lem6958309 {A : Type'} : term361 A.
Proof. exact (fun f : A -> nat => @lem6958304 A f). Qed.
Lemma lem6958310 {A : Type'} : term363 A.
Proof. exact (EQ_MP (@lem6957916 A) (@lem6958309 A)). Qed.
Lemma lem6958312 {A : Type'} : term363 A.
Proof. exact (@lem6957768 A (@lem6958310 A)). Qed.
Lemma lem6958313 {A : Type'} (h1 : term364 A) : False.
Proof. exact (@lem6958312 A (@lem6957752 A h1)). Qed.
Lemma lem6958314 {A : Type'} (h1 : term364 A) : (term364 A) = False.
Proof. exact (prop_ext (fun h2 : term364 A => @lem6958313 A h1) (fun h2 : False => @lem6957752 A h1)). Qed.
Lemma lem6958315 {A : Type'} (h1 : term364 A) : False.
Proof. exact (EQ_MP (@lem6958314 A h1) (@lem6957752 A h1)). Qed.
Lemma lem6958316 {A : Type'} : term363 A.
Proof. exact (fun h0 : term364 A => @lem6958315 A h0). Qed.
Lemma lem6958317 {A : Type'} : term361 A.
Proof. exact (EQ_MP (@lem6957751 A) (@lem6958316 A)). Qed.
Lemma lem6958318 {A : Type'} : term360 A.
Proof. exact (EQ_MP (@lem6957747 A) (@lem6958317 A)). Qed.
