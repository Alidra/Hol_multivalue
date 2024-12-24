Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZERO_ONE_OR_PRIME_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DE_MORGAN_THM_spec.
Require Import DIVIDES_LE_STRONG_spec.
Require Import INT_POS_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import ZERO_ONE_OR_PRIME_DIVPROD_spec.
Require Import prime_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032070_spec.
Require Import thm1032072_spec.
Require Import thm1032627_spec.
Require Import thm1032730_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16496_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
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
Require Import thm2405764_spec.
Require Import thm2405813_spec.
Require Import thm2416515_spec.
Require Import thm2416521_spec.
Require Import thm2416525_spec.
Require Import thm2416535_spec.
Require Import thm2416549_spec.
Require Import thm2416563_spec.
Require Import thm2416594_spec.
Require Import thm2444030_spec.
Require Import thm2444031_spec.
Require Import thm2447297_spec.
Require Import thm2447298_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3073436_spec.
Require Import thm3074596_spec.
Require Import thm3117303_spec.
Require Import thm3117507_spec.
Require Import thm3117508_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm62_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm93_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem3157344 (n : nat) : (term0 n) = (term1 n).
Proof. exact (@lem17160 (n = (NUMERAL 0)) (n = term2)). Qed.
Lemma lem3157349 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem3157350 (n : nat) : (term4 n) = (term5 n).
Proof. exact (MK_COMB (@lem3157349 n) (@lem3157344 n)). Qed.
Lemma lem3157355 (n : nat) : (term6 n) = (term6 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem3157356 (n : nat) : (term7 n) = (term8 n).
Proof. exact (MK_COMB (@lem3157355 n) (@lem3157350 n)). Qed.
Lemma lem3157357 (n : nat) : ((term9 n) = (term10 n)) = (term7 n).
Proof. exact (@lem17500 (term9 n) (term10 n)). Qed.
Lemma lem3157439 (n : nat) : ((term9 n) = (term10 n)) = (term8 n).
Proof. exact (TRANS (@lem3157357 n) (@lem3157356 n)). Qed.
Lemma lem3157441 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3157442 (n : nat) : (term9 n) = (term12 n).
Proof. exact (@lem3157441 n term2). Qed.
Lemma lem3157443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157444 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem3157443) (@lem3157442 n)). Qed.
Lemma lem3157446 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3157447 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term15).
Proof. exact (@lem3157446 n (NUMERAL 0)). Qed.
Lemma lem3157450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157451 (n : nat) : (term16 n) = (term17 n).
Proof. exact (MK_COMB (@lem3157450) (@lem3157447 n)). Qed.
Lemma lem3157453 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3157454 (n : nat) : (n = term2) = ((int_of_num n) = term18).
Proof. exact (@lem3157453 n term2). Qed.
Lemma lem3157457 (n : nat) : (term10 n) = (term19 n).
Proof. exact (MK_COMB (@lem3157451 n) (@lem3157454 n)). Qed.
Lemma lem3157458 (n : nat) : (term20 n) = (term21 n).
Proof. exact (MK_COMB (@lem3157444 n) (@lem3157457 n)). Qed.
Lemma lem3157459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157460 (n : nat) : (term6 n) = (term22 n).
Proof. exact (MK_COMB (@lem3157459) (@lem3157458 n)). Qed.
Lemma lem3157462 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3157463 (n : nat) : (term9 n) = (term12 n).
Proof. exact (@lem3157462 n term2). Qed.
Lemma lem3157464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3157465 (n : nat) : (term23 n) = (term24 n).
Proof. exact (MK_COMB (@lem3157464) (@lem3157463 n)). Qed.
Lemma lem3157466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157467 (n : nat) : (term3 n) = (term25 n).
Proof. exact (MK_COMB (@lem3157466) (@lem3157465 n)). Qed.
Lemma lem3157469 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3157470 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term15).
Proof. exact (@lem3157469 n (NUMERAL 0)). Qed.
Lemma lem3157473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3157474 (n : nat) : (term26 n) = (term27 n).
Proof. exact (MK_COMB (@lem3157473) (@lem3157470 n)). Qed.
Lemma lem3157475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157476 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem3157475) (@lem3157474 n)). Qed.
Lemma lem3157478 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3157479 (n : nat) : (n = term2) = ((int_of_num n) = term18).
Proof. exact (@lem3157478 n term2). Qed.
Lemma lem3157482 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3157483 (n : nat) : (term30 n) = (term31 n).
Proof. exact (MK_COMB (@lem3157482) (@lem3157479 n)). Qed.
Lemma lem3157484 (n : nat) : (term1 n) = (term32 n).
Proof. exact (MK_COMB (@lem3157476 n) (@lem3157483 n)). Qed.
Lemma lem3157485 (n : nat) : (term5 n) = (term33 n).
Proof. exact (MK_COMB (@lem3157467 n) (@lem3157484 n)). Qed.
Lemma lem3157486 (n : nat) : (term8 n) = (term34 n).
Proof. exact (MK_COMB (@lem3157460 n) (@lem3157485 n)). Qed.
Lemma lem3157487 (n : nat) : ((term9 n) = (term10 n)) = (term34 n).
Proof. exact (TRANS (@lem3157439 n) (@lem3157486 n)). Qed.
Lemma lem3157488 (n : nat) : term35 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3157489 (n : nat) : (term35 n) = (term36 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem3157490 (n : nat) : term36 n.
Proof. exact (EQ_MP (@lem3157489 n) (@lem3157488 n)). Qed.
Lemma lem3157491 (_32603 : int) : (term37 _32603) = (term38 _32603).
Proof. exact (@lem2318604 (term38 _32603)). Qed.
Lemma lem3157517 (_32603 : int) : (term39 _32603) = (term40 _32603).
Proof. exact (@lem17160 (_32603 = term15) (_32603 = term18)). Qed.
Lemma lem3157519 (_32603 : int) : (term41 _32603) = (term41 _32603).
Proof. exact (eq_refl (term41 _32603)). Qed.
Lemma lem3157520 (_32603 : int) : (term42 _32603) = (term43 _32603).
Proof. exact (MK_COMB (@lem3157519 _32603) (@lem3157517 _32603)). Qed.
Lemma lem3157521 (_32603 : int) : (term44 _32603) = (term42 _32603).
Proof. exact (@lem17045 (term45 _32603) (term46 _32603)). Qed.
Lemma lem3157522 (_32603 : int) : (term44 _32603) = (term43 _32603).
Proof. exact (TRANS (@lem3157521 _32603) (@lem3157520 _32603)). Qed.
Lemma lem3157525 (_32603 : int) : (term47 _32603) = (term45 _32603).
Proof. exact (@lem16933 (term45 _32603)). Qed.
Lemma lem3157528 (_32603 : int) : (term48 _32603) = (_32603 = term15).
Proof. exact (@lem16933 (_32603 = term15)). Qed.
Lemma lem3157531 (_32603 : int) : (term49 _32603) = (_32603 = term18).
Proof. exact (@lem16933 (_32603 = term18)). Qed.
Lemma lem3157532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157533 (_32603 : int) : (term50 _32603) = (term51 _32603).
Proof. exact (MK_COMB (@lem3157532) (@lem3157528 _32603)). Qed.
Lemma lem3157534 (_32603 : int) : (term52 _32603) = (term46 _32603).
Proof. exact (MK_COMB (@lem3157533 _32603) (@lem3157531 _32603)). Qed.
Lemma lem3157535 (_32603 : int) : (term53 _32603) = (term52 _32603).
Proof. exact (@lem17045 (term54 _32603) (term55 _32603)). Qed.
Lemma lem3157536 (_32603 : int) : (term53 _32603) = (term46 _32603).
Proof. exact (TRANS (@lem3157535 _32603) (@lem3157534 _32603)). Qed.
Lemma lem3157537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157538 (_32603 : int) : (term56 _32603) = (term57 _32603).
Proof. exact (MK_COMB (@lem3157537) (@lem3157525 _32603)). Qed.
Lemma lem3157539 (_32603 : int) : (term58 _32603) = (term59 _32603).
Proof. exact (MK_COMB (@lem3157538 _32603) (@lem3157536 _32603)). Qed.
Lemma lem3157540 (_32603 : int) : (term60 _32603) = (term58 _32603).
Proof. exact (@lem17045 (term61 _32603) (term40 _32603)). Qed.
Lemma lem3157541 (_32603 : int) : (term60 _32603) = (term59 _32603).
Proof. exact (TRANS (@lem3157540 _32603) (@lem3157539 _32603)). Qed.
Lemma lem3157542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157543 (_32603 : int) : (term62 _32603) = (term63 _32603).
Proof. exact (MK_COMB (@lem3157542) (@lem3157522 _32603)). Qed.
Lemma lem3157544 (_32603 : int) : (term64 _32603) = (term65 _32603).
Proof. exact (MK_COMB (@lem3157543 _32603) (@lem3157541 _32603)). Qed.
Lemma lem3157545 (_32603 : int) : (term66 _32603) = (term64 _32603).
Proof. exact (@lem17160 (term67 _32603) (term68 _32603)). Qed.
Lemma lem3157546 (_32603 : int) : (term66 _32603) = (term65 _32603).
Proof. exact (TRANS (@lem3157545 _32603) (@lem3157544 _32603)). Qed.
Lemma lem3157548 (_32603 : int) : (term69 _32603) = (term69 _32603).
Proof. exact (eq_refl (term69 _32603)). Qed.
Lemma lem3157549 (_32603 : int) : (term70 _32603) = (term71 _32603).
Proof. exact (MK_COMB (@lem3157548 _32603) (@lem3157546 _32603)). Qed.
Lemma lem3157550 (_32603 : int) : (term72 _32603) = (term70 _32603).
Proof. exact (@lem17362 (term73 _32603) (term74 _32603)). Qed.
Lemma lem3157584 (_32603 : int) : (term72 _32603) = (term71 _32603).
Proof. exact (TRANS (@lem3157550 _32603) (@lem3157549 _32603)). Qed.
Lemma lem3157587 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157588 (_32603 : int) : (term73 _32603) = (term76 _32603).
Proof. exact (@lem3157587 term15 _32603). Qed.
Lemma lem3157590 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157591 : term78 = term79.
Proof. exact (@lem3157590 (NUMERAL 0)). Qed.
Lemma lem3157592 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3157593 : term80 = term81.
Proof. exact (MK_COMB (@lem3157592) (@lem3157591)). Qed.
Lemma lem3157594 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3157595 (_32603 : int) : (term76 _32603) = (term82 _32603).
Proof. exact (MK_COMB (@lem3157593) (@lem3157594 _32603)). Qed.
Lemma lem3157597 (_32603 : int) : (term73 _32603) = (term82 _32603).
Proof. exact (TRANS (@lem3157588 _32603) (@lem3157595 _32603)). Qed.
Lemma lem3157599 (y : int) (x : int) : (term83 x y) = (term84 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3157600 (_32603 : int) : (term61 _32603) = (term85 _32603).
Proof. exact (@lem3157599 term18 _32603). Qed.
Lemma lem3157602 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157603 (_32603 : int) : (term85 _32603) = (term86 _32603).
Proof. exact (@lem3157602 term87 _32603). Qed.
Lemma lem3157605 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3157606 : term90 = term91.
Proof. exact (@lem3157605 term18 term18). Qed.
Lemma lem3157608 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157609 : term92 = term93.
Proof. exact (@lem3157608 term2). Qed.
Lemma lem3157610 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3157611 : term94 = term95.
Proof. exact (MK_COMB (@lem3157610) (@lem3157609)). Qed.
Lemma lem3157613 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157614 : term92 = term93.
Proof. exact (@lem3157613 term2). Qed.
Lemma lem3157615 : term91 = term96.
Proof. exact (MK_COMB (@lem3157611) (@lem3157614)). Qed.
Lemma lem3157616 : term90 = term96.
Proof. exact (TRANS (@lem3157606) (@lem3157615)). Qed.
Lemma lem3157617 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3157618 : term97 = term98.
Proof. exact (MK_COMB (@lem3157617) (@lem3157616)). Qed.
Lemma lem3157619 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3157620 (_32603 : int) : (term86 _32603) = (term99 _32603).
Proof. exact (MK_COMB (@lem3157618) (@lem3157619 _32603)). Qed.
Lemma lem3157621 (_32603 : int) : (term85 _32603) = (term99 _32603).
Proof. exact (TRANS (@lem3157603 _32603) (@lem3157620 _32603)). Qed.
Lemma lem3157622 (_32603 : int) : (term61 _32603) = (term99 _32603).
Proof. exact (TRANS (@lem3157600 _32603) (@lem3157621 _32603)). Qed.
Lemma lem3157624 (y : int) (x : int) : (term100 x y) = (term101 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3157625 (_32603 : int) : (term54 _32603) = (term102 _32603).
Proof. exact (@lem3157624 term15 _32603). Qed.
Lemma lem3157627 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157628 (_32603 : int) : (term103 _32603) = (term104 _32603).
Proof. exact (@lem3157627 (term105 _32603) term15). Qed.
Lemma lem3157630 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3157631 (_32603 : int) : (term106 _32603) = (term107 _32603).
Proof. exact (@lem3157630 _32603 term18). Qed.
Lemma lem3157633 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157634 : term92 = term93.
Proof. exact (@lem3157633 term2). Qed.
Lemma lem3157635 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3157636 (_32603 : int) : (term107 _32603) = (term109 _32603).
Proof. exact (MK_COMB (@lem3157635 _32603) (@lem3157634)). Qed.
Lemma lem3157637 (_32603 : int) : (term106 _32603) = (term109 _32603).
Proof. exact (TRANS (@lem3157631 _32603) (@lem3157636 _32603)). Qed.
Lemma lem3157638 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3157639 (_32603 : int) : (term110 _32603) = (term111 _32603).
Proof. exact (MK_COMB (@lem3157638) (@lem3157637 _32603)). Qed.
Lemma lem3157641 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157642 : term78 = term79.
Proof. exact (@lem3157641 (NUMERAL 0)). Qed.
Lemma lem3157643 (_32603 : int) : (term104 _32603) = (term112 _32603).
Proof. exact (MK_COMB (@lem3157639 _32603) (@lem3157642)). Qed.
Lemma lem3157644 (_32603 : int) : (term103 _32603) = (term112 _32603).
Proof. exact (TRANS (@lem3157628 _32603) (@lem3157643 _32603)). Qed.
Lemma lem3157645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157646 (_32603 : int) : (term113 _32603) = (term114 _32603).
Proof. exact (MK_COMB (@lem3157645) (@lem3157644 _32603)). Qed.
Lemma lem3157648 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157649 (_32603 : int) : (term115 _32603) = (term116 _32603).
Proof. exact (@lem3157648 term117 _32603). Qed.
Lemma lem3157651 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3157652 : term118 = term119.
Proof. exact (@lem3157651 term15 term18). Qed.
Lemma lem3157654 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157655 : term78 = term79.
Proof. exact (@lem3157654 (NUMERAL 0)). Qed.
Lemma lem3157656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3157657 : term120 = term121.
Proof. exact (MK_COMB (@lem3157656) (@lem3157655)). Qed.
Lemma lem3157659 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157660 : term92 = term93.
Proof. exact (@lem3157659 term2). Qed.
Lemma lem3157661 : term119 = term122.
Proof. exact (MK_COMB (@lem3157657) (@lem3157660)). Qed.
Lemma lem3157662 : term118 = term122.
Proof. exact (TRANS (@lem3157652) (@lem3157661)). Qed.
Lemma lem3157663 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3157664 : term123 = term124.
Proof. exact (MK_COMB (@lem3157663) (@lem3157662)). Qed.
Lemma lem3157665 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3157666 (_32603 : int) : (term116 _32603) = (term125 _32603).
Proof. exact (MK_COMB (@lem3157664) (@lem3157665 _32603)). Qed.
Lemma lem3157667 (_32603 : int) : (term115 _32603) = (term125 _32603).
Proof. exact (TRANS (@lem3157649 _32603) (@lem3157666 _32603)). Qed.
Lemma lem3157668 (_32603 : int) : (term102 _32603) = (term126 _32603).
Proof. exact (MK_COMB (@lem3157646 _32603) (@lem3157667 _32603)). Qed.
Lemma lem3157669 (_32603 : int) : (term54 _32603) = (term126 _32603).
Proof. exact (TRANS (@lem3157625 _32603) (@lem3157668 _32603)). Qed.
Lemma lem3157671 (y : int) (x : int) : (term100 x y) = (term101 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3157672 (_32603 : int) : (term55 _32603) = (term127 _32603).
Proof. exact (@lem3157671 term18 _32603). Qed.
Lemma lem3157674 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157675 (_32603 : int) : (term128 _32603) = (term129 _32603).
Proof. exact (@lem3157674 (term105 _32603) term18). Qed.
Lemma lem3157677 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3157678 (_32603 : int) : (term106 _32603) = (term107 _32603).
Proof. exact (@lem3157677 _32603 term18). Qed.
Lemma lem3157680 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157681 : term92 = term93.
Proof. exact (@lem3157680 term2). Qed.
Lemma lem3157682 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3157683 (_32603 : int) : (term107 _32603) = (term109 _32603).
Proof. exact (MK_COMB (@lem3157682 _32603) (@lem3157681)). Qed.
Lemma lem3157684 (_32603 : int) : (term106 _32603) = (term109 _32603).
Proof. exact (TRANS (@lem3157678 _32603) (@lem3157683 _32603)). Qed.
Lemma lem3157685 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3157686 (_32603 : int) : (term110 _32603) = (term111 _32603).
Proof. exact (MK_COMB (@lem3157685) (@lem3157684 _32603)). Qed.
Lemma lem3157688 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157689 : term92 = term93.
Proof. exact (@lem3157688 term2). Qed.
Lemma lem3157690 (_32603 : int) : (term129 _32603) = (term130 _32603).
Proof. exact (MK_COMB (@lem3157686 _32603) (@lem3157689)). Qed.
Lemma lem3157691 (_32603 : int) : (term128 _32603) = (term130 _32603).
Proof. exact (TRANS (@lem3157675 _32603) (@lem3157690 _32603)). Qed.
Lemma lem3157692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157693 (_32603 : int) : (term131 _32603) = (term132 _32603).
Proof. exact (MK_COMB (@lem3157692) (@lem3157691 _32603)). Qed.
Lemma lem3157695 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157696 (_32603 : int) : (term85 _32603) = (term86 _32603).
Proof. exact (@lem3157695 term87 _32603). Qed.
Lemma lem3157698 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3157699 : term90 = term91.
Proof. exact (@lem3157698 term18 term18). Qed.
Lemma lem3157701 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157702 : term92 = term93.
Proof. exact (@lem3157701 term2). Qed.
Lemma lem3157703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3157704 : term94 = term95.
Proof. exact (MK_COMB (@lem3157703) (@lem3157702)). Qed.
Lemma lem3157706 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157707 : term92 = term93.
Proof. exact (@lem3157706 term2). Qed.
Lemma lem3157708 : term91 = term96.
Proof. exact (MK_COMB (@lem3157704) (@lem3157707)). Qed.
Lemma lem3157709 : term90 = term96.
Proof. exact (TRANS (@lem3157699) (@lem3157708)). Qed.
Lemma lem3157710 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3157711 : term97 = term98.
Proof. exact (MK_COMB (@lem3157710) (@lem3157709)). Qed.
Lemma lem3157712 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3157713 (_32603 : int) : (term86 _32603) = (term99 _32603).
Proof. exact (MK_COMB (@lem3157711) (@lem3157712 _32603)). Qed.
Lemma lem3157714 (_32603 : int) : (term85 _32603) = (term99 _32603).
Proof. exact (TRANS (@lem3157696 _32603) (@lem3157713 _32603)). Qed.
Lemma lem3157715 (_32603 : int) : (term127 _32603) = (term133 _32603).
Proof. exact (MK_COMB (@lem3157693 _32603) (@lem3157714 _32603)). Qed.
Lemma lem3157716 (_32603 : int) : (term55 _32603) = (term133 _32603).
Proof. exact (TRANS (@lem3157672 _32603) (@lem3157715 _32603)). Qed.
Lemma lem3157717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157718 (_32603 : int) : (term134 _32603) = (term135 _32603).
Proof. exact (MK_COMB (@lem3157717) (@lem3157669 _32603)). Qed.
Lemma lem3157719 (_32603 : int) : (term40 _32603) = (term136 _32603).
Proof. exact (MK_COMB (@lem3157718 _32603) (@lem3157716 _32603)). Qed.
Lemma lem3157720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157721 (_32603 : int) : (term41 _32603) = (term137 _32603).
Proof. exact (MK_COMB (@lem3157720) (@lem3157622 _32603)). Qed.
Lemma lem3157722 (_32603 : int) : (term43 _32603) = (term138 _32603).
Proof. exact (MK_COMB (@lem3157721 _32603) (@lem3157719 _32603)). Qed.
Lemma lem3157725 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3157726 (_32603 : int) : (term45 _32603) = (term139 _32603).
Proof. exact (@lem3157725 _32603 term18). Qed.
Lemma lem3157728 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157729 : term92 = term93.
Proof. exact (@lem3157728 term2). Qed.
Lemma lem3157730 (_32603 : int) : (term140 _32603) = (term140 _32603).
Proof. exact (eq_refl (term140 _32603)). Qed.
Lemma lem3157731 (_32603 : int) : (term139 _32603) = (term141 _32603).
Proof. exact (MK_COMB (@lem3157730 _32603) (@lem3157729)). Qed.
Lemma lem3157733 (_32603 : int) : (term45 _32603) = (term141 _32603).
Proof. exact (TRANS (@lem3157726 _32603) (@lem3157731 _32603)). Qed.
Lemma lem3157736 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3157737 (_32603 : int) : (_32603 = term15) = ((real_of_int _32603) = term78).
Proof. exact (@lem3157736 _32603 term15). Qed.
Lemma lem3157741 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157742 : term78 = term79.
Proof. exact (@lem3157741 (NUMERAL 0)). Qed.
Lemma lem3157743 (_32603 : int) : (term142 _32603) = (term142 _32603).
Proof. exact (eq_refl (term142 _32603)). Qed.
Lemma lem3157744 (_32603 : int) : ((real_of_int _32603) = term78) = ((real_of_int _32603) = term79).
Proof. exact (MK_COMB (@lem3157743 _32603) (@lem3157742)). Qed.
Lemma lem3157746 (_32603 : int) : (_32603 = term15) = ((real_of_int _32603) = term79).
Proof. exact (TRANS (@lem3157737 _32603) (@lem3157744 _32603)). Qed.
Lemma lem3157749 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3157750 (_32603 : int) : (_32603 = term18) = ((real_of_int _32603) = term92).
Proof. exact (@lem3157749 _32603 term18). Qed.
Lemma lem3157754 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3157755 : term92 = term93.
Proof. exact (@lem3157754 term2). Qed.
Lemma lem3157756 (_32603 : int) : (term142 _32603) = (term142 _32603).
Proof. exact (eq_refl (term142 _32603)). Qed.
Lemma lem3157757 (_32603 : int) : ((real_of_int _32603) = term92) = ((real_of_int _32603) = term93).
Proof. exact (MK_COMB (@lem3157756 _32603) (@lem3157755)). Qed.
Lemma lem3157759 (_32603 : int) : (_32603 = term18) = ((real_of_int _32603) = term93).
Proof. exact (TRANS (@lem3157750 _32603) (@lem3157757 _32603)). Qed.
Lemma lem3157760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157761 (_32603 : int) : (term51 _32603) = (term143 _32603).
Proof. exact (MK_COMB (@lem3157760) (@lem3157746 _32603)). Qed.
Lemma lem3157762 (_32603 : int) : (term46 _32603) = (term144 _32603).
Proof. exact (MK_COMB (@lem3157761 _32603) (@lem3157759 _32603)). Qed.
Lemma lem3157763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3157764 (_32603 : int) : (term57 _32603) = (term145 _32603).
Proof. exact (MK_COMB (@lem3157763) (@lem3157733 _32603)). Qed.
Lemma lem3157765 (_32603 : int) : (term59 _32603) = (term146 _32603).
Proof. exact (MK_COMB (@lem3157764 _32603) (@lem3157762 _32603)). Qed.
Lemma lem3157766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157767 (_32603 : int) : (term63 _32603) = (term147 _32603).
Proof. exact (MK_COMB (@lem3157766) (@lem3157722 _32603)). Qed.
Lemma lem3157768 (_32603 : int) : (term65 _32603) = (term148 _32603).
Proof. exact (MK_COMB (@lem3157767 _32603) (@lem3157765 _32603)). Qed.
Lemma lem3157769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3157770 (_32603 : int) : (term69 _32603) = (term149 _32603).
Proof. exact (MK_COMB (@lem3157769) (@lem3157597 _32603)). Qed.
Lemma lem3157771 (_32603 : int) : (term71 _32603) = (term150 _32603).
Proof. exact (MK_COMB (@lem3157770 _32603) (@lem3157768 _32603)). Qed.
Lemma lem3157772 (_32603 : int) : (term72 _32603) = (term150 _32603).
Proof. exact (TRANS (@lem3157584 _32603) (@lem3157771 _32603)). Qed.
Lemma lem3157776 (t : Prop) : (term151 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3157862 (_32603 : int) : (term152 _32603) = (term150 _32603).
Proof. exact (@lem3157776 (term150 _32603)). Qed.
Lemma lem3157863 (_32603 : int) : (term82 _32603) = (term153 _32603).
Proof. exact (@lem1988287 (real_of_int _32603) term79). Qed.
Lemma lem3157869 (_32603 : int) : (term154 _32603) = (term155 _32603).
Proof. exact (@lem1982792 (real_of_int _32603) term79). Qed.
Lemma lem3157871 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3157872 : term79 = term157.
Proof. exact (@lem3157871 (NUMERAL 0)). Qed.
Lemma lem3157874 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3157875 : term160 = term161.
Proof. exact (@lem3157874 term2). Qed.
Lemma lem3157876 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3157877 : term162 = term163.
Proof. exact (MK_COMB (@lem3157876) (@lem3157875)). Qed.
Lemma lem3157878 : term164 = term165.
Proof. exact (MK_COMB (@lem3157877) (@lem3157872)). Qed.
Lemma lem3157879 : term165 = term166.
Proof. exact (@lem1981613 term160 term79 term93 term93). Qed.
Lemma lem3157881 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3157882 : term169 = term170.
Proof. exact (@lem3157881 term2 term2). Qed.
Lemma lem3157883 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3157884 : term172 = term2.
Proof. exact (EQ_MP (@lem3157883) (@lem940073)). Qed.
Lemma lem3157885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3157886 : term170 = term93.
Proof. exact (MK_COMB (@lem3157885) (@lem3157884)). Qed.
Lemma lem3157887 : term169 = term93.
Proof. exact (TRANS (@lem3157882) (@lem3157886)). Qed.
Lemma lem3157889 (x : nat) : (term173 x) = term79.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3157890 : term164 = term79.
Proof. exact (@lem3157889 term2). Qed.
Lemma lem3157891 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3157892 : term174 = term175.
Proof. exact (MK_COMB (@lem3157891) (@lem3157890)). Qed.
Lemma lem3157893 : term166 = term157.
Proof. exact (MK_COMB (@lem3157892) (@lem3157887)). Qed.
Lemma lem3157894 : term165 = term157.
Proof. exact (TRANS (@lem3157879) (@lem3157893)). Qed.
Lemma lem3157895 : term164 = term157.
Proof. exact (TRANS (@lem3157878) (@lem3157894)). Qed.
Lemma lem3157897 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3157898 : term157 = term79.
Proof. exact (@lem3157897 term79). Qed.
Lemma lem3157899 : term164 = term79.
Proof. exact (TRANS (@lem3157895) (@lem3157898)). Qed.
Lemma lem3157900 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3157901 (_32603 : int) : (term155 _32603) = (term177 _32603).
Proof. exact (MK_COMB (@lem3157900 _32603) (@lem3157899)). Qed.
Lemma lem3157902 (_32603 : int) : (term177 _32603) = (real_of_int _32603).
Proof. exact (@lem1982723 (real_of_int _32603)). Qed.
Lemma lem3157903 (_32603 : int) : (term155 _32603) = (real_of_int _32603).
Proof. exact (TRANS (@lem3157901 _32603) (@lem3157902 _32603)). Qed.
Lemma lem3157905 (_32603 : int) : (term154 _32603) = (real_of_int _32603).
Proof. exact (TRANS (@lem3157869 _32603) (@lem3157903 _32603)). Qed.
Lemma lem3157906 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3157907 (_32603 : int) : (term178 _32603) = (term179 _32603).
Proof. exact (MK_COMB (@lem3157906) (@lem3157905 _32603)). Qed.
Lemma lem3157908 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3157909 (_32603 : int) : (term153 _32603) = (term180 _32603).
Proof. exact (MK_COMB (@lem3157907 _32603) (@lem3157908)). Qed.
Lemma lem3157910 (_32603 : int) : (term82 _32603) = (term180 _32603).
Proof. exact (TRANS (@lem3157863 _32603) (@lem3157909 _32603)). Qed.
Lemma lem3157911 (_32603 : int) : (term99 _32603) = (term181 _32603).
Proof. exact (@lem1988287 (real_of_int _32603) term96). Qed.
Lemma lem3157918 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3157919 : term93 = term182.
Proof. exact (@lem3157918 term2). Qed.
Lemma lem3157921 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3157922 : term93 = term182.
Proof. exact (@lem3157921 term2). Qed.
Lemma lem3157923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3157924 : term95 = term183.
Proof. exact (MK_COMB (@lem3157923) (@lem3157922)). Qed.
Lemma lem3157925 : term96 = term184.
Proof. exact (MK_COMB (@lem3157924) (@lem3157919)). Qed.
Lemma lem3157926 : term185.
Proof. exact (@lem1981473 term93 term93 term93 term93 term186 term93). Qed.
Lemma lem3157928 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3157929 : term188 = term189.
Proof. exact (@lem3157928 (NUMERAL 0) term2). Qed.
Lemma lem3157930 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3157931 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3157932 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3157931 h1) (fun h1 : term189 = True => @lem3157930)). Qed.
Lemma lem3157933 : term189 = True.
Proof. exact (EQ_MP (@lem3157932) (@lem3157930)). Qed.
Lemma lem3157934 : term188 = True.
Proof. exact (TRANS (@lem3157929) (@lem3157933)). Qed.
Lemma lem3157935 : True = term188.
Proof. exact (SYM (@lem3157934)). Qed.
Lemma lem3157936 : term188.
Proof. exact (EQ_MP (@lem3157935) (@lem0)). Qed.
Lemma lem3157937 : term191.
Proof. exact (@lem3157926 (@lem3157936)). Qed.
Lemma lem3157939 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3157940 : term188 = term189.
Proof. exact (@lem3157939 (NUMERAL 0) term2). Qed.
Lemma lem3157941 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3157942 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3157943 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3157942 h1) (fun h1 : term189 = True => @lem3157941)). Qed.
Lemma lem3157944 : term189 = True.
Proof. exact (EQ_MP (@lem3157943) (@lem3157941)). Qed.
Lemma lem3157945 : term188 = True.
Proof. exact (TRANS (@lem3157940) (@lem3157944)). Qed.
Lemma lem3157946 : True = term188.
Proof. exact (SYM (@lem3157945)). Qed.
Lemma lem3157947 : term188.
Proof. exact (EQ_MP (@lem3157946) (@lem0)). Qed.
Lemma lem3157948 : term192.
Proof. exact (@lem3157937 (@lem3157947)). Qed.
Lemma lem3157950 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3157951 : term188 = term189.
Proof. exact (@lem3157950 (NUMERAL 0) term2). Qed.
Lemma lem3157952 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3157953 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3157954 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3157953 h1) (fun h1 : term189 = True => @lem3157952)). Qed.
Lemma lem3157955 : term189 = True.
Proof. exact (EQ_MP (@lem3157954) (@lem3157952)). Qed.
Lemma lem3157956 : term188 = True.
Proof. exact (TRANS (@lem3157951) (@lem3157955)). Qed.
Lemma lem3157957 : True = term188.
Proof. exact (SYM (@lem3157956)). Qed.
Lemma lem3157958 : term188.
Proof. exact (EQ_MP (@lem3157957) (@lem0)). Qed.
Lemma lem3157959 : term193.
Proof. exact (@lem3157948 (@lem3157958)). Qed.
Lemma lem3157961 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3157962 : term169 = term170.
Proof. exact (@lem3157961 term2 term2). Qed.
Lemma lem3157963 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3157964 : term172 = term2.
Proof. exact (EQ_MP (@lem3157963) (@lem940073)). Qed.
Lemma lem3157965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3157966 : term170 = term93.
Proof. exact (MK_COMB (@lem3157965) (@lem3157964)). Qed.
Lemma lem3157967 : term169 = term93.
Proof. exact (TRANS (@lem3157962) (@lem3157966)). Qed.
Lemma lem3157969 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3157970 : term169 = term170.
Proof. exact (@lem3157969 term2 term2). Qed.
Lemma lem3157971 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3157972 : term172 = term2.
Proof. exact (EQ_MP (@lem3157971) (@lem940073)). Qed.
Lemma lem3157973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3157974 : term170 = term93.
Proof. exact (MK_COMB (@lem3157973) (@lem3157972)). Qed.
Lemma lem3157975 : term169 = term93.
Proof. exact (TRANS (@lem3157970) (@lem3157974)). Qed.
Lemma lem3157976 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3157977 : term194 = term95.
Proof. exact (MK_COMB (@lem3157976) (@lem3157975)). Qed.
Lemma lem3157978 : term195 = term96.
Proof. exact (MK_COMB (@lem3157977) (@lem3157967)). Qed.
Lemma lem3157979 : term96 = term196.
Proof. exact (@lem1367770 term2 term2). Qed.
Lemma lem3157980 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3157981 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3157982 : term199 = term200.
Proof. exact (EQ_MP (@lem3157981) (@lem3157980)). Qed.
Lemma lem3157983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3157984 : term196 = term186.
Proof. exact (MK_COMB (@lem3157983) (@lem3157982)). Qed.
Lemma lem3157985 : term96 = term186.
Proof. exact (TRANS (@lem3157979) (@lem3157984)). Qed.
Lemma lem3157986 : term195 = term186.
Proof. exact (TRANS (@lem3157978) (@lem3157985)). Qed.
Lemma lem3157987 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3157988 : term201 = term202.
Proof. exact (MK_COMB (@lem3157987) (@lem3157986)). Qed.
Lemma lem3157989 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3157990 : term203 = term204.
Proof. exact (MK_COMB (@lem3157988) (@lem3157989)). Qed.
Lemma lem3157992 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3157993 : term204 = term205.
Proof. exact (@lem3157992 term200 term2). Qed.
Lemma lem3157994 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3157995 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3157996 : term207 = term200.
Proof. exact (EQ_MP (@lem3157995) (@lem3157994)). Qed.
Lemma lem3157997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3157998 : term205 = term186.
Proof. exact (MK_COMB (@lem3157997) (@lem3157996)). Qed.
Lemma lem3157999 : term204 = term186.
Proof. exact (TRANS (@lem3157993) (@lem3157998)). Qed.
Lemma lem3158000 : term203 = term186.
Proof. exact (TRANS (@lem3157990) (@lem3157999)). Qed.
Lemma lem3158002 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158003 : term169 = term170.
Proof. exact (@lem3158002 term2 term2). Qed.
Lemma lem3158004 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158005 : term172 = term2.
Proof. exact (EQ_MP (@lem3158004) (@lem940073)). Qed.
Lemma lem3158006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158007 : term170 = term93.
Proof. exact (MK_COMB (@lem3158006) (@lem3158005)). Qed.
Lemma lem3158008 : term169 = term93.
Proof. exact (TRANS (@lem3158003) (@lem3158007)). Qed.
Lemma lem3158009 : term202 = term202.
Proof. exact (eq_refl term202). Qed.
Lemma lem3158010 : term208 = term204.
Proof. exact (MK_COMB (@lem3158009) (@lem3158008)). Qed.
Lemma lem3158012 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158013 : term204 = term205.
Proof. exact (@lem3158012 term200 term2). Qed.
Lemma lem3158014 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3158015 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3158016 : term207 = term200.
Proof. exact (EQ_MP (@lem3158015) (@lem3158014)). Qed.
Lemma lem3158017 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158018 : term205 = term186.
Proof. exact (MK_COMB (@lem3158017) (@lem3158016)). Qed.
Lemma lem3158019 : term204 = term186.
Proof. exact (TRANS (@lem3158013) (@lem3158018)). Qed.
Lemma lem3158020 : term208 = term186.
Proof. exact (TRANS (@lem3158010) (@lem3158019)). Qed.
Lemma lem3158021 : term186 = term208.
Proof. exact (SYM (@lem3158020)). Qed.
Lemma lem3158022 : term203 = term208.
Proof. exact (TRANS (@lem3158000) (@lem3158021)). Qed.
Lemma lem3158023 : term184 = term209.
Proof. exact (@lem3157959 (@lem3158022)). Qed.
Lemma lem3158024 : term96 = term209.
Proof. exact (TRANS (@lem3157925) (@lem3158023)). Qed.
Lemma lem3158026 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3158027 : term209 = term186.
Proof. exact (@lem3158026 term186). Qed.
Lemma lem3158029 : term96 = term186.
Proof. exact (TRANS (@lem3158024) (@lem3158027)). Qed.
Lemma lem3158032 (_32603 : int) : (term210 _32603) = (term210 _32603).
Proof. exact (eq_refl (term210 _32603)). Qed.
Lemma lem3158033 (_32603 : int) : (term211 _32603) = (term212 _32603).
Proof. exact (MK_COMB (@lem3158032 _32603) (@lem3158029)). Qed.
Lemma lem3158034 (_32603 : int) : (term212 _32603) = (term213 _32603).
Proof. exact (@lem1982792 (real_of_int _32603) term186). Qed.
Lemma lem3158036 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158037 : term186 = term209.
Proof. exact (@lem3158036 term200). Qed.
Lemma lem3158039 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158040 : term160 = term161.
Proof. exact (@lem3158039 term2). Qed.
Lemma lem3158041 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158042 : term162 = term163.
Proof. exact (MK_COMB (@lem3158041) (@lem3158040)). Qed.
Lemma lem3158043 : term214 = term215.
Proof. exact (MK_COMB (@lem3158042) (@lem3158037)). Qed.
Lemma lem3158044 : term215 = term216.
Proof. exact (@lem1981613 term160 term186 term93 term93). Qed.
Lemma lem3158046 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158047 : term169 = term170.
Proof. exact (@lem3158046 term2 term2). Qed.
Lemma lem3158048 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158049 : term172 = term2.
Proof. exact (EQ_MP (@lem3158048) (@lem940073)). Qed.
Lemma lem3158050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158051 : term170 = term93.
Proof. exact (MK_COMB (@lem3158050) (@lem3158049)). Qed.
Lemma lem3158052 : term169 = term93.
Proof. exact (TRANS (@lem3158047) (@lem3158051)). Qed.
Lemma lem3158054 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158055 : term214 = term219.
Proof. exact (@lem3158054 term2 term200). Qed.
Lemma lem3158056 : term220 = term198.
Proof. exact (@lem996238 term198). Qed.
Lemma lem3158057 : (term220 = term198) = (term221 = term200).
Proof. exact (@lem1007663 (BIT1 0) term198 term198). Qed.
Lemma lem3158058 : term221 = term200.
Proof. exact (EQ_MP (@lem3158057) (@lem3158056)). Qed.
Lemma lem3158059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158060 : term222 = term186.
Proof. exact (MK_COMB (@lem3158059) (@lem3158058)). Qed.
Lemma lem3158061 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158062 : term219 = term223.
Proof. exact (MK_COMB (@lem3158061) (@lem3158060)). Qed.
Lemma lem3158063 : term214 = term223.
Proof. exact (TRANS (@lem3158055) (@lem3158062)). Qed.
Lemma lem3158064 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158065 : term224 = term225.
Proof. exact (MK_COMB (@lem3158064) (@lem3158063)). Qed.
Lemma lem3158066 : term216 = term226.
Proof. exact (MK_COMB (@lem3158065) (@lem3158052)). Qed.
Lemma lem3158067 : term215 = term226.
Proof. exact (TRANS (@lem3158044) (@lem3158066)). Qed.
Lemma lem3158068 : term214 = term226.
Proof. exact (TRANS (@lem3158043) (@lem3158067)). Qed.
Lemma lem3158070 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158071 : term226 = term223.
Proof. exact (@lem3158070 term223). Qed.
Lemma lem3158072 : term214 = term223.
Proof. exact (TRANS (@lem3158068) (@lem3158071)). Qed.
Lemma lem3158073 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3158076 (_32603 : int) : (term213 _32603) = (term227 _32603).
Proof. exact (MK_COMB (@lem3158073 _32603) (@lem3158072)). Qed.
Lemma lem3158077 (_32603 : int) : (term212 _32603) = (term227 _32603).
Proof. exact (TRANS (@lem3158034 _32603) (@lem3158076 _32603)). Qed.
Lemma lem3158078 (_32603 : int) : (term211 _32603) = (term227 _32603).
Proof. exact (TRANS (@lem3158033 _32603) (@lem3158077 _32603)). Qed.
Lemma lem3158079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3158080 (_32603 : int) : (term228 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3158079) (@lem3158078 _32603)). Qed.
Lemma lem3158081 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158082 (_32603 : int) : (term181 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3158080 _32603) (@lem3158081)). Qed.
Lemma lem3158083 (_32603 : int) : (term99 _32603) = (term230 _32603).
Proof. exact (TRANS (@lem3157911 _32603) (@lem3158082 _32603)). Qed.
Lemma lem3158084 (_32603 : int) : (term112 _32603) = (term231 _32603).
Proof. exact (@lem1988287 term79 (term109 _32603)). Qed.
Lemma lem3158096 (_32603 : int) : (term232 _32603) = (term233 _32603).
Proof. exact (@lem1982792 term79 (term109 _32603)). Qed.
Lemma lem3158097 (_32603 : int) : (term234 _32603) = (term235 _32603).
Proof. exact (@lem1982781 (real_of_int _32603) term160 term93). Qed.
Lemma lem3158099 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158100 : term93 = term182.
Proof. exact (@lem3158099 term2). Qed.
Lemma lem3158102 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158103 : term160 = term161.
Proof. exact (@lem3158102 term2). Qed.
Lemma lem3158104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158105 : term162 = term163.
Proof. exact (MK_COMB (@lem3158104) (@lem3158103)). Qed.
Lemma lem3158106 : term236 = term237.
Proof. exact (MK_COMB (@lem3158105) (@lem3158100)). Qed.
Lemma lem3158107 : term237 = term238.
Proof. exact (@lem1981613 term160 term93 term93 term93). Qed.
Lemma lem3158109 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158110 : term169 = term170.
Proof. exact (@lem3158109 term2 term2). Qed.
Lemma lem3158111 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158112 : term172 = term2.
Proof. exact (EQ_MP (@lem3158111) (@lem940073)). Qed.
Lemma lem3158113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158114 : term170 = term93.
Proof. exact (MK_COMB (@lem3158113) (@lem3158112)). Qed.
Lemma lem3158115 : term169 = term93.
Proof. exact (TRANS (@lem3158110) (@lem3158114)). Qed.
Lemma lem3158117 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158118 : term236 = term239.
Proof. exact (@lem3158117 term2 term2). Qed.
Lemma lem3158119 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158120 : term172 = term2.
Proof. exact (EQ_MP (@lem3158119) (@lem940073)). Qed.
Lemma lem3158121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158122 : term170 = term93.
Proof. exact (MK_COMB (@lem3158121) (@lem3158120)). Qed.
Lemma lem3158123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158124 : term239 = term160.
Proof. exact (MK_COMB (@lem3158123) (@lem3158122)). Qed.
Lemma lem3158125 : term236 = term160.
Proof. exact (TRANS (@lem3158118) (@lem3158124)). Qed.
Lemma lem3158126 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158127 : term240 = term241.
Proof. exact (MK_COMB (@lem3158126) (@lem3158125)). Qed.
Lemma lem3158128 : term238 = term161.
Proof. exact (MK_COMB (@lem3158127) (@lem3158115)). Qed.
Lemma lem3158129 : term237 = term161.
Proof. exact (TRANS (@lem3158107) (@lem3158128)). Qed.
Lemma lem3158130 : term236 = term161.
Proof. exact (TRANS (@lem3158106) (@lem3158129)). Qed.
Lemma lem3158132 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158133 : term161 = term160.
Proof. exact (@lem3158132 term160). Qed.
Lemma lem3158134 : term236 = term160.
Proof. exact (TRANS (@lem3158130) (@lem3158133)). Qed.
Lemma lem3158137 (_32603 : int) : (term242 _32603) = (term242 _32603).
Proof. exact (eq_refl (term242 _32603)). Qed.
Lemma lem3158138 (_32603 : int) : (term235 _32603) = (term243 _32603).
Proof. exact (MK_COMB (@lem3158137 _32603) (@lem3158134)). Qed.
Lemma lem3158139 (_32603 : int) : (term234 _32603) = (term243 _32603).
Proof. exact (TRANS (@lem3158097 _32603) (@lem3158138 _32603)). Qed.
Lemma lem3158140 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem3158141 (_32603 : int) : (term233 _32603) = (term244 _32603).
Proof. exact (MK_COMB (@lem3158140) (@lem3158139 _32603)). Qed.
Lemma lem3158142 (_32603 : int) : (term244 _32603) = (term243 _32603).
Proof. exact (@lem1982721 (term243 _32603)). Qed.
Lemma lem3158143 (_32603 : int) : (term233 _32603) = (term243 _32603).
Proof. exact (TRANS (@lem3158141 _32603) (@lem3158142 _32603)). Qed.
Lemma lem3158145 (_32603 : int) : (term232 _32603) = (term243 _32603).
Proof. exact (TRANS (@lem3158096 _32603) (@lem3158143 _32603)). Qed.
Lemma lem3158146 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3158147 (_32603 : int) : (term245 _32603) = (term246 _32603).
Proof. exact (MK_COMB (@lem3158146) (@lem3158145 _32603)). Qed.
Lemma lem3158148 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158149 (_32603 : int) : (term231 _32603) = (term247 _32603).
Proof. exact (MK_COMB (@lem3158147 _32603) (@lem3158148)). Qed.
Lemma lem3158150 (_32603 : int) : (term112 _32603) = (term247 _32603).
Proof. exact (TRANS (@lem3158084 _32603) (@lem3158149 _32603)). Qed.
Lemma lem3158151 (_32603 : int) : (term125 _32603) = (term248 _32603).
Proof. exact (@lem1988287 (real_of_int _32603) term122). Qed.
Lemma lem3158158 : term122 = term93.
Proof. exact (@lem1982721 term93). Qed.
Lemma lem3158161 (_32603 : int) : (term210 _32603) = (term210 _32603).
Proof. exact (eq_refl (term210 _32603)). Qed.
Lemma lem3158162 (_32603 : int) : (term249 _32603) = (term250 _32603).
Proof. exact (MK_COMB (@lem3158161 _32603) (@lem3158158)). Qed.
Lemma lem3158163 (_32603 : int) : (term250 _32603) = (term251 _32603).
Proof. exact (@lem1982792 (real_of_int _32603) term93). Qed.
Lemma lem3158165 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158166 : term93 = term182.
Proof. exact (@lem3158165 term2). Qed.
Lemma lem3158168 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158169 : term160 = term161.
Proof. exact (@lem3158168 term2). Qed.
Lemma lem3158170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158171 : term162 = term163.
Proof. exact (MK_COMB (@lem3158170) (@lem3158169)). Qed.
Lemma lem3158172 : term236 = term237.
Proof. exact (MK_COMB (@lem3158171) (@lem3158166)). Qed.
Lemma lem3158173 : term237 = term238.
Proof. exact (@lem1981613 term160 term93 term93 term93). Qed.
Lemma lem3158175 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158176 : term169 = term170.
Proof. exact (@lem3158175 term2 term2). Qed.
Lemma lem3158177 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158178 : term172 = term2.
Proof. exact (EQ_MP (@lem3158177) (@lem940073)). Qed.
Lemma lem3158179 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158180 : term170 = term93.
Proof. exact (MK_COMB (@lem3158179) (@lem3158178)). Qed.
Lemma lem3158181 : term169 = term93.
Proof. exact (TRANS (@lem3158176) (@lem3158180)). Qed.
Lemma lem3158183 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158184 : term236 = term239.
Proof. exact (@lem3158183 term2 term2). Qed.
Lemma lem3158185 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158186 : term172 = term2.
Proof. exact (EQ_MP (@lem3158185) (@lem940073)). Qed.
Lemma lem3158187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158188 : term170 = term93.
Proof. exact (MK_COMB (@lem3158187) (@lem3158186)). Qed.
Lemma lem3158189 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158190 : term239 = term160.
Proof. exact (MK_COMB (@lem3158189) (@lem3158188)). Qed.
Lemma lem3158191 : term236 = term160.
Proof. exact (TRANS (@lem3158184) (@lem3158190)). Qed.
Lemma lem3158192 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158193 : term240 = term241.
Proof. exact (MK_COMB (@lem3158192) (@lem3158191)). Qed.
Lemma lem3158194 : term238 = term161.
Proof. exact (MK_COMB (@lem3158193) (@lem3158181)). Qed.
Lemma lem3158195 : term237 = term161.
Proof. exact (TRANS (@lem3158173) (@lem3158194)). Qed.
Lemma lem3158196 : term236 = term161.
Proof. exact (TRANS (@lem3158172) (@lem3158195)). Qed.
Lemma lem3158198 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158199 : term161 = term160.
Proof. exact (@lem3158198 term160). Qed.
Lemma lem3158200 : term236 = term160.
Proof. exact (TRANS (@lem3158196) (@lem3158199)). Qed.
Lemma lem3158201 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3158204 (_32603 : int) : (term251 _32603) = (term252 _32603).
Proof. exact (MK_COMB (@lem3158201 _32603) (@lem3158200)). Qed.
Lemma lem3158205 (_32603 : int) : (term250 _32603) = (term252 _32603).
Proof. exact (TRANS (@lem3158163 _32603) (@lem3158204 _32603)). Qed.
Lemma lem3158206 (_32603 : int) : (term249 _32603) = (term252 _32603).
Proof. exact (TRANS (@lem3158162 _32603) (@lem3158205 _32603)). Qed.
Lemma lem3158207 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3158208 (_32603 : int) : (term253 _32603) = (term254 _32603).
Proof. exact (MK_COMB (@lem3158207) (@lem3158206 _32603)). Qed.
Lemma lem3158209 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158210 (_32603 : int) : (term248 _32603) = (term255 _32603).
Proof. exact (MK_COMB (@lem3158208 _32603) (@lem3158209)). Qed.
Lemma lem3158211 (_32603 : int) : (term125 _32603) = (term255 _32603).
Proof. exact (TRANS (@lem3158151 _32603) (@lem3158210 _32603)). Qed.
Lemma lem3158212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158213 (_32603 : int) : (term114 _32603) = (term256 _32603).
Proof. exact (MK_COMB (@lem3158212) (@lem3158150 _32603)). Qed.
Lemma lem3158214 (_32603 : int) : (term126 _32603) = (term257 _32603).
Proof. exact (MK_COMB (@lem3158213 _32603) (@lem3158211 _32603)). Qed.
Lemma lem3158215 (_32603 : int) : (term130 _32603) = (term258 _32603).
Proof. exact (@lem1988287 term93 (term109 _32603)). Qed.
Lemma lem3158227 (_32603 : int) : (term259 _32603) = (term260 _32603).
Proof. exact (@lem1982792 term93 (term109 _32603)). Qed.
Lemma lem3158228 (_32603 : int) : (term234 _32603) = (term235 _32603).
Proof. exact (@lem1982781 (real_of_int _32603) term160 term93). Qed.
Lemma lem3158230 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158231 : term93 = term182.
Proof. exact (@lem3158230 term2). Qed.
Lemma lem3158233 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158234 : term160 = term161.
Proof. exact (@lem3158233 term2). Qed.
Lemma lem3158235 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158236 : term162 = term163.
Proof. exact (MK_COMB (@lem3158235) (@lem3158234)). Qed.
Lemma lem3158237 : term236 = term237.
Proof. exact (MK_COMB (@lem3158236) (@lem3158231)). Qed.
Lemma lem3158238 : term237 = term238.
Proof. exact (@lem1981613 term160 term93 term93 term93). Qed.
Lemma lem3158240 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158241 : term169 = term170.
Proof. exact (@lem3158240 term2 term2). Qed.
Lemma lem3158242 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158243 : term172 = term2.
Proof. exact (EQ_MP (@lem3158242) (@lem940073)). Qed.
Lemma lem3158244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158245 : term170 = term93.
Proof. exact (MK_COMB (@lem3158244) (@lem3158243)). Qed.
Lemma lem3158246 : term169 = term93.
Proof. exact (TRANS (@lem3158241) (@lem3158245)). Qed.
Lemma lem3158248 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158249 : term236 = term239.
Proof. exact (@lem3158248 term2 term2). Qed.
Lemma lem3158250 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158251 : term172 = term2.
Proof. exact (EQ_MP (@lem3158250) (@lem940073)). Qed.
Lemma lem3158252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158253 : term170 = term93.
Proof. exact (MK_COMB (@lem3158252) (@lem3158251)). Qed.
Lemma lem3158254 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158255 : term239 = term160.
Proof. exact (MK_COMB (@lem3158254) (@lem3158253)). Qed.
Lemma lem3158256 : term236 = term160.
Proof. exact (TRANS (@lem3158249) (@lem3158255)). Qed.
Lemma lem3158257 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158258 : term240 = term241.
Proof. exact (MK_COMB (@lem3158257) (@lem3158256)). Qed.
Lemma lem3158259 : term238 = term161.
Proof. exact (MK_COMB (@lem3158258) (@lem3158246)). Qed.
Lemma lem3158260 : term237 = term161.
Proof. exact (TRANS (@lem3158238) (@lem3158259)). Qed.
Lemma lem3158261 : term236 = term161.
Proof. exact (TRANS (@lem3158237) (@lem3158260)). Qed.
Lemma lem3158263 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158264 : term161 = term160.
Proof. exact (@lem3158263 term160). Qed.
Lemma lem3158265 : term236 = term160.
Proof. exact (TRANS (@lem3158261) (@lem3158264)). Qed.
Lemma lem3158268 (_32603 : int) : (term242 _32603) = (term242 _32603).
Proof. exact (eq_refl (term242 _32603)). Qed.
Lemma lem3158269 (_32603 : int) : (term235 _32603) = (term243 _32603).
Proof. exact (MK_COMB (@lem3158268 _32603) (@lem3158265)). Qed.
Lemma lem3158270 (_32603 : int) : (term234 _32603) = (term243 _32603).
Proof. exact (TRANS (@lem3158228 _32603) (@lem3158269 _32603)). Qed.
Lemma lem3158271 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3158272 (_32603 : int) : (term260 _32603) = (term261 _32603).
Proof. exact (MK_COMB (@lem3158271) (@lem3158270 _32603)). Qed.
Lemma lem3158273 (_32603 : int) : (term261 _32603) = (term262 _32603).
Proof. exact (@lem1982757 (term263 _32603) term93 term160). Qed.
Lemma lem3158275 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158276 : term160 = term161.
Proof. exact (@lem3158275 term2). Qed.
Lemma lem3158278 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158279 : term93 = term182.
Proof. exact (@lem3158278 term2). Qed.
Lemma lem3158280 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3158281 : term95 = term183.
Proof. exact (MK_COMB (@lem3158280) (@lem3158279)). Qed.
Lemma lem3158282 : term264 = term265.
Proof. exact (MK_COMB (@lem3158281) (@lem3158276)). Qed.
Lemma lem3158283 : term266.
Proof. exact (@lem1981473 term93 term93 term160 term93 term79 term93). Qed.
Lemma lem3158285 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3158286 : term188 = term189.
Proof. exact (@lem3158285 (NUMERAL 0) term2). Qed.
Lemma lem3158287 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3158288 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3158289 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3158288 h1) (fun h1 : term189 = True => @lem3158287)). Qed.
Lemma lem3158290 : term189 = True.
Proof. exact (EQ_MP (@lem3158289) (@lem3158287)). Qed.
Lemma lem3158291 : term188 = True.
Proof. exact (TRANS (@lem3158286) (@lem3158290)). Qed.
Lemma lem3158292 : True = term188.
Proof. exact (SYM (@lem3158291)). Qed.
Lemma lem3158293 : term188.
Proof. exact (EQ_MP (@lem3158292) (@lem0)). Qed.
Lemma lem3158294 : term267.
Proof. exact (@lem3158283 (@lem3158293)). Qed.
Lemma lem3158296 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3158297 : term188 = term189.
Proof. exact (@lem3158296 (NUMERAL 0) term2). Qed.
Lemma lem3158298 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3158299 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3158300 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3158299 h1) (fun h1 : term189 = True => @lem3158298)). Qed.
Lemma lem3158301 : term189 = True.
Proof. exact (EQ_MP (@lem3158300) (@lem3158298)). Qed.
Lemma lem3158302 : term188 = True.
Proof. exact (TRANS (@lem3158297) (@lem3158301)). Qed.
Lemma lem3158303 : True = term188.
Proof. exact (SYM (@lem3158302)). Qed.
Lemma lem3158304 : term188.
Proof. exact (EQ_MP (@lem3158303) (@lem0)). Qed.
Lemma lem3158305 : term268.
Proof. exact (@lem3158294 (@lem3158304)). Qed.
Lemma lem3158307 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3158308 : term188 = term189.
Proof. exact (@lem3158307 (NUMERAL 0) term2). Qed.
Lemma lem3158309 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3158310 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3158311 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3158310 h1) (fun h1 : term189 = True => @lem3158309)). Qed.
Lemma lem3158312 : term189 = True.
Proof. exact (EQ_MP (@lem3158311) (@lem3158309)). Qed.
Lemma lem3158313 : term188 = True.
Proof. exact (TRANS (@lem3158308) (@lem3158312)). Qed.
Lemma lem3158314 : True = term188.
Proof. exact (SYM (@lem3158313)). Qed.
Lemma lem3158315 : term188.
Proof. exact (EQ_MP (@lem3158314) (@lem0)). Qed.
Lemma lem3158316 : term269.
Proof. exact (@lem3158305 (@lem3158315)). Qed.
Lemma lem3158318 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158319 : term236 = term239.
Proof. exact (@lem3158318 term2 term2). Qed.
Lemma lem3158320 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158321 : term172 = term2.
Proof. exact (EQ_MP (@lem3158320) (@lem940073)). Qed.
Lemma lem3158322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158323 : term170 = term93.
Proof. exact (MK_COMB (@lem3158322) (@lem3158321)). Qed.
Lemma lem3158324 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158325 : term239 = term160.
Proof. exact (MK_COMB (@lem3158324) (@lem3158323)). Qed.
Lemma lem3158326 : term236 = term160.
Proof. exact (TRANS (@lem3158319) (@lem3158325)). Qed.
Lemma lem3158328 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158329 : term169 = term170.
Proof. exact (@lem3158328 term2 term2). Qed.
Lemma lem3158330 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158331 : term172 = term2.
Proof. exact (EQ_MP (@lem3158330) (@lem940073)). Qed.
Lemma lem3158332 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158333 : term170 = term93.
Proof. exact (MK_COMB (@lem3158332) (@lem3158331)). Qed.
Lemma lem3158334 : term169 = term93.
Proof. exact (TRANS (@lem3158329) (@lem3158333)). Qed.
Lemma lem3158335 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3158336 : term194 = term95.
Proof. exact (MK_COMB (@lem3158335) (@lem3158334)). Qed.
Lemma lem3158337 : term270 = term264.
Proof. exact (MK_COMB (@lem3158336) (@lem3158326)). Qed.
Lemma lem3158339 (m : nat) : (term271 m) = term79.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem3158340 : term264 = term79.
Proof. exact (@lem3158339 term2). Qed.
Lemma lem3158341 : term270 = term79.
Proof. exact (TRANS (@lem3158337) (@lem3158340)). Qed.
Lemma lem3158342 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158343 : term272 = term273.
Proof. exact (MK_COMB (@lem3158342) (@lem3158341)). Qed.
Lemma lem3158344 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3158345 : term274 = term275.
Proof. exact (MK_COMB (@lem3158343) (@lem3158344)). Qed.
Lemma lem3158347 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3158348 : term275 = term79.
Proof. exact (@lem3158347 term2). Qed.
Lemma lem3158349 : term274 = term79.
Proof. exact (TRANS (@lem3158345) (@lem3158348)). Qed.
Lemma lem3158351 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158352 : term169 = term170.
Proof. exact (@lem3158351 term2 term2). Qed.
Lemma lem3158353 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158354 : term172 = term2.
Proof. exact (EQ_MP (@lem3158353) (@lem940073)). Qed.
Lemma lem3158355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158356 : term170 = term93.
Proof. exact (MK_COMB (@lem3158355) (@lem3158354)). Qed.
Lemma lem3158357 : term169 = term93.
Proof. exact (TRANS (@lem3158352) (@lem3158356)). Qed.
Lemma lem3158358 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3158359 : term277 = term275.
Proof. exact (MK_COMB (@lem3158358) (@lem3158357)). Qed.
Lemma lem3158361 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3158362 : term275 = term79.
Proof. exact (@lem3158361 term2). Qed.
Lemma lem3158363 : term277 = term79.
Proof. exact (TRANS (@lem3158359) (@lem3158362)). Qed.
Lemma lem3158364 : term79 = term277.
Proof. exact (SYM (@lem3158363)). Qed.
Lemma lem3158365 : term274 = term277.
Proof. exact (TRANS (@lem3158349) (@lem3158364)). Qed.
Lemma lem3158366 : term265 = term157.
Proof. exact (@lem3158316 (@lem3158365)). Qed.
Lemma lem3158367 : term264 = term157.
Proof. exact (TRANS (@lem3158282) (@lem3158366)). Qed.
Lemma lem3158369 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3158370 : term157 = term79.
Proof. exact (@lem3158369 term79). Qed.
Lemma lem3158371 : term264 = term79.
Proof. exact (TRANS (@lem3158367) (@lem3158370)). Qed.
Lemma lem3158372 (_32603 : int) : (term242 _32603) = (term242 _32603).
Proof. exact (eq_refl (term242 _32603)). Qed.
Lemma lem3158373 (_32603 : int) : (term262 _32603) = (term278 _32603).
Proof. exact (MK_COMB (@lem3158372 _32603) (@lem3158371)). Qed.
Lemma lem3158374 (_32603 : int) : (term261 _32603) = (term278 _32603).
Proof. exact (TRANS (@lem3158273 _32603) (@lem3158373 _32603)). Qed.
Lemma lem3158375 (_32603 : int) : (term278 _32603) = (term263 _32603).
Proof. exact (@lem1982723 (term263 _32603)). Qed.
Lemma lem3158376 (_32603 : int) : (term261 _32603) = (term263 _32603).
Proof. exact (TRANS (@lem3158374 _32603) (@lem3158375 _32603)). Qed.
Lemma lem3158377 (_32603 : int) : (term260 _32603) = (term263 _32603).
Proof. exact (TRANS (@lem3158272 _32603) (@lem3158376 _32603)). Qed.
Lemma lem3158379 (_32603 : int) : (term259 _32603) = (term263 _32603).
Proof. exact (TRANS (@lem3158227 _32603) (@lem3158377 _32603)). Qed.
Lemma lem3158380 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3158381 (_32603 : int) : (term279 _32603) = (term280 _32603).
Proof. exact (MK_COMB (@lem3158380) (@lem3158379 _32603)). Qed.
Lemma lem3158382 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158383 (_32603 : int) : (term258 _32603) = (term281 _32603).
Proof. exact (MK_COMB (@lem3158381 _32603) (@lem3158382)). Qed.
Lemma lem3158384 (_32603 : int) : (term130 _32603) = (term281 _32603).
Proof. exact (TRANS (@lem3158215 _32603) (@lem3158383 _32603)). Qed.
Lemma lem3158385 (_32603 : int) : (term99 _32603) = (term181 _32603).
Proof. exact (@lem1988287 (real_of_int _32603) term96). Qed.
Lemma lem3158392 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158393 : term93 = term182.
Proof. exact (@lem3158392 term2). Qed.
Lemma lem3158395 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158396 : term93 = term182.
Proof. exact (@lem3158395 term2). Qed.
Lemma lem3158397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3158398 : term95 = term183.
Proof. exact (MK_COMB (@lem3158397) (@lem3158396)). Qed.
Lemma lem3158399 : term96 = term184.
Proof. exact (MK_COMB (@lem3158398) (@lem3158393)). Qed.
Lemma lem3158400 : term185.
Proof. exact (@lem1981473 term93 term93 term93 term93 term186 term93). Qed.
Lemma lem3158402 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3158403 : term188 = term189.
Proof. exact (@lem3158402 (NUMERAL 0) term2). Qed.
Lemma lem3158404 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3158405 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3158406 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3158405 h1) (fun h1 : term189 = True => @lem3158404)). Qed.
Lemma lem3158407 : term189 = True.
Proof. exact (EQ_MP (@lem3158406) (@lem3158404)). Qed.
Lemma lem3158408 : term188 = True.
Proof. exact (TRANS (@lem3158403) (@lem3158407)). Qed.
Lemma lem3158409 : True = term188.
Proof. exact (SYM (@lem3158408)). Qed.
Lemma lem3158410 : term188.
Proof. exact (EQ_MP (@lem3158409) (@lem0)). Qed.
Lemma lem3158411 : term191.
Proof. exact (@lem3158400 (@lem3158410)). Qed.
Lemma lem3158413 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3158414 : term188 = term189.
Proof. exact (@lem3158413 (NUMERAL 0) term2). Qed.
Lemma lem3158415 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3158416 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3158417 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3158416 h1) (fun h1 : term189 = True => @lem3158415)). Qed.
Lemma lem3158418 : term189 = True.
Proof. exact (EQ_MP (@lem3158417) (@lem3158415)). Qed.
Lemma lem3158419 : term188 = True.
Proof. exact (TRANS (@lem3158414) (@lem3158418)). Qed.
Lemma lem3158420 : True = term188.
Proof. exact (SYM (@lem3158419)). Qed.
Lemma lem3158421 : term188.
Proof. exact (EQ_MP (@lem3158420) (@lem0)). Qed.
Lemma lem3158422 : term192.
Proof. exact (@lem3158411 (@lem3158421)). Qed.
Lemma lem3158424 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3158425 : term188 = term189.
Proof. exact (@lem3158424 (NUMERAL 0) term2). Qed.
Lemma lem3158426 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3158427 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3158428 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3158427 h1) (fun h1 : term189 = True => @lem3158426)). Qed.
Lemma lem3158429 : term189 = True.
Proof. exact (EQ_MP (@lem3158428) (@lem3158426)). Qed.
Lemma lem3158430 : term188 = True.
Proof. exact (TRANS (@lem3158425) (@lem3158429)). Qed.
Lemma lem3158431 : True = term188.
Proof. exact (SYM (@lem3158430)). Qed.
Lemma lem3158432 : term188.
Proof. exact (EQ_MP (@lem3158431) (@lem0)). Qed.
Lemma lem3158433 : term193.
Proof. exact (@lem3158422 (@lem3158432)). Qed.
Lemma lem3158435 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158436 : term169 = term170.
Proof. exact (@lem3158435 term2 term2). Qed.
Lemma lem3158437 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158438 : term172 = term2.
Proof. exact (EQ_MP (@lem3158437) (@lem940073)). Qed.
Lemma lem3158439 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158440 : term170 = term93.
Proof. exact (MK_COMB (@lem3158439) (@lem3158438)). Qed.
Lemma lem3158441 : term169 = term93.
Proof. exact (TRANS (@lem3158436) (@lem3158440)). Qed.
Lemma lem3158443 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158444 : term169 = term170.
Proof. exact (@lem3158443 term2 term2). Qed.
Lemma lem3158445 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158446 : term172 = term2.
Proof. exact (EQ_MP (@lem3158445) (@lem940073)). Qed.
Lemma lem3158447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158448 : term170 = term93.
Proof. exact (MK_COMB (@lem3158447) (@lem3158446)). Qed.
Lemma lem3158449 : term169 = term93.
Proof. exact (TRANS (@lem3158444) (@lem3158448)). Qed.
Lemma lem3158450 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3158451 : term194 = term95.
Proof. exact (MK_COMB (@lem3158450) (@lem3158449)). Qed.
Lemma lem3158452 : term195 = term96.
Proof. exact (MK_COMB (@lem3158451) (@lem3158441)). Qed.
Lemma lem3158453 : term96 = term196.
Proof. exact (@lem1367770 term2 term2). Qed.
Lemma lem3158454 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3158455 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3158456 : term199 = term200.
Proof. exact (EQ_MP (@lem3158455) (@lem3158454)). Qed.
Lemma lem3158457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158458 : term196 = term186.
Proof. exact (MK_COMB (@lem3158457) (@lem3158456)). Qed.
Lemma lem3158459 : term96 = term186.
Proof. exact (TRANS (@lem3158453) (@lem3158458)). Qed.
Lemma lem3158460 : term195 = term186.
Proof. exact (TRANS (@lem3158452) (@lem3158459)). Qed.
Lemma lem3158461 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158462 : term201 = term202.
Proof. exact (MK_COMB (@lem3158461) (@lem3158460)). Qed.
Lemma lem3158463 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3158464 : term203 = term204.
Proof. exact (MK_COMB (@lem3158462) (@lem3158463)). Qed.
Lemma lem3158466 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158467 : term204 = term205.
Proof. exact (@lem3158466 term200 term2). Qed.
Lemma lem3158468 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3158469 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3158470 : term207 = term200.
Proof. exact (EQ_MP (@lem3158469) (@lem3158468)). Qed.
Lemma lem3158471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158472 : term205 = term186.
Proof. exact (MK_COMB (@lem3158471) (@lem3158470)). Qed.
Lemma lem3158473 : term204 = term186.
Proof. exact (TRANS (@lem3158467) (@lem3158472)). Qed.
Lemma lem3158474 : term203 = term186.
Proof. exact (TRANS (@lem3158464) (@lem3158473)). Qed.
Lemma lem3158476 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158477 : term169 = term170.
Proof. exact (@lem3158476 term2 term2). Qed.
Lemma lem3158478 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158479 : term172 = term2.
Proof. exact (EQ_MP (@lem3158478) (@lem940073)). Qed.
Lemma lem3158480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158481 : term170 = term93.
Proof. exact (MK_COMB (@lem3158480) (@lem3158479)). Qed.
Lemma lem3158482 : term169 = term93.
Proof. exact (TRANS (@lem3158477) (@lem3158481)). Qed.
Lemma lem3158483 : term202 = term202.
Proof. exact (eq_refl term202). Qed.
Lemma lem3158484 : term208 = term204.
Proof. exact (MK_COMB (@lem3158483) (@lem3158482)). Qed.
Lemma lem3158486 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158487 : term204 = term205.
Proof. exact (@lem3158486 term200 term2). Qed.
Lemma lem3158488 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3158489 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3158490 : term207 = term200.
Proof. exact (EQ_MP (@lem3158489) (@lem3158488)). Qed.
Lemma lem3158491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158492 : term205 = term186.
Proof. exact (MK_COMB (@lem3158491) (@lem3158490)). Qed.
Lemma lem3158493 : term204 = term186.
Proof. exact (TRANS (@lem3158487) (@lem3158492)). Qed.
Lemma lem3158494 : term208 = term186.
Proof. exact (TRANS (@lem3158484) (@lem3158493)). Qed.
Lemma lem3158495 : term186 = term208.
Proof. exact (SYM (@lem3158494)). Qed.
Lemma lem3158496 : term203 = term208.
Proof. exact (TRANS (@lem3158474) (@lem3158495)). Qed.
Lemma lem3158497 : term184 = term209.
Proof. exact (@lem3158433 (@lem3158496)). Qed.
Lemma lem3158498 : term96 = term209.
Proof. exact (TRANS (@lem3158399) (@lem3158497)). Qed.
Lemma lem3158500 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3158501 : term209 = term186.
Proof. exact (@lem3158500 term186). Qed.
Lemma lem3158503 : term96 = term186.
Proof. exact (TRANS (@lem3158498) (@lem3158501)). Qed.
Lemma lem3158506 (_32603 : int) : (term210 _32603) = (term210 _32603).
Proof. exact (eq_refl (term210 _32603)). Qed.
Lemma lem3158507 (_32603 : int) : (term211 _32603) = (term212 _32603).
Proof. exact (MK_COMB (@lem3158506 _32603) (@lem3158503)). Qed.
Lemma lem3158508 (_32603 : int) : (term212 _32603) = (term213 _32603).
Proof. exact (@lem1982792 (real_of_int _32603) term186). Qed.
Lemma lem3158510 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158511 : term186 = term209.
Proof. exact (@lem3158510 term200). Qed.
Lemma lem3158513 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158514 : term160 = term161.
Proof. exact (@lem3158513 term2). Qed.
Lemma lem3158515 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158516 : term162 = term163.
Proof. exact (MK_COMB (@lem3158515) (@lem3158514)). Qed.
Lemma lem3158517 : term214 = term215.
Proof. exact (MK_COMB (@lem3158516) (@lem3158511)). Qed.
Lemma lem3158518 : term215 = term216.
Proof. exact (@lem1981613 term160 term186 term93 term93). Qed.
Lemma lem3158520 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158521 : term169 = term170.
Proof. exact (@lem3158520 term2 term2). Qed.
Lemma lem3158522 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158523 : term172 = term2.
Proof. exact (EQ_MP (@lem3158522) (@lem940073)). Qed.
Lemma lem3158524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158525 : term170 = term93.
Proof. exact (MK_COMB (@lem3158524) (@lem3158523)). Qed.
Lemma lem3158526 : term169 = term93.
Proof. exact (TRANS (@lem3158521) (@lem3158525)). Qed.
Lemma lem3158528 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158529 : term214 = term219.
Proof. exact (@lem3158528 term2 term200). Qed.
Lemma lem3158530 : term220 = term198.
Proof. exact (@lem996238 term198). Qed.
Lemma lem3158531 : (term220 = term198) = (term221 = term200).
Proof. exact (@lem1007663 (BIT1 0) term198 term198). Qed.
Lemma lem3158532 : term221 = term200.
Proof. exact (EQ_MP (@lem3158531) (@lem3158530)). Qed.
Lemma lem3158533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158534 : term222 = term186.
Proof. exact (MK_COMB (@lem3158533) (@lem3158532)). Qed.
Lemma lem3158535 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158536 : term219 = term223.
Proof. exact (MK_COMB (@lem3158535) (@lem3158534)). Qed.
Lemma lem3158537 : term214 = term223.
Proof. exact (TRANS (@lem3158529) (@lem3158536)). Qed.
Lemma lem3158538 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158539 : term224 = term225.
Proof. exact (MK_COMB (@lem3158538) (@lem3158537)). Qed.
Lemma lem3158540 : term216 = term226.
Proof. exact (MK_COMB (@lem3158539) (@lem3158526)). Qed.
Lemma lem3158541 : term215 = term226.
Proof. exact (TRANS (@lem3158518) (@lem3158540)). Qed.
Lemma lem3158542 : term214 = term226.
Proof. exact (TRANS (@lem3158517) (@lem3158541)). Qed.
Lemma lem3158544 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158545 : term226 = term223.
Proof. exact (@lem3158544 term223). Qed.
Lemma lem3158546 : term214 = term223.
Proof. exact (TRANS (@lem3158542) (@lem3158545)). Qed.
Lemma lem3158547 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3158550 (_32603 : int) : (term213 _32603) = (term227 _32603).
Proof. exact (MK_COMB (@lem3158547 _32603) (@lem3158546)). Qed.
Lemma lem3158551 (_32603 : int) : (term212 _32603) = (term227 _32603).
Proof. exact (TRANS (@lem3158508 _32603) (@lem3158550 _32603)). Qed.
Lemma lem3158552 (_32603 : int) : (term211 _32603) = (term227 _32603).
Proof. exact (TRANS (@lem3158507 _32603) (@lem3158551 _32603)). Qed.
Lemma lem3158553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3158554 (_32603 : int) : (term228 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3158553) (@lem3158552 _32603)). Qed.
Lemma lem3158555 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158556 (_32603 : int) : (term181 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3158554 _32603) (@lem3158555)). Qed.
Lemma lem3158557 (_32603 : int) : (term99 _32603) = (term230 _32603).
Proof. exact (TRANS (@lem3158385 _32603) (@lem3158556 _32603)). Qed.
Lemma lem3158558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158559 (_32603 : int) : (term132 _32603) = (term282 _32603).
Proof. exact (MK_COMB (@lem3158558) (@lem3158384 _32603)). Qed.
Lemma lem3158560 (_32603 : int) : (term133 _32603) = (term283 _32603).
Proof. exact (MK_COMB (@lem3158559 _32603) (@lem3158557 _32603)). Qed.
Lemma lem3158561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3158562 (_32603 : int) : (term135 _32603) = (term284 _32603).
Proof. exact (MK_COMB (@lem3158561) (@lem3158214 _32603)). Qed.
Lemma lem3158563 (_32603 : int) : (term136 _32603) = (term285 _32603).
Proof. exact (MK_COMB (@lem3158562 _32603) (@lem3158560 _32603)). Qed.
Lemma lem3158564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158565 (_32603 : int) : (term137 _32603) = (term286 _32603).
Proof. exact (MK_COMB (@lem3158564) (@lem3158083 _32603)). Qed.
Lemma lem3158566 (_32603 : int) : (term138 _32603) = (term287 _32603).
Proof. exact (MK_COMB (@lem3158565 _32603) (@lem3158563 _32603)). Qed.
Lemma lem3158567 (_32603 : int) : (term141 _32603) = (term288 _32603).
Proof. exact (@lem1988287 term93 (real_of_int _32603)). Qed.
Lemma lem3158573 (_32603 : int) : (term289 _32603) = (term290 _32603).
Proof. exact (@lem1982792 term93 (real_of_int _32603)). Qed.
Lemma lem3158578 (_32603 : int) : (term290 _32603) = (term291 _32603).
Proof. exact (@lem1982761 (term263 _32603) term93). Qed.
Lemma lem3158580 (_32603 : int) : (term289 _32603) = (term291 _32603).
Proof. exact (TRANS (@lem3158573 _32603) (@lem3158578 _32603)). Qed.
Lemma lem3158581 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3158582 (_32603 : int) : (term292 _32603) = (term293 _32603).
Proof. exact (MK_COMB (@lem3158581) (@lem3158580 _32603)). Qed.
Lemma lem3158583 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158584 (_32603 : int) : (term288 _32603) = (term294 _32603).
Proof. exact (MK_COMB (@lem3158582 _32603) (@lem3158583)). Qed.
Lemma lem3158585 (_32603 : int) : (term141 _32603) = (term294 _32603).
Proof. exact (TRANS (@lem3158567 _32603) (@lem3158584 _32603)). Qed.
Lemma lem3158586 (_32603 : int) : ((real_of_int _32603) = term79) = ((term154 _32603) = term79).
Proof. exact (@lem1988293 (real_of_int _32603) term79). Qed.
Lemma lem3158592 (_32603 : int) : (term154 _32603) = (term155 _32603).
Proof. exact (@lem1982792 (real_of_int _32603) term79). Qed.
Lemma lem3158594 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158595 : term79 = term157.
Proof. exact (@lem3158594 (NUMERAL 0)). Qed.
Lemma lem3158597 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158598 : term160 = term161.
Proof. exact (@lem3158597 term2). Qed.
Lemma lem3158599 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158600 : term162 = term163.
Proof. exact (MK_COMB (@lem3158599) (@lem3158598)). Qed.
Lemma lem3158601 : term164 = term165.
Proof. exact (MK_COMB (@lem3158600) (@lem3158595)). Qed.
Lemma lem3158602 : term165 = term166.
Proof. exact (@lem1981613 term160 term79 term93 term93). Qed.
Lemma lem3158604 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158605 : term169 = term170.
Proof. exact (@lem3158604 term2 term2). Qed.
Lemma lem3158606 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158607 : term172 = term2.
Proof. exact (EQ_MP (@lem3158606) (@lem940073)). Qed.
Lemma lem3158608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158609 : term170 = term93.
Proof. exact (MK_COMB (@lem3158608) (@lem3158607)). Qed.
Lemma lem3158610 : term169 = term93.
Proof. exact (TRANS (@lem3158605) (@lem3158609)). Qed.
Lemma lem3158612 (x : nat) : (term173 x) = term79.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3158613 : term164 = term79.
Proof. exact (@lem3158612 term2). Qed.
Lemma lem3158614 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158615 : term174 = term175.
Proof. exact (MK_COMB (@lem3158614) (@lem3158613)). Qed.
Lemma lem3158616 : term166 = term157.
Proof. exact (MK_COMB (@lem3158615) (@lem3158610)). Qed.
Lemma lem3158617 : term165 = term157.
Proof. exact (TRANS (@lem3158602) (@lem3158616)). Qed.
Lemma lem3158618 : term164 = term157.
Proof. exact (TRANS (@lem3158601) (@lem3158617)). Qed.
Lemma lem3158620 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158621 : term157 = term79.
Proof. exact (@lem3158620 term79). Qed.
Lemma lem3158622 : term164 = term79.
Proof. exact (TRANS (@lem3158618) (@lem3158621)). Qed.
Lemma lem3158623 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3158624 (_32603 : int) : (term155 _32603) = (term177 _32603).
Proof. exact (MK_COMB (@lem3158623 _32603) (@lem3158622)). Qed.
Lemma lem3158625 (_32603 : int) : (term177 _32603) = (real_of_int _32603).
Proof. exact (@lem1982723 (real_of_int _32603)). Qed.
Lemma lem3158626 (_32603 : int) : (term155 _32603) = (real_of_int _32603).
Proof. exact (TRANS (@lem3158624 _32603) (@lem3158625 _32603)). Qed.
Lemma lem3158628 (_32603 : int) : (term154 _32603) = (real_of_int _32603).
Proof. exact (TRANS (@lem3158592 _32603) (@lem3158626 _32603)). Qed.
Lemma lem3158629 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3158630 (_32603 : int) : (term295 _32603) = (term142 _32603).
Proof. exact (MK_COMB (@lem3158629) (@lem3158628 _32603)). Qed.
Lemma lem3158631 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158632 (_32603 : int) : ((term154 _32603) = term79) = ((real_of_int _32603) = term79).
Proof. exact (MK_COMB (@lem3158630 _32603) (@lem3158631)). Qed.
Lemma lem3158633 (_32603 : int) : ((real_of_int _32603) = term79) = ((real_of_int _32603) = term79).
Proof. exact (TRANS (@lem3158586 _32603) (@lem3158632 _32603)). Qed.
Lemma lem3158634 (_32603 : int) : ((real_of_int _32603) = term93) = ((term250 _32603) = term79).
Proof. exact (@lem1988293 (real_of_int _32603) term93). Qed.
Lemma lem3158640 (_32603 : int) : (term250 _32603) = (term251 _32603).
Proof. exact (@lem1982792 (real_of_int _32603) term93). Qed.
Lemma lem3158642 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3158643 : term93 = term182.
Proof. exact (@lem3158642 term2). Qed.
Lemma lem3158645 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3158646 : term160 = term161.
Proof. exact (@lem3158645 term2). Qed.
Lemma lem3158647 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3158648 : term162 = term163.
Proof. exact (MK_COMB (@lem3158647) (@lem3158646)). Qed.
Lemma lem3158649 : term236 = term237.
Proof. exact (MK_COMB (@lem3158648) (@lem3158643)). Qed.
Lemma lem3158650 : term237 = term238.
Proof. exact (@lem1981613 term160 term93 term93 term93). Qed.
Lemma lem3158652 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3158653 : term169 = term170.
Proof. exact (@lem3158652 term2 term2). Qed.
Lemma lem3158654 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158655 : term172 = term2.
Proof. exact (EQ_MP (@lem3158654) (@lem940073)). Qed.
Lemma lem3158656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158657 : term170 = term93.
Proof. exact (MK_COMB (@lem3158656) (@lem3158655)). Qed.
Lemma lem3158658 : term169 = term93.
Proof. exact (TRANS (@lem3158653) (@lem3158657)). Qed.
Lemma lem3158660 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3158661 : term236 = term239.
Proof. exact (@lem3158660 term2 term2). Qed.
Lemma lem3158662 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3158663 : term172 = term2.
Proof. exact (EQ_MP (@lem3158662) (@lem940073)). Qed.
Lemma lem3158664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3158665 : term170 = term93.
Proof. exact (MK_COMB (@lem3158664) (@lem3158663)). Qed.
Lemma lem3158666 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3158667 : term239 = term160.
Proof. exact (MK_COMB (@lem3158666) (@lem3158665)). Qed.
Lemma lem3158668 : term236 = term160.
Proof. exact (TRANS (@lem3158661) (@lem3158667)). Qed.
Lemma lem3158669 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3158670 : term240 = term241.
Proof. exact (MK_COMB (@lem3158669) (@lem3158668)). Qed.
Lemma lem3158671 : term238 = term161.
Proof. exact (MK_COMB (@lem3158670) (@lem3158658)). Qed.
Lemma lem3158672 : term237 = term161.
Proof. exact (TRANS (@lem3158650) (@lem3158671)). Qed.
Lemma lem3158673 : term236 = term161.
Proof. exact (TRANS (@lem3158649) (@lem3158672)). Qed.
Lemma lem3158675 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3158676 : term161 = term160.
Proof. exact (@lem3158675 term160). Qed.
Lemma lem3158677 : term236 = term160.
Proof. exact (TRANS (@lem3158673) (@lem3158676)). Qed.
Lemma lem3158678 (_32603 : int) : (term108 _32603) = (term108 _32603).
Proof. exact (eq_refl (term108 _32603)). Qed.
Lemma lem3158681 (_32603 : int) : (term251 _32603) = (term252 _32603).
Proof. exact (MK_COMB (@lem3158678 _32603) (@lem3158677)). Qed.
Lemma lem3158683 (_32603 : int) : (term250 _32603) = (term252 _32603).
Proof. exact (TRANS (@lem3158640 _32603) (@lem3158681 _32603)). Qed.
Lemma lem3158684 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3158685 (_32603 : int) : (term296 _32603) = (term297 _32603).
Proof. exact (MK_COMB (@lem3158684) (@lem3158683 _32603)). Qed.
Lemma lem3158686 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3158687 (_32603 : int) : ((term250 _32603) = term79) = ((term252 _32603) = term79).
Proof. exact (MK_COMB (@lem3158685 _32603) (@lem3158686)). Qed.
Lemma lem3158688 (_32603 : int) : ((real_of_int _32603) = term93) = ((term252 _32603) = term79).
Proof. exact (TRANS (@lem3158634 _32603) (@lem3158687 _32603)). Qed.
Lemma lem3158689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158690 (_32603 : int) : (term143 _32603) = (term143 _32603).
Proof. exact (MK_COMB (@lem3158689) (@lem3158633 _32603)). Qed.
Lemma lem3158691 (_32603 : int) : (term144 _32603) = (term298 _32603).
Proof. exact (MK_COMB (@lem3158690 _32603) (@lem3158688 _32603)). Qed.
Lemma lem3158692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158693 (_32603 : int) : (term145 _32603) = (term299 _32603).
Proof. exact (MK_COMB (@lem3158692) (@lem3158585 _32603)). Qed.
Lemma lem3158694 (_32603 : int) : (term146 _32603) = (term300 _32603).
Proof. exact (MK_COMB (@lem3158693 _32603) (@lem3158691 _32603)). Qed.
Lemma lem3158695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3158696 (_32603 : int) : (term147 _32603) = (term301 _32603).
Proof. exact (MK_COMB (@lem3158695) (@lem3158566 _32603)). Qed.
Lemma lem3158697 (_32603 : int) : (term148 _32603) = (term302 _32603).
Proof. exact (MK_COMB (@lem3158696 _32603) (@lem3158694 _32603)). Qed.
Lemma lem3158698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3158699 (_32603 : int) : (term149 _32603) = (term303 _32603).
Proof. exact (MK_COMB (@lem3158698) (@lem3157910 _32603)). Qed.
Lemma lem3158700 (_32603 : int) : (term150 _32603) = (term304 _32603).
Proof. exact (MK_COMB (@lem3158699 _32603) (@lem3158697 _32603)). Qed.
Lemma lem3158707 (_32603 : int) : (term152 _32603) = (term304 _32603).
Proof. exact (TRANS (@lem3157862 _32603) (@lem3158700 _32603)). Qed.
Lemma lem3158716 (_32603 : int) : (term300 _32603) = (term300 _32603).
Proof. exact (eq_refl (term300 _32603)). Qed.
Lemma lem3158730 (_32603 : int) : (term285 _32603) = (term305 _32603).
Proof. exact (@lem19158 (term281 _32603) (term257 _32603) (term230 _32603)). Qed.
Lemma lem3158737 (_32603 : int) : (term306 _32603) = (term307 _32603).
Proof. exact (@lem19367 (term247 _32603) (term255 _32603) (term230 _32603)). Qed.
Lemma lem3158744 (_32603 : int) : (term308 _32603) = (term309 _32603).
Proof. exact (@lem19367 (term247 _32603) (term255 _32603) (term281 _32603)). Qed.
Lemma lem3158745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158746 (_32603 : int) : (term310 _32603) = (term311 _32603).
Proof. exact (MK_COMB (@lem3158745) (@lem3158744 _32603)). Qed.
Lemma lem3158747 (_32603 : int) : (term305 _32603) = (term312 _32603).
Proof. exact (MK_COMB (@lem3158746 _32603) (@lem3158737 _32603)). Qed.
Lemma lem3158749 (_32603 : int) : (term285 _32603) = (term312 _32603).
Proof. exact (TRANS (@lem3158730 _32603) (@lem3158747 _32603)). Qed.
Lemma lem3158752 (_32603 : int) : (term286 _32603) = (term286 _32603).
Proof. exact (eq_refl (term286 _32603)). Qed.
Lemma lem3158753 (_32603 : int) : (term287 _32603) = (term313 _32603).
Proof. exact (MK_COMB (@lem3158752 _32603) (@lem3158749 _32603)). Qed.
Lemma lem3158754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3158755 (_32603 : int) : (term301 _32603) = (term314 _32603).
Proof. exact (MK_COMB (@lem3158754) (@lem3158753 _32603)). Qed.
Lemma lem3158756 (_32603 : int) : (term302 _32603) = (term315 _32603).
Proof. exact (MK_COMB (@lem3158755 _32603) (@lem3158716 _32603)). Qed.
Lemma lem3158757 (_32603 : int) : (term315 _32603) = (term316 _32603).
Proof. exact (@lem19158 (term294 _32603) (term313 _32603) (term298 _32603)). Qed.
Lemma lem3158758 (_32603 : int) : (term317 _32603) = (term318 _32603).
Proof. exact (@lem19158 ((real_of_int _32603) = term79) (term313 _32603) ((term252 _32603) = term79)). Qed.
Lemma lem3158759 (_32603 : int) : (term319 _32603) = (term320 _32603).
Proof. exact (@lem19367 (term230 _32603) (term312 _32603) ((term252 _32603) = term79)). Qed.
Lemma lem3158760 (_32603 : int) : (term321 _32603) = (term322 _32603).
Proof. exact (@lem19367 (term309 _32603) (term307 _32603) ((term252 _32603) = term79)). Qed.
Lemma lem3158767 (_32603 : int) : (term323 _32603) = (term324 _32603).
Proof. exact (@lem19367 (term325 _32603) (term326 _32603) ((term252 _32603) = term79)). Qed.
Lemma lem3158774 (_32603 : int) : (term327 _32603) = (term328 _32603).
Proof. exact (@lem19367 (term329 _32603) (term330 _32603) ((term252 _32603) = term79)). Qed.
Lemma lem3158775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158776 (_32603 : int) : (term331 _32603) = (term332 _32603).
Proof. exact (MK_COMB (@lem3158775) (@lem3158774 _32603)). Qed.
Lemma lem3158777 (_32603 : int) : (term322 _32603) = (term333 _32603).
Proof. exact (MK_COMB (@lem3158776 _32603) (@lem3158767 _32603)). Qed.
Lemma lem3158778 (_32603 : int) : (term321 _32603) = (term333 _32603).
Proof. exact (TRANS (@lem3158760 _32603) (@lem3158777 _32603)). Qed.
Lemma lem3158781 (_32603 : int) : (term334 _32603) = (term334 _32603).
Proof. exact (eq_refl (term334 _32603)). Qed.
Lemma lem3158782 (_32603 : int) : (term320 _32603) = (term335 _32603).
Proof. exact (MK_COMB (@lem3158781 _32603) (@lem3158778 _32603)). Qed.
Lemma lem3158783 (_32603 : int) : (term319 _32603) = (term335 _32603).
Proof. exact (TRANS (@lem3158759 _32603) (@lem3158782 _32603)). Qed.
Lemma lem3158784 (_32603 : int) : (term336 _32603) = (term337 _32603).
Proof. exact (@lem19367 (term230 _32603) (term312 _32603) ((real_of_int _32603) = term79)). Qed.
Lemma lem3158785 (_32603 : int) : (term338 _32603) = (term339 _32603).
Proof. exact (@lem19367 (term309 _32603) (term307 _32603) ((real_of_int _32603) = term79)). Qed.
Lemma lem3158792 (_32603 : int) : (term340 _32603) = (term341 _32603).
Proof. exact (@lem19367 (term325 _32603) (term326 _32603) ((real_of_int _32603) = term79)). Qed.
Lemma lem3158799 (_32603 : int) : (term342 _32603) = (term343 _32603).
Proof. exact (@lem19367 (term329 _32603) (term330 _32603) ((real_of_int _32603) = term79)). Qed.
Lemma lem3158800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158801 (_32603 : int) : (term344 _32603) = (term345 _32603).
Proof. exact (MK_COMB (@lem3158800) (@lem3158799 _32603)). Qed.
Lemma lem3158802 (_32603 : int) : (term339 _32603) = (term346 _32603).
Proof. exact (MK_COMB (@lem3158801 _32603) (@lem3158792 _32603)). Qed.
Lemma lem3158803 (_32603 : int) : (term338 _32603) = (term346 _32603).
Proof. exact (TRANS (@lem3158785 _32603) (@lem3158802 _32603)). Qed.
Lemma lem3158806 (_32603 : int) : (term347 _32603) = (term347 _32603).
Proof. exact (eq_refl (term347 _32603)). Qed.
Lemma lem3158807 (_32603 : int) : (term337 _32603) = (term348 _32603).
Proof. exact (MK_COMB (@lem3158806 _32603) (@lem3158803 _32603)). Qed.
Lemma lem3158808 (_32603 : int) : (term336 _32603) = (term348 _32603).
Proof. exact (TRANS (@lem3158784 _32603) (@lem3158807 _32603)). Qed.
Lemma lem3158809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158810 (_32603 : int) : (term349 _32603) = (term350 _32603).
Proof. exact (MK_COMB (@lem3158809) (@lem3158808 _32603)). Qed.
Lemma lem3158811 (_32603 : int) : (term318 _32603) = (term351 _32603).
Proof. exact (MK_COMB (@lem3158810 _32603) (@lem3158783 _32603)). Qed.
Lemma lem3158812 (_32603 : int) : (term317 _32603) = (term351 _32603).
Proof. exact (TRANS (@lem3158758 _32603) (@lem3158811 _32603)). Qed.
Lemma lem3158813 (_32603 : int) : (term352 _32603) = (term353 _32603).
Proof. exact (@lem19367 (term230 _32603) (term312 _32603) (term294 _32603)). Qed.
Lemma lem3158814 (_32603 : int) : (term354 _32603) = (term355 _32603).
Proof. exact (@lem19367 (term309 _32603) (term307 _32603) (term294 _32603)). Qed.
Lemma lem3158821 (_32603 : int) : (term356 _32603) = (term357 _32603).
Proof. exact (@lem19367 (term325 _32603) (term326 _32603) (term294 _32603)). Qed.
Lemma lem3158828 (_32603 : int) : (term358 _32603) = (term359 _32603).
Proof. exact (@lem19367 (term329 _32603) (term330 _32603) (term294 _32603)). Qed.
Lemma lem3158829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158830 (_32603 : int) : (term360 _32603) = (term361 _32603).
Proof. exact (MK_COMB (@lem3158829) (@lem3158828 _32603)). Qed.
Lemma lem3158831 (_32603 : int) : (term355 _32603) = (term362 _32603).
Proof. exact (MK_COMB (@lem3158830 _32603) (@lem3158821 _32603)). Qed.
Lemma lem3158832 (_32603 : int) : (term354 _32603) = (term362 _32603).
Proof. exact (TRANS (@lem3158814 _32603) (@lem3158831 _32603)). Qed.
Lemma lem3158835 (_32603 : int) : (term363 _32603) = (term363 _32603).
Proof. exact (eq_refl (term363 _32603)). Qed.
Lemma lem3158836 (_32603 : int) : (term353 _32603) = (term364 _32603).
Proof. exact (MK_COMB (@lem3158835 _32603) (@lem3158832 _32603)). Qed.
Lemma lem3158837 (_32603 : int) : (term352 _32603) = (term364 _32603).
Proof. exact (TRANS (@lem3158813 _32603) (@lem3158836 _32603)). Qed.
Lemma lem3158838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158839 (_32603 : int) : (term365 _32603) = (term366 _32603).
Proof. exact (MK_COMB (@lem3158838) (@lem3158837 _32603)). Qed.
Lemma lem3158840 (_32603 : int) : (term316 _32603) = (term367 _32603).
Proof. exact (MK_COMB (@lem3158839 _32603) (@lem3158812 _32603)). Qed.
Lemma lem3158841 (_32603 : int) : (term315 _32603) = (term367 _32603).
Proof. exact (TRANS (@lem3158757 _32603) (@lem3158840 _32603)). Qed.
Lemma lem3158842 (_32603 : int) : (term302 _32603) = (term367 _32603).
Proof. exact (TRANS (@lem3158756 _32603) (@lem3158841 _32603)). Qed.
Lemma lem3158845 (_32603 : int) : (term303 _32603) = (term303 _32603).
Proof. exact (eq_refl (term303 _32603)). Qed.
Lemma lem3158846 (_32603 : int) : (term304 _32603) = (term368 _32603).
Proof. exact (MK_COMB (@lem3158845 _32603) (@lem3158842 _32603)). Qed.
Lemma lem3158847 (_32603 : int) : (term368 _32603) = (term369 _32603).
Proof. exact (@lem19158 (term364 _32603) (term180 _32603) (term351 _32603)). Qed.
Lemma lem3158848 (_32603 : int) : (term370 _32603) = (term371 _32603).
Proof. exact (@lem19158 (term348 _32603) (term180 _32603) (term335 _32603)). Qed.
Lemma lem3158849 (_32603 : int) : (term372 _32603) = (term373 _32603).
Proof. exact (@lem19158 (term374 _32603) (term180 _32603) (term333 _32603)). Qed.
Lemma lem3158850 (_32603 : int) : (term375 _32603) = (term376 _32603).
Proof. exact (@lem19158 (term328 _32603) (term180 _32603) (term324 _32603)). Qed.
Lemma lem3158857 (_32603 : int) : (term377 _32603) = (term378 _32603).
Proof. exact (@lem19158 (term379 _32603) (term180 _32603) (term380 _32603)). Qed.
Lemma lem3158864 (_32603 : int) : (term381 _32603) = (term382 _32603).
Proof. exact (@lem19158 (term383 _32603) (term180 _32603) (term384 _32603)). Qed.
Lemma lem3158865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158866 (_32603 : int) : (term385 _32603) = (term386 _32603).
Proof. exact (MK_COMB (@lem3158865) (@lem3158864 _32603)). Qed.
Lemma lem3158867 (_32603 : int) : (term376 _32603) = (term387 _32603).
Proof. exact (MK_COMB (@lem3158866 _32603) (@lem3158857 _32603)). Qed.
Lemma lem3158868 (_32603 : int) : (term375 _32603) = (term387 _32603).
Proof. exact (TRANS (@lem3158850 _32603) (@lem3158867 _32603)). Qed.
Lemma lem3158871 (_32603 : int) : (term388 _32603) = (term388 _32603).
Proof. exact (eq_refl (term388 _32603)). Qed.
Lemma lem3158872 (_32603 : int) : (term373 _32603) = (term389 _32603).
Proof. exact (MK_COMB (@lem3158871 _32603) (@lem3158868 _32603)). Qed.
Lemma lem3158873 (_32603 : int) : (term372 _32603) = (term389 _32603).
Proof. exact (TRANS (@lem3158849 _32603) (@lem3158872 _32603)). Qed.
Lemma lem3158874 (_32603 : int) : (term390 _32603) = (term391 _32603).
Proof. exact (@lem19158 (term392 _32603) (term180 _32603) (term346 _32603)). Qed.
Lemma lem3158875 (_32603 : int) : (term393 _32603) = (term394 _32603).
Proof. exact (@lem19158 (term343 _32603) (term180 _32603) (term341 _32603)). Qed.
Lemma lem3158882 (_32603 : int) : (term395 _32603) = (term396 _32603).
Proof. exact (@lem19158 (term397 _32603) (term180 _32603) (term398 _32603)). Qed.
Lemma lem3158889 (_32603 : int) : (term399 _32603) = (term400 _32603).
Proof. exact (@lem19158 (term401 _32603) (term180 _32603) (term402 _32603)). Qed.
Lemma lem3158890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158891 (_32603 : int) : (term403 _32603) = (term404 _32603).
Proof. exact (MK_COMB (@lem3158890) (@lem3158889 _32603)). Qed.
Lemma lem3158892 (_32603 : int) : (term394 _32603) = (term405 _32603).
Proof. exact (MK_COMB (@lem3158891 _32603) (@lem3158882 _32603)). Qed.
Lemma lem3158893 (_32603 : int) : (term393 _32603) = (term405 _32603).
Proof. exact (TRANS (@lem3158875 _32603) (@lem3158892 _32603)). Qed.
Lemma lem3158896 (_32603 : int) : (term406 _32603) = (term406 _32603).
Proof. exact (eq_refl (term406 _32603)). Qed.
Lemma lem3158897 (_32603 : int) : (term391 _32603) = (term407 _32603).
Proof. exact (MK_COMB (@lem3158896 _32603) (@lem3158893 _32603)). Qed.
Lemma lem3158898 (_32603 : int) : (term390 _32603) = (term407 _32603).
Proof. exact (TRANS (@lem3158874 _32603) (@lem3158897 _32603)). Qed.
Lemma lem3158899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158900 (_32603 : int) : (term408 _32603) = (term409 _32603).
Proof. exact (MK_COMB (@lem3158899) (@lem3158898 _32603)). Qed.
Lemma lem3158901 (_32603 : int) : (term371 _32603) = (term410 _32603).
Proof. exact (MK_COMB (@lem3158900 _32603) (@lem3158873 _32603)). Qed.
Lemma lem3158902 (_32603 : int) : (term370 _32603) = (term410 _32603).
Proof. exact (TRANS (@lem3158848 _32603) (@lem3158901 _32603)). Qed.
Lemma lem3158903 (_32603 : int) : (term411 _32603) = (term412 _32603).
Proof. exact (@lem19158 (term413 _32603) (term180 _32603) (term362 _32603)). Qed.
Lemma lem3158904 (_32603 : int) : (term414 _32603) = (term415 _32603).
Proof. exact (@lem19158 (term359 _32603) (term180 _32603) (term357 _32603)). Qed.
Lemma lem3158911 (_32603 : int) : (term416 _32603) = (term417 _32603).
Proof. exact (@lem19158 (term418 _32603) (term180 _32603) (term419 _32603)). Qed.
Lemma lem3158918 (_32603 : int) : (term420 _32603) = (term421 _32603).
Proof. exact (@lem19158 (term422 _32603) (term180 _32603) (term423 _32603)). Qed.
Lemma lem3158919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158920 (_32603 : int) : (term424 _32603) = (term425 _32603).
Proof. exact (MK_COMB (@lem3158919) (@lem3158918 _32603)). Qed.
Lemma lem3158921 (_32603 : int) : (term415 _32603) = (term426 _32603).
Proof. exact (MK_COMB (@lem3158920 _32603) (@lem3158911 _32603)). Qed.
Lemma lem3158922 (_32603 : int) : (term414 _32603) = (term426 _32603).
Proof. exact (TRANS (@lem3158904 _32603) (@lem3158921 _32603)). Qed.
Lemma lem3158925 (_32603 : int) : (term427 _32603) = (term427 _32603).
Proof. exact (eq_refl (term427 _32603)). Qed.
Lemma lem3158926 (_32603 : int) : (term412 _32603) = (term428 _32603).
Proof. exact (MK_COMB (@lem3158925 _32603) (@lem3158922 _32603)). Qed.
Lemma lem3158927 (_32603 : int) : (term411 _32603) = (term428 _32603).
Proof. exact (TRANS (@lem3158903 _32603) (@lem3158926 _32603)). Qed.
Lemma lem3158928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3158929 (_32603 : int) : (term429 _32603) = (term430 _32603).
Proof. exact (MK_COMB (@lem3158928) (@lem3158927 _32603)). Qed.
Lemma lem3158930 (_32603 : int) : (term369 _32603) = (term431 _32603).
Proof. exact (MK_COMB (@lem3158929 _32603) (@lem3158902 _32603)). Qed.
Lemma lem3158931 (_32603 : int) : (term368 _32603) = (term431 _32603).
Proof. exact (TRANS (@lem3158847 _32603) (@lem3158930 _32603)). Qed.
Lemma lem3158932 (_32603 : int) : (term304 _32603) = (term431 _32603).
Proof. exact (TRANS (@lem3158846 _32603) (@lem3158931 _32603)). Qed.
Lemma lem3158933 (_32603 : int) : (term152 _32603) = (term431 _32603).
Proof. exact (TRANS (@lem3158707 _32603) (@lem3158932 _32603)). Qed.
Lemma lem3159021 (_32603 : int) (h1 : term431 _32603) : term431 _32603.
Proof. exact (h1). Qed.
Lemma lem3159022 (_32603 : int) (h1 : term428 _32603) : term428 _32603.
Proof. exact (h1). Qed.
Lemma lem3159023 (_32603 : int) (h1 : term432 _32603) : term432 _32603.
Proof. exact (h1). Qed.
Lemma lem3159024 (_32603 : int) (h1 : term432 _32603) : term413 _32603.
Proof. exact (proj2 (@lem3159023 _32603 h1)). Qed.
Lemma lem3159026 (_32603 : int) (h1 : term432 _32603) : term294 _32603.
Proof. exact (proj2 (@lem3159024 _32603 h1)). Qed.
Lemma lem3159027 (_32603 : int) (h1 : term432 _32603) : term230 _32603.
Proof. exact (proj1 (@lem3159024 _32603 h1)). Qed.
Lemma lem3159029 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3159030 : term433 = term188.
Proof. exact (@lem3159029 term79 term93). Qed.
Lemma lem3159032 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159033 : term93 = term182.
Proof. exact (@lem3159032 term2). Qed.
Lemma lem3159035 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159036 : term79 = term157.
Proof. exact (@lem3159035 (NUMERAL 0)). Qed.
Lemma lem3159037 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159038 : term434 = term435.
Proof. exact (MK_COMB (@lem3159037) (@lem3159036)). Qed.
Lemma lem3159039 : term188 = term436.
Proof. exact (MK_COMB (@lem3159038) (@lem3159033)). Qed.
Lemma lem3159040 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3159042 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159043 : term188 = term189.
Proof. exact (@lem3159042 (NUMERAL 0) term2). Qed.
Lemma lem3159044 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159045 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159046 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159045 h1) (fun h1 : term189 = True => @lem3159044)). Qed.
Lemma lem3159047 : term189 = True.
Proof. exact (EQ_MP (@lem3159046) (@lem3159044)). Qed.
Lemma lem3159048 : term188 = True.
Proof. exact (TRANS (@lem3159043) (@lem3159047)). Qed.
Lemma lem3159049 : True = term188.
Proof. exact (SYM (@lem3159048)). Qed.
Lemma lem3159050 : term188.
Proof. exact (EQ_MP (@lem3159049) (@lem0)). Qed.
Lemma lem3159051 : term438.
Proof. exact (@lem3159040 (@lem3159050)). Qed.
Lemma lem3159053 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159054 : term188 = term189.
Proof. exact (@lem3159053 (NUMERAL 0) term2). Qed.
Lemma lem3159055 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159056 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159057 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159056 h1) (fun h1 : term189 = True => @lem3159055)). Qed.
Lemma lem3159058 : term189 = True.
Proof. exact (EQ_MP (@lem3159057) (@lem3159055)). Qed.
Lemma lem3159059 : term188 = True.
Proof. exact (TRANS (@lem3159054) (@lem3159058)). Qed.
Lemma lem3159060 : True = term188.
Proof. exact (SYM (@lem3159059)). Qed.
Lemma lem3159061 : term188.
Proof. exact (EQ_MP (@lem3159060) (@lem0)). Qed.
Lemma lem3159062 : term436 = term439.
Proof. exact (@lem3159051 (@lem3159061)). Qed.
Lemma lem3159064 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159065 : term169 = term170.
Proof. exact (@lem3159064 term2 term2). Qed.
Lemma lem3159066 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159067 : term172 = term2.
Proof. exact (EQ_MP (@lem3159066) (@lem940073)). Qed.
Lemma lem3159068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159069 : term170 = term93.
Proof. exact (MK_COMB (@lem3159068) (@lem3159067)). Qed.
Lemma lem3159070 : term169 = term93.
Proof. exact (TRANS (@lem3159065) (@lem3159069)). Qed.
Lemma lem3159072 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159073 : term275 = term79.
Proof. exact (@lem3159072 term2). Qed.
Lemma lem3159074 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159075 : term440 = term434.
Proof. exact (MK_COMB (@lem3159074) (@lem3159073)). Qed.
Lemma lem3159076 : term439 = term188.
Proof. exact (MK_COMB (@lem3159075) (@lem3159070)). Qed.
Lemma lem3159078 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159079 : term188 = term189.
Proof. exact (@lem3159078 (NUMERAL 0) term2). Qed.
Lemma lem3159080 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159081 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159082 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159081 h1) (fun h1 : term189 = True => @lem3159080)). Qed.
Lemma lem3159083 : term189 = True.
Proof. exact (EQ_MP (@lem3159082) (@lem3159080)). Qed.
Lemma lem3159084 : term188 = True.
Proof. exact (TRANS (@lem3159079) (@lem3159083)). Qed.
Lemma lem3159085 : term439 = True.
Proof. exact (TRANS (@lem3159076) (@lem3159084)). Qed.
Lemma lem3159086 : term436 = True.
Proof. exact (TRANS (@lem3159062) (@lem3159085)). Qed.
Lemma lem3159087 : term188 = True.
Proof. exact (TRANS (@lem3159039) (@lem3159086)). Qed.
Lemma lem3159088 : term433 = True.
Proof. exact (TRANS (@lem3159030) (@lem3159087)). Qed.
Lemma lem3159089 : True = term433.
Proof. exact (SYM (@lem3159088)). Qed.
Lemma lem3159090 : term433.
Proof. exact (EQ_MP (@lem3159089) (@lem0)). Qed.
Lemma lem3159091 (_32603 : int) (h1 : term432 _32603) : term441 _32603.
Proof. exact (conj (@lem3159090) (@lem3159027 _32603 h1)). Qed.
Lemma lem3159093 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3159094 (_32603 : int) : term443 _32603.
Proof. exact (@lem3159093 term93 (term227 _32603)). Qed.
Lemma lem3159095 (_32603 : int) (h1 : term432 _32603) : term444 _32603.
Proof. exact (@lem3159094 _32603 (@lem3159091 _32603 h1)). Qed.
Lemma lem3159096 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3159097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159098 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3159097) (@lem3159096 _32603)). Qed.
Lemma lem3159099 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159100 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3159098 _32603) (@lem3159099)). Qed.
Lemma lem3159101 (_32603 : int) (h1 : term432 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3159100 _32603) (@lem3159095 _32603 h1)). Qed.
Lemma lem3159103 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3159104 : term433 = term188.
Proof. exact (@lem3159103 term79 term93). Qed.
Lemma lem3159106 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159107 : term93 = term182.
Proof. exact (@lem3159106 term2). Qed.
Lemma lem3159109 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159110 : term79 = term157.
Proof. exact (@lem3159109 (NUMERAL 0)). Qed.
Lemma lem3159111 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159112 : term434 = term435.
Proof. exact (MK_COMB (@lem3159111) (@lem3159110)). Qed.
Lemma lem3159113 : term188 = term436.
Proof. exact (MK_COMB (@lem3159112) (@lem3159107)). Qed.
Lemma lem3159114 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3159116 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159117 : term188 = term189.
Proof. exact (@lem3159116 (NUMERAL 0) term2). Qed.
Lemma lem3159118 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159119 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159120 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159119 h1) (fun h1 : term189 = True => @lem3159118)). Qed.
Lemma lem3159121 : term189 = True.
Proof. exact (EQ_MP (@lem3159120) (@lem3159118)). Qed.
Lemma lem3159122 : term188 = True.
Proof. exact (TRANS (@lem3159117) (@lem3159121)). Qed.
Lemma lem3159123 : True = term188.
Proof. exact (SYM (@lem3159122)). Qed.
Lemma lem3159124 : term188.
Proof. exact (EQ_MP (@lem3159123) (@lem0)). Qed.
Lemma lem3159125 : term438.
Proof. exact (@lem3159114 (@lem3159124)). Qed.
Lemma lem3159127 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159128 : term188 = term189.
Proof. exact (@lem3159127 (NUMERAL 0) term2). Qed.
Lemma lem3159129 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159130 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159131 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159130 h1) (fun h1 : term189 = True => @lem3159129)). Qed.
Lemma lem3159132 : term189 = True.
Proof. exact (EQ_MP (@lem3159131) (@lem3159129)). Qed.
Lemma lem3159133 : term188 = True.
Proof. exact (TRANS (@lem3159128) (@lem3159132)). Qed.
Lemma lem3159134 : True = term188.
Proof. exact (SYM (@lem3159133)). Qed.
Lemma lem3159135 : term188.
Proof. exact (EQ_MP (@lem3159134) (@lem0)). Qed.
Lemma lem3159136 : term436 = term439.
Proof. exact (@lem3159125 (@lem3159135)). Qed.
Lemma lem3159138 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159139 : term169 = term170.
Proof. exact (@lem3159138 term2 term2). Qed.
Lemma lem3159140 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159141 : term172 = term2.
Proof. exact (EQ_MP (@lem3159140) (@lem940073)). Qed.
Lemma lem3159142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159143 : term170 = term93.
Proof. exact (MK_COMB (@lem3159142) (@lem3159141)). Qed.
Lemma lem3159144 : term169 = term93.
Proof. exact (TRANS (@lem3159139) (@lem3159143)). Qed.
Lemma lem3159146 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159147 : term275 = term79.
Proof. exact (@lem3159146 term2). Qed.
Lemma lem3159148 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159149 : term440 = term434.
Proof. exact (MK_COMB (@lem3159148) (@lem3159147)). Qed.
Lemma lem3159150 : term439 = term188.
Proof. exact (MK_COMB (@lem3159149) (@lem3159144)). Qed.
Lemma lem3159152 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159153 : term188 = term189.
Proof. exact (@lem3159152 (NUMERAL 0) term2). Qed.
Lemma lem3159154 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159155 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159156 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159155 h1) (fun h1 : term189 = True => @lem3159154)). Qed.
Lemma lem3159157 : term189 = True.
Proof. exact (EQ_MP (@lem3159156) (@lem3159154)). Qed.
Lemma lem3159158 : term188 = True.
Proof. exact (TRANS (@lem3159153) (@lem3159157)). Qed.
Lemma lem3159159 : term439 = True.
Proof. exact (TRANS (@lem3159150) (@lem3159158)). Qed.
Lemma lem3159160 : term436 = True.
Proof. exact (TRANS (@lem3159136) (@lem3159159)). Qed.
Lemma lem3159161 : term188 = True.
Proof. exact (TRANS (@lem3159113) (@lem3159160)). Qed.
Lemma lem3159162 : term433 = True.
Proof. exact (TRANS (@lem3159104) (@lem3159161)). Qed.
Lemma lem3159163 : True = term433.
Proof. exact (SYM (@lem3159162)). Qed.
Lemma lem3159164 : term433.
Proof. exact (EQ_MP (@lem3159163) (@lem0)). Qed.
Lemma lem3159165 (_32603 : int) (h1 : term432 _32603) : term447 _32603.
Proof. exact (conj (@lem3159164) (@lem3159026 _32603 h1)). Qed.
Lemma lem3159167 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3159168 (_32603 : int) : term448 _32603.
Proof. exact (@lem3159167 term93 (term291 _32603)). Qed.
Lemma lem3159169 (_32603 : int) (h1 : term432 _32603) : term449 _32603.
Proof. exact (@lem3159168 _32603 (@lem3159165 _32603 h1)). Qed.
Lemma lem3159170 (_32603 : int) : (term450 _32603) = (term291 _32603).
Proof. exact (@lem1982733 (term291 _32603)). Qed.
Lemma lem3159171 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159172 (_32603 : int) : (term451 _32603) = (term293 _32603).
Proof. exact (MK_COMB (@lem3159171) (@lem3159170 _32603)). Qed.
Lemma lem3159173 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159174 (_32603 : int) : (term449 _32603) = (term294 _32603).
Proof. exact (MK_COMB (@lem3159172 _32603) (@lem3159173)). Qed.
Lemma lem3159175 (_32603 : int) (h1 : term432 _32603) : term294 _32603.
Proof. exact (EQ_MP (@lem3159174 _32603) (@lem3159169 _32603 h1)). Qed.
Lemma lem3159176 (_32603 : int) (h1 : term432 _32603) : term452 _32603.
Proof. exact (conj (@lem3159175 _32603 h1) (@lem3159101 _32603 h1)). Qed.
Lemma lem3159178 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3159179 (_32603 : int) : term454 _32603.
Proof. exact (@lem3159178 (term291 _32603) (term227 _32603)). Qed.
Lemma lem3159180 (_32603 : int) (h1 : term432 _32603) : term455 _32603.
Proof. exact (@lem3159179 _32603 (@lem3159176 _32603 h1)). Qed.
Lemma lem3159181 (_32603 : int) : (term456 _32603) = (term457 _32603).
Proof. exact (@lem1982753 (term263 _32603) (real_of_int _32603) term93 term223). Qed.
Lemma lem3159182 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3159184 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159185 : term93 = term182.
Proof. exact (@lem3159184 term2). Qed.
Lemma lem3159187 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3159188 : term160 = term161.
Proof. exact (@lem3159187 term2). Qed.
Lemma lem3159189 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159190 : term460 = term461.
Proof. exact (MK_COMB (@lem3159189) (@lem3159188)). Qed.
Lemma lem3159191 : term462 = term463.
Proof. exact (MK_COMB (@lem3159190) (@lem3159185)). Qed.
Lemma lem3159192 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3159194 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159195 : term188 = term189.
Proof. exact (@lem3159194 (NUMERAL 0) term2). Qed.
Lemma lem3159196 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159197 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159198 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159197 h1) (fun h1 : term189 = True => @lem3159196)). Qed.
Lemma lem3159199 : term189 = True.
Proof. exact (EQ_MP (@lem3159198) (@lem3159196)). Qed.
Lemma lem3159200 : term188 = True.
Proof. exact (TRANS (@lem3159195) (@lem3159199)). Qed.
Lemma lem3159201 : True = term188.
Proof. exact (SYM (@lem3159200)). Qed.
Lemma lem3159202 : term188.
Proof. exact (EQ_MP (@lem3159201) (@lem0)). Qed.
Lemma lem3159203 : term465.
Proof. exact (@lem3159192 (@lem3159202)). Qed.
Lemma lem3159205 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159206 : term188 = term189.
Proof. exact (@lem3159205 (NUMERAL 0) term2). Qed.
Lemma lem3159207 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159208 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159209 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159208 h1) (fun h1 : term189 = True => @lem3159207)). Qed.
Lemma lem3159210 : term189 = True.
Proof. exact (EQ_MP (@lem3159209) (@lem3159207)). Qed.
Lemma lem3159211 : term188 = True.
Proof. exact (TRANS (@lem3159206) (@lem3159210)). Qed.
Lemma lem3159212 : True = term188.
Proof. exact (SYM (@lem3159211)). Qed.
Lemma lem3159213 : term188.
Proof. exact (EQ_MP (@lem3159212) (@lem0)). Qed.
Lemma lem3159214 : term466.
Proof. exact (@lem3159203 (@lem3159213)). Qed.
Lemma lem3159216 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159217 : term188 = term189.
Proof. exact (@lem3159216 (NUMERAL 0) term2). Qed.
Lemma lem3159218 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159219 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159220 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159219 h1) (fun h1 : term189 = True => @lem3159218)). Qed.
Lemma lem3159221 : term189 = True.
Proof. exact (EQ_MP (@lem3159220) (@lem3159218)). Qed.
Lemma lem3159222 : term188 = True.
Proof. exact (TRANS (@lem3159217) (@lem3159221)). Qed.
Lemma lem3159223 : True = term188.
Proof. exact (SYM (@lem3159222)). Qed.
Lemma lem3159224 : term188.
Proof. exact (EQ_MP (@lem3159223) (@lem0)). Qed.
Lemma lem3159225 : term467.
Proof. exact (@lem3159214 (@lem3159224)). Qed.
Lemma lem3159227 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159228 : term169 = term170.
Proof. exact (@lem3159227 term2 term2). Qed.
Lemma lem3159229 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159230 : term172 = term2.
Proof. exact (EQ_MP (@lem3159229) (@lem940073)). Qed.
Lemma lem3159231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159232 : term170 = term93.
Proof. exact (MK_COMB (@lem3159231) (@lem3159230)). Qed.
Lemma lem3159233 : term169 = term93.
Proof. exact (TRANS (@lem3159228) (@lem3159232)). Qed.
Lemma lem3159235 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159236 : term236 = term239.
Proof. exact (@lem3159235 term2 term2). Qed.
Lemma lem3159237 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159238 : term172 = term2.
Proof. exact (EQ_MP (@lem3159237) (@lem940073)). Qed.
Lemma lem3159239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159240 : term170 = term93.
Proof. exact (MK_COMB (@lem3159239) (@lem3159238)). Qed.
Lemma lem3159241 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159242 : term239 = term160.
Proof. exact (MK_COMB (@lem3159241) (@lem3159240)). Qed.
Lemma lem3159243 : term236 = term160.
Proof. exact (TRANS (@lem3159236) (@lem3159242)). Qed.
Lemma lem3159244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159245 : term468 = term460.
Proof. exact (MK_COMB (@lem3159244) (@lem3159243)). Qed.
Lemma lem3159246 : term469 = term462.
Proof. exact (MK_COMB (@lem3159245) (@lem3159233)). Qed.
Lemma lem3159248 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3159249 : term462 = term79.
Proof. exact (@lem3159248 term2). Qed.
Lemma lem3159250 : term469 = term79.
Proof. exact (TRANS (@lem3159246) (@lem3159249)). Qed.
Lemma lem3159251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3159252 : term471 = term273.
Proof. exact (MK_COMB (@lem3159251) (@lem3159250)). Qed.
Lemma lem3159253 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3159254 : term472 = term275.
Proof. exact (MK_COMB (@lem3159252) (@lem3159253)). Qed.
Lemma lem3159256 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159257 : term275 = term79.
Proof. exact (@lem3159256 term2). Qed.
Lemma lem3159258 : term472 = term79.
Proof. exact (TRANS (@lem3159254) (@lem3159257)). Qed.
Lemma lem3159260 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159261 : term169 = term170.
Proof. exact (@lem3159260 term2 term2). Qed.
Lemma lem3159262 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159263 : term172 = term2.
Proof. exact (EQ_MP (@lem3159262) (@lem940073)). Qed.
Lemma lem3159264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159265 : term170 = term93.
Proof. exact (MK_COMB (@lem3159264) (@lem3159263)). Qed.
Lemma lem3159266 : term169 = term93.
Proof. exact (TRANS (@lem3159261) (@lem3159265)). Qed.
Lemma lem3159267 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3159268 : term277 = term275.
Proof. exact (MK_COMB (@lem3159267) (@lem3159266)). Qed.
Lemma lem3159270 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159271 : term275 = term79.
Proof. exact (@lem3159270 term2). Qed.
Lemma lem3159272 : term277 = term79.
Proof. exact (TRANS (@lem3159268) (@lem3159271)). Qed.
Lemma lem3159273 : term79 = term277.
Proof. exact (SYM (@lem3159272)). Qed.
Lemma lem3159274 : term472 = term277.
Proof. exact (TRANS (@lem3159258) (@lem3159273)). Qed.
Lemma lem3159275 : term463 = term157.
Proof. exact (@lem3159225 (@lem3159274)). Qed.
Lemma lem3159276 : term462 = term157.
Proof. exact (TRANS (@lem3159191) (@lem3159275)). Qed.
Lemma lem3159278 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3159279 : term157 = term79.
Proof. exact (@lem3159278 term79). Qed.
Lemma lem3159280 : term462 = term79.
Proof. exact (TRANS (@lem3159276) (@lem3159279)). Qed.
Lemma lem3159281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3159282 : term473 = term273.
Proof. exact (MK_COMB (@lem3159281) (@lem3159280)). Qed.
Lemma lem3159283 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3159284 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3159282) (@lem3159283 _32603)). Qed.
Lemma lem3159285 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3159182 _32603) (@lem3159284 _32603)). Qed.
Lemma lem3159286 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3159287 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3159285 _32603) (@lem3159286 _32603)). Qed.
Lemma lem3159288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159289 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3159288) (@lem3159287 _32603)). Qed.
Lemma lem3159291 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3159292 : term223 = term226.
Proof. exact (@lem3159291 term200). Qed.
Lemma lem3159294 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159295 : term93 = term182.
Proof. exact (@lem3159294 term2). Qed.
Lemma lem3159296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159297 : term95 = term183.
Proof. exact (MK_COMB (@lem3159296) (@lem3159295)). Qed.
Lemma lem3159298 : term476 = term477.
Proof. exact (MK_COMB (@lem3159297) (@lem3159292)). Qed.
Lemma lem3159299 : term478.
Proof. exact (@lem1981473 term93 term93 term223 term93 term160 term93). Qed.
Lemma lem3159301 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159302 : term188 = term189.
Proof. exact (@lem3159301 (NUMERAL 0) term2). Qed.
Lemma lem3159303 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159304 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159305 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159304 h1) (fun h1 : term189 = True => @lem3159303)). Qed.
Lemma lem3159306 : term189 = True.
Proof. exact (EQ_MP (@lem3159305) (@lem3159303)). Qed.
Lemma lem3159307 : term188 = True.
Proof. exact (TRANS (@lem3159302) (@lem3159306)). Qed.
Lemma lem3159308 : True = term188.
Proof. exact (SYM (@lem3159307)). Qed.
Lemma lem3159309 : term188.
Proof. exact (EQ_MP (@lem3159308) (@lem0)). Qed.
Lemma lem3159310 : term479.
Proof. exact (@lem3159299 (@lem3159309)). Qed.
Lemma lem3159312 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159313 : term188 = term189.
Proof. exact (@lem3159312 (NUMERAL 0) term2). Qed.
Lemma lem3159314 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159315 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159316 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159315 h1) (fun h1 : term189 = True => @lem3159314)). Qed.
Lemma lem3159317 : term189 = True.
Proof. exact (EQ_MP (@lem3159316) (@lem3159314)). Qed.
Lemma lem3159318 : term188 = True.
Proof. exact (TRANS (@lem3159313) (@lem3159317)). Qed.
Lemma lem3159319 : True = term188.
Proof. exact (SYM (@lem3159318)). Qed.
Lemma lem3159320 : term188.
Proof. exact (EQ_MP (@lem3159319) (@lem0)). Qed.
Lemma lem3159321 : term480.
Proof. exact (@lem3159310 (@lem3159320)). Qed.
Lemma lem3159323 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159324 : term188 = term189.
Proof. exact (@lem3159323 (NUMERAL 0) term2). Qed.
Lemma lem3159325 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159326 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159327 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159326 h1) (fun h1 : term189 = True => @lem3159325)). Qed.
Lemma lem3159328 : term189 = True.
Proof. exact (EQ_MP (@lem3159327) (@lem3159325)). Qed.
Lemma lem3159329 : term188 = True.
Proof. exact (TRANS (@lem3159324) (@lem3159328)). Qed.
Lemma lem3159330 : True = term188.
Proof. exact (SYM (@lem3159329)). Qed.
Lemma lem3159331 : term188.
Proof. exact (EQ_MP (@lem3159330) (@lem0)). Qed.
Lemma lem3159332 : term481.
Proof. exact (@lem3159321 (@lem3159331)). Qed.
Lemma lem3159334 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159335 : term482 = term483.
Proof. exact (@lem3159334 term200 term2). Qed.
Lemma lem3159336 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3159337 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3159338 : term207 = term200.
Proof. exact (EQ_MP (@lem3159337) (@lem3159336)). Qed.
Lemma lem3159339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159340 : term205 = term186.
Proof. exact (MK_COMB (@lem3159339) (@lem3159338)). Qed.
Lemma lem3159341 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159342 : term483 = term223.
Proof. exact (MK_COMB (@lem3159341) (@lem3159340)). Qed.
Lemma lem3159343 : term482 = term223.
Proof. exact (TRANS (@lem3159335) (@lem3159342)). Qed.
Lemma lem3159345 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159346 : term169 = term170.
Proof. exact (@lem3159345 term2 term2). Qed.
Lemma lem3159347 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159348 : term172 = term2.
Proof. exact (EQ_MP (@lem3159347) (@lem940073)). Qed.
Lemma lem3159349 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159350 : term170 = term93.
Proof. exact (MK_COMB (@lem3159349) (@lem3159348)). Qed.
Lemma lem3159351 : term169 = term93.
Proof. exact (TRANS (@lem3159346) (@lem3159350)). Qed.
Lemma lem3159352 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159353 : term194 = term95.
Proof. exact (MK_COMB (@lem3159352) (@lem3159351)). Qed.
Lemma lem3159354 : term484 = term476.
Proof. exact (MK_COMB (@lem3159353) (@lem3159343)). Qed.
Lemma lem3159357 : term485 = term160.
Proof. exact (@lem1367771 term2 term2). Qed.
Lemma lem3159358 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3159359 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3159360 : term199 = term200.
Proof. exact (EQ_MP (@lem3159359) (@lem3159358)). Qed.
Lemma lem3159361 : term200 = term199.
Proof. exact (SYM (@lem3159360)). Qed.
Lemma lem3159362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159363 : term186 = term196.
Proof. exact (MK_COMB (@lem3159362) (@lem3159361)). Qed.
Lemma lem3159364 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159365 : term223 = term486.
Proof. exact (MK_COMB (@lem3159364) (@lem3159363)). Qed.
Lemma lem3159366 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3159367 : term476 = term485.
Proof. exact (MK_COMB (@lem3159366) (@lem3159365)). Qed.
Lemma lem3159368 : term476 = term160.
Proof. exact (TRANS (@lem3159367) (@lem3159357)). Qed.
Lemma lem3159369 : term484 = term160.
Proof. exact (TRANS (@lem3159354) (@lem3159368)). Qed.
Lemma lem3159370 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3159371 : term487 = term162.
Proof. exact (MK_COMB (@lem3159370) (@lem3159369)). Qed.
Lemma lem3159372 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3159373 : term488 = term236.
Proof. exact (MK_COMB (@lem3159371) (@lem3159372)). Qed.
Lemma lem3159375 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159376 : term236 = term239.
Proof. exact (@lem3159375 term2 term2). Qed.
Lemma lem3159377 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159378 : term172 = term2.
Proof. exact (EQ_MP (@lem3159377) (@lem940073)). Qed.
Lemma lem3159379 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159380 : term170 = term93.
Proof. exact (MK_COMB (@lem3159379) (@lem3159378)). Qed.
Lemma lem3159381 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159382 : term239 = term160.
Proof. exact (MK_COMB (@lem3159381) (@lem3159380)). Qed.
Lemma lem3159383 : term236 = term160.
Proof. exact (TRANS (@lem3159376) (@lem3159382)). Qed.
Lemma lem3159384 : term488 = term160.
Proof. exact (TRANS (@lem3159373) (@lem3159383)). Qed.
Lemma lem3159386 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159387 : term169 = term170.
Proof. exact (@lem3159386 term2 term2). Qed.
Lemma lem3159388 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159389 : term172 = term2.
Proof. exact (EQ_MP (@lem3159388) (@lem940073)). Qed.
Lemma lem3159390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159391 : term170 = term93.
Proof. exact (MK_COMB (@lem3159390) (@lem3159389)). Qed.
Lemma lem3159392 : term169 = term93.
Proof. exact (TRANS (@lem3159387) (@lem3159391)). Qed.
Lemma lem3159393 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem3159394 : term489 = term236.
Proof. exact (MK_COMB (@lem3159393) (@lem3159392)). Qed.
Lemma lem3159396 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159397 : term236 = term239.
Proof. exact (@lem3159396 term2 term2). Qed.
Lemma lem3159398 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159399 : term172 = term2.
Proof. exact (EQ_MP (@lem3159398) (@lem940073)). Qed.
Lemma lem3159400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159401 : term170 = term93.
Proof. exact (MK_COMB (@lem3159400) (@lem3159399)). Qed.
Lemma lem3159402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159403 : term239 = term160.
Proof. exact (MK_COMB (@lem3159402) (@lem3159401)). Qed.
Lemma lem3159404 : term236 = term160.
Proof. exact (TRANS (@lem3159397) (@lem3159403)). Qed.
Lemma lem3159405 : term489 = term160.
Proof. exact (TRANS (@lem3159394) (@lem3159404)). Qed.
Lemma lem3159406 : term160 = term489.
Proof. exact (SYM (@lem3159405)). Qed.
Lemma lem3159407 : term488 = term489.
Proof. exact (TRANS (@lem3159384) (@lem3159406)). Qed.
Lemma lem3159408 : term477 = term161.
Proof. exact (@lem3159332 (@lem3159407)). Qed.
Lemma lem3159409 : term476 = term161.
Proof. exact (TRANS (@lem3159298) (@lem3159408)). Qed.
Lemma lem3159411 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3159412 : term161 = term160.
Proof. exact (@lem3159411 term160). Qed.
Lemma lem3159413 : term476 = term160.
Proof. exact (TRANS (@lem3159409) (@lem3159412)). Qed.
Lemma lem3159414 (_32603 : int) : (term457 _32603) = term490.
Proof. exact (MK_COMB (@lem3159289 _32603) (@lem3159413)). Qed.
Lemma lem3159415 (_32603 : int) : (term456 _32603) = term490.
Proof. exact (TRANS (@lem3159181 _32603) (@lem3159414 _32603)). Qed.
Lemma lem3159416 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3159417 (_32603 : int) : (term456 _32603) = term160.
Proof. exact (TRANS (@lem3159415 _32603) (@lem3159416)). Qed.
Lemma lem3159418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159419 (_32603 : int) : (term491 _32603) = term492.
Proof. exact (MK_COMB (@lem3159418) (@lem3159417 _32603)). Qed.
Lemma lem3159420 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159421 (_32603 : int) : (term455 _32603) = term493.
Proof. exact (MK_COMB (@lem3159419 _32603) (@lem3159420)). Qed.
Lemma lem3159422 (_32603 : int) (h1 : term432 _32603) : term493.
Proof. exact (EQ_MP (@lem3159421 _32603) (@lem3159180 _32603 h1)). Qed.
Lemma lem3159424 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3159425 : term493 = term494.
Proof. exact (@lem3159424 term79 term160). Qed.
Lemma lem3159427 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3159428 : term160 = term161.
Proof. exact (@lem3159427 term2). Qed.
Lemma lem3159430 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159431 : term79 = term157.
Proof. exact (@lem3159430 (NUMERAL 0)). Qed.
Lemma lem3159432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3159433 : term81 = term495.
Proof. exact (MK_COMB (@lem3159432) (@lem3159431)). Qed.
Lemma lem3159434 : term494 = term496.
Proof. exact (MK_COMB (@lem3159433) (@lem3159428)). Qed.
Lemma lem3159435 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3159437 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159438 : term188 = term189.
Proof. exact (@lem3159437 (NUMERAL 0) term2). Qed.
Lemma lem3159439 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159440 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159441 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159440 h1) (fun h1 : term189 = True => @lem3159439)). Qed.
Lemma lem3159442 : term189 = True.
Proof. exact (EQ_MP (@lem3159441) (@lem3159439)). Qed.
Lemma lem3159443 : term188 = True.
Proof. exact (TRANS (@lem3159438) (@lem3159442)). Qed.
Lemma lem3159444 : True = term188.
Proof. exact (SYM (@lem3159443)). Qed.
Lemma lem3159445 : term188.
Proof. exact (EQ_MP (@lem3159444) (@lem0)). Qed.
Lemma lem3159446 : term498.
Proof. exact (@lem3159435 (@lem3159445)). Qed.
Lemma lem3159448 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159449 : term188 = term189.
Proof. exact (@lem3159448 (NUMERAL 0) term2). Qed.
Lemma lem3159450 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159451 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159452 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159451 h1) (fun h1 : term189 = True => @lem3159450)). Qed.
Lemma lem3159453 : term189 = True.
Proof. exact (EQ_MP (@lem3159452) (@lem3159450)). Qed.
Lemma lem3159454 : term188 = True.
Proof. exact (TRANS (@lem3159449) (@lem3159453)). Qed.
Lemma lem3159455 : True = term188.
Proof. exact (SYM (@lem3159454)). Qed.
Lemma lem3159456 : term188.
Proof. exact (EQ_MP (@lem3159455) (@lem0)). Qed.
Lemma lem3159457 : term496 = term499.
Proof. exact (@lem3159446 (@lem3159456)). Qed.
Lemma lem3159459 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159460 : term236 = term239.
Proof. exact (@lem3159459 term2 term2). Qed.
Lemma lem3159461 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159462 : term172 = term2.
Proof. exact (EQ_MP (@lem3159461) (@lem940073)). Qed.
Lemma lem3159463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159464 : term170 = term93.
Proof. exact (MK_COMB (@lem3159463) (@lem3159462)). Qed.
Lemma lem3159465 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159466 : term239 = term160.
Proof. exact (MK_COMB (@lem3159465) (@lem3159464)). Qed.
Lemma lem3159467 : term236 = term160.
Proof. exact (TRANS (@lem3159460) (@lem3159466)). Qed.
Lemma lem3159469 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159470 : term275 = term79.
Proof. exact (@lem3159469 term2). Qed.
Lemma lem3159471 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3159472 : term500 = term81.
Proof. exact (MK_COMB (@lem3159471) (@lem3159470)). Qed.
Lemma lem3159473 : term499 = term494.
Proof. exact (MK_COMB (@lem3159472) (@lem3159467)). Qed.
Lemma lem3159475 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3159476 : term494 = term503.
Proof. exact (@lem3159475 (NUMERAL 0) term2). Qed.
Lemma lem3159477 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159478 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3159479 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159478 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3159477)). Qed.
Lemma lem3159480 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3159479) (@lem3159477)). Qed.
Lemma lem3159481 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3159482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3159483 : term504 = (and True).
Proof. exact (MK_COMB (@lem3159482) (@lem3159481)). Qed.
Lemma lem3159484 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3159483) (@lem3159480)). Qed.
Lemma lem3159486 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3159487 : term503 = False.
Proof. exact (TRANS (@lem3159484) (@lem3159486)). Qed.
Lemma lem3159488 : term494 = False.
Proof. exact (TRANS (@lem3159476) (@lem3159487)). Qed.
Lemma lem3159489 : term499 = False.
Proof. exact (TRANS (@lem3159473) (@lem3159488)). Qed.
Lemma lem3159490 : term496 = False.
Proof. exact (TRANS (@lem3159457) (@lem3159489)). Qed.
Lemma lem3159491 : term494 = False.
Proof. exact (TRANS (@lem3159434) (@lem3159490)). Qed.
Lemma lem3159492 : term493 = False.
Proof. exact (TRANS (@lem3159425) (@lem3159491)). Qed.
Lemma lem3159493 (_32603 : int) (h1 : term432 _32603) : False.
Proof. exact (EQ_MP (@lem3159492) (@lem3159422 _32603 h1)). Qed.
Lemma lem3159494 (_32603 : int) (h1 : term426 _32603) : term426 _32603.
Proof. exact (h1). Qed.
Lemma lem3159495 (_32603 : int) (h1 : term421 _32603) : term421 _32603.
Proof. exact (h1). Qed.
Lemma lem3159496 (_32603 : int) (h1 : term505 _32603) : term505 _32603.
Proof. exact (h1). Qed.
Lemma lem3159497 (_32603 : int) (h1 : term505 _32603) : term422 _32603.
Proof. exact (proj2 (@lem3159496 _32603 h1)). Qed.
Lemma lem3159498 (_32603 : int) (h1 : term505 _32603) : term180 _32603.
Proof. exact (proj1 (@lem3159496 _32603 h1)). Qed.
Lemma lem3159500 (_32603 : int) (h1 : term505 _32603) : term329 _32603.
Proof. exact (proj1 (@lem3159497 _32603 h1)). Qed.
Lemma lem3159502 (_32603 : int) (h1 : term505 _32603) : term247 _32603.
Proof. exact (proj1 (@lem3159500 _32603 h1)). Qed.
Lemma lem3159504 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3159505 : term433 = term188.
Proof. exact (@lem3159504 term79 term93). Qed.
Lemma lem3159507 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159508 : term93 = term182.
Proof. exact (@lem3159507 term2). Qed.
Lemma lem3159510 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159511 : term79 = term157.
Proof. exact (@lem3159510 (NUMERAL 0)). Qed.
Lemma lem3159512 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159513 : term434 = term435.
Proof. exact (MK_COMB (@lem3159512) (@lem3159511)). Qed.
Lemma lem3159514 : term188 = term436.
Proof. exact (MK_COMB (@lem3159513) (@lem3159508)). Qed.
Lemma lem3159515 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3159517 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159518 : term188 = term189.
Proof. exact (@lem3159517 (NUMERAL 0) term2). Qed.
Lemma lem3159519 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159520 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159521 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159520 h1) (fun h1 : term189 = True => @lem3159519)). Qed.
Lemma lem3159522 : term189 = True.
Proof. exact (EQ_MP (@lem3159521) (@lem3159519)). Qed.
Lemma lem3159523 : term188 = True.
Proof. exact (TRANS (@lem3159518) (@lem3159522)). Qed.
Lemma lem3159524 : True = term188.
Proof. exact (SYM (@lem3159523)). Qed.
Lemma lem3159525 : term188.
Proof. exact (EQ_MP (@lem3159524) (@lem0)). Qed.
Lemma lem3159526 : term438.
Proof. exact (@lem3159515 (@lem3159525)). Qed.
Lemma lem3159528 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159529 : term188 = term189.
Proof. exact (@lem3159528 (NUMERAL 0) term2). Qed.
Lemma lem3159530 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159531 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159532 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159531 h1) (fun h1 : term189 = True => @lem3159530)). Qed.
Lemma lem3159533 : term189 = True.
Proof. exact (EQ_MP (@lem3159532) (@lem3159530)). Qed.
Lemma lem3159534 : term188 = True.
Proof. exact (TRANS (@lem3159529) (@lem3159533)). Qed.
Lemma lem3159535 : True = term188.
Proof. exact (SYM (@lem3159534)). Qed.
Lemma lem3159536 : term188.
Proof. exact (EQ_MP (@lem3159535) (@lem0)). Qed.
Lemma lem3159537 : term436 = term439.
Proof. exact (@lem3159526 (@lem3159536)). Qed.
Lemma lem3159539 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159540 : term169 = term170.
Proof. exact (@lem3159539 term2 term2). Qed.
Lemma lem3159541 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159542 : term172 = term2.
Proof. exact (EQ_MP (@lem3159541) (@lem940073)). Qed.
Lemma lem3159543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159544 : term170 = term93.
Proof. exact (MK_COMB (@lem3159543) (@lem3159542)). Qed.
Lemma lem3159545 : term169 = term93.
Proof. exact (TRANS (@lem3159540) (@lem3159544)). Qed.
Lemma lem3159547 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159548 : term275 = term79.
Proof. exact (@lem3159547 term2). Qed.
Lemma lem3159549 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159550 : term440 = term434.
Proof. exact (MK_COMB (@lem3159549) (@lem3159548)). Qed.
Lemma lem3159551 : term439 = term188.
Proof. exact (MK_COMB (@lem3159550) (@lem3159545)). Qed.
Lemma lem3159553 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159554 : term188 = term189.
Proof. exact (@lem3159553 (NUMERAL 0) term2). Qed.
Lemma lem3159555 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159556 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159557 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159556 h1) (fun h1 : term189 = True => @lem3159555)). Qed.
Lemma lem3159558 : term189 = True.
Proof. exact (EQ_MP (@lem3159557) (@lem3159555)). Qed.
Lemma lem3159559 : term188 = True.
Proof. exact (TRANS (@lem3159554) (@lem3159558)). Qed.
Lemma lem3159560 : term439 = True.
Proof. exact (TRANS (@lem3159551) (@lem3159559)). Qed.
Lemma lem3159561 : term436 = True.
Proof. exact (TRANS (@lem3159537) (@lem3159560)). Qed.
Lemma lem3159562 : term188 = True.
Proof. exact (TRANS (@lem3159514) (@lem3159561)). Qed.
Lemma lem3159563 : term433 = True.
Proof. exact (TRANS (@lem3159505) (@lem3159562)). Qed.
Lemma lem3159564 : True = term433.
Proof. exact (SYM (@lem3159563)). Qed.
Lemma lem3159565 : term433.
Proof. exact (EQ_MP (@lem3159564) (@lem0)). Qed.
Lemma lem3159566 (_32603 : int) (h1 : term505 _32603) : term506 _32603.
Proof. exact (conj (@lem3159565) (@lem3159498 _32603 h1)). Qed.
Lemma lem3159568 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3159569 (_32603 : int) : term507 _32603.
Proof. exact (@lem3159568 term93 (real_of_int _32603)). Qed.
Lemma lem3159570 (_32603 : int) (h1 : term505 _32603) : term508 _32603.
Proof. exact (@lem3159569 _32603 (@lem3159566 _32603 h1)). Qed.
Lemma lem3159571 (_32603 : int) : (term509 _32603) = (real_of_int _32603).
Proof. exact (@lem1982733 (real_of_int _32603)). Qed.
Lemma lem3159572 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159573 (_32603 : int) : (term510 _32603) = (term179 _32603).
Proof. exact (MK_COMB (@lem3159572) (@lem3159571 _32603)). Qed.
Lemma lem3159574 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159575 (_32603 : int) : (term508 _32603) = (term180 _32603).
Proof. exact (MK_COMB (@lem3159573 _32603) (@lem3159574)). Qed.
Lemma lem3159576 (_32603 : int) (h1 : term505 _32603) : term180 _32603.
Proof. exact (EQ_MP (@lem3159575 _32603) (@lem3159570 _32603 h1)). Qed.
Lemma lem3159578 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3159579 : term433 = term188.
Proof. exact (@lem3159578 term79 term93). Qed.
Lemma lem3159581 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159582 : term93 = term182.
Proof. exact (@lem3159581 term2). Qed.
Lemma lem3159584 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159585 : term79 = term157.
Proof. exact (@lem3159584 (NUMERAL 0)). Qed.
Lemma lem3159586 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159587 : term434 = term435.
Proof. exact (MK_COMB (@lem3159586) (@lem3159585)). Qed.
Lemma lem3159588 : term188 = term436.
Proof. exact (MK_COMB (@lem3159587) (@lem3159582)). Qed.
Lemma lem3159589 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3159591 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159592 : term188 = term189.
Proof. exact (@lem3159591 (NUMERAL 0) term2). Qed.
Lemma lem3159593 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159594 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159595 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159594 h1) (fun h1 : term189 = True => @lem3159593)). Qed.
Lemma lem3159596 : term189 = True.
Proof. exact (EQ_MP (@lem3159595) (@lem3159593)). Qed.
Lemma lem3159597 : term188 = True.
Proof. exact (TRANS (@lem3159592) (@lem3159596)). Qed.
Lemma lem3159598 : True = term188.
Proof. exact (SYM (@lem3159597)). Qed.
Lemma lem3159599 : term188.
Proof. exact (EQ_MP (@lem3159598) (@lem0)). Qed.
Lemma lem3159600 : term438.
Proof. exact (@lem3159589 (@lem3159599)). Qed.
Lemma lem3159602 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159603 : term188 = term189.
Proof. exact (@lem3159602 (NUMERAL 0) term2). Qed.
Lemma lem3159604 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159605 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159606 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159605 h1) (fun h1 : term189 = True => @lem3159604)). Qed.
Lemma lem3159607 : term189 = True.
Proof. exact (EQ_MP (@lem3159606) (@lem3159604)). Qed.
Lemma lem3159608 : term188 = True.
Proof. exact (TRANS (@lem3159603) (@lem3159607)). Qed.
Lemma lem3159609 : True = term188.
Proof. exact (SYM (@lem3159608)). Qed.
Lemma lem3159610 : term188.
Proof. exact (EQ_MP (@lem3159609) (@lem0)). Qed.
Lemma lem3159611 : term436 = term439.
Proof. exact (@lem3159600 (@lem3159610)). Qed.
Lemma lem3159613 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159614 : term169 = term170.
Proof. exact (@lem3159613 term2 term2). Qed.
Lemma lem3159615 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159616 : term172 = term2.
Proof. exact (EQ_MP (@lem3159615) (@lem940073)). Qed.
Lemma lem3159617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159618 : term170 = term93.
Proof. exact (MK_COMB (@lem3159617) (@lem3159616)). Qed.
Lemma lem3159619 : term169 = term93.
Proof. exact (TRANS (@lem3159614) (@lem3159618)). Qed.
Lemma lem3159621 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159622 : term275 = term79.
Proof. exact (@lem3159621 term2). Qed.
Lemma lem3159623 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159624 : term440 = term434.
Proof. exact (MK_COMB (@lem3159623) (@lem3159622)). Qed.
Lemma lem3159625 : term439 = term188.
Proof. exact (MK_COMB (@lem3159624) (@lem3159619)). Qed.
Lemma lem3159627 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159628 : term188 = term189.
Proof. exact (@lem3159627 (NUMERAL 0) term2). Qed.
Lemma lem3159629 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159630 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159631 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159630 h1) (fun h1 : term189 = True => @lem3159629)). Qed.
Lemma lem3159632 : term189 = True.
Proof. exact (EQ_MP (@lem3159631) (@lem3159629)). Qed.
Lemma lem3159633 : term188 = True.
Proof. exact (TRANS (@lem3159628) (@lem3159632)). Qed.
Lemma lem3159634 : term439 = True.
Proof. exact (TRANS (@lem3159625) (@lem3159633)). Qed.
Lemma lem3159635 : term436 = True.
Proof. exact (TRANS (@lem3159611) (@lem3159634)). Qed.
Lemma lem3159636 : term188 = True.
Proof. exact (TRANS (@lem3159588) (@lem3159635)). Qed.
Lemma lem3159637 : term433 = True.
Proof. exact (TRANS (@lem3159579) (@lem3159636)). Qed.
Lemma lem3159638 : True = term433.
Proof. exact (SYM (@lem3159637)). Qed.
Lemma lem3159639 : term433.
Proof. exact (EQ_MP (@lem3159638) (@lem0)). Qed.
Lemma lem3159640 (_32603 : int) (h1 : term505 _32603) : term511 _32603.
Proof. exact (conj (@lem3159639) (@lem3159502 _32603 h1)). Qed.
Lemma lem3159642 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3159643 (_32603 : int) : term512 _32603.
Proof. exact (@lem3159642 term93 (term243 _32603)). Qed.
Lemma lem3159644 (_32603 : int) (h1 : term505 _32603) : term513 _32603.
Proof. exact (@lem3159643 _32603 (@lem3159640 _32603 h1)). Qed.
Lemma lem3159645 (_32603 : int) : (term514 _32603) = (term243 _32603).
Proof. exact (@lem1982733 (term243 _32603)). Qed.
Lemma lem3159646 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159647 (_32603 : int) : (term515 _32603) = (term246 _32603).
Proof. exact (MK_COMB (@lem3159646) (@lem3159645 _32603)). Qed.
Lemma lem3159648 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159649 (_32603 : int) : (term513 _32603) = (term247 _32603).
Proof. exact (MK_COMB (@lem3159647 _32603) (@lem3159648)). Qed.
Lemma lem3159650 (_32603 : int) (h1 : term505 _32603) : term247 _32603.
Proof. exact (EQ_MP (@lem3159649 _32603) (@lem3159644 _32603 h1)). Qed.
Lemma lem3159651 (_32603 : int) (h1 : term505 _32603) : term516 _32603.
Proof. exact (conj (@lem3159650 _32603 h1) (@lem3159576 _32603 h1)). Qed.
Lemma lem3159653 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3159654 (_32603 : int) : term517 _32603.
Proof. exact (@lem3159653 (term243 _32603) (real_of_int _32603)). Qed.
Lemma lem3159655 (_32603 : int) (h1 : term505 _32603) : term518 _32603.
Proof. exact (@lem3159654 _32603 (@lem3159651 _32603 h1)). Qed.
Lemma lem3159656 (_32603 : int) : (term519 _32603) = (term520 _32603).
Proof. exact (@lem1982759 (term263 _32603) (real_of_int _32603) term160). Qed.
Lemma lem3159657 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3159659 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159660 : term93 = term182.
Proof. exact (@lem3159659 term2). Qed.
Lemma lem3159662 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3159663 : term160 = term161.
Proof. exact (@lem3159662 term2). Qed.
Lemma lem3159664 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159665 : term460 = term461.
Proof. exact (MK_COMB (@lem3159664) (@lem3159663)). Qed.
Lemma lem3159666 : term462 = term463.
Proof. exact (MK_COMB (@lem3159665) (@lem3159660)). Qed.
Lemma lem3159667 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3159669 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159670 : term188 = term189.
Proof. exact (@lem3159669 (NUMERAL 0) term2). Qed.
Lemma lem3159671 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159672 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159673 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159672 h1) (fun h1 : term189 = True => @lem3159671)). Qed.
Lemma lem3159674 : term189 = True.
Proof. exact (EQ_MP (@lem3159673) (@lem3159671)). Qed.
Lemma lem3159675 : term188 = True.
Proof. exact (TRANS (@lem3159670) (@lem3159674)). Qed.
Lemma lem3159676 : True = term188.
Proof. exact (SYM (@lem3159675)). Qed.
Lemma lem3159677 : term188.
Proof. exact (EQ_MP (@lem3159676) (@lem0)). Qed.
Lemma lem3159678 : term465.
Proof. exact (@lem3159667 (@lem3159677)). Qed.
Lemma lem3159680 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159681 : term188 = term189.
Proof. exact (@lem3159680 (NUMERAL 0) term2). Qed.
Lemma lem3159682 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159683 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159684 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159683 h1) (fun h1 : term189 = True => @lem3159682)). Qed.
Lemma lem3159685 : term189 = True.
Proof. exact (EQ_MP (@lem3159684) (@lem3159682)). Qed.
Lemma lem3159686 : term188 = True.
Proof. exact (TRANS (@lem3159681) (@lem3159685)). Qed.
Lemma lem3159687 : True = term188.
Proof. exact (SYM (@lem3159686)). Qed.
Lemma lem3159688 : term188.
Proof. exact (EQ_MP (@lem3159687) (@lem0)). Qed.
Lemma lem3159689 : term466.
Proof. exact (@lem3159678 (@lem3159688)). Qed.
Lemma lem3159691 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159692 : term188 = term189.
Proof. exact (@lem3159691 (NUMERAL 0) term2). Qed.
Lemma lem3159693 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159694 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159695 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159694 h1) (fun h1 : term189 = True => @lem3159693)). Qed.
Lemma lem3159696 : term189 = True.
Proof. exact (EQ_MP (@lem3159695) (@lem3159693)). Qed.
Lemma lem3159697 : term188 = True.
Proof. exact (TRANS (@lem3159692) (@lem3159696)). Qed.
Lemma lem3159698 : True = term188.
Proof. exact (SYM (@lem3159697)). Qed.
Lemma lem3159699 : term188.
Proof. exact (EQ_MP (@lem3159698) (@lem0)). Qed.
Lemma lem3159700 : term467.
Proof. exact (@lem3159689 (@lem3159699)). Qed.
Lemma lem3159702 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159703 : term169 = term170.
Proof. exact (@lem3159702 term2 term2). Qed.
Lemma lem3159704 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159705 : term172 = term2.
Proof. exact (EQ_MP (@lem3159704) (@lem940073)). Qed.
Lemma lem3159706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159707 : term170 = term93.
Proof. exact (MK_COMB (@lem3159706) (@lem3159705)). Qed.
Lemma lem3159708 : term169 = term93.
Proof. exact (TRANS (@lem3159703) (@lem3159707)). Qed.
Lemma lem3159710 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159711 : term236 = term239.
Proof. exact (@lem3159710 term2 term2). Qed.
Lemma lem3159712 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159713 : term172 = term2.
Proof. exact (EQ_MP (@lem3159712) (@lem940073)). Qed.
Lemma lem3159714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159715 : term170 = term93.
Proof. exact (MK_COMB (@lem3159714) (@lem3159713)). Qed.
Lemma lem3159716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159717 : term239 = term160.
Proof. exact (MK_COMB (@lem3159716) (@lem3159715)). Qed.
Lemma lem3159718 : term236 = term160.
Proof. exact (TRANS (@lem3159711) (@lem3159717)). Qed.
Lemma lem3159719 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159720 : term468 = term460.
Proof. exact (MK_COMB (@lem3159719) (@lem3159718)). Qed.
Lemma lem3159721 : term469 = term462.
Proof. exact (MK_COMB (@lem3159720) (@lem3159708)). Qed.
Lemma lem3159723 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3159724 : term462 = term79.
Proof. exact (@lem3159723 term2). Qed.
Lemma lem3159725 : term469 = term79.
Proof. exact (TRANS (@lem3159721) (@lem3159724)). Qed.
Lemma lem3159726 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3159727 : term471 = term273.
Proof. exact (MK_COMB (@lem3159726) (@lem3159725)). Qed.
Lemma lem3159728 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3159729 : term472 = term275.
Proof. exact (MK_COMB (@lem3159727) (@lem3159728)). Qed.
Lemma lem3159731 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159732 : term275 = term79.
Proof. exact (@lem3159731 term2). Qed.
Lemma lem3159733 : term472 = term79.
Proof. exact (TRANS (@lem3159729) (@lem3159732)). Qed.
Lemma lem3159735 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159736 : term169 = term170.
Proof. exact (@lem3159735 term2 term2). Qed.
Lemma lem3159737 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159738 : term172 = term2.
Proof. exact (EQ_MP (@lem3159737) (@lem940073)). Qed.
Lemma lem3159739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159740 : term170 = term93.
Proof. exact (MK_COMB (@lem3159739) (@lem3159738)). Qed.
Lemma lem3159741 : term169 = term93.
Proof. exact (TRANS (@lem3159736) (@lem3159740)). Qed.
Lemma lem3159742 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3159743 : term277 = term275.
Proof. exact (MK_COMB (@lem3159742) (@lem3159741)). Qed.
Lemma lem3159745 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159746 : term275 = term79.
Proof. exact (@lem3159745 term2). Qed.
Lemma lem3159747 : term277 = term79.
Proof. exact (TRANS (@lem3159743) (@lem3159746)). Qed.
Lemma lem3159748 : term79 = term277.
Proof. exact (SYM (@lem3159747)). Qed.
Lemma lem3159749 : term472 = term277.
Proof. exact (TRANS (@lem3159733) (@lem3159748)). Qed.
Lemma lem3159750 : term463 = term157.
Proof. exact (@lem3159700 (@lem3159749)). Qed.
Lemma lem3159751 : term462 = term157.
Proof. exact (TRANS (@lem3159666) (@lem3159750)). Qed.
Lemma lem3159753 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3159754 : term157 = term79.
Proof. exact (@lem3159753 term79). Qed.
Lemma lem3159755 : term462 = term79.
Proof. exact (TRANS (@lem3159751) (@lem3159754)). Qed.
Lemma lem3159756 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3159757 : term473 = term273.
Proof. exact (MK_COMB (@lem3159756) (@lem3159755)). Qed.
Lemma lem3159758 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3159759 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3159757) (@lem3159758 _32603)). Qed.
Lemma lem3159760 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3159657 _32603) (@lem3159759 _32603)). Qed.
Lemma lem3159761 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3159762 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3159760 _32603) (@lem3159761 _32603)). Qed.
Lemma lem3159763 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3159764 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3159763) (@lem3159762 _32603)). Qed.
Lemma lem3159765 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3159766 (_32603 : int) : (term520 _32603) = term490.
Proof. exact (MK_COMB (@lem3159764 _32603) (@lem3159765)). Qed.
Lemma lem3159767 (_32603 : int) : (term519 _32603) = term490.
Proof. exact (TRANS (@lem3159656 _32603) (@lem3159766 _32603)). Qed.
Lemma lem3159768 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3159769 (_32603 : int) : (term519 _32603) = term160.
Proof. exact (TRANS (@lem3159767 _32603) (@lem3159768)). Qed.
Lemma lem3159770 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159771 (_32603 : int) : (term521 _32603) = term492.
Proof. exact (MK_COMB (@lem3159770) (@lem3159769 _32603)). Qed.
Lemma lem3159772 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159773 (_32603 : int) : (term518 _32603) = term493.
Proof. exact (MK_COMB (@lem3159771 _32603) (@lem3159772)). Qed.
Lemma lem3159774 (_32603 : int) (h1 : term505 _32603) : term493.
Proof. exact (EQ_MP (@lem3159773 _32603) (@lem3159655 _32603 h1)). Qed.
Lemma lem3159776 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3159777 : term493 = term494.
Proof. exact (@lem3159776 term79 term160). Qed.
Lemma lem3159779 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3159780 : term160 = term161.
Proof. exact (@lem3159779 term2). Qed.
Lemma lem3159782 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159783 : term79 = term157.
Proof. exact (@lem3159782 (NUMERAL 0)). Qed.
Lemma lem3159784 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3159785 : term81 = term495.
Proof. exact (MK_COMB (@lem3159784) (@lem3159783)). Qed.
Lemma lem3159786 : term494 = term496.
Proof. exact (MK_COMB (@lem3159785) (@lem3159780)). Qed.
Lemma lem3159787 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3159789 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159790 : term188 = term189.
Proof. exact (@lem3159789 (NUMERAL 0) term2). Qed.
Lemma lem3159791 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159792 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159793 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159792 h1) (fun h1 : term189 = True => @lem3159791)). Qed.
Lemma lem3159794 : term189 = True.
Proof. exact (EQ_MP (@lem3159793) (@lem3159791)). Qed.
Lemma lem3159795 : term188 = True.
Proof. exact (TRANS (@lem3159790) (@lem3159794)). Qed.
Lemma lem3159796 : True = term188.
Proof. exact (SYM (@lem3159795)). Qed.
Lemma lem3159797 : term188.
Proof. exact (EQ_MP (@lem3159796) (@lem0)). Qed.
Lemma lem3159798 : term498.
Proof. exact (@lem3159787 (@lem3159797)). Qed.
Lemma lem3159800 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159801 : term188 = term189.
Proof. exact (@lem3159800 (NUMERAL 0) term2). Qed.
Lemma lem3159802 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159803 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159804 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159803 h1) (fun h1 : term189 = True => @lem3159802)). Qed.
Lemma lem3159805 : term189 = True.
Proof. exact (EQ_MP (@lem3159804) (@lem3159802)). Qed.
Lemma lem3159806 : term188 = True.
Proof. exact (TRANS (@lem3159801) (@lem3159805)). Qed.
Lemma lem3159807 : True = term188.
Proof. exact (SYM (@lem3159806)). Qed.
Lemma lem3159808 : term188.
Proof. exact (EQ_MP (@lem3159807) (@lem0)). Qed.
Lemma lem3159809 : term496 = term499.
Proof. exact (@lem3159798 (@lem3159808)). Qed.
Lemma lem3159811 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3159812 : term236 = term239.
Proof. exact (@lem3159811 term2 term2). Qed.
Lemma lem3159813 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159814 : term172 = term2.
Proof. exact (EQ_MP (@lem3159813) (@lem940073)). Qed.
Lemma lem3159815 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159816 : term170 = term93.
Proof. exact (MK_COMB (@lem3159815) (@lem3159814)). Qed.
Lemma lem3159817 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3159818 : term239 = term160.
Proof. exact (MK_COMB (@lem3159817) (@lem3159816)). Qed.
Lemma lem3159819 : term236 = term160.
Proof. exact (TRANS (@lem3159812) (@lem3159818)). Qed.
Lemma lem3159821 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159822 : term275 = term79.
Proof. exact (@lem3159821 term2). Qed.
Lemma lem3159823 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3159824 : term500 = term81.
Proof. exact (MK_COMB (@lem3159823) (@lem3159822)). Qed.
Lemma lem3159825 : term499 = term494.
Proof. exact (MK_COMB (@lem3159824) (@lem3159819)). Qed.
Lemma lem3159827 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3159828 : term494 = term503.
Proof. exact (@lem3159827 (NUMERAL 0) term2). Qed.
Lemma lem3159829 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159830 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3159831 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159830 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3159829)). Qed.
Lemma lem3159832 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3159831) (@lem3159829)). Qed.
Lemma lem3159833 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3159834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3159835 : term504 = (and True).
Proof. exact (MK_COMB (@lem3159834) (@lem3159833)). Qed.
Lemma lem3159836 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3159835) (@lem3159832)). Qed.
Lemma lem3159838 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3159839 : term503 = False.
Proof. exact (TRANS (@lem3159836) (@lem3159838)). Qed.
Lemma lem3159840 : term494 = False.
Proof. exact (TRANS (@lem3159828) (@lem3159839)). Qed.
Lemma lem3159841 : term499 = False.
Proof. exact (TRANS (@lem3159825) (@lem3159840)). Qed.
Lemma lem3159842 : term496 = False.
Proof. exact (TRANS (@lem3159809) (@lem3159841)). Qed.
Lemma lem3159843 : term494 = False.
Proof. exact (TRANS (@lem3159786) (@lem3159842)). Qed.
Lemma lem3159844 : term493 = False.
Proof. exact (TRANS (@lem3159777) (@lem3159843)). Qed.
Lemma lem3159845 (_32603 : int) (h1 : term505 _32603) : False.
Proof. exact (EQ_MP (@lem3159844) (@lem3159774 _32603 h1)). Qed.
Lemma lem3159846 (_32603 : int) (h1 : term522 _32603) : term522 _32603.
Proof. exact (h1). Qed.
Lemma lem3159847 (_32603 : int) (h1 : term522 _32603) : term423 _32603.
Proof. exact (proj2 (@lem3159846 _32603 h1)). Qed.
Lemma lem3159850 (_32603 : int) (h1 : term522 _32603) : term330 _32603.
Proof. exact (proj1 (@lem3159847 _32603 h1)). Qed.
Lemma lem3159851 (_32603 : int) (h1 : term522 _32603) : term281 _32603.
Proof. exact (proj2 (@lem3159850 _32603 h1)). Qed.
Lemma lem3159852 (_32603 : int) (h1 : term522 _32603) : term255 _32603.
Proof. exact (proj1 (@lem3159850 _32603 h1)). Qed.
Lemma lem3159854 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3159855 : term433 = term188.
Proof. exact (@lem3159854 term79 term93). Qed.
Lemma lem3159857 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159858 : term93 = term182.
Proof. exact (@lem3159857 term2). Qed.
Lemma lem3159860 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159861 : term79 = term157.
Proof. exact (@lem3159860 (NUMERAL 0)). Qed.
Lemma lem3159862 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159863 : term434 = term435.
Proof. exact (MK_COMB (@lem3159862) (@lem3159861)). Qed.
Lemma lem3159864 : term188 = term436.
Proof. exact (MK_COMB (@lem3159863) (@lem3159858)). Qed.
Lemma lem3159865 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3159867 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159868 : term188 = term189.
Proof. exact (@lem3159867 (NUMERAL 0) term2). Qed.
Lemma lem3159869 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159870 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159871 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159870 h1) (fun h1 : term189 = True => @lem3159869)). Qed.
Lemma lem3159872 : term189 = True.
Proof. exact (EQ_MP (@lem3159871) (@lem3159869)). Qed.
Lemma lem3159873 : term188 = True.
Proof. exact (TRANS (@lem3159868) (@lem3159872)). Qed.
Lemma lem3159874 : True = term188.
Proof. exact (SYM (@lem3159873)). Qed.
Lemma lem3159875 : term188.
Proof. exact (EQ_MP (@lem3159874) (@lem0)). Qed.
Lemma lem3159876 : term438.
Proof. exact (@lem3159865 (@lem3159875)). Qed.
Lemma lem3159878 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159879 : term188 = term189.
Proof. exact (@lem3159878 (NUMERAL 0) term2). Qed.
Lemma lem3159880 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159881 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159882 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159881 h1) (fun h1 : term189 = True => @lem3159880)). Qed.
Lemma lem3159883 : term189 = True.
Proof. exact (EQ_MP (@lem3159882) (@lem3159880)). Qed.
Lemma lem3159884 : term188 = True.
Proof. exact (TRANS (@lem3159879) (@lem3159883)). Qed.
Lemma lem3159885 : True = term188.
Proof. exact (SYM (@lem3159884)). Qed.
Lemma lem3159886 : term188.
Proof. exact (EQ_MP (@lem3159885) (@lem0)). Qed.
Lemma lem3159887 : term436 = term439.
Proof. exact (@lem3159876 (@lem3159886)). Qed.
Lemma lem3159889 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159890 : term169 = term170.
Proof. exact (@lem3159889 term2 term2). Qed.
Lemma lem3159891 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159892 : term172 = term2.
Proof. exact (EQ_MP (@lem3159891) (@lem940073)). Qed.
Lemma lem3159893 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159894 : term170 = term93.
Proof. exact (MK_COMB (@lem3159893) (@lem3159892)). Qed.
Lemma lem3159895 : term169 = term93.
Proof. exact (TRANS (@lem3159890) (@lem3159894)). Qed.
Lemma lem3159897 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159898 : term275 = term79.
Proof. exact (@lem3159897 term2). Qed.
Lemma lem3159899 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159900 : term440 = term434.
Proof. exact (MK_COMB (@lem3159899) (@lem3159898)). Qed.
Lemma lem3159901 : term439 = term188.
Proof. exact (MK_COMB (@lem3159900) (@lem3159895)). Qed.
Lemma lem3159903 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159904 : term188 = term189.
Proof. exact (@lem3159903 (NUMERAL 0) term2). Qed.
Lemma lem3159905 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159906 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159907 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159906 h1) (fun h1 : term189 = True => @lem3159905)). Qed.
Lemma lem3159908 : term189 = True.
Proof. exact (EQ_MP (@lem3159907) (@lem3159905)). Qed.
Lemma lem3159909 : term188 = True.
Proof. exact (TRANS (@lem3159904) (@lem3159908)). Qed.
Lemma lem3159910 : term439 = True.
Proof. exact (TRANS (@lem3159901) (@lem3159909)). Qed.
Lemma lem3159911 : term436 = True.
Proof. exact (TRANS (@lem3159887) (@lem3159910)). Qed.
Lemma lem3159912 : term188 = True.
Proof. exact (TRANS (@lem3159864) (@lem3159911)). Qed.
Lemma lem3159913 : term433 = True.
Proof. exact (TRANS (@lem3159855) (@lem3159912)). Qed.
Lemma lem3159914 : True = term433.
Proof. exact (SYM (@lem3159913)). Qed.
Lemma lem3159915 : term433.
Proof. exact (EQ_MP (@lem3159914) (@lem0)). Qed.
Lemma lem3159916 (_32603 : int) (h1 : term522 _32603) : term523 _32603.
Proof. exact (conj (@lem3159915) (@lem3159852 _32603 h1)). Qed.
Lemma lem3159918 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3159919 (_32603 : int) : term524 _32603.
Proof. exact (@lem3159918 term93 (term252 _32603)). Qed.
Lemma lem3159920 (_32603 : int) (h1 : term522 _32603) : term525 _32603.
Proof. exact (@lem3159919 _32603 (@lem3159916 _32603 h1)). Qed.
Lemma lem3159921 (_32603 : int) : (term526 _32603) = (term252 _32603).
Proof. exact (@lem1982733 (term252 _32603)). Qed.
Lemma lem3159922 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159923 (_32603 : int) : (term527 _32603) = (term254 _32603).
Proof. exact (MK_COMB (@lem3159922) (@lem3159921 _32603)). Qed.
Lemma lem3159924 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159925 (_32603 : int) : (term525 _32603) = (term255 _32603).
Proof. exact (MK_COMB (@lem3159923 _32603) (@lem3159924)). Qed.
Lemma lem3159926 (_32603 : int) (h1 : term522 _32603) : term255 _32603.
Proof. exact (EQ_MP (@lem3159925 _32603) (@lem3159920 _32603 h1)). Qed.
Lemma lem3159928 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3159929 : term433 = term188.
Proof. exact (@lem3159928 term79 term93). Qed.
Lemma lem3159931 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159932 : term93 = term182.
Proof. exact (@lem3159931 term2). Qed.
Lemma lem3159934 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3159935 : term79 = term157.
Proof. exact (@lem3159934 (NUMERAL 0)). Qed.
Lemma lem3159936 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159937 : term434 = term435.
Proof. exact (MK_COMB (@lem3159936) (@lem3159935)). Qed.
Lemma lem3159938 : term188 = term436.
Proof. exact (MK_COMB (@lem3159937) (@lem3159932)). Qed.
Lemma lem3159939 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3159941 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159942 : term188 = term189.
Proof. exact (@lem3159941 (NUMERAL 0) term2). Qed.
Lemma lem3159943 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159944 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159945 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159944 h1) (fun h1 : term189 = True => @lem3159943)). Qed.
Lemma lem3159946 : term189 = True.
Proof. exact (EQ_MP (@lem3159945) (@lem3159943)). Qed.
Lemma lem3159947 : term188 = True.
Proof. exact (TRANS (@lem3159942) (@lem3159946)). Qed.
Lemma lem3159948 : True = term188.
Proof. exact (SYM (@lem3159947)). Qed.
Lemma lem3159949 : term188.
Proof. exact (EQ_MP (@lem3159948) (@lem0)). Qed.
Lemma lem3159950 : term438.
Proof. exact (@lem3159939 (@lem3159949)). Qed.
Lemma lem3159952 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159953 : term188 = term189.
Proof. exact (@lem3159952 (NUMERAL 0) term2). Qed.
Lemma lem3159954 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159955 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159956 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159955 h1) (fun h1 : term189 = True => @lem3159954)). Qed.
Lemma lem3159957 : term189 = True.
Proof. exact (EQ_MP (@lem3159956) (@lem3159954)). Qed.
Lemma lem3159958 : term188 = True.
Proof. exact (TRANS (@lem3159953) (@lem3159957)). Qed.
Lemma lem3159959 : True = term188.
Proof. exact (SYM (@lem3159958)). Qed.
Lemma lem3159960 : term188.
Proof. exact (EQ_MP (@lem3159959) (@lem0)). Qed.
Lemma lem3159961 : term436 = term439.
Proof. exact (@lem3159950 (@lem3159960)). Qed.
Lemma lem3159963 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3159964 : term169 = term170.
Proof. exact (@lem3159963 term2 term2). Qed.
Lemma lem3159965 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3159966 : term172 = term2.
Proof. exact (EQ_MP (@lem3159965) (@lem940073)). Qed.
Lemma lem3159967 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3159968 : term170 = term93.
Proof. exact (MK_COMB (@lem3159967) (@lem3159966)). Qed.
Lemma lem3159969 : term169 = term93.
Proof. exact (TRANS (@lem3159964) (@lem3159968)). Qed.
Lemma lem3159971 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3159972 : term275 = term79.
Proof. exact (@lem3159971 term2). Qed.
Lemma lem3159973 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3159974 : term440 = term434.
Proof. exact (MK_COMB (@lem3159973) (@lem3159972)). Qed.
Lemma lem3159975 : term439 = term188.
Proof. exact (MK_COMB (@lem3159974) (@lem3159969)). Qed.
Lemma lem3159977 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3159978 : term188 = term189.
Proof. exact (@lem3159977 (NUMERAL 0) term2). Qed.
Lemma lem3159979 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3159980 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3159981 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3159980 h1) (fun h1 : term189 = True => @lem3159979)). Qed.
Lemma lem3159982 : term189 = True.
Proof. exact (EQ_MP (@lem3159981) (@lem3159979)). Qed.
Lemma lem3159983 : term188 = True.
Proof. exact (TRANS (@lem3159978) (@lem3159982)). Qed.
Lemma lem3159984 : term439 = True.
Proof. exact (TRANS (@lem3159975) (@lem3159983)). Qed.
Lemma lem3159985 : term436 = True.
Proof. exact (TRANS (@lem3159961) (@lem3159984)). Qed.
Lemma lem3159986 : term188 = True.
Proof. exact (TRANS (@lem3159938) (@lem3159985)). Qed.
Lemma lem3159987 : term433 = True.
Proof. exact (TRANS (@lem3159929) (@lem3159986)). Qed.
Lemma lem3159988 : True = term433.
Proof. exact (SYM (@lem3159987)). Qed.
Lemma lem3159989 : term433.
Proof. exact (EQ_MP (@lem3159988) (@lem0)). Qed.
Lemma lem3159990 (_32603 : int) (h1 : term522 _32603) : term528 _32603.
Proof. exact (conj (@lem3159989) (@lem3159851 _32603 h1)). Qed.
Lemma lem3159992 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3159993 (_32603 : int) : term529 _32603.
Proof. exact (@lem3159992 term93 (term263 _32603)). Qed.
Lemma lem3159994 (_32603 : int) (h1 : term522 _32603) : term530 _32603.
Proof. exact (@lem3159993 _32603 (@lem3159990 _32603 h1)). Qed.
Lemma lem3159995 (_32603 : int) : (term531 _32603) = (term263 _32603).
Proof. exact (@lem1982733 (term263 _32603)). Qed.
Lemma lem3159996 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3159997 (_32603 : int) : (term532 _32603) = (term280 _32603).
Proof. exact (MK_COMB (@lem3159996) (@lem3159995 _32603)). Qed.
Lemma lem3159998 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3159999 (_32603 : int) : (term530 _32603) = (term281 _32603).
Proof. exact (MK_COMB (@lem3159997 _32603) (@lem3159998)). Qed.
Lemma lem3160000 (_32603 : int) (h1 : term522 _32603) : term281 _32603.
Proof. exact (EQ_MP (@lem3159999 _32603) (@lem3159994 _32603 h1)). Qed.
Lemma lem3160001 (_32603 : int) (h1 : term522 _32603) : term533 _32603.
Proof. exact (conj (@lem3160000 _32603 h1) (@lem3159926 _32603 h1)). Qed.
Lemma lem3160003 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3160004 (_32603 : int) : term534 _32603.
Proof. exact (@lem3160003 (term263 _32603) (term252 _32603)). Qed.
Lemma lem3160005 (_32603 : int) (h1 : term522 _32603) : term535 _32603.
Proof. exact (@lem3160004 _32603 (@lem3160001 _32603 h1)). Qed.
Lemma lem3160006 (_32603 : int) : (term536 _32603) = (term520 _32603).
Proof. exact (@lem1982763 (term263 _32603) (real_of_int _32603) term160). Qed.
Lemma lem3160007 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3160009 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160010 : term93 = term182.
Proof. exact (@lem3160009 term2). Qed.
Lemma lem3160012 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160013 : term160 = term161.
Proof. exact (@lem3160012 term2). Qed.
Lemma lem3160014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160015 : term460 = term461.
Proof. exact (MK_COMB (@lem3160014) (@lem3160013)). Qed.
Lemma lem3160016 : term462 = term463.
Proof. exact (MK_COMB (@lem3160015) (@lem3160010)). Qed.
Lemma lem3160017 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3160019 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160020 : term188 = term189.
Proof. exact (@lem3160019 (NUMERAL 0) term2). Qed.
Lemma lem3160021 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160022 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160023 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160022 h1) (fun h1 : term189 = True => @lem3160021)). Qed.
Lemma lem3160024 : term189 = True.
Proof. exact (EQ_MP (@lem3160023) (@lem3160021)). Qed.
Lemma lem3160025 : term188 = True.
Proof. exact (TRANS (@lem3160020) (@lem3160024)). Qed.
Lemma lem3160026 : True = term188.
Proof. exact (SYM (@lem3160025)). Qed.
Lemma lem3160027 : term188.
Proof. exact (EQ_MP (@lem3160026) (@lem0)). Qed.
Lemma lem3160028 : term465.
Proof. exact (@lem3160017 (@lem3160027)). Qed.
Lemma lem3160030 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160031 : term188 = term189.
Proof. exact (@lem3160030 (NUMERAL 0) term2). Qed.
Lemma lem3160032 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160033 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160034 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160033 h1) (fun h1 : term189 = True => @lem3160032)). Qed.
Lemma lem3160035 : term189 = True.
Proof. exact (EQ_MP (@lem3160034) (@lem3160032)). Qed.
Lemma lem3160036 : term188 = True.
Proof. exact (TRANS (@lem3160031) (@lem3160035)). Qed.
Lemma lem3160037 : True = term188.
Proof. exact (SYM (@lem3160036)). Qed.
Lemma lem3160038 : term188.
Proof. exact (EQ_MP (@lem3160037) (@lem0)). Qed.
Lemma lem3160039 : term466.
Proof. exact (@lem3160028 (@lem3160038)). Qed.
Lemma lem3160041 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160042 : term188 = term189.
Proof. exact (@lem3160041 (NUMERAL 0) term2). Qed.
Lemma lem3160043 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160044 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160045 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160044 h1) (fun h1 : term189 = True => @lem3160043)). Qed.
Lemma lem3160046 : term189 = True.
Proof. exact (EQ_MP (@lem3160045) (@lem3160043)). Qed.
Lemma lem3160047 : term188 = True.
Proof. exact (TRANS (@lem3160042) (@lem3160046)). Qed.
Lemma lem3160048 : True = term188.
Proof. exact (SYM (@lem3160047)). Qed.
Lemma lem3160049 : term188.
Proof. exact (EQ_MP (@lem3160048) (@lem0)). Qed.
Lemma lem3160050 : term467.
Proof. exact (@lem3160039 (@lem3160049)). Qed.
Lemma lem3160052 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160053 : term169 = term170.
Proof. exact (@lem3160052 term2 term2). Qed.
Lemma lem3160054 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160055 : term172 = term2.
Proof. exact (EQ_MP (@lem3160054) (@lem940073)). Qed.
Lemma lem3160056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160057 : term170 = term93.
Proof. exact (MK_COMB (@lem3160056) (@lem3160055)). Qed.
Lemma lem3160058 : term169 = term93.
Proof. exact (TRANS (@lem3160053) (@lem3160057)). Qed.
Lemma lem3160060 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160061 : term236 = term239.
Proof. exact (@lem3160060 term2 term2). Qed.
Lemma lem3160062 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160063 : term172 = term2.
Proof. exact (EQ_MP (@lem3160062) (@lem940073)). Qed.
Lemma lem3160064 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160065 : term170 = term93.
Proof. exact (MK_COMB (@lem3160064) (@lem3160063)). Qed.
Lemma lem3160066 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160067 : term239 = term160.
Proof. exact (MK_COMB (@lem3160066) (@lem3160065)). Qed.
Lemma lem3160068 : term236 = term160.
Proof. exact (TRANS (@lem3160061) (@lem3160067)). Qed.
Lemma lem3160069 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160070 : term468 = term460.
Proof. exact (MK_COMB (@lem3160069) (@lem3160068)). Qed.
Lemma lem3160071 : term469 = term462.
Proof. exact (MK_COMB (@lem3160070) (@lem3160058)). Qed.
Lemma lem3160073 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3160074 : term462 = term79.
Proof. exact (@lem3160073 term2). Qed.
Lemma lem3160075 : term469 = term79.
Proof. exact (TRANS (@lem3160071) (@lem3160074)). Qed.
Lemma lem3160076 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160077 : term471 = term273.
Proof. exact (MK_COMB (@lem3160076) (@lem3160075)). Qed.
Lemma lem3160078 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3160079 : term472 = term275.
Proof. exact (MK_COMB (@lem3160077) (@lem3160078)). Qed.
Lemma lem3160081 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160082 : term275 = term79.
Proof. exact (@lem3160081 term2). Qed.
Lemma lem3160083 : term472 = term79.
Proof. exact (TRANS (@lem3160079) (@lem3160082)). Qed.
Lemma lem3160085 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160086 : term169 = term170.
Proof. exact (@lem3160085 term2 term2). Qed.
Lemma lem3160087 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160088 : term172 = term2.
Proof. exact (EQ_MP (@lem3160087) (@lem940073)). Qed.
Lemma lem3160089 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160090 : term170 = term93.
Proof. exact (MK_COMB (@lem3160089) (@lem3160088)). Qed.
Lemma lem3160091 : term169 = term93.
Proof. exact (TRANS (@lem3160086) (@lem3160090)). Qed.
Lemma lem3160092 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3160093 : term277 = term275.
Proof. exact (MK_COMB (@lem3160092) (@lem3160091)). Qed.
Lemma lem3160095 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160096 : term275 = term79.
Proof. exact (@lem3160095 term2). Qed.
Lemma lem3160097 : term277 = term79.
Proof. exact (TRANS (@lem3160093) (@lem3160096)). Qed.
Lemma lem3160098 : term79 = term277.
Proof. exact (SYM (@lem3160097)). Qed.
Lemma lem3160099 : term472 = term277.
Proof. exact (TRANS (@lem3160083) (@lem3160098)). Qed.
Lemma lem3160100 : term463 = term157.
Proof. exact (@lem3160050 (@lem3160099)). Qed.
Lemma lem3160101 : term462 = term157.
Proof. exact (TRANS (@lem3160016) (@lem3160100)). Qed.
Lemma lem3160103 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3160104 : term157 = term79.
Proof. exact (@lem3160103 term79). Qed.
Lemma lem3160105 : term462 = term79.
Proof. exact (TRANS (@lem3160101) (@lem3160104)). Qed.
Lemma lem3160106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160107 : term473 = term273.
Proof. exact (MK_COMB (@lem3160106) (@lem3160105)). Qed.
Lemma lem3160108 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3160109 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3160107) (@lem3160108 _32603)). Qed.
Lemma lem3160110 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3160007 _32603) (@lem3160109 _32603)). Qed.
Lemma lem3160111 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3160112 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3160110 _32603) (@lem3160111 _32603)). Qed.
Lemma lem3160113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160114 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3160113) (@lem3160112 _32603)). Qed.
Lemma lem3160115 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3160116 (_32603 : int) : (term520 _32603) = term490.
Proof. exact (MK_COMB (@lem3160114 _32603) (@lem3160115)). Qed.
Lemma lem3160117 (_32603 : int) : (term536 _32603) = term490.
Proof. exact (TRANS (@lem3160006 _32603) (@lem3160116 _32603)). Qed.
Lemma lem3160118 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3160119 (_32603 : int) : (term536 _32603) = term160.
Proof. exact (TRANS (@lem3160117 _32603) (@lem3160118)). Qed.
Lemma lem3160120 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3160121 (_32603 : int) : (term537 _32603) = term492.
Proof. exact (MK_COMB (@lem3160120) (@lem3160119 _32603)). Qed.
Lemma lem3160122 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3160123 (_32603 : int) : (term535 _32603) = term493.
Proof. exact (MK_COMB (@lem3160121 _32603) (@lem3160122)). Qed.
Lemma lem3160124 (_32603 : int) (h1 : term522 _32603) : term493.
Proof. exact (EQ_MP (@lem3160123 _32603) (@lem3160005 _32603 h1)). Qed.
Lemma lem3160126 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3160127 : term493 = term494.
Proof. exact (@lem3160126 term79 term160). Qed.
Lemma lem3160129 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160130 : term160 = term161.
Proof. exact (@lem3160129 term2). Qed.
Lemma lem3160132 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160133 : term79 = term157.
Proof. exact (@lem3160132 (NUMERAL 0)). Qed.
Lemma lem3160134 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3160135 : term81 = term495.
Proof. exact (MK_COMB (@lem3160134) (@lem3160133)). Qed.
Lemma lem3160136 : term494 = term496.
Proof. exact (MK_COMB (@lem3160135) (@lem3160130)). Qed.
Lemma lem3160137 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3160139 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160140 : term188 = term189.
Proof. exact (@lem3160139 (NUMERAL 0) term2). Qed.
Lemma lem3160141 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160142 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160143 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160142 h1) (fun h1 : term189 = True => @lem3160141)). Qed.
Lemma lem3160144 : term189 = True.
Proof. exact (EQ_MP (@lem3160143) (@lem3160141)). Qed.
Lemma lem3160145 : term188 = True.
Proof. exact (TRANS (@lem3160140) (@lem3160144)). Qed.
Lemma lem3160146 : True = term188.
Proof. exact (SYM (@lem3160145)). Qed.
Lemma lem3160147 : term188.
Proof. exact (EQ_MP (@lem3160146) (@lem0)). Qed.
Lemma lem3160148 : term498.
Proof. exact (@lem3160137 (@lem3160147)). Qed.
Lemma lem3160150 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160151 : term188 = term189.
Proof. exact (@lem3160150 (NUMERAL 0) term2). Qed.
Lemma lem3160152 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160153 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160154 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160153 h1) (fun h1 : term189 = True => @lem3160152)). Qed.
Lemma lem3160155 : term189 = True.
Proof. exact (EQ_MP (@lem3160154) (@lem3160152)). Qed.
Lemma lem3160156 : term188 = True.
Proof. exact (TRANS (@lem3160151) (@lem3160155)). Qed.
Lemma lem3160157 : True = term188.
Proof. exact (SYM (@lem3160156)). Qed.
Lemma lem3160158 : term188.
Proof. exact (EQ_MP (@lem3160157) (@lem0)). Qed.
Lemma lem3160159 : term496 = term499.
Proof. exact (@lem3160148 (@lem3160158)). Qed.
Lemma lem3160161 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160162 : term236 = term239.
Proof. exact (@lem3160161 term2 term2). Qed.
Lemma lem3160163 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160164 : term172 = term2.
Proof. exact (EQ_MP (@lem3160163) (@lem940073)). Qed.
Lemma lem3160165 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160166 : term170 = term93.
Proof. exact (MK_COMB (@lem3160165) (@lem3160164)). Qed.
Lemma lem3160167 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160168 : term239 = term160.
Proof. exact (MK_COMB (@lem3160167) (@lem3160166)). Qed.
Lemma lem3160169 : term236 = term160.
Proof. exact (TRANS (@lem3160162) (@lem3160168)). Qed.
Lemma lem3160171 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160172 : term275 = term79.
Proof. exact (@lem3160171 term2). Qed.
Lemma lem3160173 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3160174 : term500 = term81.
Proof. exact (MK_COMB (@lem3160173) (@lem3160172)). Qed.
Lemma lem3160175 : term499 = term494.
Proof. exact (MK_COMB (@lem3160174) (@lem3160169)). Qed.
Lemma lem3160177 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3160178 : term494 = term503.
Proof. exact (@lem3160177 (NUMERAL 0) term2). Qed.
Lemma lem3160179 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160180 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3160181 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160180 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3160179)). Qed.
Lemma lem3160182 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3160181) (@lem3160179)). Qed.
Lemma lem3160183 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3160184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3160185 : term504 = (and True).
Proof. exact (MK_COMB (@lem3160184) (@lem3160183)). Qed.
Lemma lem3160186 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3160185) (@lem3160182)). Qed.
Lemma lem3160188 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3160189 : term503 = False.
Proof. exact (TRANS (@lem3160186) (@lem3160188)). Qed.
Lemma lem3160190 : term494 = False.
Proof. exact (TRANS (@lem3160178) (@lem3160189)). Qed.
Lemma lem3160191 : term499 = False.
Proof. exact (TRANS (@lem3160175) (@lem3160190)). Qed.
Lemma lem3160192 : term496 = False.
Proof. exact (TRANS (@lem3160159) (@lem3160191)). Qed.
Lemma lem3160193 : term494 = False.
Proof. exact (TRANS (@lem3160136) (@lem3160192)). Qed.
Lemma lem3160194 : term493 = False.
Proof. exact (TRANS (@lem3160127) (@lem3160193)). Qed.
Lemma lem3160195 (_32603 : int) (h1 : term522 _32603) : False.
Proof. exact (EQ_MP (@lem3160194) (@lem3160124 _32603 h1)). Qed.
Lemma lem3160196 (_32603 : int) (h1 : term421 _32603) : False.
Proof. exact (or_elim (@lem3159495 _32603 h1) (fun h0 : term505 _32603 => @lem3159845 _32603 h0) (fun h0 : term522 _32603 => @lem3160195 _32603 h0)). Qed.
Lemma lem3160197 (_32603 : int) (h1 : term417 _32603) : term417 _32603.
Proof. exact (h1). Qed.
Lemma lem3160198 (_32603 : int) (h1 : term538 _32603) : term538 _32603.
Proof. exact (h1). Qed.
Lemma lem3160199 (_32603 : int) (h1 : term538 _32603) : term418 _32603.
Proof. exact (proj2 (@lem3160198 _32603 h1)). Qed.
Lemma lem3160201 (_32603 : int) (h1 : term538 _32603) : term294 _32603.
Proof. exact (proj2 (@lem3160199 _32603 h1)). Qed.
Lemma lem3160202 (_32603 : int) (h1 : term538 _32603) : term325 _32603.
Proof. exact (proj1 (@lem3160199 _32603 h1)). Qed.
Lemma lem3160203 (_32603 : int) (h1 : term538 _32603) : term230 _32603.
Proof. exact (proj2 (@lem3160202 _32603 h1)). Qed.
Lemma lem3160206 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3160207 : term433 = term188.
Proof. exact (@lem3160206 term79 term93). Qed.
Lemma lem3160209 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160210 : term93 = term182.
Proof. exact (@lem3160209 term2). Qed.
Lemma lem3160212 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160213 : term79 = term157.
Proof. exact (@lem3160212 (NUMERAL 0)). Qed.
Lemma lem3160214 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160215 : term434 = term435.
Proof. exact (MK_COMB (@lem3160214) (@lem3160213)). Qed.
Lemma lem3160216 : term188 = term436.
Proof. exact (MK_COMB (@lem3160215) (@lem3160210)). Qed.
Lemma lem3160217 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3160219 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160220 : term188 = term189.
Proof. exact (@lem3160219 (NUMERAL 0) term2). Qed.
Lemma lem3160221 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160222 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160223 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160222 h1) (fun h1 : term189 = True => @lem3160221)). Qed.
Lemma lem3160224 : term189 = True.
Proof. exact (EQ_MP (@lem3160223) (@lem3160221)). Qed.
Lemma lem3160225 : term188 = True.
Proof. exact (TRANS (@lem3160220) (@lem3160224)). Qed.
Lemma lem3160226 : True = term188.
Proof. exact (SYM (@lem3160225)). Qed.
Lemma lem3160227 : term188.
Proof. exact (EQ_MP (@lem3160226) (@lem0)). Qed.
Lemma lem3160228 : term438.
Proof. exact (@lem3160217 (@lem3160227)). Qed.
Lemma lem3160230 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160231 : term188 = term189.
Proof. exact (@lem3160230 (NUMERAL 0) term2). Qed.
Lemma lem3160232 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160233 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160234 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160233 h1) (fun h1 : term189 = True => @lem3160232)). Qed.
Lemma lem3160235 : term189 = True.
Proof. exact (EQ_MP (@lem3160234) (@lem3160232)). Qed.
Lemma lem3160236 : term188 = True.
Proof. exact (TRANS (@lem3160231) (@lem3160235)). Qed.
Lemma lem3160237 : True = term188.
Proof. exact (SYM (@lem3160236)). Qed.
Lemma lem3160238 : term188.
Proof. exact (EQ_MP (@lem3160237) (@lem0)). Qed.
Lemma lem3160239 : term436 = term439.
Proof. exact (@lem3160228 (@lem3160238)). Qed.
Lemma lem3160241 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160242 : term169 = term170.
Proof. exact (@lem3160241 term2 term2). Qed.
Lemma lem3160243 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160244 : term172 = term2.
Proof. exact (EQ_MP (@lem3160243) (@lem940073)). Qed.
Lemma lem3160245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160246 : term170 = term93.
Proof. exact (MK_COMB (@lem3160245) (@lem3160244)). Qed.
Lemma lem3160247 : term169 = term93.
Proof. exact (TRANS (@lem3160242) (@lem3160246)). Qed.
Lemma lem3160249 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160250 : term275 = term79.
Proof. exact (@lem3160249 term2). Qed.
Lemma lem3160251 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160252 : term440 = term434.
Proof. exact (MK_COMB (@lem3160251) (@lem3160250)). Qed.
Lemma lem3160253 : term439 = term188.
Proof. exact (MK_COMB (@lem3160252) (@lem3160247)). Qed.
Lemma lem3160255 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160256 : term188 = term189.
Proof. exact (@lem3160255 (NUMERAL 0) term2). Qed.
Lemma lem3160257 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160258 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160259 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160258 h1) (fun h1 : term189 = True => @lem3160257)). Qed.
Lemma lem3160260 : term189 = True.
Proof. exact (EQ_MP (@lem3160259) (@lem3160257)). Qed.
Lemma lem3160261 : term188 = True.
Proof. exact (TRANS (@lem3160256) (@lem3160260)). Qed.
Lemma lem3160262 : term439 = True.
Proof. exact (TRANS (@lem3160253) (@lem3160261)). Qed.
Lemma lem3160263 : term436 = True.
Proof. exact (TRANS (@lem3160239) (@lem3160262)). Qed.
Lemma lem3160264 : term188 = True.
Proof. exact (TRANS (@lem3160216) (@lem3160263)). Qed.
Lemma lem3160265 : term433 = True.
Proof. exact (TRANS (@lem3160207) (@lem3160264)). Qed.
Lemma lem3160266 : True = term433.
Proof. exact (SYM (@lem3160265)). Qed.
Lemma lem3160267 : term433.
Proof. exact (EQ_MP (@lem3160266) (@lem0)). Qed.
Lemma lem3160268 (_32603 : int) (h1 : term538 _32603) : term441 _32603.
Proof. exact (conj (@lem3160267) (@lem3160203 _32603 h1)). Qed.
Lemma lem3160270 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3160271 (_32603 : int) : term443 _32603.
Proof. exact (@lem3160270 term93 (term227 _32603)). Qed.
Lemma lem3160272 (_32603 : int) (h1 : term538 _32603) : term444 _32603.
Proof. exact (@lem3160271 _32603 (@lem3160268 _32603 h1)). Qed.
Lemma lem3160273 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3160274 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3160275 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3160274) (@lem3160273 _32603)). Qed.
Lemma lem3160276 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3160277 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3160275 _32603) (@lem3160276)). Qed.
Lemma lem3160278 (_32603 : int) (h1 : term538 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3160277 _32603) (@lem3160272 _32603 h1)). Qed.
Lemma lem3160280 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3160281 : term433 = term188.
Proof. exact (@lem3160280 term79 term93). Qed.
Lemma lem3160283 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160284 : term93 = term182.
Proof. exact (@lem3160283 term2). Qed.
Lemma lem3160286 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160287 : term79 = term157.
Proof. exact (@lem3160286 (NUMERAL 0)). Qed.
Lemma lem3160288 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160289 : term434 = term435.
Proof. exact (MK_COMB (@lem3160288) (@lem3160287)). Qed.
Lemma lem3160290 : term188 = term436.
Proof. exact (MK_COMB (@lem3160289) (@lem3160284)). Qed.
Lemma lem3160291 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3160293 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160294 : term188 = term189.
Proof. exact (@lem3160293 (NUMERAL 0) term2). Qed.
Lemma lem3160295 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160296 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160297 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160296 h1) (fun h1 : term189 = True => @lem3160295)). Qed.
Lemma lem3160298 : term189 = True.
Proof. exact (EQ_MP (@lem3160297) (@lem3160295)). Qed.
Lemma lem3160299 : term188 = True.
Proof. exact (TRANS (@lem3160294) (@lem3160298)). Qed.
Lemma lem3160300 : True = term188.
Proof. exact (SYM (@lem3160299)). Qed.
Lemma lem3160301 : term188.
Proof. exact (EQ_MP (@lem3160300) (@lem0)). Qed.
Lemma lem3160302 : term438.
Proof. exact (@lem3160291 (@lem3160301)). Qed.
Lemma lem3160304 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160305 : term188 = term189.
Proof. exact (@lem3160304 (NUMERAL 0) term2). Qed.
Lemma lem3160306 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160307 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160308 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160307 h1) (fun h1 : term189 = True => @lem3160306)). Qed.
Lemma lem3160309 : term189 = True.
Proof. exact (EQ_MP (@lem3160308) (@lem3160306)). Qed.
Lemma lem3160310 : term188 = True.
Proof. exact (TRANS (@lem3160305) (@lem3160309)). Qed.
Lemma lem3160311 : True = term188.
Proof. exact (SYM (@lem3160310)). Qed.
Lemma lem3160312 : term188.
Proof. exact (EQ_MP (@lem3160311) (@lem0)). Qed.
Lemma lem3160313 : term436 = term439.
Proof. exact (@lem3160302 (@lem3160312)). Qed.
Lemma lem3160315 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160316 : term169 = term170.
Proof. exact (@lem3160315 term2 term2). Qed.
Lemma lem3160317 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160318 : term172 = term2.
Proof. exact (EQ_MP (@lem3160317) (@lem940073)). Qed.
Lemma lem3160319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160320 : term170 = term93.
Proof. exact (MK_COMB (@lem3160319) (@lem3160318)). Qed.
Lemma lem3160321 : term169 = term93.
Proof. exact (TRANS (@lem3160316) (@lem3160320)). Qed.
Lemma lem3160323 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160324 : term275 = term79.
Proof. exact (@lem3160323 term2). Qed.
Lemma lem3160325 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160326 : term440 = term434.
Proof. exact (MK_COMB (@lem3160325) (@lem3160324)). Qed.
Lemma lem3160327 : term439 = term188.
Proof. exact (MK_COMB (@lem3160326) (@lem3160321)). Qed.
Lemma lem3160329 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160330 : term188 = term189.
Proof. exact (@lem3160329 (NUMERAL 0) term2). Qed.
Lemma lem3160331 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160332 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160333 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160332 h1) (fun h1 : term189 = True => @lem3160331)). Qed.
Lemma lem3160334 : term189 = True.
Proof. exact (EQ_MP (@lem3160333) (@lem3160331)). Qed.
Lemma lem3160335 : term188 = True.
Proof. exact (TRANS (@lem3160330) (@lem3160334)). Qed.
Lemma lem3160336 : term439 = True.
Proof. exact (TRANS (@lem3160327) (@lem3160335)). Qed.
Lemma lem3160337 : term436 = True.
Proof. exact (TRANS (@lem3160313) (@lem3160336)). Qed.
Lemma lem3160338 : term188 = True.
Proof. exact (TRANS (@lem3160290) (@lem3160337)). Qed.
Lemma lem3160339 : term433 = True.
Proof. exact (TRANS (@lem3160281) (@lem3160338)). Qed.
Lemma lem3160340 : True = term433.
Proof. exact (SYM (@lem3160339)). Qed.
Lemma lem3160341 : term433.
Proof. exact (EQ_MP (@lem3160340) (@lem0)). Qed.
Lemma lem3160342 (_32603 : int) (h1 : term538 _32603) : term447 _32603.
Proof. exact (conj (@lem3160341) (@lem3160201 _32603 h1)). Qed.
Lemma lem3160344 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3160345 (_32603 : int) : term448 _32603.
Proof. exact (@lem3160344 term93 (term291 _32603)). Qed.
Lemma lem3160346 (_32603 : int) (h1 : term538 _32603) : term449 _32603.
Proof. exact (@lem3160345 _32603 (@lem3160342 _32603 h1)). Qed.
Lemma lem3160347 (_32603 : int) : (term450 _32603) = (term291 _32603).
Proof. exact (@lem1982733 (term291 _32603)). Qed.
Lemma lem3160348 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3160349 (_32603 : int) : (term451 _32603) = (term293 _32603).
Proof. exact (MK_COMB (@lem3160348) (@lem3160347 _32603)). Qed.
Lemma lem3160350 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3160351 (_32603 : int) : (term449 _32603) = (term294 _32603).
Proof. exact (MK_COMB (@lem3160349 _32603) (@lem3160350)). Qed.
Lemma lem3160352 (_32603 : int) (h1 : term538 _32603) : term294 _32603.
Proof. exact (EQ_MP (@lem3160351 _32603) (@lem3160346 _32603 h1)). Qed.
Lemma lem3160353 (_32603 : int) (h1 : term538 _32603) : term452 _32603.
Proof. exact (conj (@lem3160352 _32603 h1) (@lem3160278 _32603 h1)). Qed.
Lemma lem3160355 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3160356 (_32603 : int) : term454 _32603.
Proof. exact (@lem3160355 (term291 _32603) (term227 _32603)). Qed.
Lemma lem3160357 (_32603 : int) (h1 : term538 _32603) : term455 _32603.
Proof. exact (@lem3160356 _32603 (@lem3160353 _32603 h1)). Qed.
Lemma lem3160358 (_32603 : int) : (term456 _32603) = (term457 _32603).
Proof. exact (@lem1982753 (term263 _32603) (real_of_int _32603) term93 term223). Qed.
Lemma lem3160359 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3160361 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160362 : term93 = term182.
Proof. exact (@lem3160361 term2). Qed.
Lemma lem3160364 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160365 : term160 = term161.
Proof. exact (@lem3160364 term2). Qed.
Lemma lem3160366 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160367 : term460 = term461.
Proof. exact (MK_COMB (@lem3160366) (@lem3160365)). Qed.
Lemma lem3160368 : term462 = term463.
Proof. exact (MK_COMB (@lem3160367) (@lem3160362)). Qed.
Lemma lem3160369 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3160371 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160372 : term188 = term189.
Proof. exact (@lem3160371 (NUMERAL 0) term2). Qed.
Lemma lem3160373 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160374 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160375 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160374 h1) (fun h1 : term189 = True => @lem3160373)). Qed.
Lemma lem3160376 : term189 = True.
Proof. exact (EQ_MP (@lem3160375) (@lem3160373)). Qed.
Lemma lem3160377 : term188 = True.
Proof. exact (TRANS (@lem3160372) (@lem3160376)). Qed.
Lemma lem3160378 : True = term188.
Proof. exact (SYM (@lem3160377)). Qed.
Lemma lem3160379 : term188.
Proof. exact (EQ_MP (@lem3160378) (@lem0)). Qed.
Lemma lem3160380 : term465.
Proof. exact (@lem3160369 (@lem3160379)). Qed.
Lemma lem3160382 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160383 : term188 = term189.
Proof. exact (@lem3160382 (NUMERAL 0) term2). Qed.
Lemma lem3160384 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160385 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160386 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160385 h1) (fun h1 : term189 = True => @lem3160384)). Qed.
Lemma lem3160387 : term189 = True.
Proof. exact (EQ_MP (@lem3160386) (@lem3160384)). Qed.
Lemma lem3160388 : term188 = True.
Proof. exact (TRANS (@lem3160383) (@lem3160387)). Qed.
Lemma lem3160389 : True = term188.
Proof. exact (SYM (@lem3160388)). Qed.
Lemma lem3160390 : term188.
Proof. exact (EQ_MP (@lem3160389) (@lem0)). Qed.
Lemma lem3160391 : term466.
Proof. exact (@lem3160380 (@lem3160390)). Qed.
Lemma lem3160393 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160394 : term188 = term189.
Proof. exact (@lem3160393 (NUMERAL 0) term2). Qed.
Lemma lem3160395 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160396 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160397 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160396 h1) (fun h1 : term189 = True => @lem3160395)). Qed.
Lemma lem3160398 : term189 = True.
Proof. exact (EQ_MP (@lem3160397) (@lem3160395)). Qed.
Lemma lem3160399 : term188 = True.
Proof. exact (TRANS (@lem3160394) (@lem3160398)). Qed.
Lemma lem3160400 : True = term188.
Proof. exact (SYM (@lem3160399)). Qed.
Lemma lem3160401 : term188.
Proof. exact (EQ_MP (@lem3160400) (@lem0)). Qed.
Lemma lem3160402 : term467.
Proof. exact (@lem3160391 (@lem3160401)). Qed.
Lemma lem3160404 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160405 : term169 = term170.
Proof. exact (@lem3160404 term2 term2). Qed.
Lemma lem3160406 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160407 : term172 = term2.
Proof. exact (EQ_MP (@lem3160406) (@lem940073)). Qed.
Lemma lem3160408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160409 : term170 = term93.
Proof. exact (MK_COMB (@lem3160408) (@lem3160407)). Qed.
Lemma lem3160410 : term169 = term93.
Proof. exact (TRANS (@lem3160405) (@lem3160409)). Qed.
Lemma lem3160412 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160413 : term236 = term239.
Proof. exact (@lem3160412 term2 term2). Qed.
Lemma lem3160414 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160415 : term172 = term2.
Proof. exact (EQ_MP (@lem3160414) (@lem940073)). Qed.
Lemma lem3160416 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160417 : term170 = term93.
Proof. exact (MK_COMB (@lem3160416) (@lem3160415)). Qed.
Lemma lem3160418 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160419 : term239 = term160.
Proof. exact (MK_COMB (@lem3160418) (@lem3160417)). Qed.
Lemma lem3160420 : term236 = term160.
Proof. exact (TRANS (@lem3160413) (@lem3160419)). Qed.
Lemma lem3160421 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160422 : term468 = term460.
Proof. exact (MK_COMB (@lem3160421) (@lem3160420)). Qed.
Lemma lem3160423 : term469 = term462.
Proof. exact (MK_COMB (@lem3160422) (@lem3160410)). Qed.
Lemma lem3160425 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3160426 : term462 = term79.
Proof. exact (@lem3160425 term2). Qed.
Lemma lem3160427 : term469 = term79.
Proof. exact (TRANS (@lem3160423) (@lem3160426)). Qed.
Lemma lem3160428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160429 : term471 = term273.
Proof. exact (MK_COMB (@lem3160428) (@lem3160427)). Qed.
Lemma lem3160430 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3160431 : term472 = term275.
Proof. exact (MK_COMB (@lem3160429) (@lem3160430)). Qed.
Lemma lem3160433 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160434 : term275 = term79.
Proof. exact (@lem3160433 term2). Qed.
Lemma lem3160435 : term472 = term79.
Proof. exact (TRANS (@lem3160431) (@lem3160434)). Qed.
Lemma lem3160437 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160438 : term169 = term170.
Proof. exact (@lem3160437 term2 term2). Qed.
Lemma lem3160439 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160440 : term172 = term2.
Proof. exact (EQ_MP (@lem3160439) (@lem940073)). Qed.
Lemma lem3160441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160442 : term170 = term93.
Proof. exact (MK_COMB (@lem3160441) (@lem3160440)). Qed.
Lemma lem3160443 : term169 = term93.
Proof. exact (TRANS (@lem3160438) (@lem3160442)). Qed.
Lemma lem3160444 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3160445 : term277 = term275.
Proof. exact (MK_COMB (@lem3160444) (@lem3160443)). Qed.
Lemma lem3160447 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160448 : term275 = term79.
Proof. exact (@lem3160447 term2). Qed.
Lemma lem3160449 : term277 = term79.
Proof. exact (TRANS (@lem3160445) (@lem3160448)). Qed.
Lemma lem3160450 : term79 = term277.
Proof. exact (SYM (@lem3160449)). Qed.
Lemma lem3160451 : term472 = term277.
Proof. exact (TRANS (@lem3160435) (@lem3160450)). Qed.
Lemma lem3160452 : term463 = term157.
Proof. exact (@lem3160402 (@lem3160451)). Qed.
Lemma lem3160453 : term462 = term157.
Proof. exact (TRANS (@lem3160368) (@lem3160452)). Qed.
Lemma lem3160455 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3160456 : term157 = term79.
Proof. exact (@lem3160455 term79). Qed.
Lemma lem3160457 : term462 = term79.
Proof. exact (TRANS (@lem3160453) (@lem3160456)). Qed.
Lemma lem3160458 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160459 : term473 = term273.
Proof. exact (MK_COMB (@lem3160458) (@lem3160457)). Qed.
Lemma lem3160460 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3160461 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3160459) (@lem3160460 _32603)). Qed.
Lemma lem3160462 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3160359 _32603) (@lem3160461 _32603)). Qed.
Lemma lem3160463 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3160464 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3160462 _32603) (@lem3160463 _32603)). Qed.
Lemma lem3160465 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160466 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3160465) (@lem3160464 _32603)). Qed.
Lemma lem3160468 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160469 : term223 = term226.
Proof. exact (@lem3160468 term200). Qed.
Lemma lem3160471 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160472 : term93 = term182.
Proof. exact (@lem3160471 term2). Qed.
Lemma lem3160473 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160474 : term95 = term183.
Proof. exact (MK_COMB (@lem3160473) (@lem3160472)). Qed.
Lemma lem3160475 : term476 = term477.
Proof. exact (MK_COMB (@lem3160474) (@lem3160469)). Qed.
Lemma lem3160476 : term478.
Proof. exact (@lem1981473 term93 term93 term223 term93 term160 term93). Qed.
Lemma lem3160478 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160479 : term188 = term189.
Proof. exact (@lem3160478 (NUMERAL 0) term2). Qed.
Lemma lem3160480 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160481 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160482 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160481 h1) (fun h1 : term189 = True => @lem3160480)). Qed.
Lemma lem3160483 : term189 = True.
Proof. exact (EQ_MP (@lem3160482) (@lem3160480)). Qed.
Lemma lem3160484 : term188 = True.
Proof. exact (TRANS (@lem3160479) (@lem3160483)). Qed.
Lemma lem3160485 : True = term188.
Proof. exact (SYM (@lem3160484)). Qed.
Lemma lem3160486 : term188.
Proof. exact (EQ_MP (@lem3160485) (@lem0)). Qed.
Lemma lem3160487 : term479.
Proof. exact (@lem3160476 (@lem3160486)). Qed.
Lemma lem3160489 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160490 : term188 = term189.
Proof. exact (@lem3160489 (NUMERAL 0) term2). Qed.
Lemma lem3160491 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160492 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160493 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160492 h1) (fun h1 : term189 = True => @lem3160491)). Qed.
Lemma lem3160494 : term189 = True.
Proof. exact (EQ_MP (@lem3160493) (@lem3160491)). Qed.
Lemma lem3160495 : term188 = True.
Proof. exact (TRANS (@lem3160490) (@lem3160494)). Qed.
Lemma lem3160496 : True = term188.
Proof. exact (SYM (@lem3160495)). Qed.
Lemma lem3160497 : term188.
Proof. exact (EQ_MP (@lem3160496) (@lem0)). Qed.
Lemma lem3160498 : term480.
Proof. exact (@lem3160487 (@lem3160497)). Qed.
Lemma lem3160500 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160501 : term188 = term189.
Proof. exact (@lem3160500 (NUMERAL 0) term2). Qed.
Lemma lem3160502 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160503 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160504 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160503 h1) (fun h1 : term189 = True => @lem3160502)). Qed.
Lemma lem3160505 : term189 = True.
Proof. exact (EQ_MP (@lem3160504) (@lem3160502)). Qed.
Lemma lem3160506 : term188 = True.
Proof. exact (TRANS (@lem3160501) (@lem3160505)). Qed.
Lemma lem3160507 : True = term188.
Proof. exact (SYM (@lem3160506)). Qed.
Lemma lem3160508 : term188.
Proof. exact (EQ_MP (@lem3160507) (@lem0)). Qed.
Lemma lem3160509 : term481.
Proof. exact (@lem3160498 (@lem3160508)). Qed.
Lemma lem3160511 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160512 : term482 = term483.
Proof. exact (@lem3160511 term200 term2). Qed.
Lemma lem3160513 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3160514 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3160515 : term207 = term200.
Proof. exact (EQ_MP (@lem3160514) (@lem3160513)). Qed.
Lemma lem3160516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160517 : term205 = term186.
Proof. exact (MK_COMB (@lem3160516) (@lem3160515)). Qed.
Lemma lem3160518 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160519 : term483 = term223.
Proof. exact (MK_COMB (@lem3160518) (@lem3160517)). Qed.
Lemma lem3160520 : term482 = term223.
Proof. exact (TRANS (@lem3160512) (@lem3160519)). Qed.
Lemma lem3160522 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160523 : term169 = term170.
Proof. exact (@lem3160522 term2 term2). Qed.
Lemma lem3160524 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160525 : term172 = term2.
Proof. exact (EQ_MP (@lem3160524) (@lem940073)). Qed.
Lemma lem3160526 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160527 : term170 = term93.
Proof. exact (MK_COMB (@lem3160526) (@lem3160525)). Qed.
Lemma lem3160528 : term169 = term93.
Proof. exact (TRANS (@lem3160523) (@lem3160527)). Qed.
Lemma lem3160529 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160530 : term194 = term95.
Proof. exact (MK_COMB (@lem3160529) (@lem3160528)). Qed.
Lemma lem3160531 : term484 = term476.
Proof. exact (MK_COMB (@lem3160530) (@lem3160520)). Qed.
Lemma lem3160534 : term485 = term160.
Proof. exact (@lem1367771 term2 term2). Qed.
Lemma lem3160535 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3160536 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3160537 : term199 = term200.
Proof. exact (EQ_MP (@lem3160536) (@lem3160535)). Qed.
Lemma lem3160538 : term200 = term199.
Proof. exact (SYM (@lem3160537)). Qed.
Lemma lem3160539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160540 : term186 = term196.
Proof. exact (MK_COMB (@lem3160539) (@lem3160538)). Qed.
Lemma lem3160541 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160542 : term223 = term486.
Proof. exact (MK_COMB (@lem3160541) (@lem3160540)). Qed.
Lemma lem3160543 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3160544 : term476 = term485.
Proof. exact (MK_COMB (@lem3160543) (@lem3160542)). Qed.
Lemma lem3160545 : term476 = term160.
Proof. exact (TRANS (@lem3160544) (@lem3160534)). Qed.
Lemma lem3160546 : term484 = term160.
Proof. exact (TRANS (@lem3160531) (@lem3160545)). Qed.
Lemma lem3160547 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160548 : term487 = term162.
Proof. exact (MK_COMB (@lem3160547) (@lem3160546)). Qed.
Lemma lem3160549 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3160550 : term488 = term236.
Proof. exact (MK_COMB (@lem3160548) (@lem3160549)). Qed.
Lemma lem3160552 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160553 : term236 = term239.
Proof. exact (@lem3160552 term2 term2). Qed.
Lemma lem3160554 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160555 : term172 = term2.
Proof. exact (EQ_MP (@lem3160554) (@lem940073)). Qed.
Lemma lem3160556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160557 : term170 = term93.
Proof. exact (MK_COMB (@lem3160556) (@lem3160555)). Qed.
Lemma lem3160558 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160559 : term239 = term160.
Proof. exact (MK_COMB (@lem3160558) (@lem3160557)). Qed.
Lemma lem3160560 : term236 = term160.
Proof. exact (TRANS (@lem3160553) (@lem3160559)). Qed.
Lemma lem3160561 : term488 = term160.
Proof. exact (TRANS (@lem3160550) (@lem3160560)). Qed.
Lemma lem3160563 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160564 : term169 = term170.
Proof. exact (@lem3160563 term2 term2). Qed.
Lemma lem3160565 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160566 : term172 = term2.
Proof. exact (EQ_MP (@lem3160565) (@lem940073)). Qed.
Lemma lem3160567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160568 : term170 = term93.
Proof. exact (MK_COMB (@lem3160567) (@lem3160566)). Qed.
Lemma lem3160569 : term169 = term93.
Proof. exact (TRANS (@lem3160564) (@lem3160568)). Qed.
Lemma lem3160570 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem3160571 : term489 = term236.
Proof. exact (MK_COMB (@lem3160570) (@lem3160569)). Qed.
Lemma lem3160573 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160574 : term236 = term239.
Proof. exact (@lem3160573 term2 term2). Qed.
Lemma lem3160575 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160576 : term172 = term2.
Proof. exact (EQ_MP (@lem3160575) (@lem940073)). Qed.
Lemma lem3160577 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160578 : term170 = term93.
Proof. exact (MK_COMB (@lem3160577) (@lem3160576)). Qed.
Lemma lem3160579 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160580 : term239 = term160.
Proof. exact (MK_COMB (@lem3160579) (@lem3160578)). Qed.
Lemma lem3160581 : term236 = term160.
Proof. exact (TRANS (@lem3160574) (@lem3160580)). Qed.
Lemma lem3160582 : term489 = term160.
Proof. exact (TRANS (@lem3160571) (@lem3160581)). Qed.
Lemma lem3160583 : term160 = term489.
Proof. exact (SYM (@lem3160582)). Qed.
Lemma lem3160584 : term488 = term489.
Proof. exact (TRANS (@lem3160561) (@lem3160583)). Qed.
Lemma lem3160585 : term477 = term161.
Proof. exact (@lem3160509 (@lem3160584)). Qed.
Lemma lem3160586 : term476 = term161.
Proof. exact (TRANS (@lem3160475) (@lem3160585)). Qed.
Lemma lem3160588 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3160589 : term161 = term160.
Proof. exact (@lem3160588 term160). Qed.
Lemma lem3160590 : term476 = term160.
Proof. exact (TRANS (@lem3160586) (@lem3160589)). Qed.
Lemma lem3160591 (_32603 : int) : (term457 _32603) = term490.
Proof. exact (MK_COMB (@lem3160466 _32603) (@lem3160590)). Qed.
Lemma lem3160592 (_32603 : int) : (term456 _32603) = term490.
Proof. exact (TRANS (@lem3160358 _32603) (@lem3160591 _32603)). Qed.
Lemma lem3160593 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3160594 (_32603 : int) : (term456 _32603) = term160.
Proof. exact (TRANS (@lem3160592 _32603) (@lem3160593)). Qed.
Lemma lem3160595 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3160596 (_32603 : int) : (term491 _32603) = term492.
Proof. exact (MK_COMB (@lem3160595) (@lem3160594 _32603)). Qed.
Lemma lem3160597 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3160598 (_32603 : int) : (term455 _32603) = term493.
Proof. exact (MK_COMB (@lem3160596 _32603) (@lem3160597)). Qed.
Lemma lem3160599 (_32603 : int) (h1 : term538 _32603) : term493.
Proof. exact (EQ_MP (@lem3160598 _32603) (@lem3160357 _32603 h1)). Qed.
Lemma lem3160601 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3160602 : term493 = term494.
Proof. exact (@lem3160601 term79 term160). Qed.
Lemma lem3160604 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160605 : term160 = term161.
Proof. exact (@lem3160604 term2). Qed.
Lemma lem3160607 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160608 : term79 = term157.
Proof. exact (@lem3160607 (NUMERAL 0)). Qed.
Lemma lem3160609 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3160610 : term81 = term495.
Proof. exact (MK_COMB (@lem3160609) (@lem3160608)). Qed.
Lemma lem3160611 : term494 = term496.
Proof. exact (MK_COMB (@lem3160610) (@lem3160605)). Qed.
Lemma lem3160612 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3160614 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160615 : term188 = term189.
Proof. exact (@lem3160614 (NUMERAL 0) term2). Qed.
Lemma lem3160616 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160617 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160618 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160617 h1) (fun h1 : term189 = True => @lem3160616)). Qed.
Lemma lem3160619 : term189 = True.
Proof. exact (EQ_MP (@lem3160618) (@lem3160616)). Qed.
Lemma lem3160620 : term188 = True.
Proof. exact (TRANS (@lem3160615) (@lem3160619)). Qed.
Lemma lem3160621 : True = term188.
Proof. exact (SYM (@lem3160620)). Qed.
Lemma lem3160622 : term188.
Proof. exact (EQ_MP (@lem3160621) (@lem0)). Qed.
Lemma lem3160623 : term498.
Proof. exact (@lem3160612 (@lem3160622)). Qed.
Lemma lem3160625 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160626 : term188 = term189.
Proof. exact (@lem3160625 (NUMERAL 0) term2). Qed.
Lemma lem3160627 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160628 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160629 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160628 h1) (fun h1 : term189 = True => @lem3160627)). Qed.
Lemma lem3160630 : term189 = True.
Proof. exact (EQ_MP (@lem3160629) (@lem3160627)). Qed.
Lemma lem3160631 : term188 = True.
Proof. exact (TRANS (@lem3160626) (@lem3160630)). Qed.
Lemma lem3160632 : True = term188.
Proof. exact (SYM (@lem3160631)). Qed.
Lemma lem3160633 : term188.
Proof. exact (EQ_MP (@lem3160632) (@lem0)). Qed.
Lemma lem3160634 : term496 = term499.
Proof. exact (@lem3160623 (@lem3160633)). Qed.
Lemma lem3160636 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160637 : term236 = term239.
Proof. exact (@lem3160636 term2 term2). Qed.
Lemma lem3160638 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160639 : term172 = term2.
Proof. exact (EQ_MP (@lem3160638) (@lem940073)). Qed.
Lemma lem3160640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160641 : term170 = term93.
Proof. exact (MK_COMB (@lem3160640) (@lem3160639)). Qed.
Lemma lem3160642 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160643 : term239 = term160.
Proof. exact (MK_COMB (@lem3160642) (@lem3160641)). Qed.
Lemma lem3160644 : term236 = term160.
Proof. exact (TRANS (@lem3160637) (@lem3160643)). Qed.
Lemma lem3160646 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160647 : term275 = term79.
Proof. exact (@lem3160646 term2). Qed.
Lemma lem3160648 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3160649 : term500 = term81.
Proof. exact (MK_COMB (@lem3160648) (@lem3160647)). Qed.
Lemma lem3160650 : term499 = term494.
Proof. exact (MK_COMB (@lem3160649) (@lem3160644)). Qed.
Lemma lem3160652 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3160653 : term494 = term503.
Proof. exact (@lem3160652 (NUMERAL 0) term2). Qed.
Lemma lem3160654 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160655 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3160656 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160655 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3160654)). Qed.
Lemma lem3160657 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3160656) (@lem3160654)). Qed.
Lemma lem3160658 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3160659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3160660 : term504 = (and True).
Proof. exact (MK_COMB (@lem3160659) (@lem3160658)). Qed.
Lemma lem3160661 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3160660) (@lem3160657)). Qed.
Lemma lem3160663 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3160664 : term503 = False.
Proof. exact (TRANS (@lem3160661) (@lem3160663)). Qed.
Lemma lem3160665 : term494 = False.
Proof. exact (TRANS (@lem3160653) (@lem3160664)). Qed.
Lemma lem3160666 : term499 = False.
Proof. exact (TRANS (@lem3160650) (@lem3160665)). Qed.
Lemma lem3160667 : term496 = False.
Proof. exact (TRANS (@lem3160634) (@lem3160666)). Qed.
Lemma lem3160668 : term494 = False.
Proof. exact (TRANS (@lem3160611) (@lem3160667)). Qed.
Lemma lem3160669 : term493 = False.
Proof. exact (TRANS (@lem3160602) (@lem3160668)). Qed.
Lemma lem3160670 (_32603 : int) (h1 : term538 _32603) : False.
Proof. exact (EQ_MP (@lem3160669) (@lem3160599 _32603 h1)). Qed.
Lemma lem3160671 (_32603 : int) (h1 : term539 _32603) : term539 _32603.
Proof. exact (h1). Qed.
Lemma lem3160672 (_32603 : int) (h1 : term539 _32603) : term419 _32603.
Proof. exact (proj2 (@lem3160671 _32603 h1)). Qed.
Lemma lem3160674 (_32603 : int) (h1 : term539 _32603) : term294 _32603.
Proof. exact (proj2 (@lem3160672 _32603 h1)). Qed.
Lemma lem3160675 (_32603 : int) (h1 : term539 _32603) : term326 _32603.
Proof. exact (proj1 (@lem3160672 _32603 h1)). Qed.
Lemma lem3160676 (_32603 : int) (h1 : term539 _32603) : term230 _32603.
Proof. exact (proj2 (@lem3160675 _32603 h1)). Qed.
Lemma lem3160679 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3160680 : term433 = term188.
Proof. exact (@lem3160679 term79 term93). Qed.
Lemma lem3160682 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160683 : term93 = term182.
Proof. exact (@lem3160682 term2). Qed.
Lemma lem3160685 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160686 : term79 = term157.
Proof. exact (@lem3160685 (NUMERAL 0)). Qed.
Lemma lem3160687 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160688 : term434 = term435.
Proof. exact (MK_COMB (@lem3160687) (@lem3160686)). Qed.
Lemma lem3160689 : term188 = term436.
Proof. exact (MK_COMB (@lem3160688) (@lem3160683)). Qed.
Lemma lem3160690 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3160692 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160693 : term188 = term189.
Proof. exact (@lem3160692 (NUMERAL 0) term2). Qed.
Lemma lem3160694 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160695 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160696 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160695 h1) (fun h1 : term189 = True => @lem3160694)). Qed.
Lemma lem3160697 : term189 = True.
Proof. exact (EQ_MP (@lem3160696) (@lem3160694)). Qed.
Lemma lem3160698 : term188 = True.
Proof. exact (TRANS (@lem3160693) (@lem3160697)). Qed.
Lemma lem3160699 : True = term188.
Proof. exact (SYM (@lem3160698)). Qed.
Lemma lem3160700 : term188.
Proof. exact (EQ_MP (@lem3160699) (@lem0)). Qed.
Lemma lem3160701 : term438.
Proof. exact (@lem3160690 (@lem3160700)). Qed.
Lemma lem3160703 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160704 : term188 = term189.
Proof. exact (@lem3160703 (NUMERAL 0) term2). Qed.
Lemma lem3160705 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160706 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160707 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160706 h1) (fun h1 : term189 = True => @lem3160705)). Qed.
Lemma lem3160708 : term189 = True.
Proof. exact (EQ_MP (@lem3160707) (@lem3160705)). Qed.
Lemma lem3160709 : term188 = True.
Proof. exact (TRANS (@lem3160704) (@lem3160708)). Qed.
Lemma lem3160710 : True = term188.
Proof. exact (SYM (@lem3160709)). Qed.
Lemma lem3160711 : term188.
Proof. exact (EQ_MP (@lem3160710) (@lem0)). Qed.
Lemma lem3160712 : term436 = term439.
Proof. exact (@lem3160701 (@lem3160711)). Qed.
Lemma lem3160714 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160715 : term169 = term170.
Proof. exact (@lem3160714 term2 term2). Qed.
Lemma lem3160716 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160717 : term172 = term2.
Proof. exact (EQ_MP (@lem3160716) (@lem940073)). Qed.
Lemma lem3160718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160719 : term170 = term93.
Proof. exact (MK_COMB (@lem3160718) (@lem3160717)). Qed.
Lemma lem3160720 : term169 = term93.
Proof. exact (TRANS (@lem3160715) (@lem3160719)). Qed.
Lemma lem3160722 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160723 : term275 = term79.
Proof. exact (@lem3160722 term2). Qed.
Lemma lem3160724 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160725 : term440 = term434.
Proof. exact (MK_COMB (@lem3160724) (@lem3160723)). Qed.
Lemma lem3160726 : term439 = term188.
Proof. exact (MK_COMB (@lem3160725) (@lem3160720)). Qed.
Lemma lem3160728 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160729 : term188 = term189.
Proof. exact (@lem3160728 (NUMERAL 0) term2). Qed.
Lemma lem3160730 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160731 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160732 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160731 h1) (fun h1 : term189 = True => @lem3160730)). Qed.
Lemma lem3160733 : term189 = True.
Proof. exact (EQ_MP (@lem3160732) (@lem3160730)). Qed.
Lemma lem3160734 : term188 = True.
Proof. exact (TRANS (@lem3160729) (@lem3160733)). Qed.
Lemma lem3160735 : term439 = True.
Proof. exact (TRANS (@lem3160726) (@lem3160734)). Qed.
Lemma lem3160736 : term436 = True.
Proof. exact (TRANS (@lem3160712) (@lem3160735)). Qed.
Lemma lem3160737 : term188 = True.
Proof. exact (TRANS (@lem3160689) (@lem3160736)). Qed.
Lemma lem3160738 : term433 = True.
Proof. exact (TRANS (@lem3160680) (@lem3160737)). Qed.
Lemma lem3160739 : True = term433.
Proof. exact (SYM (@lem3160738)). Qed.
Lemma lem3160740 : term433.
Proof. exact (EQ_MP (@lem3160739) (@lem0)). Qed.
Lemma lem3160741 (_32603 : int) (h1 : term539 _32603) : term441 _32603.
Proof. exact (conj (@lem3160740) (@lem3160676 _32603 h1)). Qed.
Lemma lem3160743 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3160744 (_32603 : int) : term443 _32603.
Proof. exact (@lem3160743 term93 (term227 _32603)). Qed.
Lemma lem3160745 (_32603 : int) (h1 : term539 _32603) : term444 _32603.
Proof. exact (@lem3160744 _32603 (@lem3160741 _32603 h1)). Qed.
Lemma lem3160746 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3160747 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3160748 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3160747) (@lem3160746 _32603)). Qed.
Lemma lem3160749 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3160750 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3160748 _32603) (@lem3160749)). Qed.
Lemma lem3160751 (_32603 : int) (h1 : term539 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3160750 _32603) (@lem3160745 _32603 h1)). Qed.
Lemma lem3160753 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3160754 : term433 = term188.
Proof. exact (@lem3160753 term79 term93). Qed.
Lemma lem3160756 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160757 : term93 = term182.
Proof. exact (@lem3160756 term2). Qed.
Lemma lem3160759 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160760 : term79 = term157.
Proof. exact (@lem3160759 (NUMERAL 0)). Qed.
Lemma lem3160761 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160762 : term434 = term435.
Proof. exact (MK_COMB (@lem3160761) (@lem3160760)). Qed.
Lemma lem3160763 : term188 = term436.
Proof. exact (MK_COMB (@lem3160762) (@lem3160757)). Qed.
Lemma lem3160764 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3160766 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160767 : term188 = term189.
Proof. exact (@lem3160766 (NUMERAL 0) term2). Qed.
Lemma lem3160768 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160769 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160770 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160769 h1) (fun h1 : term189 = True => @lem3160768)). Qed.
Lemma lem3160771 : term189 = True.
Proof. exact (EQ_MP (@lem3160770) (@lem3160768)). Qed.
Lemma lem3160772 : term188 = True.
Proof. exact (TRANS (@lem3160767) (@lem3160771)). Qed.
Lemma lem3160773 : True = term188.
Proof. exact (SYM (@lem3160772)). Qed.
Lemma lem3160774 : term188.
Proof. exact (EQ_MP (@lem3160773) (@lem0)). Qed.
Lemma lem3160775 : term438.
Proof. exact (@lem3160764 (@lem3160774)). Qed.
Lemma lem3160777 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160778 : term188 = term189.
Proof. exact (@lem3160777 (NUMERAL 0) term2). Qed.
Lemma lem3160779 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160780 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160781 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160780 h1) (fun h1 : term189 = True => @lem3160779)). Qed.
Lemma lem3160782 : term189 = True.
Proof. exact (EQ_MP (@lem3160781) (@lem3160779)). Qed.
Lemma lem3160783 : term188 = True.
Proof. exact (TRANS (@lem3160778) (@lem3160782)). Qed.
Lemma lem3160784 : True = term188.
Proof. exact (SYM (@lem3160783)). Qed.
Lemma lem3160785 : term188.
Proof. exact (EQ_MP (@lem3160784) (@lem0)). Qed.
Lemma lem3160786 : term436 = term439.
Proof. exact (@lem3160775 (@lem3160785)). Qed.
Lemma lem3160788 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160789 : term169 = term170.
Proof. exact (@lem3160788 term2 term2). Qed.
Lemma lem3160790 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160791 : term172 = term2.
Proof. exact (EQ_MP (@lem3160790) (@lem940073)). Qed.
Lemma lem3160792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160793 : term170 = term93.
Proof. exact (MK_COMB (@lem3160792) (@lem3160791)). Qed.
Lemma lem3160794 : term169 = term93.
Proof. exact (TRANS (@lem3160789) (@lem3160793)). Qed.
Lemma lem3160796 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160797 : term275 = term79.
Proof. exact (@lem3160796 term2). Qed.
Lemma lem3160798 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3160799 : term440 = term434.
Proof. exact (MK_COMB (@lem3160798) (@lem3160797)). Qed.
Lemma lem3160800 : term439 = term188.
Proof. exact (MK_COMB (@lem3160799) (@lem3160794)). Qed.
Lemma lem3160802 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160803 : term188 = term189.
Proof. exact (@lem3160802 (NUMERAL 0) term2). Qed.
Lemma lem3160804 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160805 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160806 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160805 h1) (fun h1 : term189 = True => @lem3160804)). Qed.
Lemma lem3160807 : term189 = True.
Proof. exact (EQ_MP (@lem3160806) (@lem3160804)). Qed.
Lemma lem3160808 : term188 = True.
Proof. exact (TRANS (@lem3160803) (@lem3160807)). Qed.
Lemma lem3160809 : term439 = True.
Proof. exact (TRANS (@lem3160800) (@lem3160808)). Qed.
Lemma lem3160810 : term436 = True.
Proof. exact (TRANS (@lem3160786) (@lem3160809)). Qed.
Lemma lem3160811 : term188 = True.
Proof. exact (TRANS (@lem3160763) (@lem3160810)). Qed.
Lemma lem3160812 : term433 = True.
Proof. exact (TRANS (@lem3160754) (@lem3160811)). Qed.
Lemma lem3160813 : True = term433.
Proof. exact (SYM (@lem3160812)). Qed.
Lemma lem3160814 : term433.
Proof. exact (EQ_MP (@lem3160813) (@lem0)). Qed.
Lemma lem3160815 (_32603 : int) (h1 : term539 _32603) : term447 _32603.
Proof. exact (conj (@lem3160814) (@lem3160674 _32603 h1)). Qed.
Lemma lem3160817 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3160818 (_32603 : int) : term448 _32603.
Proof. exact (@lem3160817 term93 (term291 _32603)). Qed.
Lemma lem3160819 (_32603 : int) (h1 : term539 _32603) : term449 _32603.
Proof. exact (@lem3160818 _32603 (@lem3160815 _32603 h1)). Qed.
Lemma lem3160820 (_32603 : int) : (term450 _32603) = (term291 _32603).
Proof. exact (@lem1982733 (term291 _32603)). Qed.
Lemma lem3160821 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3160822 (_32603 : int) : (term451 _32603) = (term293 _32603).
Proof. exact (MK_COMB (@lem3160821) (@lem3160820 _32603)). Qed.
Lemma lem3160823 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3160824 (_32603 : int) : (term449 _32603) = (term294 _32603).
Proof. exact (MK_COMB (@lem3160822 _32603) (@lem3160823)). Qed.
Lemma lem3160825 (_32603 : int) (h1 : term539 _32603) : term294 _32603.
Proof. exact (EQ_MP (@lem3160824 _32603) (@lem3160819 _32603 h1)). Qed.
Lemma lem3160826 (_32603 : int) (h1 : term539 _32603) : term452 _32603.
Proof. exact (conj (@lem3160825 _32603 h1) (@lem3160751 _32603 h1)). Qed.
Lemma lem3160828 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3160829 (_32603 : int) : term454 _32603.
Proof. exact (@lem3160828 (term291 _32603) (term227 _32603)). Qed.
Lemma lem3160830 (_32603 : int) (h1 : term539 _32603) : term455 _32603.
Proof. exact (@lem3160829 _32603 (@lem3160826 _32603 h1)). Qed.
Lemma lem3160831 (_32603 : int) : (term456 _32603) = (term457 _32603).
Proof. exact (@lem1982753 (term263 _32603) (real_of_int _32603) term93 term223). Qed.
Lemma lem3160832 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3160834 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160835 : term93 = term182.
Proof. exact (@lem3160834 term2). Qed.
Lemma lem3160837 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160838 : term160 = term161.
Proof. exact (@lem3160837 term2). Qed.
Lemma lem3160839 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160840 : term460 = term461.
Proof. exact (MK_COMB (@lem3160839) (@lem3160838)). Qed.
Lemma lem3160841 : term462 = term463.
Proof. exact (MK_COMB (@lem3160840) (@lem3160835)). Qed.
Lemma lem3160842 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3160844 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160845 : term188 = term189.
Proof. exact (@lem3160844 (NUMERAL 0) term2). Qed.
Lemma lem3160846 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160847 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160848 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160847 h1) (fun h1 : term189 = True => @lem3160846)). Qed.
Lemma lem3160849 : term189 = True.
Proof. exact (EQ_MP (@lem3160848) (@lem3160846)). Qed.
Lemma lem3160850 : term188 = True.
Proof. exact (TRANS (@lem3160845) (@lem3160849)). Qed.
Lemma lem3160851 : True = term188.
Proof. exact (SYM (@lem3160850)). Qed.
Lemma lem3160852 : term188.
Proof. exact (EQ_MP (@lem3160851) (@lem0)). Qed.
Lemma lem3160853 : term465.
Proof. exact (@lem3160842 (@lem3160852)). Qed.
Lemma lem3160855 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160856 : term188 = term189.
Proof. exact (@lem3160855 (NUMERAL 0) term2). Qed.
Lemma lem3160857 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160858 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160859 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160858 h1) (fun h1 : term189 = True => @lem3160857)). Qed.
Lemma lem3160860 : term189 = True.
Proof. exact (EQ_MP (@lem3160859) (@lem3160857)). Qed.
Lemma lem3160861 : term188 = True.
Proof. exact (TRANS (@lem3160856) (@lem3160860)). Qed.
Lemma lem3160862 : True = term188.
Proof. exact (SYM (@lem3160861)). Qed.
Lemma lem3160863 : term188.
Proof. exact (EQ_MP (@lem3160862) (@lem0)). Qed.
Lemma lem3160864 : term466.
Proof. exact (@lem3160853 (@lem3160863)). Qed.
Lemma lem3160866 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160867 : term188 = term189.
Proof. exact (@lem3160866 (NUMERAL 0) term2). Qed.
Lemma lem3160868 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160869 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160870 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160869 h1) (fun h1 : term189 = True => @lem3160868)). Qed.
Lemma lem3160871 : term189 = True.
Proof. exact (EQ_MP (@lem3160870) (@lem3160868)). Qed.
Lemma lem3160872 : term188 = True.
Proof. exact (TRANS (@lem3160867) (@lem3160871)). Qed.
Lemma lem3160873 : True = term188.
Proof. exact (SYM (@lem3160872)). Qed.
Lemma lem3160874 : term188.
Proof. exact (EQ_MP (@lem3160873) (@lem0)). Qed.
Lemma lem3160875 : term467.
Proof. exact (@lem3160864 (@lem3160874)). Qed.
Lemma lem3160877 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160878 : term169 = term170.
Proof. exact (@lem3160877 term2 term2). Qed.
Lemma lem3160879 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160880 : term172 = term2.
Proof. exact (EQ_MP (@lem3160879) (@lem940073)). Qed.
Lemma lem3160881 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160882 : term170 = term93.
Proof. exact (MK_COMB (@lem3160881) (@lem3160880)). Qed.
Lemma lem3160883 : term169 = term93.
Proof. exact (TRANS (@lem3160878) (@lem3160882)). Qed.
Lemma lem3160885 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160886 : term236 = term239.
Proof. exact (@lem3160885 term2 term2). Qed.
Lemma lem3160887 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160888 : term172 = term2.
Proof. exact (EQ_MP (@lem3160887) (@lem940073)). Qed.
Lemma lem3160889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160890 : term170 = term93.
Proof. exact (MK_COMB (@lem3160889) (@lem3160888)). Qed.
Lemma lem3160891 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160892 : term239 = term160.
Proof. exact (MK_COMB (@lem3160891) (@lem3160890)). Qed.
Lemma lem3160893 : term236 = term160.
Proof. exact (TRANS (@lem3160886) (@lem3160892)). Qed.
Lemma lem3160894 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160895 : term468 = term460.
Proof. exact (MK_COMB (@lem3160894) (@lem3160893)). Qed.
Lemma lem3160896 : term469 = term462.
Proof. exact (MK_COMB (@lem3160895) (@lem3160883)). Qed.
Lemma lem3160898 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3160899 : term462 = term79.
Proof. exact (@lem3160898 term2). Qed.
Lemma lem3160900 : term469 = term79.
Proof. exact (TRANS (@lem3160896) (@lem3160899)). Qed.
Lemma lem3160901 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160902 : term471 = term273.
Proof. exact (MK_COMB (@lem3160901) (@lem3160900)). Qed.
Lemma lem3160903 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3160904 : term472 = term275.
Proof. exact (MK_COMB (@lem3160902) (@lem3160903)). Qed.
Lemma lem3160906 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160907 : term275 = term79.
Proof. exact (@lem3160906 term2). Qed.
Lemma lem3160908 : term472 = term79.
Proof. exact (TRANS (@lem3160904) (@lem3160907)). Qed.
Lemma lem3160910 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160911 : term169 = term170.
Proof. exact (@lem3160910 term2 term2). Qed.
Lemma lem3160912 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160913 : term172 = term2.
Proof. exact (EQ_MP (@lem3160912) (@lem940073)). Qed.
Lemma lem3160914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160915 : term170 = term93.
Proof. exact (MK_COMB (@lem3160914) (@lem3160913)). Qed.
Lemma lem3160916 : term169 = term93.
Proof. exact (TRANS (@lem3160911) (@lem3160915)). Qed.
Lemma lem3160917 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3160918 : term277 = term275.
Proof. exact (MK_COMB (@lem3160917) (@lem3160916)). Qed.
Lemma lem3160920 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3160921 : term275 = term79.
Proof. exact (@lem3160920 term2). Qed.
Lemma lem3160922 : term277 = term79.
Proof. exact (TRANS (@lem3160918) (@lem3160921)). Qed.
Lemma lem3160923 : term79 = term277.
Proof. exact (SYM (@lem3160922)). Qed.
Lemma lem3160924 : term472 = term277.
Proof. exact (TRANS (@lem3160908) (@lem3160923)). Qed.
Lemma lem3160925 : term463 = term157.
Proof. exact (@lem3160875 (@lem3160924)). Qed.
Lemma lem3160926 : term462 = term157.
Proof. exact (TRANS (@lem3160841) (@lem3160925)). Qed.
Lemma lem3160928 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3160929 : term157 = term79.
Proof. exact (@lem3160928 term79). Qed.
Lemma lem3160930 : term462 = term79.
Proof. exact (TRANS (@lem3160926) (@lem3160929)). Qed.
Lemma lem3160931 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3160932 : term473 = term273.
Proof. exact (MK_COMB (@lem3160931) (@lem3160930)). Qed.
Lemma lem3160933 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3160934 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3160932) (@lem3160933 _32603)). Qed.
Lemma lem3160935 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3160832 _32603) (@lem3160934 _32603)). Qed.
Lemma lem3160936 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3160937 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3160935 _32603) (@lem3160936 _32603)). Qed.
Lemma lem3160938 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160939 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3160938) (@lem3160937 _32603)). Qed.
Lemma lem3160941 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3160942 : term223 = term226.
Proof. exact (@lem3160941 term200). Qed.
Lemma lem3160944 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3160945 : term93 = term182.
Proof. exact (@lem3160944 term2). Qed.
Lemma lem3160946 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3160947 : term95 = term183.
Proof. exact (MK_COMB (@lem3160946) (@lem3160945)). Qed.
Lemma lem3160948 : term476 = term477.
Proof. exact (MK_COMB (@lem3160947) (@lem3160942)). Qed.
Lemma lem3160949 : term478.
Proof. exact (@lem1981473 term93 term93 term223 term93 term160 term93). Qed.
Lemma lem3160951 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160952 : term188 = term189.
Proof. exact (@lem3160951 (NUMERAL 0) term2). Qed.
Lemma lem3160953 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160954 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160955 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160954 h1) (fun h1 : term189 = True => @lem3160953)). Qed.
Lemma lem3160956 : term189 = True.
Proof. exact (EQ_MP (@lem3160955) (@lem3160953)). Qed.
Lemma lem3160957 : term188 = True.
Proof. exact (TRANS (@lem3160952) (@lem3160956)). Qed.
Lemma lem3160958 : True = term188.
Proof. exact (SYM (@lem3160957)). Qed.
Lemma lem3160959 : term188.
Proof. exact (EQ_MP (@lem3160958) (@lem0)). Qed.
Lemma lem3160960 : term479.
Proof. exact (@lem3160949 (@lem3160959)). Qed.
Lemma lem3160962 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160963 : term188 = term189.
Proof. exact (@lem3160962 (NUMERAL 0) term2). Qed.
Lemma lem3160964 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160965 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160966 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160965 h1) (fun h1 : term189 = True => @lem3160964)). Qed.
Lemma lem3160967 : term189 = True.
Proof. exact (EQ_MP (@lem3160966) (@lem3160964)). Qed.
Lemma lem3160968 : term188 = True.
Proof. exact (TRANS (@lem3160963) (@lem3160967)). Qed.
Lemma lem3160969 : True = term188.
Proof. exact (SYM (@lem3160968)). Qed.
Lemma lem3160970 : term188.
Proof. exact (EQ_MP (@lem3160969) (@lem0)). Qed.
Lemma lem3160971 : term480.
Proof. exact (@lem3160960 (@lem3160970)). Qed.
Lemma lem3160973 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3160974 : term188 = term189.
Proof. exact (@lem3160973 (NUMERAL 0) term2). Qed.
Lemma lem3160975 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3160976 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3160977 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3160976 h1) (fun h1 : term189 = True => @lem3160975)). Qed.
Lemma lem3160978 : term189 = True.
Proof. exact (EQ_MP (@lem3160977) (@lem3160975)). Qed.
Lemma lem3160979 : term188 = True.
Proof. exact (TRANS (@lem3160974) (@lem3160978)). Qed.
Lemma lem3160980 : True = term188.
Proof. exact (SYM (@lem3160979)). Qed.
Lemma lem3160981 : term188.
Proof. exact (EQ_MP (@lem3160980) (@lem0)). Qed.
Lemma lem3160982 : term481.
Proof. exact (@lem3160971 (@lem3160981)). Qed.
Lemma lem3160984 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3160985 : term482 = term483.
Proof. exact (@lem3160984 term200 term2). Qed.
Lemma lem3160986 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3160987 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3160988 : term207 = term200.
Proof. exact (EQ_MP (@lem3160987) (@lem3160986)). Qed.
Lemma lem3160989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3160990 : term205 = term186.
Proof. exact (MK_COMB (@lem3160989) (@lem3160988)). Qed.
Lemma lem3160991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3160992 : term483 = term223.
Proof. exact (MK_COMB (@lem3160991) (@lem3160990)). Qed.
Lemma lem3160993 : term482 = term223.
Proof. exact (TRANS (@lem3160985) (@lem3160992)). Qed.
Lemma lem3160995 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3160996 : term169 = term170.
Proof. exact (@lem3160995 term2 term2). Qed.
Lemma lem3160997 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3160998 : term172 = term2.
Proof. exact (EQ_MP (@lem3160997) (@lem940073)). Qed.
Lemma lem3160999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161000 : term170 = term93.
Proof. exact (MK_COMB (@lem3160999) (@lem3160998)). Qed.
Lemma lem3161001 : term169 = term93.
Proof. exact (TRANS (@lem3160996) (@lem3161000)). Qed.
Lemma lem3161002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161003 : term194 = term95.
Proof. exact (MK_COMB (@lem3161002) (@lem3161001)). Qed.
Lemma lem3161004 : term484 = term476.
Proof. exact (MK_COMB (@lem3161003) (@lem3160993)). Qed.
Lemma lem3161007 : term485 = term160.
Proof. exact (@lem1367771 term2 term2). Qed.
Lemma lem3161008 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3161009 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3161010 : term199 = term200.
Proof. exact (EQ_MP (@lem3161009) (@lem3161008)). Qed.
Lemma lem3161011 : term200 = term199.
Proof. exact (SYM (@lem3161010)). Qed.
Lemma lem3161012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161013 : term186 = term196.
Proof. exact (MK_COMB (@lem3161012) (@lem3161011)). Qed.
Lemma lem3161014 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161015 : term223 = term486.
Proof. exact (MK_COMB (@lem3161014) (@lem3161013)). Qed.
Lemma lem3161016 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3161017 : term476 = term485.
Proof. exact (MK_COMB (@lem3161016) (@lem3161015)). Qed.
Lemma lem3161018 : term476 = term160.
Proof. exact (TRANS (@lem3161017) (@lem3161007)). Qed.
Lemma lem3161019 : term484 = term160.
Proof. exact (TRANS (@lem3161004) (@lem3161018)). Qed.
Lemma lem3161020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161021 : term487 = term162.
Proof. exact (MK_COMB (@lem3161020) (@lem3161019)). Qed.
Lemma lem3161022 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3161023 : term488 = term236.
Proof. exact (MK_COMB (@lem3161021) (@lem3161022)). Qed.
Lemma lem3161025 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161026 : term236 = term239.
Proof. exact (@lem3161025 term2 term2). Qed.
Lemma lem3161027 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161028 : term172 = term2.
Proof. exact (EQ_MP (@lem3161027) (@lem940073)). Qed.
Lemma lem3161029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161030 : term170 = term93.
Proof. exact (MK_COMB (@lem3161029) (@lem3161028)). Qed.
Lemma lem3161031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161032 : term239 = term160.
Proof. exact (MK_COMB (@lem3161031) (@lem3161030)). Qed.
Lemma lem3161033 : term236 = term160.
Proof. exact (TRANS (@lem3161026) (@lem3161032)). Qed.
Lemma lem3161034 : term488 = term160.
Proof. exact (TRANS (@lem3161023) (@lem3161033)). Qed.
Lemma lem3161036 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161037 : term169 = term170.
Proof. exact (@lem3161036 term2 term2). Qed.
Lemma lem3161038 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161039 : term172 = term2.
Proof. exact (EQ_MP (@lem3161038) (@lem940073)). Qed.
Lemma lem3161040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161041 : term170 = term93.
Proof. exact (MK_COMB (@lem3161040) (@lem3161039)). Qed.
Lemma lem3161042 : term169 = term93.
Proof. exact (TRANS (@lem3161037) (@lem3161041)). Qed.
Lemma lem3161043 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem3161044 : term489 = term236.
Proof. exact (MK_COMB (@lem3161043) (@lem3161042)). Qed.
Lemma lem3161046 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161047 : term236 = term239.
Proof. exact (@lem3161046 term2 term2). Qed.
Lemma lem3161048 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161049 : term172 = term2.
Proof. exact (EQ_MP (@lem3161048) (@lem940073)). Qed.
Lemma lem3161050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161051 : term170 = term93.
Proof. exact (MK_COMB (@lem3161050) (@lem3161049)). Qed.
Lemma lem3161052 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161053 : term239 = term160.
Proof. exact (MK_COMB (@lem3161052) (@lem3161051)). Qed.
Lemma lem3161054 : term236 = term160.
Proof. exact (TRANS (@lem3161047) (@lem3161053)). Qed.
Lemma lem3161055 : term489 = term160.
Proof. exact (TRANS (@lem3161044) (@lem3161054)). Qed.
Lemma lem3161056 : term160 = term489.
Proof. exact (SYM (@lem3161055)). Qed.
Lemma lem3161057 : term488 = term489.
Proof. exact (TRANS (@lem3161034) (@lem3161056)). Qed.
Lemma lem3161058 : term477 = term161.
Proof. exact (@lem3160982 (@lem3161057)). Qed.
Lemma lem3161059 : term476 = term161.
Proof. exact (TRANS (@lem3160948) (@lem3161058)). Qed.
Lemma lem3161061 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3161062 : term161 = term160.
Proof. exact (@lem3161061 term160). Qed.
Lemma lem3161063 : term476 = term160.
Proof. exact (TRANS (@lem3161059) (@lem3161062)). Qed.
Lemma lem3161064 (_32603 : int) : (term457 _32603) = term490.
Proof. exact (MK_COMB (@lem3160939 _32603) (@lem3161063)). Qed.
Lemma lem3161065 (_32603 : int) : (term456 _32603) = term490.
Proof. exact (TRANS (@lem3160831 _32603) (@lem3161064 _32603)). Qed.
Lemma lem3161066 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3161067 (_32603 : int) : (term456 _32603) = term160.
Proof. exact (TRANS (@lem3161065 _32603) (@lem3161066)). Qed.
Lemma lem3161068 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161069 (_32603 : int) : (term491 _32603) = term492.
Proof. exact (MK_COMB (@lem3161068) (@lem3161067 _32603)). Qed.
Lemma lem3161070 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161071 (_32603 : int) : (term455 _32603) = term493.
Proof. exact (MK_COMB (@lem3161069 _32603) (@lem3161070)). Qed.
Lemma lem3161072 (_32603 : int) (h1 : term539 _32603) : term493.
Proof. exact (EQ_MP (@lem3161071 _32603) (@lem3160830 _32603 h1)). Qed.
Lemma lem3161074 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3161075 : term493 = term494.
Proof. exact (@lem3161074 term79 term160). Qed.
Lemma lem3161077 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161078 : term160 = term161.
Proof. exact (@lem3161077 term2). Qed.
Lemma lem3161080 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161081 : term79 = term157.
Proof. exact (@lem3161080 (NUMERAL 0)). Qed.
Lemma lem3161082 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161083 : term81 = term495.
Proof. exact (MK_COMB (@lem3161082) (@lem3161081)). Qed.
Lemma lem3161084 : term494 = term496.
Proof. exact (MK_COMB (@lem3161083) (@lem3161078)). Qed.
Lemma lem3161085 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3161087 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161088 : term188 = term189.
Proof. exact (@lem3161087 (NUMERAL 0) term2). Qed.
Lemma lem3161089 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161090 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161091 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161090 h1) (fun h1 : term189 = True => @lem3161089)). Qed.
Lemma lem3161092 : term189 = True.
Proof. exact (EQ_MP (@lem3161091) (@lem3161089)). Qed.
Lemma lem3161093 : term188 = True.
Proof. exact (TRANS (@lem3161088) (@lem3161092)). Qed.
Lemma lem3161094 : True = term188.
Proof. exact (SYM (@lem3161093)). Qed.
Lemma lem3161095 : term188.
Proof. exact (EQ_MP (@lem3161094) (@lem0)). Qed.
Lemma lem3161096 : term498.
Proof. exact (@lem3161085 (@lem3161095)). Qed.
Lemma lem3161098 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161099 : term188 = term189.
Proof. exact (@lem3161098 (NUMERAL 0) term2). Qed.
Lemma lem3161100 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161101 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161102 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161101 h1) (fun h1 : term189 = True => @lem3161100)). Qed.
Lemma lem3161103 : term189 = True.
Proof. exact (EQ_MP (@lem3161102) (@lem3161100)). Qed.
Lemma lem3161104 : term188 = True.
Proof. exact (TRANS (@lem3161099) (@lem3161103)). Qed.
Lemma lem3161105 : True = term188.
Proof. exact (SYM (@lem3161104)). Qed.
Lemma lem3161106 : term188.
Proof. exact (EQ_MP (@lem3161105) (@lem0)). Qed.
Lemma lem3161107 : term496 = term499.
Proof. exact (@lem3161096 (@lem3161106)). Qed.
Lemma lem3161109 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161110 : term236 = term239.
Proof. exact (@lem3161109 term2 term2). Qed.
Lemma lem3161111 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161112 : term172 = term2.
Proof. exact (EQ_MP (@lem3161111) (@lem940073)). Qed.
Lemma lem3161113 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161114 : term170 = term93.
Proof. exact (MK_COMB (@lem3161113) (@lem3161112)). Qed.
Lemma lem3161115 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161116 : term239 = term160.
Proof. exact (MK_COMB (@lem3161115) (@lem3161114)). Qed.
Lemma lem3161117 : term236 = term160.
Proof. exact (TRANS (@lem3161110) (@lem3161116)). Qed.
Lemma lem3161119 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161120 : term275 = term79.
Proof. exact (@lem3161119 term2). Qed.
Lemma lem3161121 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161122 : term500 = term81.
Proof. exact (MK_COMB (@lem3161121) (@lem3161120)). Qed.
Lemma lem3161123 : term499 = term494.
Proof. exact (MK_COMB (@lem3161122) (@lem3161117)). Qed.
Lemma lem3161125 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3161126 : term494 = term503.
Proof. exact (@lem3161125 (NUMERAL 0) term2). Qed.
Lemma lem3161127 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161128 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3161129 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161128 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3161127)). Qed.
Lemma lem3161130 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3161129) (@lem3161127)). Qed.
Lemma lem3161131 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3161132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3161133 : term504 = (and True).
Proof. exact (MK_COMB (@lem3161132) (@lem3161131)). Qed.
Lemma lem3161134 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3161133) (@lem3161130)). Qed.
Lemma lem3161136 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3161137 : term503 = False.
Proof. exact (TRANS (@lem3161134) (@lem3161136)). Qed.
Lemma lem3161138 : term494 = False.
Proof. exact (TRANS (@lem3161126) (@lem3161137)). Qed.
Lemma lem3161139 : term499 = False.
Proof. exact (TRANS (@lem3161123) (@lem3161138)). Qed.
Lemma lem3161140 : term496 = False.
Proof. exact (TRANS (@lem3161107) (@lem3161139)). Qed.
Lemma lem3161141 : term494 = False.
Proof. exact (TRANS (@lem3161084) (@lem3161140)). Qed.
Lemma lem3161142 : term493 = False.
Proof. exact (TRANS (@lem3161075) (@lem3161141)). Qed.
Lemma lem3161143 (_32603 : int) (h1 : term539 _32603) : False.
Proof. exact (EQ_MP (@lem3161142) (@lem3161072 _32603 h1)). Qed.
Lemma lem3161144 (_32603 : int) (h1 : term417 _32603) : False.
Proof. exact (or_elim (@lem3160197 _32603 h1) (fun h0 : term538 _32603 => @lem3160670 _32603 h0) (fun h0 : term539 _32603 => @lem3161143 _32603 h0)). Qed.
Lemma lem3161145 (_32603 : int) (h1 : term426 _32603) : False.
Proof. exact (or_elim (@lem3159494 _32603 h1) (fun h0 : term421 _32603 => @lem3160196 _32603 h0) (fun h0 : term417 _32603 => @lem3161144 _32603 h0)). Qed.
Lemma lem3161146 (_32603 : int) (h1 : term428 _32603) : False.
Proof. exact (or_elim (@lem3159022 _32603 h1) (fun h0 : term432 _32603 => @lem3159493 _32603 h0) (fun h0 : term426 _32603 => @lem3161145 _32603 h0)). Qed.
Lemma lem3161147 (_32603 : int) (h1 : term410 _32603) : term410 _32603.
Proof. exact (h1). Qed.
Lemma lem3161148 (_32603 : int) (h1 : term407 _32603) : term407 _32603.
Proof. exact (h1). Qed.
Lemma lem3161149 (_32603 : int) (h1 : term540 _32603) : term540 _32603.
Proof. exact (h1). Qed.
Lemma lem3161150 (_32603 : int) (h1 : term540 _32603) : term392 _32603.
Proof. exact (proj2 (@lem3161149 _32603 h1)). Qed.
Lemma lem3161152 (_32603 : int) (h1 : term540 _32603) : (real_of_int _32603) = term79.
Proof. exact (proj2 (@lem3161150 _32603 h1)). Qed.
Lemma lem3161153 (_32603 : int) (h1 : term540 _32603) : term230 _32603.
Proof. exact (proj1 (@lem3161150 _32603 h1)). Qed.
Lemma lem3161155 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3161156 : term433 = term188.
Proof. exact (@lem3161155 term79 term93). Qed.
Lemma lem3161158 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161159 : term93 = term182.
Proof. exact (@lem3161158 term2). Qed.
Lemma lem3161161 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161162 : term79 = term157.
Proof. exact (@lem3161161 (NUMERAL 0)). Qed.
Lemma lem3161163 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3161164 : term434 = term435.
Proof. exact (MK_COMB (@lem3161163) (@lem3161162)). Qed.
Lemma lem3161165 : term188 = term436.
Proof. exact (MK_COMB (@lem3161164) (@lem3161159)). Qed.
Lemma lem3161166 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3161168 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161169 : term188 = term189.
Proof. exact (@lem3161168 (NUMERAL 0) term2). Qed.
Lemma lem3161170 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161171 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161172 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161171 h1) (fun h1 : term189 = True => @lem3161170)). Qed.
Lemma lem3161173 : term189 = True.
Proof. exact (EQ_MP (@lem3161172) (@lem3161170)). Qed.
Lemma lem3161174 : term188 = True.
Proof. exact (TRANS (@lem3161169) (@lem3161173)). Qed.
Lemma lem3161175 : True = term188.
Proof. exact (SYM (@lem3161174)). Qed.
Lemma lem3161176 : term188.
Proof. exact (EQ_MP (@lem3161175) (@lem0)). Qed.
Lemma lem3161177 : term438.
Proof. exact (@lem3161166 (@lem3161176)). Qed.
Lemma lem3161179 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161180 : term188 = term189.
Proof. exact (@lem3161179 (NUMERAL 0) term2). Qed.
Lemma lem3161181 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161182 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161183 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161182 h1) (fun h1 : term189 = True => @lem3161181)). Qed.
Lemma lem3161184 : term189 = True.
Proof. exact (EQ_MP (@lem3161183) (@lem3161181)). Qed.
Lemma lem3161185 : term188 = True.
Proof. exact (TRANS (@lem3161180) (@lem3161184)). Qed.
Lemma lem3161186 : True = term188.
Proof. exact (SYM (@lem3161185)). Qed.
Lemma lem3161187 : term188.
Proof. exact (EQ_MP (@lem3161186) (@lem0)). Qed.
Lemma lem3161188 : term436 = term439.
Proof. exact (@lem3161177 (@lem3161187)). Qed.
Lemma lem3161190 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161191 : term169 = term170.
Proof. exact (@lem3161190 term2 term2). Qed.
Lemma lem3161192 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161193 : term172 = term2.
Proof. exact (EQ_MP (@lem3161192) (@lem940073)). Qed.
Lemma lem3161194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161195 : term170 = term93.
Proof. exact (MK_COMB (@lem3161194) (@lem3161193)). Qed.
Lemma lem3161196 : term169 = term93.
Proof. exact (TRANS (@lem3161191) (@lem3161195)). Qed.
Lemma lem3161198 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161199 : term275 = term79.
Proof. exact (@lem3161198 term2). Qed.
Lemma lem3161200 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3161201 : term440 = term434.
Proof. exact (MK_COMB (@lem3161200) (@lem3161199)). Qed.
Lemma lem3161202 : term439 = term188.
Proof. exact (MK_COMB (@lem3161201) (@lem3161196)). Qed.
Lemma lem3161204 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161205 : term188 = term189.
Proof. exact (@lem3161204 (NUMERAL 0) term2). Qed.
Lemma lem3161206 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161207 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161208 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161207 h1) (fun h1 : term189 = True => @lem3161206)). Qed.
Lemma lem3161209 : term189 = True.
Proof. exact (EQ_MP (@lem3161208) (@lem3161206)). Qed.
Lemma lem3161210 : term188 = True.
Proof. exact (TRANS (@lem3161205) (@lem3161209)). Qed.
Lemma lem3161211 : term439 = True.
Proof. exact (TRANS (@lem3161202) (@lem3161210)). Qed.
Lemma lem3161212 : term436 = True.
Proof. exact (TRANS (@lem3161188) (@lem3161211)). Qed.
Lemma lem3161213 : term188 = True.
Proof. exact (TRANS (@lem3161165) (@lem3161212)). Qed.
Lemma lem3161214 : term433 = True.
Proof. exact (TRANS (@lem3161156) (@lem3161213)). Qed.
Lemma lem3161215 : True = term433.
Proof. exact (SYM (@lem3161214)). Qed.
Lemma lem3161216 : term433.
Proof. exact (EQ_MP (@lem3161215) (@lem0)). Qed.
Lemma lem3161217 (_32603 : int) (h1 : term540 _32603) : term441 _32603.
Proof. exact (conj (@lem3161216) (@lem3161153 _32603 h1)). Qed.
Lemma lem3161219 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3161220 (_32603 : int) : term443 _32603.
Proof. exact (@lem3161219 term93 (term227 _32603)). Qed.
Lemma lem3161221 (_32603 : int) (h1 : term540 _32603) : term444 _32603.
Proof. exact (@lem3161220 _32603 (@lem3161217 _32603 h1)). Qed.
Lemma lem3161222 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3161223 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161224 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3161223) (@lem3161222 _32603)). Qed.
Lemma lem3161225 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161226 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3161224 _32603) (@lem3161225)). Qed.
Lemma lem3161227 (_32603 : int) (h1 : term540 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3161226 _32603) (@lem3161221 _32603 h1)). Qed.
Lemma lem3161229 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3161230 (_32603 : int) : term542 _32603.
Proof. exact (@lem3161229 (real_of_int _32603)). Qed.
Lemma lem3161231 (_32603 : int) (h1 : term540 _32603) : term543 _32603.
Proof. exact (@lem3161230 _32603 (@lem3161152 _32603 h1)). Qed.
Lemma lem3161232 (_32603 : int) (h1 : term540 _32603) : term544 _32603.
Proof. exact (@lem3161231 _32603 h1 term160). Qed.
Lemma lem3161233 (_32603 : int) : (term544 _32603) = ((term263 _32603) = term79).
Proof. exact (eq_refl (term544 _32603)). Qed.
Lemma lem3161240 (_32603 : int) (h1 : term540 _32603) : (term263 _32603) = term79.
Proof. exact (EQ_MP (@lem3161233 _32603) (@lem3161232 _32603 h1)). Qed.
Lemma lem3161241 (_32603 : int) (h1 : term540 _32603) : term545 _32603.
Proof. exact (conj (@lem3161240 _32603 h1) (@lem3161227 _32603 h1)). Qed.
Lemma lem3161243 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3161244 (_32603 : int) : term547 _32603.
Proof. exact (@lem3161243 (term263 _32603) (term227 _32603)). Qed.
Lemma lem3161245 (_32603 : int) (h1 : term540 _32603) : term548 _32603.
Proof. exact (@lem3161244 _32603 (@lem3161241 _32603 h1)). Qed.
Lemma lem3161246 (_32603 : int) : (term549 _32603) = (term550 _32603).
Proof. exact (@lem1982763 (term263 _32603) (real_of_int _32603) term223). Qed.
Lemma lem3161247 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3161249 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161250 : term93 = term182.
Proof. exact (@lem3161249 term2). Qed.
Lemma lem3161252 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161253 : term160 = term161.
Proof. exact (@lem3161252 term2). Qed.
Lemma lem3161254 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161255 : term460 = term461.
Proof. exact (MK_COMB (@lem3161254) (@lem3161253)). Qed.
Lemma lem3161256 : term462 = term463.
Proof. exact (MK_COMB (@lem3161255) (@lem3161250)). Qed.
Lemma lem3161257 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3161259 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161260 : term188 = term189.
Proof. exact (@lem3161259 (NUMERAL 0) term2). Qed.
Lemma lem3161261 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161262 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161263 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161262 h1) (fun h1 : term189 = True => @lem3161261)). Qed.
Lemma lem3161264 : term189 = True.
Proof. exact (EQ_MP (@lem3161263) (@lem3161261)). Qed.
Lemma lem3161265 : term188 = True.
Proof. exact (TRANS (@lem3161260) (@lem3161264)). Qed.
Lemma lem3161266 : True = term188.
Proof. exact (SYM (@lem3161265)). Qed.
Lemma lem3161267 : term188.
Proof. exact (EQ_MP (@lem3161266) (@lem0)). Qed.
Lemma lem3161268 : term465.
Proof. exact (@lem3161257 (@lem3161267)). Qed.
Lemma lem3161270 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161271 : term188 = term189.
Proof. exact (@lem3161270 (NUMERAL 0) term2). Qed.
Lemma lem3161272 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161273 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161274 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161273 h1) (fun h1 : term189 = True => @lem3161272)). Qed.
Lemma lem3161275 : term189 = True.
Proof. exact (EQ_MP (@lem3161274) (@lem3161272)). Qed.
Lemma lem3161276 : term188 = True.
Proof. exact (TRANS (@lem3161271) (@lem3161275)). Qed.
Lemma lem3161277 : True = term188.
Proof. exact (SYM (@lem3161276)). Qed.
Lemma lem3161278 : term188.
Proof. exact (EQ_MP (@lem3161277) (@lem0)). Qed.
Lemma lem3161279 : term466.
Proof. exact (@lem3161268 (@lem3161278)). Qed.
Lemma lem3161281 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161282 : term188 = term189.
Proof. exact (@lem3161281 (NUMERAL 0) term2). Qed.
Lemma lem3161283 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161284 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161285 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161284 h1) (fun h1 : term189 = True => @lem3161283)). Qed.
Lemma lem3161286 : term189 = True.
Proof. exact (EQ_MP (@lem3161285) (@lem3161283)). Qed.
Lemma lem3161287 : term188 = True.
Proof. exact (TRANS (@lem3161282) (@lem3161286)). Qed.
Lemma lem3161288 : True = term188.
Proof. exact (SYM (@lem3161287)). Qed.
Lemma lem3161289 : term188.
Proof. exact (EQ_MP (@lem3161288) (@lem0)). Qed.
Lemma lem3161290 : term467.
Proof. exact (@lem3161279 (@lem3161289)). Qed.
Lemma lem3161292 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161293 : term169 = term170.
Proof. exact (@lem3161292 term2 term2). Qed.
Lemma lem3161294 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161295 : term172 = term2.
Proof. exact (EQ_MP (@lem3161294) (@lem940073)). Qed.
Lemma lem3161296 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161297 : term170 = term93.
Proof. exact (MK_COMB (@lem3161296) (@lem3161295)). Qed.
Lemma lem3161298 : term169 = term93.
Proof. exact (TRANS (@lem3161293) (@lem3161297)). Qed.
Lemma lem3161300 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161301 : term236 = term239.
Proof. exact (@lem3161300 term2 term2). Qed.
Lemma lem3161302 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161303 : term172 = term2.
Proof. exact (EQ_MP (@lem3161302) (@lem940073)). Qed.
Lemma lem3161304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161305 : term170 = term93.
Proof. exact (MK_COMB (@lem3161304) (@lem3161303)). Qed.
Lemma lem3161306 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161307 : term239 = term160.
Proof. exact (MK_COMB (@lem3161306) (@lem3161305)). Qed.
Lemma lem3161308 : term236 = term160.
Proof. exact (TRANS (@lem3161301) (@lem3161307)). Qed.
Lemma lem3161309 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161310 : term468 = term460.
Proof. exact (MK_COMB (@lem3161309) (@lem3161308)). Qed.
Lemma lem3161311 : term469 = term462.
Proof. exact (MK_COMB (@lem3161310) (@lem3161298)). Qed.
Lemma lem3161313 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3161314 : term462 = term79.
Proof. exact (@lem3161313 term2). Qed.
Lemma lem3161315 : term469 = term79.
Proof. exact (TRANS (@lem3161311) (@lem3161314)). Qed.
Lemma lem3161316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161317 : term471 = term273.
Proof. exact (MK_COMB (@lem3161316) (@lem3161315)). Qed.
Lemma lem3161318 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3161319 : term472 = term275.
Proof. exact (MK_COMB (@lem3161317) (@lem3161318)). Qed.
Lemma lem3161321 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161322 : term275 = term79.
Proof. exact (@lem3161321 term2). Qed.
Lemma lem3161323 : term472 = term79.
Proof. exact (TRANS (@lem3161319) (@lem3161322)). Qed.
Lemma lem3161325 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161326 : term169 = term170.
Proof. exact (@lem3161325 term2 term2). Qed.
Lemma lem3161327 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161328 : term172 = term2.
Proof. exact (EQ_MP (@lem3161327) (@lem940073)). Qed.
Lemma lem3161329 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161330 : term170 = term93.
Proof. exact (MK_COMB (@lem3161329) (@lem3161328)). Qed.
Lemma lem3161331 : term169 = term93.
Proof. exact (TRANS (@lem3161326) (@lem3161330)). Qed.
Lemma lem3161332 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3161333 : term277 = term275.
Proof. exact (MK_COMB (@lem3161332) (@lem3161331)). Qed.
Lemma lem3161335 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161336 : term275 = term79.
Proof. exact (@lem3161335 term2). Qed.
Lemma lem3161337 : term277 = term79.
Proof. exact (TRANS (@lem3161333) (@lem3161336)). Qed.
Lemma lem3161338 : term79 = term277.
Proof. exact (SYM (@lem3161337)). Qed.
Lemma lem3161339 : term472 = term277.
Proof. exact (TRANS (@lem3161323) (@lem3161338)). Qed.
Lemma lem3161340 : term463 = term157.
Proof. exact (@lem3161290 (@lem3161339)). Qed.
Lemma lem3161341 : term462 = term157.
Proof. exact (TRANS (@lem3161256) (@lem3161340)). Qed.
Lemma lem3161343 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3161344 : term157 = term79.
Proof. exact (@lem3161343 term79). Qed.
Lemma lem3161345 : term462 = term79.
Proof. exact (TRANS (@lem3161341) (@lem3161344)). Qed.
Lemma lem3161346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161347 : term473 = term273.
Proof. exact (MK_COMB (@lem3161346) (@lem3161345)). Qed.
Lemma lem3161348 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3161349 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3161347) (@lem3161348 _32603)). Qed.
Lemma lem3161350 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3161247 _32603) (@lem3161349 _32603)). Qed.
Lemma lem3161351 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3161352 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3161350 _32603) (@lem3161351 _32603)). Qed.
Lemma lem3161353 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161354 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3161353) (@lem3161352 _32603)). Qed.
Lemma lem3161355 : term223 = term223.
Proof. exact (eq_refl term223). Qed.
Lemma lem3161356 (_32603 : int) : (term550 _32603) = term551.
Proof. exact (MK_COMB (@lem3161354 _32603) (@lem3161355)). Qed.
Lemma lem3161357 (_32603 : int) : (term549 _32603) = term551.
Proof. exact (TRANS (@lem3161246 _32603) (@lem3161356 _32603)). Qed.
Lemma lem3161358 : term551 = term223.
Proof. exact (@lem1982721 term223). Qed.
Lemma lem3161359 (_32603 : int) : (term549 _32603) = term223.
Proof. exact (TRANS (@lem3161357 _32603) (@lem3161358)). Qed.
Lemma lem3161360 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161361 (_32603 : int) : (term552 _32603) = term553.
Proof. exact (MK_COMB (@lem3161360) (@lem3161359 _32603)). Qed.
Lemma lem3161362 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161363 (_32603 : int) : (term548 _32603) = term554.
Proof. exact (MK_COMB (@lem3161361 _32603) (@lem3161362)). Qed.
Lemma lem3161364 (_32603 : int) (h1 : term540 _32603) : term554.
Proof. exact (EQ_MP (@lem3161363 _32603) (@lem3161245 _32603 h1)). Qed.
Lemma lem3161366 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3161367 : term554 = term555.
Proof. exact (@lem3161366 term79 term223). Qed.
Lemma lem3161369 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161370 : term223 = term226.
Proof. exact (@lem3161369 term200). Qed.
Lemma lem3161372 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161373 : term79 = term157.
Proof. exact (@lem3161372 (NUMERAL 0)). Qed.
Lemma lem3161374 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161375 : term81 = term495.
Proof. exact (MK_COMB (@lem3161374) (@lem3161373)). Qed.
Lemma lem3161376 : term555 = term556.
Proof. exact (MK_COMB (@lem3161375) (@lem3161370)). Qed.
Lemma lem3161377 : term557.
Proof. exact (@lem1980026 term79 term93 term223 term93). Qed.
Lemma lem3161379 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161380 : term188 = term189.
Proof. exact (@lem3161379 (NUMERAL 0) term2). Qed.
Lemma lem3161381 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161382 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161383 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161382 h1) (fun h1 : term189 = True => @lem3161381)). Qed.
Lemma lem3161384 : term189 = True.
Proof. exact (EQ_MP (@lem3161383) (@lem3161381)). Qed.
Lemma lem3161385 : term188 = True.
Proof. exact (TRANS (@lem3161380) (@lem3161384)). Qed.
Lemma lem3161386 : True = term188.
Proof. exact (SYM (@lem3161385)). Qed.
Lemma lem3161387 : term188.
Proof. exact (EQ_MP (@lem3161386) (@lem0)). Qed.
Lemma lem3161388 : term558.
Proof. exact (@lem3161377 (@lem3161387)). Qed.
Lemma lem3161390 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161391 : term188 = term189.
Proof. exact (@lem3161390 (NUMERAL 0) term2). Qed.
Lemma lem3161392 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161393 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161394 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161393 h1) (fun h1 : term189 = True => @lem3161392)). Qed.
Lemma lem3161395 : term189 = True.
Proof. exact (EQ_MP (@lem3161394) (@lem3161392)). Qed.
Lemma lem3161396 : term188 = True.
Proof. exact (TRANS (@lem3161391) (@lem3161395)). Qed.
Lemma lem3161397 : True = term188.
Proof. exact (SYM (@lem3161396)). Qed.
Lemma lem3161398 : term188.
Proof. exact (EQ_MP (@lem3161397) (@lem0)). Qed.
Lemma lem3161399 : term556 = term559.
Proof. exact (@lem3161388 (@lem3161398)). Qed.
Lemma lem3161401 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161402 : term482 = term483.
Proof. exact (@lem3161401 term200 term2). Qed.
Lemma lem3161403 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3161404 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3161405 : term207 = term200.
Proof. exact (EQ_MP (@lem3161404) (@lem3161403)). Qed.
Lemma lem3161406 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161407 : term205 = term186.
Proof. exact (MK_COMB (@lem3161406) (@lem3161405)). Qed.
Lemma lem3161408 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161409 : term483 = term223.
Proof. exact (MK_COMB (@lem3161408) (@lem3161407)). Qed.
Lemma lem3161410 : term482 = term223.
Proof. exact (TRANS (@lem3161402) (@lem3161409)). Qed.
Lemma lem3161412 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161413 : term275 = term79.
Proof. exact (@lem3161412 term2). Qed.
Lemma lem3161414 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161415 : term500 = term81.
Proof. exact (MK_COMB (@lem3161414) (@lem3161413)). Qed.
Lemma lem3161416 : term559 = term555.
Proof. exact (MK_COMB (@lem3161415) (@lem3161410)). Qed.
Lemma lem3161418 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3161419 : term555 = term560.
Proof. exact (@lem3161418 (NUMERAL 0) term200). Qed.
Lemma lem3161420 : term561 = term198.
Proof. exact (@lem912803). Qed.
Lemma lem3161421 (h1 : term561 = term198) : (term200 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term198 h1). Qed.
Lemma lem3161422 : (term561 = term198) = ((term200 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term561 = term198 => @lem3161421 h1) (fun h1 : (term200 = (NUMERAL 0)) = False => @lem3161420)). Qed.
Lemma lem3161423 : (term200 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3161422) (@lem3161420)). Qed.
Lemma lem3161424 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3161425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3161426 : term504 = (and True).
Proof. exact (MK_COMB (@lem3161425) (@lem3161424)). Qed.
Lemma lem3161427 : term560 = (True /\ False).
Proof. exact (MK_COMB (@lem3161426) (@lem3161423)). Qed.
Lemma lem3161429 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3161430 : term560 = False.
Proof. exact (TRANS (@lem3161427) (@lem3161429)). Qed.
Lemma lem3161431 : term555 = False.
Proof. exact (TRANS (@lem3161419) (@lem3161430)). Qed.
Lemma lem3161432 : term559 = False.
Proof. exact (TRANS (@lem3161416) (@lem3161431)). Qed.
Lemma lem3161433 : term556 = False.
Proof. exact (TRANS (@lem3161399) (@lem3161432)). Qed.
Lemma lem3161434 : term555 = False.
Proof. exact (TRANS (@lem3161376) (@lem3161433)). Qed.
Lemma lem3161435 : term554 = False.
Proof. exact (TRANS (@lem3161367) (@lem3161434)). Qed.
Lemma lem3161436 (_32603 : int) (h1 : term540 _32603) : False.
Proof. exact (EQ_MP (@lem3161435) (@lem3161364 _32603 h1)). Qed.
Lemma lem3161437 (_32603 : int) (h1 : term405 _32603) : term405 _32603.
Proof. exact (h1). Qed.
Lemma lem3161438 (_32603 : int) (h1 : term400 _32603) : term400 _32603.
Proof. exact (h1). Qed.
Lemma lem3161439 (_32603 : int) (h1 : term562 _32603) : term562 _32603.
Proof. exact (h1). Qed.
Lemma lem3161440 (_32603 : int) (h1 : term562 _32603) : term401 _32603.
Proof. exact (proj2 (@lem3161439 _32603 h1)). Qed.
Lemma lem3161442 (_32603 : int) (h1 : term562 _32603) : (real_of_int _32603) = term79.
Proof. exact (proj2 (@lem3161440 _32603 h1)). Qed.
Lemma lem3161443 (_32603 : int) (h1 : term562 _32603) : term329 _32603.
Proof. exact (proj1 (@lem3161440 _32603 h1)). Qed.
Lemma lem3161445 (_32603 : int) (h1 : term562 _32603) : term247 _32603.
Proof. exact (proj1 (@lem3161443 _32603 h1)). Qed.
Lemma lem3161447 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3161448 : term433 = term188.
Proof. exact (@lem3161447 term79 term93). Qed.
Lemma lem3161450 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161451 : term93 = term182.
Proof. exact (@lem3161450 term2). Qed.
Lemma lem3161453 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161454 : term79 = term157.
Proof. exact (@lem3161453 (NUMERAL 0)). Qed.
Lemma lem3161455 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3161456 : term434 = term435.
Proof. exact (MK_COMB (@lem3161455) (@lem3161454)). Qed.
Lemma lem3161457 : term188 = term436.
Proof. exact (MK_COMB (@lem3161456) (@lem3161451)). Qed.
Lemma lem3161458 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3161460 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161461 : term188 = term189.
Proof. exact (@lem3161460 (NUMERAL 0) term2). Qed.
Lemma lem3161462 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161463 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161464 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161463 h1) (fun h1 : term189 = True => @lem3161462)). Qed.
Lemma lem3161465 : term189 = True.
Proof. exact (EQ_MP (@lem3161464) (@lem3161462)). Qed.
Lemma lem3161466 : term188 = True.
Proof. exact (TRANS (@lem3161461) (@lem3161465)). Qed.
Lemma lem3161467 : True = term188.
Proof. exact (SYM (@lem3161466)). Qed.
Lemma lem3161468 : term188.
Proof. exact (EQ_MP (@lem3161467) (@lem0)). Qed.
Lemma lem3161469 : term438.
Proof. exact (@lem3161458 (@lem3161468)). Qed.
Lemma lem3161471 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161472 : term188 = term189.
Proof. exact (@lem3161471 (NUMERAL 0) term2). Qed.
Lemma lem3161473 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161474 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161475 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161474 h1) (fun h1 : term189 = True => @lem3161473)). Qed.
Lemma lem3161476 : term189 = True.
Proof. exact (EQ_MP (@lem3161475) (@lem3161473)). Qed.
Lemma lem3161477 : term188 = True.
Proof. exact (TRANS (@lem3161472) (@lem3161476)). Qed.
Lemma lem3161478 : True = term188.
Proof. exact (SYM (@lem3161477)). Qed.
Lemma lem3161479 : term188.
Proof. exact (EQ_MP (@lem3161478) (@lem0)). Qed.
Lemma lem3161480 : term436 = term439.
Proof. exact (@lem3161469 (@lem3161479)). Qed.
Lemma lem3161482 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161483 : term169 = term170.
Proof. exact (@lem3161482 term2 term2). Qed.
Lemma lem3161484 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161485 : term172 = term2.
Proof. exact (EQ_MP (@lem3161484) (@lem940073)). Qed.
Lemma lem3161486 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161487 : term170 = term93.
Proof. exact (MK_COMB (@lem3161486) (@lem3161485)). Qed.
Lemma lem3161488 : term169 = term93.
Proof. exact (TRANS (@lem3161483) (@lem3161487)). Qed.
Lemma lem3161490 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161491 : term275 = term79.
Proof. exact (@lem3161490 term2). Qed.
Lemma lem3161492 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3161493 : term440 = term434.
Proof. exact (MK_COMB (@lem3161492) (@lem3161491)). Qed.
Lemma lem3161494 : term439 = term188.
Proof. exact (MK_COMB (@lem3161493) (@lem3161488)). Qed.
Lemma lem3161496 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161497 : term188 = term189.
Proof. exact (@lem3161496 (NUMERAL 0) term2). Qed.
Lemma lem3161498 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161499 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161500 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161499 h1) (fun h1 : term189 = True => @lem3161498)). Qed.
Lemma lem3161501 : term189 = True.
Proof. exact (EQ_MP (@lem3161500) (@lem3161498)). Qed.
Lemma lem3161502 : term188 = True.
Proof. exact (TRANS (@lem3161497) (@lem3161501)). Qed.
Lemma lem3161503 : term439 = True.
Proof. exact (TRANS (@lem3161494) (@lem3161502)). Qed.
Lemma lem3161504 : term436 = True.
Proof. exact (TRANS (@lem3161480) (@lem3161503)). Qed.
Lemma lem3161505 : term188 = True.
Proof. exact (TRANS (@lem3161457) (@lem3161504)). Qed.
Lemma lem3161506 : term433 = True.
Proof. exact (TRANS (@lem3161448) (@lem3161505)). Qed.
Lemma lem3161507 : True = term433.
Proof. exact (SYM (@lem3161506)). Qed.
Lemma lem3161508 : term433.
Proof. exact (EQ_MP (@lem3161507) (@lem0)). Qed.
Lemma lem3161509 (_32603 : int) (h1 : term562 _32603) : term511 _32603.
Proof. exact (conj (@lem3161508) (@lem3161445 _32603 h1)). Qed.
Lemma lem3161511 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3161512 (_32603 : int) : term512 _32603.
Proof. exact (@lem3161511 term93 (term243 _32603)). Qed.
Lemma lem3161513 (_32603 : int) (h1 : term562 _32603) : term513 _32603.
Proof. exact (@lem3161512 _32603 (@lem3161509 _32603 h1)). Qed.
Lemma lem3161514 (_32603 : int) : (term514 _32603) = (term243 _32603).
Proof. exact (@lem1982733 (term243 _32603)). Qed.
Lemma lem3161515 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161516 (_32603 : int) : (term515 _32603) = (term246 _32603).
Proof. exact (MK_COMB (@lem3161515) (@lem3161514 _32603)). Qed.
Lemma lem3161517 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161518 (_32603 : int) : (term513 _32603) = (term247 _32603).
Proof. exact (MK_COMB (@lem3161516 _32603) (@lem3161517)). Qed.
Lemma lem3161519 (_32603 : int) (h1 : term562 _32603) : term247 _32603.
Proof. exact (EQ_MP (@lem3161518 _32603) (@lem3161513 _32603 h1)). Qed.
Lemma lem3161521 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3161522 (_32603 : int) : term542 _32603.
Proof. exact (@lem3161521 (real_of_int _32603)). Qed.
Lemma lem3161523 (_32603 : int) (h1 : term562 _32603) : term543 _32603.
Proof. exact (@lem3161522 _32603 (@lem3161442 _32603 h1)). Qed.
Lemma lem3161524 (_32603 : int) (h1 : term562 _32603) : term563 _32603.
Proof. exact (@lem3161523 _32603 h1 term93). Qed.
Lemma lem3161525 (_32603 : int) : (term563 _32603) = ((term509 _32603) = term79).
Proof. exact (eq_refl (term563 _32603)). Qed.
Lemma lem3161526 (_32603 : int) (h1 : term562 _32603) : (term509 _32603) = term79.
Proof. exact (EQ_MP (@lem3161525 _32603) (@lem3161524 _32603 h1)). Qed.
Lemma lem3161527 (_32603 : int) : (term509 _32603) = (real_of_int _32603).
Proof. exact (@lem1982733 (real_of_int _32603)). Qed.
Lemma lem3161528 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3161529 (_32603 : int) : (term564 _32603) = (term142 _32603).
Proof. exact (MK_COMB (@lem3161528) (@lem3161527 _32603)). Qed.
Lemma lem3161530 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161531 (_32603 : int) : ((term509 _32603) = term79) = ((real_of_int _32603) = term79).
Proof. exact (MK_COMB (@lem3161529 _32603) (@lem3161530)). Qed.
Lemma lem3161532 (_32603 : int) (h1 : term562 _32603) : (real_of_int _32603) = term79.
Proof. exact (EQ_MP (@lem3161531 _32603) (@lem3161526 _32603 h1)). Qed.
Lemma lem3161533 (_32603 : int) (h1 : term562 _32603) : term565 _32603.
Proof. exact (conj (@lem3161532 _32603 h1) (@lem3161519 _32603 h1)). Qed.
Lemma lem3161535 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3161536 (_32603 : int) : term566 _32603.
Proof. exact (@lem3161535 (real_of_int _32603) (term243 _32603)). Qed.
Lemma lem3161537 (_32603 : int) (h1 : term562 _32603) : term567 _32603.
Proof. exact (@lem3161536 _32603 (@lem3161533 _32603 h1)). Qed.
Lemma lem3161538 (_32603 : int) : (term568 _32603) = (term569 _32603).
Proof. exact (@lem1982763 (real_of_int _32603) (term263 _32603) term160). Qed.
Lemma lem3161539 (_32603 : int) : (term570 _32603) = (term459 _32603).
Proof. exact (@lem1982715 term160 (real_of_int _32603)). Qed.
Lemma lem3161541 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161542 : term93 = term182.
Proof. exact (@lem3161541 term2). Qed.
Lemma lem3161544 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161545 : term160 = term161.
Proof. exact (@lem3161544 term2). Qed.
Lemma lem3161546 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161547 : term460 = term461.
Proof. exact (MK_COMB (@lem3161546) (@lem3161545)). Qed.
Lemma lem3161548 : term462 = term463.
Proof. exact (MK_COMB (@lem3161547) (@lem3161542)). Qed.
Lemma lem3161549 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3161551 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161552 : term188 = term189.
Proof. exact (@lem3161551 (NUMERAL 0) term2). Qed.
Lemma lem3161553 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161554 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161555 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161554 h1) (fun h1 : term189 = True => @lem3161553)). Qed.
Lemma lem3161556 : term189 = True.
Proof. exact (EQ_MP (@lem3161555) (@lem3161553)). Qed.
Lemma lem3161557 : term188 = True.
Proof. exact (TRANS (@lem3161552) (@lem3161556)). Qed.
Lemma lem3161558 : True = term188.
Proof. exact (SYM (@lem3161557)). Qed.
Lemma lem3161559 : term188.
Proof. exact (EQ_MP (@lem3161558) (@lem0)). Qed.
Lemma lem3161560 : term465.
Proof. exact (@lem3161549 (@lem3161559)). Qed.
Lemma lem3161562 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161563 : term188 = term189.
Proof. exact (@lem3161562 (NUMERAL 0) term2). Qed.
Lemma lem3161564 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161565 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161566 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161565 h1) (fun h1 : term189 = True => @lem3161564)). Qed.
Lemma lem3161567 : term189 = True.
Proof. exact (EQ_MP (@lem3161566) (@lem3161564)). Qed.
Lemma lem3161568 : term188 = True.
Proof. exact (TRANS (@lem3161563) (@lem3161567)). Qed.
Lemma lem3161569 : True = term188.
Proof. exact (SYM (@lem3161568)). Qed.
Lemma lem3161570 : term188.
Proof. exact (EQ_MP (@lem3161569) (@lem0)). Qed.
Lemma lem3161571 : term466.
Proof. exact (@lem3161560 (@lem3161570)). Qed.
Lemma lem3161573 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161574 : term188 = term189.
Proof. exact (@lem3161573 (NUMERAL 0) term2). Qed.
Lemma lem3161575 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161576 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161577 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161576 h1) (fun h1 : term189 = True => @lem3161575)). Qed.
Lemma lem3161578 : term189 = True.
Proof. exact (EQ_MP (@lem3161577) (@lem3161575)). Qed.
Lemma lem3161579 : term188 = True.
Proof. exact (TRANS (@lem3161574) (@lem3161578)). Qed.
Lemma lem3161580 : True = term188.
Proof. exact (SYM (@lem3161579)). Qed.
Lemma lem3161581 : term188.
Proof. exact (EQ_MP (@lem3161580) (@lem0)). Qed.
Lemma lem3161582 : term467.
Proof. exact (@lem3161571 (@lem3161581)). Qed.
Lemma lem3161584 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161585 : term169 = term170.
Proof. exact (@lem3161584 term2 term2). Qed.
Lemma lem3161586 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161587 : term172 = term2.
Proof. exact (EQ_MP (@lem3161586) (@lem940073)). Qed.
Lemma lem3161588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161589 : term170 = term93.
Proof. exact (MK_COMB (@lem3161588) (@lem3161587)). Qed.
Lemma lem3161590 : term169 = term93.
Proof. exact (TRANS (@lem3161585) (@lem3161589)). Qed.
Lemma lem3161592 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161593 : term236 = term239.
Proof. exact (@lem3161592 term2 term2). Qed.
Lemma lem3161594 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161595 : term172 = term2.
Proof. exact (EQ_MP (@lem3161594) (@lem940073)). Qed.
Lemma lem3161596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161597 : term170 = term93.
Proof. exact (MK_COMB (@lem3161596) (@lem3161595)). Qed.
Lemma lem3161598 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161599 : term239 = term160.
Proof. exact (MK_COMB (@lem3161598) (@lem3161597)). Qed.
Lemma lem3161600 : term236 = term160.
Proof. exact (TRANS (@lem3161593) (@lem3161599)). Qed.
Lemma lem3161601 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161602 : term468 = term460.
Proof. exact (MK_COMB (@lem3161601) (@lem3161600)). Qed.
Lemma lem3161603 : term469 = term462.
Proof. exact (MK_COMB (@lem3161602) (@lem3161590)). Qed.
Lemma lem3161605 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3161606 : term462 = term79.
Proof. exact (@lem3161605 term2). Qed.
Lemma lem3161607 : term469 = term79.
Proof. exact (TRANS (@lem3161603) (@lem3161606)). Qed.
Lemma lem3161608 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161609 : term471 = term273.
Proof. exact (MK_COMB (@lem3161608) (@lem3161607)). Qed.
Lemma lem3161610 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3161611 : term472 = term275.
Proof. exact (MK_COMB (@lem3161609) (@lem3161610)). Qed.
Lemma lem3161613 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161614 : term275 = term79.
Proof. exact (@lem3161613 term2). Qed.
Lemma lem3161615 : term472 = term79.
Proof. exact (TRANS (@lem3161611) (@lem3161614)). Qed.
Lemma lem3161617 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161618 : term169 = term170.
Proof. exact (@lem3161617 term2 term2). Qed.
Lemma lem3161619 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161620 : term172 = term2.
Proof. exact (EQ_MP (@lem3161619) (@lem940073)). Qed.
Lemma lem3161621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161622 : term170 = term93.
Proof. exact (MK_COMB (@lem3161621) (@lem3161620)). Qed.
Lemma lem3161623 : term169 = term93.
Proof. exact (TRANS (@lem3161618) (@lem3161622)). Qed.
Lemma lem3161624 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3161625 : term277 = term275.
Proof. exact (MK_COMB (@lem3161624) (@lem3161623)). Qed.
Lemma lem3161627 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161628 : term275 = term79.
Proof. exact (@lem3161627 term2). Qed.
Lemma lem3161629 : term277 = term79.
Proof. exact (TRANS (@lem3161625) (@lem3161628)). Qed.
Lemma lem3161630 : term79 = term277.
Proof. exact (SYM (@lem3161629)). Qed.
Lemma lem3161631 : term472 = term277.
Proof. exact (TRANS (@lem3161615) (@lem3161630)). Qed.
Lemma lem3161632 : term463 = term157.
Proof. exact (@lem3161582 (@lem3161631)). Qed.
Lemma lem3161633 : term462 = term157.
Proof. exact (TRANS (@lem3161548) (@lem3161632)). Qed.
Lemma lem3161635 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3161636 : term157 = term79.
Proof. exact (@lem3161635 term79). Qed.
Lemma lem3161637 : term462 = term79.
Proof. exact (TRANS (@lem3161633) (@lem3161636)). Qed.
Lemma lem3161638 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161639 : term473 = term273.
Proof. exact (MK_COMB (@lem3161638) (@lem3161637)). Qed.
Lemma lem3161640 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3161641 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3161639) (@lem3161640 _32603)). Qed.
Lemma lem3161642 (_32603 : int) : (term570 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3161539 _32603) (@lem3161641 _32603)). Qed.
Lemma lem3161643 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3161644 (_32603 : int) : (term570 _32603) = term79.
Proof. exact (TRANS (@lem3161642 _32603) (@lem3161643 _32603)). Qed.
Lemma lem3161645 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161646 (_32603 : int) : (term571 _32603) = term121.
Proof. exact (MK_COMB (@lem3161645) (@lem3161644 _32603)). Qed.
Lemma lem3161647 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3161648 (_32603 : int) : (term569 _32603) = term490.
Proof. exact (MK_COMB (@lem3161646 _32603) (@lem3161647)). Qed.
Lemma lem3161649 (_32603 : int) : (term568 _32603) = term490.
Proof. exact (TRANS (@lem3161538 _32603) (@lem3161648 _32603)). Qed.
Lemma lem3161650 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3161651 (_32603 : int) : (term568 _32603) = term160.
Proof. exact (TRANS (@lem3161649 _32603) (@lem3161650)). Qed.
Lemma lem3161652 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161653 (_32603 : int) : (term572 _32603) = term492.
Proof. exact (MK_COMB (@lem3161652) (@lem3161651 _32603)). Qed.
Lemma lem3161654 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161655 (_32603 : int) : (term567 _32603) = term493.
Proof. exact (MK_COMB (@lem3161653 _32603) (@lem3161654)). Qed.
Lemma lem3161656 (_32603 : int) (h1 : term562 _32603) : term493.
Proof. exact (EQ_MP (@lem3161655 _32603) (@lem3161537 _32603 h1)). Qed.
Lemma lem3161658 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3161659 : term493 = term494.
Proof. exact (@lem3161658 term79 term160). Qed.
Lemma lem3161661 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161662 : term160 = term161.
Proof. exact (@lem3161661 term2). Qed.
Lemma lem3161664 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161665 : term79 = term157.
Proof. exact (@lem3161664 (NUMERAL 0)). Qed.
Lemma lem3161666 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161667 : term81 = term495.
Proof. exact (MK_COMB (@lem3161666) (@lem3161665)). Qed.
Lemma lem3161668 : term494 = term496.
Proof. exact (MK_COMB (@lem3161667) (@lem3161662)). Qed.
Lemma lem3161669 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3161671 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161672 : term188 = term189.
Proof. exact (@lem3161671 (NUMERAL 0) term2). Qed.
Lemma lem3161673 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161674 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161675 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161674 h1) (fun h1 : term189 = True => @lem3161673)). Qed.
Lemma lem3161676 : term189 = True.
Proof. exact (EQ_MP (@lem3161675) (@lem3161673)). Qed.
Lemma lem3161677 : term188 = True.
Proof. exact (TRANS (@lem3161672) (@lem3161676)). Qed.
Lemma lem3161678 : True = term188.
Proof. exact (SYM (@lem3161677)). Qed.
Lemma lem3161679 : term188.
Proof. exact (EQ_MP (@lem3161678) (@lem0)). Qed.
Lemma lem3161680 : term498.
Proof. exact (@lem3161669 (@lem3161679)). Qed.
Lemma lem3161682 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161683 : term188 = term189.
Proof. exact (@lem3161682 (NUMERAL 0) term2). Qed.
Lemma lem3161684 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161685 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161686 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161685 h1) (fun h1 : term189 = True => @lem3161684)). Qed.
Lemma lem3161687 : term189 = True.
Proof. exact (EQ_MP (@lem3161686) (@lem3161684)). Qed.
Lemma lem3161688 : term188 = True.
Proof. exact (TRANS (@lem3161683) (@lem3161687)). Qed.
Lemma lem3161689 : True = term188.
Proof. exact (SYM (@lem3161688)). Qed.
Lemma lem3161690 : term188.
Proof. exact (EQ_MP (@lem3161689) (@lem0)). Qed.
Lemma lem3161691 : term496 = term499.
Proof. exact (@lem3161680 (@lem3161690)). Qed.
Lemma lem3161693 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161694 : term236 = term239.
Proof. exact (@lem3161693 term2 term2). Qed.
Lemma lem3161695 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161696 : term172 = term2.
Proof. exact (EQ_MP (@lem3161695) (@lem940073)). Qed.
Lemma lem3161697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161698 : term170 = term93.
Proof. exact (MK_COMB (@lem3161697) (@lem3161696)). Qed.
Lemma lem3161699 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161700 : term239 = term160.
Proof. exact (MK_COMB (@lem3161699) (@lem3161698)). Qed.
Lemma lem3161701 : term236 = term160.
Proof. exact (TRANS (@lem3161694) (@lem3161700)). Qed.
Lemma lem3161703 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161704 : term275 = term79.
Proof. exact (@lem3161703 term2). Qed.
Lemma lem3161705 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161706 : term500 = term81.
Proof. exact (MK_COMB (@lem3161705) (@lem3161704)). Qed.
Lemma lem3161707 : term499 = term494.
Proof. exact (MK_COMB (@lem3161706) (@lem3161701)). Qed.
Lemma lem3161709 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3161710 : term494 = term503.
Proof. exact (@lem3161709 (NUMERAL 0) term2). Qed.
Lemma lem3161711 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161712 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3161713 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161712 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3161711)). Qed.
Lemma lem3161714 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3161713) (@lem3161711)). Qed.
Lemma lem3161715 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3161716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3161717 : term504 = (and True).
Proof. exact (MK_COMB (@lem3161716) (@lem3161715)). Qed.
Lemma lem3161718 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3161717) (@lem3161714)). Qed.
Lemma lem3161720 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3161721 : term503 = False.
Proof. exact (TRANS (@lem3161718) (@lem3161720)). Qed.
Lemma lem3161722 : term494 = False.
Proof. exact (TRANS (@lem3161710) (@lem3161721)). Qed.
Lemma lem3161723 : term499 = False.
Proof. exact (TRANS (@lem3161707) (@lem3161722)). Qed.
Lemma lem3161724 : term496 = False.
Proof. exact (TRANS (@lem3161691) (@lem3161723)). Qed.
Lemma lem3161725 : term494 = False.
Proof. exact (TRANS (@lem3161668) (@lem3161724)). Qed.
Lemma lem3161726 : term493 = False.
Proof. exact (TRANS (@lem3161659) (@lem3161725)). Qed.
Lemma lem3161727 (_32603 : int) (h1 : term562 _32603) : False.
Proof. exact (EQ_MP (@lem3161726) (@lem3161656 _32603 h1)). Qed.
Lemma lem3161728 (_32603 : int) (h1 : term573 _32603) : term573 _32603.
Proof. exact (h1). Qed.
Lemma lem3161729 (_32603 : int) (h1 : term573 _32603) : term402 _32603.
Proof. exact (proj2 (@lem3161728 _32603 h1)). Qed.
Lemma lem3161731 (_32603 : int) (h1 : term573 _32603) : (real_of_int _32603) = term79.
Proof. exact (proj2 (@lem3161729 _32603 h1)). Qed.
Lemma lem3161732 (_32603 : int) (h1 : term573 _32603) : term330 _32603.
Proof. exact (proj1 (@lem3161729 _32603 h1)). Qed.
Lemma lem3161734 (_32603 : int) (h1 : term573 _32603) : term255 _32603.
Proof. exact (proj1 (@lem3161732 _32603 h1)). Qed.
Lemma lem3161736 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3161737 : term433 = term188.
Proof. exact (@lem3161736 term79 term93). Qed.
Lemma lem3161739 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161740 : term93 = term182.
Proof. exact (@lem3161739 term2). Qed.
Lemma lem3161742 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161743 : term79 = term157.
Proof. exact (@lem3161742 (NUMERAL 0)). Qed.
Lemma lem3161744 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3161745 : term434 = term435.
Proof. exact (MK_COMB (@lem3161744) (@lem3161743)). Qed.
Lemma lem3161746 : term188 = term436.
Proof. exact (MK_COMB (@lem3161745) (@lem3161740)). Qed.
Lemma lem3161747 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3161749 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161750 : term188 = term189.
Proof. exact (@lem3161749 (NUMERAL 0) term2). Qed.
Lemma lem3161751 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161752 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161753 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161752 h1) (fun h1 : term189 = True => @lem3161751)). Qed.
Lemma lem3161754 : term189 = True.
Proof. exact (EQ_MP (@lem3161753) (@lem3161751)). Qed.
Lemma lem3161755 : term188 = True.
Proof. exact (TRANS (@lem3161750) (@lem3161754)). Qed.
Lemma lem3161756 : True = term188.
Proof. exact (SYM (@lem3161755)). Qed.
Lemma lem3161757 : term188.
Proof. exact (EQ_MP (@lem3161756) (@lem0)). Qed.
Lemma lem3161758 : term438.
Proof. exact (@lem3161747 (@lem3161757)). Qed.
Lemma lem3161760 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161761 : term188 = term189.
Proof. exact (@lem3161760 (NUMERAL 0) term2). Qed.
Lemma lem3161762 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161763 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161764 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161763 h1) (fun h1 : term189 = True => @lem3161762)). Qed.
Lemma lem3161765 : term189 = True.
Proof. exact (EQ_MP (@lem3161764) (@lem3161762)). Qed.
Lemma lem3161766 : term188 = True.
Proof. exact (TRANS (@lem3161761) (@lem3161765)). Qed.
Lemma lem3161767 : True = term188.
Proof. exact (SYM (@lem3161766)). Qed.
Lemma lem3161768 : term188.
Proof. exact (EQ_MP (@lem3161767) (@lem0)). Qed.
Lemma lem3161769 : term436 = term439.
Proof. exact (@lem3161758 (@lem3161768)). Qed.
Lemma lem3161771 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161772 : term169 = term170.
Proof. exact (@lem3161771 term2 term2). Qed.
Lemma lem3161773 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161774 : term172 = term2.
Proof. exact (EQ_MP (@lem3161773) (@lem940073)). Qed.
Lemma lem3161775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161776 : term170 = term93.
Proof. exact (MK_COMB (@lem3161775) (@lem3161774)). Qed.
Lemma lem3161777 : term169 = term93.
Proof. exact (TRANS (@lem3161772) (@lem3161776)). Qed.
Lemma lem3161779 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161780 : term275 = term79.
Proof. exact (@lem3161779 term2). Qed.
Lemma lem3161781 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3161782 : term440 = term434.
Proof. exact (MK_COMB (@lem3161781) (@lem3161780)). Qed.
Lemma lem3161783 : term439 = term188.
Proof. exact (MK_COMB (@lem3161782) (@lem3161777)). Qed.
Lemma lem3161785 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161786 : term188 = term189.
Proof. exact (@lem3161785 (NUMERAL 0) term2). Qed.
Lemma lem3161787 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161788 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161789 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161788 h1) (fun h1 : term189 = True => @lem3161787)). Qed.
Lemma lem3161790 : term189 = True.
Proof. exact (EQ_MP (@lem3161789) (@lem3161787)). Qed.
Lemma lem3161791 : term188 = True.
Proof. exact (TRANS (@lem3161786) (@lem3161790)). Qed.
Lemma lem3161792 : term439 = True.
Proof. exact (TRANS (@lem3161783) (@lem3161791)). Qed.
Lemma lem3161793 : term436 = True.
Proof. exact (TRANS (@lem3161769) (@lem3161792)). Qed.
Lemma lem3161794 : term188 = True.
Proof. exact (TRANS (@lem3161746) (@lem3161793)). Qed.
Lemma lem3161795 : term433 = True.
Proof. exact (TRANS (@lem3161737) (@lem3161794)). Qed.
Lemma lem3161796 : True = term433.
Proof. exact (SYM (@lem3161795)). Qed.
Lemma lem3161797 : term433.
Proof. exact (EQ_MP (@lem3161796) (@lem0)). Qed.
Lemma lem3161798 (_32603 : int) (h1 : term573 _32603) : term523 _32603.
Proof. exact (conj (@lem3161797) (@lem3161734 _32603 h1)). Qed.
Lemma lem3161800 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3161801 (_32603 : int) : term524 _32603.
Proof. exact (@lem3161800 term93 (term252 _32603)). Qed.
Lemma lem3161802 (_32603 : int) (h1 : term573 _32603) : term525 _32603.
Proof. exact (@lem3161801 _32603 (@lem3161798 _32603 h1)). Qed.
Lemma lem3161803 (_32603 : int) : (term526 _32603) = (term252 _32603).
Proof. exact (@lem1982733 (term252 _32603)). Qed.
Lemma lem3161804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161805 (_32603 : int) : (term527 _32603) = (term254 _32603).
Proof. exact (MK_COMB (@lem3161804) (@lem3161803 _32603)). Qed.
Lemma lem3161806 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161807 (_32603 : int) : (term525 _32603) = (term255 _32603).
Proof. exact (MK_COMB (@lem3161805 _32603) (@lem3161806)). Qed.
Lemma lem3161808 (_32603 : int) (h1 : term573 _32603) : term255 _32603.
Proof. exact (EQ_MP (@lem3161807 _32603) (@lem3161802 _32603 h1)). Qed.
Lemma lem3161810 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3161811 (_32603 : int) : term542 _32603.
Proof. exact (@lem3161810 (real_of_int _32603)). Qed.
Lemma lem3161812 (_32603 : int) (h1 : term573 _32603) : term543 _32603.
Proof. exact (@lem3161811 _32603 (@lem3161731 _32603 h1)). Qed.
Lemma lem3161813 (_32603 : int) (h1 : term573 _32603) : term544 _32603.
Proof. exact (@lem3161812 _32603 h1 term160). Qed.
Lemma lem3161814 (_32603 : int) : (term544 _32603) = ((term263 _32603) = term79).
Proof. exact (eq_refl (term544 _32603)). Qed.
Lemma lem3161821 (_32603 : int) (h1 : term573 _32603) : (term263 _32603) = term79.
Proof. exact (EQ_MP (@lem3161814 _32603) (@lem3161813 _32603 h1)). Qed.
Lemma lem3161822 (_32603 : int) (h1 : term573 _32603) : term574 _32603.
Proof. exact (conj (@lem3161821 _32603 h1) (@lem3161808 _32603 h1)). Qed.
Lemma lem3161824 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3161825 (_32603 : int) : term575 _32603.
Proof. exact (@lem3161824 (term263 _32603) (term252 _32603)). Qed.
Lemma lem3161826 (_32603 : int) (h1 : term573 _32603) : term535 _32603.
Proof. exact (@lem3161825 _32603 (@lem3161822 _32603 h1)). Qed.
Lemma lem3161827 (_32603 : int) : (term536 _32603) = (term520 _32603).
Proof. exact (@lem1982763 (term263 _32603) (real_of_int _32603) term160). Qed.
Lemma lem3161828 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3161830 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161831 : term93 = term182.
Proof. exact (@lem3161830 term2). Qed.
Lemma lem3161833 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161834 : term160 = term161.
Proof. exact (@lem3161833 term2). Qed.
Lemma lem3161835 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161836 : term460 = term461.
Proof. exact (MK_COMB (@lem3161835) (@lem3161834)). Qed.
Lemma lem3161837 : term462 = term463.
Proof. exact (MK_COMB (@lem3161836) (@lem3161831)). Qed.
Lemma lem3161838 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3161840 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161841 : term188 = term189.
Proof. exact (@lem3161840 (NUMERAL 0) term2). Qed.
Lemma lem3161842 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161843 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161844 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161843 h1) (fun h1 : term189 = True => @lem3161842)). Qed.
Lemma lem3161845 : term189 = True.
Proof. exact (EQ_MP (@lem3161844) (@lem3161842)). Qed.
Lemma lem3161846 : term188 = True.
Proof. exact (TRANS (@lem3161841) (@lem3161845)). Qed.
Lemma lem3161847 : True = term188.
Proof. exact (SYM (@lem3161846)). Qed.
Lemma lem3161848 : term188.
Proof. exact (EQ_MP (@lem3161847) (@lem0)). Qed.
Lemma lem3161849 : term465.
Proof. exact (@lem3161838 (@lem3161848)). Qed.
Lemma lem3161851 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161852 : term188 = term189.
Proof. exact (@lem3161851 (NUMERAL 0) term2). Qed.
Lemma lem3161853 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161854 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161855 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161854 h1) (fun h1 : term189 = True => @lem3161853)). Qed.
Lemma lem3161856 : term189 = True.
Proof. exact (EQ_MP (@lem3161855) (@lem3161853)). Qed.
Lemma lem3161857 : term188 = True.
Proof. exact (TRANS (@lem3161852) (@lem3161856)). Qed.
Lemma lem3161858 : True = term188.
Proof. exact (SYM (@lem3161857)). Qed.
Lemma lem3161859 : term188.
Proof. exact (EQ_MP (@lem3161858) (@lem0)). Qed.
Lemma lem3161860 : term466.
Proof. exact (@lem3161849 (@lem3161859)). Qed.
Lemma lem3161862 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161863 : term188 = term189.
Proof. exact (@lem3161862 (NUMERAL 0) term2). Qed.
Lemma lem3161864 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161865 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161866 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161865 h1) (fun h1 : term189 = True => @lem3161864)). Qed.
Lemma lem3161867 : term189 = True.
Proof. exact (EQ_MP (@lem3161866) (@lem3161864)). Qed.
Lemma lem3161868 : term188 = True.
Proof. exact (TRANS (@lem3161863) (@lem3161867)). Qed.
Lemma lem3161869 : True = term188.
Proof. exact (SYM (@lem3161868)). Qed.
Lemma lem3161870 : term188.
Proof. exact (EQ_MP (@lem3161869) (@lem0)). Qed.
Lemma lem3161871 : term467.
Proof. exact (@lem3161860 (@lem3161870)). Qed.
Lemma lem3161873 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161874 : term169 = term170.
Proof. exact (@lem3161873 term2 term2). Qed.
Lemma lem3161875 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161876 : term172 = term2.
Proof. exact (EQ_MP (@lem3161875) (@lem940073)). Qed.
Lemma lem3161877 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161878 : term170 = term93.
Proof. exact (MK_COMB (@lem3161877) (@lem3161876)). Qed.
Lemma lem3161879 : term169 = term93.
Proof. exact (TRANS (@lem3161874) (@lem3161878)). Qed.
Lemma lem3161881 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161882 : term236 = term239.
Proof. exact (@lem3161881 term2 term2). Qed.
Lemma lem3161883 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161884 : term172 = term2.
Proof. exact (EQ_MP (@lem3161883) (@lem940073)). Qed.
Lemma lem3161885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161886 : term170 = term93.
Proof. exact (MK_COMB (@lem3161885) (@lem3161884)). Qed.
Lemma lem3161887 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161888 : term239 = term160.
Proof. exact (MK_COMB (@lem3161887) (@lem3161886)). Qed.
Lemma lem3161889 : term236 = term160.
Proof. exact (TRANS (@lem3161882) (@lem3161888)). Qed.
Lemma lem3161890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161891 : term468 = term460.
Proof. exact (MK_COMB (@lem3161890) (@lem3161889)). Qed.
Lemma lem3161892 : term469 = term462.
Proof. exact (MK_COMB (@lem3161891) (@lem3161879)). Qed.
Lemma lem3161894 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3161895 : term462 = term79.
Proof. exact (@lem3161894 term2). Qed.
Lemma lem3161896 : term469 = term79.
Proof. exact (TRANS (@lem3161892) (@lem3161895)). Qed.
Lemma lem3161897 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161898 : term471 = term273.
Proof. exact (MK_COMB (@lem3161897) (@lem3161896)). Qed.
Lemma lem3161899 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3161900 : term472 = term275.
Proof. exact (MK_COMB (@lem3161898) (@lem3161899)). Qed.
Lemma lem3161902 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161903 : term275 = term79.
Proof. exact (@lem3161902 term2). Qed.
Lemma lem3161904 : term472 = term79.
Proof. exact (TRANS (@lem3161900) (@lem3161903)). Qed.
Lemma lem3161906 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3161907 : term169 = term170.
Proof. exact (@lem3161906 term2 term2). Qed.
Lemma lem3161908 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161909 : term172 = term2.
Proof. exact (EQ_MP (@lem3161908) (@lem940073)). Qed.
Lemma lem3161910 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161911 : term170 = term93.
Proof. exact (MK_COMB (@lem3161910) (@lem3161909)). Qed.
Lemma lem3161912 : term169 = term93.
Proof. exact (TRANS (@lem3161907) (@lem3161911)). Qed.
Lemma lem3161913 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3161914 : term277 = term275.
Proof. exact (MK_COMB (@lem3161913) (@lem3161912)). Qed.
Lemma lem3161916 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161917 : term275 = term79.
Proof. exact (@lem3161916 term2). Qed.
Lemma lem3161918 : term277 = term79.
Proof. exact (TRANS (@lem3161914) (@lem3161917)). Qed.
Lemma lem3161919 : term79 = term277.
Proof. exact (SYM (@lem3161918)). Qed.
Lemma lem3161920 : term472 = term277.
Proof. exact (TRANS (@lem3161904) (@lem3161919)). Qed.
Lemma lem3161921 : term463 = term157.
Proof. exact (@lem3161871 (@lem3161920)). Qed.
Lemma lem3161922 : term462 = term157.
Proof. exact (TRANS (@lem3161837) (@lem3161921)). Qed.
Lemma lem3161924 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3161925 : term157 = term79.
Proof. exact (@lem3161924 term79). Qed.
Lemma lem3161926 : term462 = term79.
Proof. exact (TRANS (@lem3161922) (@lem3161925)). Qed.
Lemma lem3161927 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3161928 : term473 = term273.
Proof. exact (MK_COMB (@lem3161927) (@lem3161926)). Qed.
Lemma lem3161929 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3161930 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3161928) (@lem3161929 _32603)). Qed.
Lemma lem3161931 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3161828 _32603) (@lem3161930 _32603)). Qed.
Lemma lem3161932 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3161933 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3161931 _32603) (@lem3161932 _32603)). Qed.
Lemma lem3161934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3161935 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3161934) (@lem3161933 _32603)). Qed.
Lemma lem3161936 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3161937 (_32603 : int) : (term520 _32603) = term490.
Proof. exact (MK_COMB (@lem3161935 _32603) (@lem3161936)). Qed.
Lemma lem3161938 (_32603 : int) : (term536 _32603) = term490.
Proof. exact (TRANS (@lem3161827 _32603) (@lem3161937 _32603)). Qed.
Lemma lem3161939 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3161940 (_32603 : int) : (term536 _32603) = term160.
Proof. exact (TRANS (@lem3161938 _32603) (@lem3161939)). Qed.
Lemma lem3161941 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3161942 (_32603 : int) : (term537 _32603) = term492.
Proof. exact (MK_COMB (@lem3161941) (@lem3161940 _32603)). Qed.
Lemma lem3161943 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3161944 (_32603 : int) : (term535 _32603) = term493.
Proof. exact (MK_COMB (@lem3161942 _32603) (@lem3161943)). Qed.
Lemma lem3161945 (_32603 : int) (h1 : term573 _32603) : term493.
Proof. exact (EQ_MP (@lem3161944 _32603) (@lem3161826 _32603 h1)). Qed.
Lemma lem3161947 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3161948 : term493 = term494.
Proof. exact (@lem3161947 term79 term160). Qed.
Lemma lem3161950 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3161951 : term160 = term161.
Proof. exact (@lem3161950 term2). Qed.
Lemma lem3161953 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3161954 : term79 = term157.
Proof. exact (@lem3161953 (NUMERAL 0)). Qed.
Lemma lem3161955 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161956 : term81 = term495.
Proof. exact (MK_COMB (@lem3161955) (@lem3161954)). Qed.
Lemma lem3161957 : term494 = term496.
Proof. exact (MK_COMB (@lem3161956) (@lem3161951)). Qed.
Lemma lem3161958 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3161960 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161961 : term188 = term189.
Proof. exact (@lem3161960 (NUMERAL 0) term2). Qed.
Lemma lem3161962 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161963 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161964 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161963 h1) (fun h1 : term189 = True => @lem3161962)). Qed.
Lemma lem3161965 : term189 = True.
Proof. exact (EQ_MP (@lem3161964) (@lem3161962)). Qed.
Lemma lem3161966 : term188 = True.
Proof. exact (TRANS (@lem3161961) (@lem3161965)). Qed.
Lemma lem3161967 : True = term188.
Proof. exact (SYM (@lem3161966)). Qed.
Lemma lem3161968 : term188.
Proof. exact (EQ_MP (@lem3161967) (@lem0)). Qed.
Lemma lem3161969 : term498.
Proof. exact (@lem3161958 (@lem3161968)). Qed.
Lemma lem3161971 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3161972 : term188 = term189.
Proof. exact (@lem3161971 (NUMERAL 0) term2). Qed.
Lemma lem3161973 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3161974 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3161975 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3161974 h1) (fun h1 : term189 = True => @lem3161973)). Qed.
Lemma lem3161976 : term189 = True.
Proof. exact (EQ_MP (@lem3161975) (@lem3161973)). Qed.
Lemma lem3161977 : term188 = True.
Proof. exact (TRANS (@lem3161972) (@lem3161976)). Qed.
Lemma lem3161978 : True = term188.
Proof. exact (SYM (@lem3161977)). Qed.
Lemma lem3161979 : term188.
Proof. exact (EQ_MP (@lem3161978) (@lem0)). Qed.
Lemma lem3161980 : term496 = term499.
Proof. exact (@lem3161969 (@lem3161979)). Qed.
Lemma lem3161982 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3161983 : term236 = term239.
Proof. exact (@lem3161982 term2 term2). Qed.
Lemma lem3161984 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3161985 : term172 = term2.
Proof. exact (EQ_MP (@lem3161984) (@lem940073)). Qed.
Lemma lem3161986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3161987 : term170 = term93.
Proof. exact (MK_COMB (@lem3161986) (@lem3161985)). Qed.
Lemma lem3161988 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3161989 : term239 = term160.
Proof. exact (MK_COMB (@lem3161988) (@lem3161987)). Qed.
Lemma lem3161990 : term236 = term160.
Proof. exact (TRANS (@lem3161983) (@lem3161989)). Qed.
Lemma lem3161992 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3161993 : term275 = term79.
Proof. exact (@lem3161992 term2). Qed.
Lemma lem3161994 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3161995 : term500 = term81.
Proof. exact (MK_COMB (@lem3161994) (@lem3161993)). Qed.
Lemma lem3161996 : term499 = term494.
Proof. exact (MK_COMB (@lem3161995) (@lem3161990)). Qed.
Lemma lem3161998 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3161999 : term494 = term503.
Proof. exact (@lem3161998 (NUMERAL 0) term2). Qed.
Lemma lem3162000 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162001 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3162002 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162001 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3162000)). Qed.
Lemma lem3162003 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3162002) (@lem3162000)). Qed.
Lemma lem3162004 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3162005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3162006 : term504 = (and True).
Proof. exact (MK_COMB (@lem3162005) (@lem3162004)). Qed.
Lemma lem3162007 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3162006) (@lem3162003)). Qed.
Lemma lem3162009 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3162010 : term503 = False.
Proof. exact (TRANS (@lem3162007) (@lem3162009)). Qed.
Lemma lem3162011 : term494 = False.
Proof. exact (TRANS (@lem3161999) (@lem3162010)). Qed.
Lemma lem3162012 : term499 = False.
Proof. exact (TRANS (@lem3161996) (@lem3162011)). Qed.
Lemma lem3162013 : term496 = False.
Proof. exact (TRANS (@lem3161980) (@lem3162012)). Qed.
Lemma lem3162014 : term494 = False.
Proof. exact (TRANS (@lem3161957) (@lem3162013)). Qed.
Lemma lem3162015 : term493 = False.
Proof. exact (TRANS (@lem3161948) (@lem3162014)). Qed.
Lemma lem3162016 (_32603 : int) (h1 : term573 _32603) : False.
Proof. exact (EQ_MP (@lem3162015) (@lem3161945 _32603 h1)). Qed.
Lemma lem3162017 (_32603 : int) (h1 : term400 _32603) : False.
Proof. exact (or_elim (@lem3161438 _32603 h1) (fun h0 : term562 _32603 => @lem3161727 _32603 h0) (fun h0 : term573 _32603 => @lem3162016 _32603 h0)). Qed.
Lemma lem3162018 (_32603 : int) (h1 : term396 _32603) : term396 _32603.
Proof. exact (h1). Qed.
Lemma lem3162019 (_32603 : int) (h1 : term576 _32603) : term576 _32603.
Proof. exact (h1). Qed.
Lemma lem3162020 (_32603 : int) (h1 : term576 _32603) : term397 _32603.
Proof. exact (proj2 (@lem3162019 _32603 h1)). Qed.
Lemma lem3162022 (_32603 : int) (h1 : term576 _32603) : (real_of_int _32603) = term79.
Proof. exact (proj2 (@lem3162020 _32603 h1)). Qed.
Lemma lem3162023 (_32603 : int) (h1 : term576 _32603) : term325 _32603.
Proof. exact (proj1 (@lem3162020 _32603 h1)). Qed.
Lemma lem3162024 (_32603 : int) (h1 : term576 _32603) : term230 _32603.
Proof. exact (proj2 (@lem3162023 _32603 h1)). Qed.
Lemma lem3162027 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3162028 : term433 = term188.
Proof. exact (@lem3162027 term79 term93). Qed.
Lemma lem3162030 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162031 : term93 = term182.
Proof. exact (@lem3162030 term2). Qed.
Lemma lem3162033 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162034 : term79 = term157.
Proof. exact (@lem3162033 (NUMERAL 0)). Qed.
Lemma lem3162035 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3162036 : term434 = term435.
Proof. exact (MK_COMB (@lem3162035) (@lem3162034)). Qed.
Lemma lem3162037 : term188 = term436.
Proof. exact (MK_COMB (@lem3162036) (@lem3162031)). Qed.
Lemma lem3162038 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3162040 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162041 : term188 = term189.
Proof. exact (@lem3162040 (NUMERAL 0) term2). Qed.
Lemma lem3162042 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162043 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162044 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162043 h1) (fun h1 : term189 = True => @lem3162042)). Qed.
Lemma lem3162045 : term189 = True.
Proof. exact (EQ_MP (@lem3162044) (@lem3162042)). Qed.
Lemma lem3162046 : term188 = True.
Proof. exact (TRANS (@lem3162041) (@lem3162045)). Qed.
Lemma lem3162047 : True = term188.
Proof. exact (SYM (@lem3162046)). Qed.
Lemma lem3162048 : term188.
Proof. exact (EQ_MP (@lem3162047) (@lem0)). Qed.
Lemma lem3162049 : term438.
Proof. exact (@lem3162038 (@lem3162048)). Qed.
Lemma lem3162051 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162052 : term188 = term189.
Proof. exact (@lem3162051 (NUMERAL 0) term2). Qed.
Lemma lem3162053 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162054 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162055 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162054 h1) (fun h1 : term189 = True => @lem3162053)). Qed.
Lemma lem3162056 : term189 = True.
Proof. exact (EQ_MP (@lem3162055) (@lem3162053)). Qed.
Lemma lem3162057 : term188 = True.
Proof. exact (TRANS (@lem3162052) (@lem3162056)). Qed.
Lemma lem3162058 : True = term188.
Proof. exact (SYM (@lem3162057)). Qed.
Lemma lem3162059 : term188.
Proof. exact (EQ_MP (@lem3162058) (@lem0)). Qed.
Lemma lem3162060 : term436 = term439.
Proof. exact (@lem3162049 (@lem3162059)). Qed.
Lemma lem3162062 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162063 : term169 = term170.
Proof. exact (@lem3162062 term2 term2). Qed.
Lemma lem3162064 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162065 : term172 = term2.
Proof. exact (EQ_MP (@lem3162064) (@lem940073)). Qed.
Lemma lem3162066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162067 : term170 = term93.
Proof. exact (MK_COMB (@lem3162066) (@lem3162065)). Qed.
Lemma lem3162068 : term169 = term93.
Proof. exact (TRANS (@lem3162063) (@lem3162067)). Qed.
Lemma lem3162070 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162071 : term275 = term79.
Proof. exact (@lem3162070 term2). Qed.
Lemma lem3162072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3162073 : term440 = term434.
Proof. exact (MK_COMB (@lem3162072) (@lem3162071)). Qed.
Lemma lem3162074 : term439 = term188.
Proof. exact (MK_COMB (@lem3162073) (@lem3162068)). Qed.
Lemma lem3162076 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162077 : term188 = term189.
Proof. exact (@lem3162076 (NUMERAL 0) term2). Qed.
Lemma lem3162078 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162079 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162080 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162079 h1) (fun h1 : term189 = True => @lem3162078)). Qed.
Lemma lem3162081 : term189 = True.
Proof. exact (EQ_MP (@lem3162080) (@lem3162078)). Qed.
Lemma lem3162082 : term188 = True.
Proof. exact (TRANS (@lem3162077) (@lem3162081)). Qed.
Lemma lem3162083 : term439 = True.
Proof. exact (TRANS (@lem3162074) (@lem3162082)). Qed.
Lemma lem3162084 : term436 = True.
Proof. exact (TRANS (@lem3162060) (@lem3162083)). Qed.
Lemma lem3162085 : term188 = True.
Proof. exact (TRANS (@lem3162037) (@lem3162084)). Qed.
Lemma lem3162086 : term433 = True.
Proof. exact (TRANS (@lem3162028) (@lem3162085)). Qed.
Lemma lem3162087 : True = term433.
Proof. exact (SYM (@lem3162086)). Qed.
Lemma lem3162088 : term433.
Proof. exact (EQ_MP (@lem3162087) (@lem0)). Qed.
Lemma lem3162089 (_32603 : int) (h1 : term576 _32603) : term441 _32603.
Proof. exact (conj (@lem3162088) (@lem3162024 _32603 h1)). Qed.
Lemma lem3162091 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3162092 (_32603 : int) : term443 _32603.
Proof. exact (@lem3162091 term93 (term227 _32603)). Qed.
Lemma lem3162093 (_32603 : int) (h1 : term576 _32603) : term444 _32603.
Proof. exact (@lem3162092 _32603 (@lem3162089 _32603 h1)). Qed.
Lemma lem3162094 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3162095 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3162096 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3162095) (@lem3162094 _32603)). Qed.
Lemma lem3162097 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162098 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3162096 _32603) (@lem3162097)). Qed.
Lemma lem3162099 (_32603 : int) (h1 : term576 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3162098 _32603) (@lem3162093 _32603 h1)). Qed.
Lemma lem3162101 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3162102 (_32603 : int) : term542 _32603.
Proof. exact (@lem3162101 (real_of_int _32603)). Qed.
Lemma lem3162103 (_32603 : int) (h1 : term576 _32603) : term543 _32603.
Proof. exact (@lem3162102 _32603 (@lem3162022 _32603 h1)). Qed.
Lemma lem3162104 (_32603 : int) (h1 : term576 _32603) : term544 _32603.
Proof. exact (@lem3162103 _32603 h1 term160). Qed.
Lemma lem3162105 (_32603 : int) : (term544 _32603) = ((term263 _32603) = term79).
Proof. exact (eq_refl (term544 _32603)). Qed.
Lemma lem3162112 (_32603 : int) (h1 : term576 _32603) : (term263 _32603) = term79.
Proof. exact (EQ_MP (@lem3162105 _32603) (@lem3162104 _32603 h1)). Qed.
Lemma lem3162113 (_32603 : int) (h1 : term576 _32603) : term545 _32603.
Proof. exact (conj (@lem3162112 _32603 h1) (@lem3162099 _32603 h1)). Qed.
Lemma lem3162115 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3162116 (_32603 : int) : term547 _32603.
Proof. exact (@lem3162115 (term263 _32603) (term227 _32603)). Qed.
Lemma lem3162117 (_32603 : int) (h1 : term576 _32603) : term548 _32603.
Proof. exact (@lem3162116 _32603 (@lem3162113 _32603 h1)). Qed.
Lemma lem3162118 (_32603 : int) : (term549 _32603) = (term550 _32603).
Proof. exact (@lem1982763 (term263 _32603) (real_of_int _32603) term223). Qed.
Lemma lem3162119 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3162121 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162122 : term93 = term182.
Proof. exact (@lem3162121 term2). Qed.
Lemma lem3162124 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162125 : term160 = term161.
Proof. exact (@lem3162124 term2). Qed.
Lemma lem3162126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162127 : term460 = term461.
Proof. exact (MK_COMB (@lem3162126) (@lem3162125)). Qed.
Lemma lem3162128 : term462 = term463.
Proof. exact (MK_COMB (@lem3162127) (@lem3162122)). Qed.
Lemma lem3162129 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3162131 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162132 : term188 = term189.
Proof. exact (@lem3162131 (NUMERAL 0) term2). Qed.
Lemma lem3162133 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162134 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162135 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162134 h1) (fun h1 : term189 = True => @lem3162133)). Qed.
Lemma lem3162136 : term189 = True.
Proof. exact (EQ_MP (@lem3162135) (@lem3162133)). Qed.
Lemma lem3162137 : term188 = True.
Proof. exact (TRANS (@lem3162132) (@lem3162136)). Qed.
Lemma lem3162138 : True = term188.
Proof. exact (SYM (@lem3162137)). Qed.
Lemma lem3162139 : term188.
Proof. exact (EQ_MP (@lem3162138) (@lem0)). Qed.
Lemma lem3162140 : term465.
Proof. exact (@lem3162129 (@lem3162139)). Qed.
Lemma lem3162142 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162143 : term188 = term189.
Proof. exact (@lem3162142 (NUMERAL 0) term2). Qed.
Lemma lem3162144 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162145 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162146 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162145 h1) (fun h1 : term189 = True => @lem3162144)). Qed.
Lemma lem3162147 : term189 = True.
Proof. exact (EQ_MP (@lem3162146) (@lem3162144)). Qed.
Lemma lem3162148 : term188 = True.
Proof. exact (TRANS (@lem3162143) (@lem3162147)). Qed.
Lemma lem3162149 : True = term188.
Proof. exact (SYM (@lem3162148)). Qed.
Lemma lem3162150 : term188.
Proof. exact (EQ_MP (@lem3162149) (@lem0)). Qed.
Lemma lem3162151 : term466.
Proof. exact (@lem3162140 (@lem3162150)). Qed.
Lemma lem3162153 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162154 : term188 = term189.
Proof. exact (@lem3162153 (NUMERAL 0) term2). Qed.
Lemma lem3162155 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162156 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162157 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162156 h1) (fun h1 : term189 = True => @lem3162155)). Qed.
Lemma lem3162158 : term189 = True.
Proof. exact (EQ_MP (@lem3162157) (@lem3162155)). Qed.
Lemma lem3162159 : term188 = True.
Proof. exact (TRANS (@lem3162154) (@lem3162158)). Qed.
Lemma lem3162160 : True = term188.
Proof. exact (SYM (@lem3162159)). Qed.
Lemma lem3162161 : term188.
Proof. exact (EQ_MP (@lem3162160) (@lem0)). Qed.
Lemma lem3162162 : term467.
Proof. exact (@lem3162151 (@lem3162161)). Qed.
Lemma lem3162164 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162165 : term169 = term170.
Proof. exact (@lem3162164 term2 term2). Qed.
Lemma lem3162166 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162167 : term172 = term2.
Proof. exact (EQ_MP (@lem3162166) (@lem940073)). Qed.
Lemma lem3162168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162169 : term170 = term93.
Proof. exact (MK_COMB (@lem3162168) (@lem3162167)). Qed.
Lemma lem3162170 : term169 = term93.
Proof. exact (TRANS (@lem3162165) (@lem3162169)). Qed.
Lemma lem3162172 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162173 : term236 = term239.
Proof. exact (@lem3162172 term2 term2). Qed.
Lemma lem3162174 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162175 : term172 = term2.
Proof. exact (EQ_MP (@lem3162174) (@lem940073)). Qed.
Lemma lem3162176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162177 : term170 = term93.
Proof. exact (MK_COMB (@lem3162176) (@lem3162175)). Qed.
Lemma lem3162178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162179 : term239 = term160.
Proof. exact (MK_COMB (@lem3162178) (@lem3162177)). Qed.
Lemma lem3162180 : term236 = term160.
Proof. exact (TRANS (@lem3162173) (@lem3162179)). Qed.
Lemma lem3162181 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162182 : term468 = term460.
Proof. exact (MK_COMB (@lem3162181) (@lem3162180)). Qed.
Lemma lem3162183 : term469 = term462.
Proof. exact (MK_COMB (@lem3162182) (@lem3162170)). Qed.
Lemma lem3162185 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3162186 : term462 = term79.
Proof. exact (@lem3162185 term2). Qed.
Lemma lem3162187 : term469 = term79.
Proof. exact (TRANS (@lem3162183) (@lem3162186)). Qed.
Lemma lem3162188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162189 : term471 = term273.
Proof. exact (MK_COMB (@lem3162188) (@lem3162187)). Qed.
Lemma lem3162190 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3162191 : term472 = term275.
Proof. exact (MK_COMB (@lem3162189) (@lem3162190)). Qed.
Lemma lem3162193 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162194 : term275 = term79.
Proof. exact (@lem3162193 term2). Qed.
Lemma lem3162195 : term472 = term79.
Proof. exact (TRANS (@lem3162191) (@lem3162194)). Qed.
Lemma lem3162197 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162198 : term169 = term170.
Proof. exact (@lem3162197 term2 term2). Qed.
Lemma lem3162199 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162200 : term172 = term2.
Proof. exact (EQ_MP (@lem3162199) (@lem940073)). Qed.
Lemma lem3162201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162202 : term170 = term93.
Proof. exact (MK_COMB (@lem3162201) (@lem3162200)). Qed.
Lemma lem3162203 : term169 = term93.
Proof. exact (TRANS (@lem3162198) (@lem3162202)). Qed.
Lemma lem3162204 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3162205 : term277 = term275.
Proof. exact (MK_COMB (@lem3162204) (@lem3162203)). Qed.
Lemma lem3162207 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162208 : term275 = term79.
Proof. exact (@lem3162207 term2). Qed.
Lemma lem3162209 : term277 = term79.
Proof. exact (TRANS (@lem3162205) (@lem3162208)). Qed.
Lemma lem3162210 : term79 = term277.
Proof. exact (SYM (@lem3162209)). Qed.
Lemma lem3162211 : term472 = term277.
Proof. exact (TRANS (@lem3162195) (@lem3162210)). Qed.
Lemma lem3162212 : term463 = term157.
Proof. exact (@lem3162162 (@lem3162211)). Qed.
Lemma lem3162213 : term462 = term157.
Proof. exact (TRANS (@lem3162128) (@lem3162212)). Qed.
Lemma lem3162215 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3162216 : term157 = term79.
Proof. exact (@lem3162215 term79). Qed.
Lemma lem3162217 : term462 = term79.
Proof. exact (TRANS (@lem3162213) (@lem3162216)). Qed.
Lemma lem3162218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162219 : term473 = term273.
Proof. exact (MK_COMB (@lem3162218) (@lem3162217)). Qed.
Lemma lem3162220 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3162221 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3162219) (@lem3162220 _32603)). Qed.
Lemma lem3162222 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3162119 _32603) (@lem3162221 _32603)). Qed.
Lemma lem3162223 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3162224 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3162222 _32603) (@lem3162223 _32603)). Qed.
Lemma lem3162225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162226 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3162225) (@lem3162224 _32603)). Qed.
Lemma lem3162227 : term223 = term223.
Proof. exact (eq_refl term223). Qed.
Lemma lem3162228 (_32603 : int) : (term550 _32603) = term551.
Proof. exact (MK_COMB (@lem3162226 _32603) (@lem3162227)). Qed.
Lemma lem3162229 (_32603 : int) : (term549 _32603) = term551.
Proof. exact (TRANS (@lem3162118 _32603) (@lem3162228 _32603)). Qed.
Lemma lem3162230 : term551 = term223.
Proof. exact (@lem1982721 term223). Qed.
Lemma lem3162231 (_32603 : int) : (term549 _32603) = term223.
Proof. exact (TRANS (@lem3162229 _32603) (@lem3162230)). Qed.
Lemma lem3162232 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3162233 (_32603 : int) : (term552 _32603) = term553.
Proof. exact (MK_COMB (@lem3162232) (@lem3162231 _32603)). Qed.
Lemma lem3162234 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162235 (_32603 : int) : (term548 _32603) = term554.
Proof. exact (MK_COMB (@lem3162233 _32603) (@lem3162234)). Qed.
Lemma lem3162236 (_32603 : int) (h1 : term576 _32603) : term554.
Proof. exact (EQ_MP (@lem3162235 _32603) (@lem3162117 _32603 h1)). Qed.
Lemma lem3162238 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3162239 : term554 = term555.
Proof. exact (@lem3162238 term79 term223). Qed.
Lemma lem3162241 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162242 : term223 = term226.
Proof. exact (@lem3162241 term200). Qed.
Lemma lem3162244 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162245 : term79 = term157.
Proof. exact (@lem3162244 (NUMERAL 0)). Qed.
Lemma lem3162246 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3162247 : term81 = term495.
Proof. exact (MK_COMB (@lem3162246) (@lem3162245)). Qed.
Lemma lem3162248 : term555 = term556.
Proof. exact (MK_COMB (@lem3162247) (@lem3162242)). Qed.
Lemma lem3162249 : term557.
Proof. exact (@lem1980026 term79 term93 term223 term93). Qed.
Lemma lem3162251 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162252 : term188 = term189.
Proof. exact (@lem3162251 (NUMERAL 0) term2). Qed.
Lemma lem3162253 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162254 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162255 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162254 h1) (fun h1 : term189 = True => @lem3162253)). Qed.
Lemma lem3162256 : term189 = True.
Proof. exact (EQ_MP (@lem3162255) (@lem3162253)). Qed.
Lemma lem3162257 : term188 = True.
Proof. exact (TRANS (@lem3162252) (@lem3162256)). Qed.
Lemma lem3162258 : True = term188.
Proof. exact (SYM (@lem3162257)). Qed.
Lemma lem3162259 : term188.
Proof. exact (EQ_MP (@lem3162258) (@lem0)). Qed.
Lemma lem3162260 : term558.
Proof. exact (@lem3162249 (@lem3162259)). Qed.
Lemma lem3162262 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162263 : term188 = term189.
Proof. exact (@lem3162262 (NUMERAL 0) term2). Qed.
Lemma lem3162264 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162265 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162266 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162265 h1) (fun h1 : term189 = True => @lem3162264)). Qed.
Lemma lem3162267 : term189 = True.
Proof. exact (EQ_MP (@lem3162266) (@lem3162264)). Qed.
Lemma lem3162268 : term188 = True.
Proof. exact (TRANS (@lem3162263) (@lem3162267)). Qed.
Lemma lem3162269 : True = term188.
Proof. exact (SYM (@lem3162268)). Qed.
Lemma lem3162270 : term188.
Proof. exact (EQ_MP (@lem3162269) (@lem0)). Qed.
Lemma lem3162271 : term556 = term559.
Proof. exact (@lem3162260 (@lem3162270)). Qed.
Lemma lem3162273 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162274 : term482 = term483.
Proof. exact (@lem3162273 term200 term2). Qed.
Lemma lem3162275 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3162276 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3162277 : term207 = term200.
Proof. exact (EQ_MP (@lem3162276) (@lem3162275)). Qed.
Lemma lem3162278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162279 : term205 = term186.
Proof. exact (MK_COMB (@lem3162278) (@lem3162277)). Qed.
Lemma lem3162280 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162281 : term483 = term223.
Proof. exact (MK_COMB (@lem3162280) (@lem3162279)). Qed.
Lemma lem3162282 : term482 = term223.
Proof. exact (TRANS (@lem3162274) (@lem3162281)). Qed.
Lemma lem3162284 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162285 : term275 = term79.
Proof. exact (@lem3162284 term2). Qed.
Lemma lem3162286 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3162287 : term500 = term81.
Proof. exact (MK_COMB (@lem3162286) (@lem3162285)). Qed.
Lemma lem3162288 : term559 = term555.
Proof. exact (MK_COMB (@lem3162287) (@lem3162282)). Qed.
Lemma lem3162290 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3162291 : term555 = term560.
Proof. exact (@lem3162290 (NUMERAL 0) term200). Qed.
Lemma lem3162292 : term561 = term198.
Proof. exact (@lem912803). Qed.
Lemma lem3162293 (h1 : term561 = term198) : (term200 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term198 h1). Qed.
Lemma lem3162294 : (term561 = term198) = ((term200 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term561 = term198 => @lem3162293 h1) (fun h1 : (term200 = (NUMERAL 0)) = False => @lem3162292)). Qed.
Lemma lem3162295 : (term200 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3162294) (@lem3162292)). Qed.
Lemma lem3162296 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3162297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3162298 : term504 = (and True).
Proof. exact (MK_COMB (@lem3162297) (@lem3162296)). Qed.
Lemma lem3162299 : term560 = (True /\ False).
Proof. exact (MK_COMB (@lem3162298) (@lem3162295)). Qed.
Lemma lem3162301 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3162302 : term560 = False.
Proof. exact (TRANS (@lem3162299) (@lem3162301)). Qed.
Lemma lem3162303 : term555 = False.
Proof. exact (TRANS (@lem3162291) (@lem3162302)). Qed.
Lemma lem3162304 : term559 = False.
Proof. exact (TRANS (@lem3162288) (@lem3162303)). Qed.
Lemma lem3162305 : term556 = False.
Proof. exact (TRANS (@lem3162271) (@lem3162304)). Qed.
Lemma lem3162306 : term555 = False.
Proof. exact (TRANS (@lem3162248) (@lem3162305)). Qed.
Lemma lem3162307 : term554 = False.
Proof. exact (TRANS (@lem3162239) (@lem3162306)). Qed.
Lemma lem3162308 (_32603 : int) (h1 : term576 _32603) : False.
Proof. exact (EQ_MP (@lem3162307) (@lem3162236 _32603 h1)). Qed.
Lemma lem3162309 (_32603 : int) (h1 : term577 _32603) : term577 _32603.
Proof. exact (h1). Qed.
Lemma lem3162310 (_32603 : int) (h1 : term577 _32603) : term398 _32603.
Proof. exact (proj2 (@lem3162309 _32603 h1)). Qed.
Lemma lem3162312 (_32603 : int) (h1 : term577 _32603) : (real_of_int _32603) = term79.
Proof. exact (proj2 (@lem3162310 _32603 h1)). Qed.
Lemma lem3162313 (_32603 : int) (h1 : term577 _32603) : term326 _32603.
Proof. exact (proj1 (@lem3162310 _32603 h1)). Qed.
Lemma lem3162314 (_32603 : int) (h1 : term577 _32603) : term230 _32603.
Proof. exact (proj2 (@lem3162313 _32603 h1)). Qed.
Lemma lem3162317 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3162318 : term433 = term188.
Proof. exact (@lem3162317 term79 term93). Qed.
Lemma lem3162320 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162321 : term93 = term182.
Proof. exact (@lem3162320 term2). Qed.
Lemma lem3162323 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162324 : term79 = term157.
Proof. exact (@lem3162323 (NUMERAL 0)). Qed.
Lemma lem3162325 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3162326 : term434 = term435.
Proof. exact (MK_COMB (@lem3162325) (@lem3162324)). Qed.
Lemma lem3162327 : term188 = term436.
Proof. exact (MK_COMB (@lem3162326) (@lem3162321)). Qed.
Lemma lem3162328 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3162330 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162331 : term188 = term189.
Proof. exact (@lem3162330 (NUMERAL 0) term2). Qed.
Lemma lem3162332 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162333 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162334 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162333 h1) (fun h1 : term189 = True => @lem3162332)). Qed.
Lemma lem3162335 : term189 = True.
Proof. exact (EQ_MP (@lem3162334) (@lem3162332)). Qed.
Lemma lem3162336 : term188 = True.
Proof. exact (TRANS (@lem3162331) (@lem3162335)). Qed.
Lemma lem3162337 : True = term188.
Proof. exact (SYM (@lem3162336)). Qed.
Lemma lem3162338 : term188.
Proof. exact (EQ_MP (@lem3162337) (@lem0)). Qed.
Lemma lem3162339 : term438.
Proof. exact (@lem3162328 (@lem3162338)). Qed.
Lemma lem3162341 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162342 : term188 = term189.
Proof. exact (@lem3162341 (NUMERAL 0) term2). Qed.
Lemma lem3162343 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162344 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162345 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162344 h1) (fun h1 : term189 = True => @lem3162343)). Qed.
Lemma lem3162346 : term189 = True.
Proof. exact (EQ_MP (@lem3162345) (@lem3162343)). Qed.
Lemma lem3162347 : term188 = True.
Proof. exact (TRANS (@lem3162342) (@lem3162346)). Qed.
Lemma lem3162348 : True = term188.
Proof. exact (SYM (@lem3162347)). Qed.
Lemma lem3162349 : term188.
Proof. exact (EQ_MP (@lem3162348) (@lem0)). Qed.
Lemma lem3162350 : term436 = term439.
Proof. exact (@lem3162339 (@lem3162349)). Qed.
Lemma lem3162352 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162353 : term169 = term170.
Proof. exact (@lem3162352 term2 term2). Qed.
Lemma lem3162354 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162355 : term172 = term2.
Proof. exact (EQ_MP (@lem3162354) (@lem940073)). Qed.
Lemma lem3162356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162357 : term170 = term93.
Proof. exact (MK_COMB (@lem3162356) (@lem3162355)). Qed.
Lemma lem3162358 : term169 = term93.
Proof. exact (TRANS (@lem3162353) (@lem3162357)). Qed.
Lemma lem3162360 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162361 : term275 = term79.
Proof. exact (@lem3162360 term2). Qed.
Lemma lem3162362 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3162363 : term440 = term434.
Proof. exact (MK_COMB (@lem3162362) (@lem3162361)). Qed.
Lemma lem3162364 : term439 = term188.
Proof. exact (MK_COMB (@lem3162363) (@lem3162358)). Qed.
Lemma lem3162366 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162367 : term188 = term189.
Proof. exact (@lem3162366 (NUMERAL 0) term2). Qed.
Lemma lem3162368 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162369 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162370 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162369 h1) (fun h1 : term189 = True => @lem3162368)). Qed.
Lemma lem3162371 : term189 = True.
Proof. exact (EQ_MP (@lem3162370) (@lem3162368)). Qed.
Lemma lem3162372 : term188 = True.
Proof. exact (TRANS (@lem3162367) (@lem3162371)). Qed.
Lemma lem3162373 : term439 = True.
Proof. exact (TRANS (@lem3162364) (@lem3162372)). Qed.
Lemma lem3162374 : term436 = True.
Proof. exact (TRANS (@lem3162350) (@lem3162373)). Qed.
Lemma lem3162375 : term188 = True.
Proof. exact (TRANS (@lem3162327) (@lem3162374)). Qed.
Lemma lem3162376 : term433 = True.
Proof. exact (TRANS (@lem3162318) (@lem3162375)). Qed.
Lemma lem3162377 : True = term433.
Proof. exact (SYM (@lem3162376)). Qed.
Lemma lem3162378 : term433.
Proof. exact (EQ_MP (@lem3162377) (@lem0)). Qed.
Lemma lem3162379 (_32603 : int) (h1 : term577 _32603) : term441 _32603.
Proof. exact (conj (@lem3162378) (@lem3162314 _32603 h1)). Qed.
Lemma lem3162381 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3162382 (_32603 : int) : term443 _32603.
Proof. exact (@lem3162381 term93 (term227 _32603)). Qed.
Lemma lem3162383 (_32603 : int) (h1 : term577 _32603) : term444 _32603.
Proof. exact (@lem3162382 _32603 (@lem3162379 _32603 h1)). Qed.
Lemma lem3162384 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3162385 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3162386 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3162385) (@lem3162384 _32603)). Qed.
Lemma lem3162387 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162388 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3162386 _32603) (@lem3162387)). Qed.
Lemma lem3162389 (_32603 : int) (h1 : term577 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3162388 _32603) (@lem3162383 _32603 h1)). Qed.
Lemma lem3162391 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3162392 (_32603 : int) : term542 _32603.
Proof. exact (@lem3162391 (real_of_int _32603)). Qed.
Lemma lem3162393 (_32603 : int) (h1 : term577 _32603) : term543 _32603.
Proof. exact (@lem3162392 _32603 (@lem3162312 _32603 h1)). Qed.
Lemma lem3162394 (_32603 : int) (h1 : term577 _32603) : term544 _32603.
Proof. exact (@lem3162393 _32603 h1 term160). Qed.
Lemma lem3162395 (_32603 : int) : (term544 _32603) = ((term263 _32603) = term79).
Proof. exact (eq_refl (term544 _32603)). Qed.
Lemma lem3162402 (_32603 : int) (h1 : term577 _32603) : (term263 _32603) = term79.
Proof. exact (EQ_MP (@lem3162395 _32603) (@lem3162394 _32603 h1)). Qed.
Lemma lem3162403 (_32603 : int) (h1 : term577 _32603) : term545 _32603.
Proof. exact (conj (@lem3162402 _32603 h1) (@lem3162389 _32603 h1)). Qed.
Lemma lem3162405 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3162406 (_32603 : int) : term547 _32603.
Proof. exact (@lem3162405 (term263 _32603) (term227 _32603)). Qed.
Lemma lem3162407 (_32603 : int) (h1 : term577 _32603) : term548 _32603.
Proof. exact (@lem3162406 _32603 (@lem3162403 _32603 h1)). Qed.
Lemma lem3162408 (_32603 : int) : (term549 _32603) = (term550 _32603).
Proof. exact (@lem1982763 (term263 _32603) (real_of_int _32603) term223). Qed.
Lemma lem3162409 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3162411 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162412 : term93 = term182.
Proof. exact (@lem3162411 term2). Qed.
Lemma lem3162414 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162415 : term160 = term161.
Proof. exact (@lem3162414 term2). Qed.
Lemma lem3162416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162417 : term460 = term461.
Proof. exact (MK_COMB (@lem3162416) (@lem3162415)). Qed.
Lemma lem3162418 : term462 = term463.
Proof. exact (MK_COMB (@lem3162417) (@lem3162412)). Qed.
Lemma lem3162419 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3162421 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162422 : term188 = term189.
Proof. exact (@lem3162421 (NUMERAL 0) term2). Qed.
Lemma lem3162423 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162424 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162425 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162424 h1) (fun h1 : term189 = True => @lem3162423)). Qed.
Lemma lem3162426 : term189 = True.
Proof. exact (EQ_MP (@lem3162425) (@lem3162423)). Qed.
Lemma lem3162427 : term188 = True.
Proof. exact (TRANS (@lem3162422) (@lem3162426)). Qed.
Lemma lem3162428 : True = term188.
Proof. exact (SYM (@lem3162427)). Qed.
Lemma lem3162429 : term188.
Proof. exact (EQ_MP (@lem3162428) (@lem0)). Qed.
Lemma lem3162430 : term465.
Proof. exact (@lem3162419 (@lem3162429)). Qed.
Lemma lem3162432 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162433 : term188 = term189.
Proof. exact (@lem3162432 (NUMERAL 0) term2). Qed.
Lemma lem3162434 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162435 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162436 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162435 h1) (fun h1 : term189 = True => @lem3162434)). Qed.
Lemma lem3162437 : term189 = True.
Proof. exact (EQ_MP (@lem3162436) (@lem3162434)). Qed.
Lemma lem3162438 : term188 = True.
Proof. exact (TRANS (@lem3162433) (@lem3162437)). Qed.
Lemma lem3162439 : True = term188.
Proof. exact (SYM (@lem3162438)). Qed.
Lemma lem3162440 : term188.
Proof. exact (EQ_MP (@lem3162439) (@lem0)). Qed.
Lemma lem3162441 : term466.
Proof. exact (@lem3162430 (@lem3162440)). Qed.
Lemma lem3162443 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162444 : term188 = term189.
Proof. exact (@lem3162443 (NUMERAL 0) term2). Qed.
Lemma lem3162445 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162446 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162447 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162446 h1) (fun h1 : term189 = True => @lem3162445)). Qed.
Lemma lem3162448 : term189 = True.
Proof. exact (EQ_MP (@lem3162447) (@lem3162445)). Qed.
Lemma lem3162449 : term188 = True.
Proof. exact (TRANS (@lem3162444) (@lem3162448)). Qed.
Lemma lem3162450 : True = term188.
Proof. exact (SYM (@lem3162449)). Qed.
Lemma lem3162451 : term188.
Proof. exact (EQ_MP (@lem3162450) (@lem0)). Qed.
Lemma lem3162452 : term467.
Proof. exact (@lem3162441 (@lem3162451)). Qed.
Lemma lem3162454 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162455 : term169 = term170.
Proof. exact (@lem3162454 term2 term2). Qed.
Lemma lem3162456 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162457 : term172 = term2.
Proof. exact (EQ_MP (@lem3162456) (@lem940073)). Qed.
Lemma lem3162458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162459 : term170 = term93.
Proof. exact (MK_COMB (@lem3162458) (@lem3162457)). Qed.
Lemma lem3162460 : term169 = term93.
Proof. exact (TRANS (@lem3162455) (@lem3162459)). Qed.
Lemma lem3162462 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162463 : term236 = term239.
Proof. exact (@lem3162462 term2 term2). Qed.
Lemma lem3162464 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162465 : term172 = term2.
Proof. exact (EQ_MP (@lem3162464) (@lem940073)). Qed.
Lemma lem3162466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162467 : term170 = term93.
Proof. exact (MK_COMB (@lem3162466) (@lem3162465)). Qed.
Lemma lem3162468 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162469 : term239 = term160.
Proof. exact (MK_COMB (@lem3162468) (@lem3162467)). Qed.
Lemma lem3162470 : term236 = term160.
Proof. exact (TRANS (@lem3162463) (@lem3162469)). Qed.
Lemma lem3162471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162472 : term468 = term460.
Proof. exact (MK_COMB (@lem3162471) (@lem3162470)). Qed.
Lemma lem3162473 : term469 = term462.
Proof. exact (MK_COMB (@lem3162472) (@lem3162460)). Qed.
Lemma lem3162475 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3162476 : term462 = term79.
Proof. exact (@lem3162475 term2). Qed.
Lemma lem3162477 : term469 = term79.
Proof. exact (TRANS (@lem3162473) (@lem3162476)). Qed.
Lemma lem3162478 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162479 : term471 = term273.
Proof. exact (MK_COMB (@lem3162478) (@lem3162477)). Qed.
Lemma lem3162480 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3162481 : term472 = term275.
Proof. exact (MK_COMB (@lem3162479) (@lem3162480)). Qed.
Lemma lem3162483 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162484 : term275 = term79.
Proof. exact (@lem3162483 term2). Qed.
Lemma lem3162485 : term472 = term79.
Proof. exact (TRANS (@lem3162481) (@lem3162484)). Qed.
Lemma lem3162487 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162488 : term169 = term170.
Proof. exact (@lem3162487 term2 term2). Qed.
Lemma lem3162489 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162490 : term172 = term2.
Proof. exact (EQ_MP (@lem3162489) (@lem940073)). Qed.
Lemma lem3162491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162492 : term170 = term93.
Proof. exact (MK_COMB (@lem3162491) (@lem3162490)). Qed.
Lemma lem3162493 : term169 = term93.
Proof. exact (TRANS (@lem3162488) (@lem3162492)). Qed.
Lemma lem3162494 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3162495 : term277 = term275.
Proof. exact (MK_COMB (@lem3162494) (@lem3162493)). Qed.
Lemma lem3162497 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162498 : term275 = term79.
Proof. exact (@lem3162497 term2). Qed.
Lemma lem3162499 : term277 = term79.
Proof. exact (TRANS (@lem3162495) (@lem3162498)). Qed.
Lemma lem3162500 : term79 = term277.
Proof. exact (SYM (@lem3162499)). Qed.
Lemma lem3162501 : term472 = term277.
Proof. exact (TRANS (@lem3162485) (@lem3162500)). Qed.
Lemma lem3162502 : term463 = term157.
Proof. exact (@lem3162452 (@lem3162501)). Qed.
Lemma lem3162503 : term462 = term157.
Proof. exact (TRANS (@lem3162418) (@lem3162502)). Qed.
Lemma lem3162505 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3162506 : term157 = term79.
Proof. exact (@lem3162505 term79). Qed.
Lemma lem3162507 : term462 = term79.
Proof. exact (TRANS (@lem3162503) (@lem3162506)). Qed.
Lemma lem3162508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162509 : term473 = term273.
Proof. exact (MK_COMB (@lem3162508) (@lem3162507)). Qed.
Lemma lem3162510 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3162511 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3162509) (@lem3162510 _32603)). Qed.
Lemma lem3162512 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3162409 _32603) (@lem3162511 _32603)). Qed.
Lemma lem3162513 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3162514 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3162512 _32603) (@lem3162513 _32603)). Qed.
Lemma lem3162515 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162516 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3162515) (@lem3162514 _32603)). Qed.
Lemma lem3162517 : term223 = term223.
Proof. exact (eq_refl term223). Qed.
Lemma lem3162518 (_32603 : int) : (term550 _32603) = term551.
Proof. exact (MK_COMB (@lem3162516 _32603) (@lem3162517)). Qed.
Lemma lem3162519 (_32603 : int) : (term549 _32603) = term551.
Proof. exact (TRANS (@lem3162408 _32603) (@lem3162518 _32603)). Qed.
Lemma lem3162520 : term551 = term223.
Proof. exact (@lem1982721 term223). Qed.
Lemma lem3162521 (_32603 : int) : (term549 _32603) = term223.
Proof. exact (TRANS (@lem3162519 _32603) (@lem3162520)). Qed.
Lemma lem3162522 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3162523 (_32603 : int) : (term552 _32603) = term553.
Proof. exact (MK_COMB (@lem3162522) (@lem3162521 _32603)). Qed.
Lemma lem3162524 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162525 (_32603 : int) : (term548 _32603) = term554.
Proof. exact (MK_COMB (@lem3162523 _32603) (@lem3162524)). Qed.
Lemma lem3162526 (_32603 : int) (h1 : term577 _32603) : term554.
Proof. exact (EQ_MP (@lem3162525 _32603) (@lem3162407 _32603 h1)). Qed.
Lemma lem3162528 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3162529 : term554 = term555.
Proof. exact (@lem3162528 term79 term223). Qed.
Lemma lem3162531 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162532 : term223 = term226.
Proof. exact (@lem3162531 term200). Qed.
Lemma lem3162534 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162535 : term79 = term157.
Proof. exact (@lem3162534 (NUMERAL 0)). Qed.
Lemma lem3162536 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3162537 : term81 = term495.
Proof. exact (MK_COMB (@lem3162536) (@lem3162535)). Qed.
Lemma lem3162538 : term555 = term556.
Proof. exact (MK_COMB (@lem3162537) (@lem3162532)). Qed.
Lemma lem3162539 : term557.
Proof. exact (@lem1980026 term79 term93 term223 term93). Qed.
Lemma lem3162541 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162542 : term188 = term189.
Proof. exact (@lem3162541 (NUMERAL 0) term2). Qed.
Lemma lem3162543 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162544 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162545 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162544 h1) (fun h1 : term189 = True => @lem3162543)). Qed.
Lemma lem3162546 : term189 = True.
Proof. exact (EQ_MP (@lem3162545) (@lem3162543)). Qed.
Lemma lem3162547 : term188 = True.
Proof. exact (TRANS (@lem3162542) (@lem3162546)). Qed.
Lemma lem3162548 : True = term188.
Proof. exact (SYM (@lem3162547)). Qed.
Lemma lem3162549 : term188.
Proof. exact (EQ_MP (@lem3162548) (@lem0)). Qed.
Lemma lem3162550 : term558.
Proof. exact (@lem3162539 (@lem3162549)). Qed.
Lemma lem3162552 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162553 : term188 = term189.
Proof. exact (@lem3162552 (NUMERAL 0) term2). Qed.
Lemma lem3162554 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162555 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162556 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162555 h1) (fun h1 : term189 = True => @lem3162554)). Qed.
Lemma lem3162557 : term189 = True.
Proof. exact (EQ_MP (@lem3162556) (@lem3162554)). Qed.
Lemma lem3162558 : term188 = True.
Proof. exact (TRANS (@lem3162553) (@lem3162557)). Qed.
Lemma lem3162559 : True = term188.
Proof. exact (SYM (@lem3162558)). Qed.
Lemma lem3162560 : term188.
Proof. exact (EQ_MP (@lem3162559) (@lem0)). Qed.
Lemma lem3162561 : term556 = term559.
Proof. exact (@lem3162550 (@lem3162560)). Qed.
Lemma lem3162563 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162564 : term482 = term483.
Proof. exact (@lem3162563 term200 term2). Qed.
Lemma lem3162565 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3162566 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3162567 : term207 = term200.
Proof. exact (EQ_MP (@lem3162566) (@lem3162565)). Qed.
Lemma lem3162568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162569 : term205 = term186.
Proof. exact (MK_COMB (@lem3162568) (@lem3162567)). Qed.
Lemma lem3162570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162571 : term483 = term223.
Proof. exact (MK_COMB (@lem3162570) (@lem3162569)). Qed.
Lemma lem3162572 : term482 = term223.
Proof. exact (TRANS (@lem3162564) (@lem3162571)). Qed.
Lemma lem3162574 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162575 : term275 = term79.
Proof. exact (@lem3162574 term2). Qed.
Lemma lem3162576 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3162577 : term500 = term81.
Proof. exact (MK_COMB (@lem3162576) (@lem3162575)). Qed.
Lemma lem3162578 : term559 = term555.
Proof. exact (MK_COMB (@lem3162577) (@lem3162572)). Qed.
Lemma lem3162580 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3162581 : term555 = term560.
Proof. exact (@lem3162580 (NUMERAL 0) term200). Qed.
Lemma lem3162582 : term561 = term198.
Proof. exact (@lem912803). Qed.
Lemma lem3162583 (h1 : term561 = term198) : (term200 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term198 h1). Qed.
Lemma lem3162584 : (term561 = term198) = ((term200 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term561 = term198 => @lem3162583 h1) (fun h1 : (term200 = (NUMERAL 0)) = False => @lem3162582)). Qed.
Lemma lem3162585 : (term200 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3162584) (@lem3162582)). Qed.
Lemma lem3162586 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3162587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3162588 : term504 = (and True).
Proof. exact (MK_COMB (@lem3162587) (@lem3162586)). Qed.
Lemma lem3162589 : term560 = (True /\ False).
Proof. exact (MK_COMB (@lem3162588) (@lem3162585)). Qed.
Lemma lem3162591 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3162592 : term560 = False.
Proof. exact (TRANS (@lem3162589) (@lem3162591)). Qed.
Lemma lem3162593 : term555 = False.
Proof. exact (TRANS (@lem3162581) (@lem3162592)). Qed.
Lemma lem3162594 : term559 = False.
Proof. exact (TRANS (@lem3162578) (@lem3162593)). Qed.
Lemma lem3162595 : term556 = False.
Proof. exact (TRANS (@lem3162561) (@lem3162594)). Qed.
Lemma lem3162596 : term555 = False.
Proof. exact (TRANS (@lem3162538) (@lem3162595)). Qed.
Lemma lem3162597 : term554 = False.
Proof. exact (TRANS (@lem3162529) (@lem3162596)). Qed.
Lemma lem3162598 (_32603 : int) (h1 : term577 _32603) : False.
Proof. exact (EQ_MP (@lem3162597) (@lem3162526 _32603 h1)). Qed.
Lemma lem3162599 (_32603 : int) (h1 : term396 _32603) : False.
Proof. exact (or_elim (@lem3162018 _32603 h1) (fun h0 : term576 _32603 => @lem3162308 _32603 h0) (fun h0 : term577 _32603 => @lem3162598 _32603 h0)). Qed.
Lemma lem3162600 (_32603 : int) (h1 : term405 _32603) : False.
Proof. exact (or_elim (@lem3161437 _32603 h1) (fun h0 : term400 _32603 => @lem3162017 _32603 h0) (fun h0 : term396 _32603 => @lem3162599 _32603 h0)). Qed.
Lemma lem3162601 (_32603 : int) (h1 : term407 _32603) : False.
Proof. exact (or_elim (@lem3161148 _32603 h1) (fun h0 : term540 _32603 => @lem3161436 _32603 h0) (fun h0 : term405 _32603 => @lem3162600 _32603 h0)). Qed.
Lemma lem3162602 (_32603 : int) (h1 : term389 _32603) : term389 _32603.
Proof. exact (h1). Qed.
Lemma lem3162603 (_32603 : int) (h1 : term578 _32603) : term578 _32603.
Proof. exact (h1). Qed.
Lemma lem3162604 (_32603 : int) (h1 : term578 _32603) : term374 _32603.
Proof. exact (proj2 (@lem3162603 _32603 h1)). Qed.
Lemma lem3162606 (_32603 : int) (h1 : term578 _32603) : (term252 _32603) = term79.
Proof. exact (proj2 (@lem3162604 _32603 h1)). Qed.
Lemma lem3162607 (_32603 : int) (h1 : term578 _32603) : term230 _32603.
Proof. exact (proj1 (@lem3162604 _32603 h1)). Qed.
Lemma lem3162609 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3162610 : term433 = term188.
Proof. exact (@lem3162609 term79 term93). Qed.
Lemma lem3162612 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162613 : term93 = term182.
Proof. exact (@lem3162612 term2). Qed.
Lemma lem3162615 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162616 : term79 = term157.
Proof. exact (@lem3162615 (NUMERAL 0)). Qed.
Lemma lem3162617 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3162618 : term434 = term435.
Proof. exact (MK_COMB (@lem3162617) (@lem3162616)). Qed.
Lemma lem3162619 : term188 = term436.
Proof. exact (MK_COMB (@lem3162618) (@lem3162613)). Qed.
Lemma lem3162620 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3162622 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162623 : term188 = term189.
Proof. exact (@lem3162622 (NUMERAL 0) term2). Qed.
Lemma lem3162624 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162625 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162626 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162625 h1) (fun h1 : term189 = True => @lem3162624)). Qed.
Lemma lem3162627 : term189 = True.
Proof. exact (EQ_MP (@lem3162626) (@lem3162624)). Qed.
Lemma lem3162628 : term188 = True.
Proof. exact (TRANS (@lem3162623) (@lem3162627)). Qed.
Lemma lem3162629 : True = term188.
Proof. exact (SYM (@lem3162628)). Qed.
Lemma lem3162630 : term188.
Proof. exact (EQ_MP (@lem3162629) (@lem0)). Qed.
Lemma lem3162631 : term438.
Proof. exact (@lem3162620 (@lem3162630)). Qed.
Lemma lem3162633 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162634 : term188 = term189.
Proof. exact (@lem3162633 (NUMERAL 0) term2). Qed.
Lemma lem3162635 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162636 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162637 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162636 h1) (fun h1 : term189 = True => @lem3162635)). Qed.
Lemma lem3162638 : term189 = True.
Proof. exact (EQ_MP (@lem3162637) (@lem3162635)). Qed.
Lemma lem3162639 : term188 = True.
Proof. exact (TRANS (@lem3162634) (@lem3162638)). Qed.
Lemma lem3162640 : True = term188.
Proof. exact (SYM (@lem3162639)). Qed.
Lemma lem3162641 : term188.
Proof. exact (EQ_MP (@lem3162640) (@lem0)). Qed.
Lemma lem3162642 : term436 = term439.
Proof. exact (@lem3162631 (@lem3162641)). Qed.
Lemma lem3162644 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162645 : term169 = term170.
Proof. exact (@lem3162644 term2 term2). Qed.
Lemma lem3162646 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162647 : term172 = term2.
Proof. exact (EQ_MP (@lem3162646) (@lem940073)). Qed.
Lemma lem3162648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162649 : term170 = term93.
Proof. exact (MK_COMB (@lem3162648) (@lem3162647)). Qed.
Lemma lem3162650 : term169 = term93.
Proof. exact (TRANS (@lem3162645) (@lem3162649)). Qed.
Lemma lem3162652 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162653 : term275 = term79.
Proof. exact (@lem3162652 term2). Qed.
Lemma lem3162654 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3162655 : term440 = term434.
Proof. exact (MK_COMB (@lem3162654) (@lem3162653)). Qed.
Lemma lem3162656 : term439 = term188.
Proof. exact (MK_COMB (@lem3162655) (@lem3162650)). Qed.
Lemma lem3162658 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162659 : term188 = term189.
Proof. exact (@lem3162658 (NUMERAL 0) term2). Qed.
Lemma lem3162660 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162661 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162662 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162661 h1) (fun h1 : term189 = True => @lem3162660)). Qed.
Lemma lem3162663 : term189 = True.
Proof. exact (EQ_MP (@lem3162662) (@lem3162660)). Qed.
Lemma lem3162664 : term188 = True.
Proof. exact (TRANS (@lem3162659) (@lem3162663)). Qed.
Lemma lem3162665 : term439 = True.
Proof. exact (TRANS (@lem3162656) (@lem3162664)). Qed.
Lemma lem3162666 : term436 = True.
Proof. exact (TRANS (@lem3162642) (@lem3162665)). Qed.
Lemma lem3162667 : term188 = True.
Proof. exact (TRANS (@lem3162619) (@lem3162666)). Qed.
Lemma lem3162668 : term433 = True.
Proof. exact (TRANS (@lem3162610) (@lem3162667)). Qed.
Lemma lem3162669 : True = term433.
Proof. exact (SYM (@lem3162668)). Qed.
Lemma lem3162670 : term433.
Proof. exact (EQ_MP (@lem3162669) (@lem0)). Qed.
Lemma lem3162671 (_32603 : int) (h1 : term578 _32603) : term441 _32603.
Proof. exact (conj (@lem3162670) (@lem3162607 _32603 h1)). Qed.
Lemma lem3162673 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3162674 (_32603 : int) : term443 _32603.
Proof. exact (@lem3162673 term93 (term227 _32603)). Qed.
Lemma lem3162675 (_32603 : int) (h1 : term578 _32603) : term444 _32603.
Proof. exact (@lem3162674 _32603 (@lem3162671 _32603 h1)). Qed.
Lemma lem3162676 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3162677 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3162678 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3162677) (@lem3162676 _32603)). Qed.
Lemma lem3162679 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162680 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3162678 _32603) (@lem3162679)). Qed.
Lemma lem3162681 (_32603 : int) (h1 : term578 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3162680 _32603) (@lem3162675 _32603 h1)). Qed.
Lemma lem3162683 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3162684 (_32603 : int) : term579 _32603.
Proof. exact (@lem3162683 (term252 _32603)). Qed.
Lemma lem3162685 (_32603 : int) (h1 : term578 _32603) : term580 _32603.
Proof. exact (@lem3162684 _32603 (@lem3162606 _32603 h1)). Qed.
Lemma lem3162686 (_32603 : int) (h1 : term578 _32603) : term581 _32603.
Proof. exact (@lem3162685 _32603 h1 term160). Qed.
Lemma lem3162687 (_32603 : int) : (term581 _32603) = ((term582 _32603) = term79).
Proof. exact (eq_refl (term581 _32603)). Qed.
Lemma lem3162688 (_32603 : int) (h1 : term578 _32603) : (term582 _32603) = term79.
Proof. exact (EQ_MP (@lem3162687 _32603) (@lem3162686 _32603 h1)). Qed.
Lemma lem3162689 (_32603 : int) : (term582 _32603) = (term583 _32603).
Proof. exact (@lem1982781 (real_of_int _32603) term160 term160). Qed.
Lemma lem3162691 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162692 : term160 = term161.
Proof. exact (@lem3162691 term2). Qed.
Lemma lem3162694 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162695 : term160 = term161.
Proof. exact (@lem3162694 term2). Qed.
Lemma lem3162696 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162697 : term162 = term163.
Proof. exact (MK_COMB (@lem3162696) (@lem3162695)). Qed.
Lemma lem3162698 : term584 = term585.
Proof. exact (MK_COMB (@lem3162697) (@lem3162692)). Qed.
Lemma lem3162699 : term585 = term586.
Proof. exact (@lem1981613 term160 term160 term93 term93). Qed.
Lemma lem3162701 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162702 : term169 = term170.
Proof. exact (@lem3162701 term2 term2). Qed.
Lemma lem3162703 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162704 : term172 = term2.
Proof. exact (EQ_MP (@lem3162703) (@lem940073)). Qed.
Lemma lem3162705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162706 : term170 = term93.
Proof. exact (MK_COMB (@lem3162705) (@lem3162704)). Qed.
Lemma lem3162707 : term169 = term93.
Proof. exact (TRANS (@lem3162702) (@lem3162706)). Qed.
Lemma lem3162709 (m : nat) (n : nat) : (term587 m n) = (term168 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3162710 : term584 = term170.
Proof. exact (@lem3162709 term2 term2). Qed.
Lemma lem3162711 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162712 : term172 = term2.
Proof. exact (EQ_MP (@lem3162711) (@lem940073)). Qed.
Lemma lem3162713 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162714 : term170 = term93.
Proof. exact (MK_COMB (@lem3162713) (@lem3162712)). Qed.
Lemma lem3162715 : term584 = term93.
Proof. exact (TRANS (@lem3162710) (@lem3162714)). Qed.
Lemma lem3162716 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3162717 : term588 = term589.
Proof. exact (MK_COMB (@lem3162716) (@lem3162715)). Qed.
Lemma lem3162718 : term586 = term182.
Proof. exact (MK_COMB (@lem3162717) (@lem3162707)). Qed.
Lemma lem3162719 : term585 = term182.
Proof. exact (TRANS (@lem3162699) (@lem3162718)). Qed.
Lemma lem3162720 : term584 = term182.
Proof. exact (TRANS (@lem3162698) (@lem3162719)). Qed.
Lemma lem3162722 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3162723 : term182 = term93.
Proof. exact (@lem3162722 term93). Qed.
Lemma lem3162724 : term584 = term93.
Proof. exact (TRANS (@lem3162720) (@lem3162723)). Qed.
Lemma lem3162727 (_32603 : int) : (term242 _32603) = (term242 _32603).
Proof. exact (eq_refl (term242 _32603)). Qed.
Lemma lem3162728 (_32603 : int) : (term583 _32603) = (term291 _32603).
Proof. exact (MK_COMB (@lem3162727 _32603) (@lem3162724)). Qed.
Lemma lem3162729 (_32603 : int) : (term582 _32603) = (term291 _32603).
Proof. exact (TRANS (@lem3162689 _32603) (@lem3162728 _32603)). Qed.
Lemma lem3162730 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3162731 (_32603 : int) : (term590 _32603) = (term591 _32603).
Proof. exact (MK_COMB (@lem3162730) (@lem3162729 _32603)). Qed.
Lemma lem3162732 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162733 (_32603 : int) : ((term582 _32603) = term79) = ((term291 _32603) = term79).
Proof. exact (MK_COMB (@lem3162731 _32603) (@lem3162732)). Qed.
Lemma lem3162734 (_32603 : int) (h1 : term578 _32603) : (term291 _32603) = term79.
Proof. exact (EQ_MP (@lem3162733 _32603) (@lem3162688 _32603 h1)). Qed.
Lemma lem3162735 (_32603 : int) (h1 : term578 _32603) : term592 _32603.
Proof. exact (conj (@lem3162734 _32603 h1) (@lem3162681 _32603 h1)). Qed.
Lemma lem3162737 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3162738 (_32603 : int) : term593 _32603.
Proof. exact (@lem3162737 (term291 _32603) (term227 _32603)). Qed.
Lemma lem3162739 (_32603 : int) (h1 : term578 _32603) : term455 _32603.
Proof. exact (@lem3162738 _32603 (@lem3162735 _32603 h1)). Qed.
Lemma lem3162740 (_32603 : int) : (term456 _32603) = (term457 _32603).
Proof. exact (@lem1982753 (term263 _32603) (real_of_int _32603) term93 term223). Qed.
Lemma lem3162741 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3162743 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162744 : term93 = term182.
Proof. exact (@lem3162743 term2). Qed.
Lemma lem3162746 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162747 : term160 = term161.
Proof. exact (@lem3162746 term2). Qed.
Lemma lem3162748 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162749 : term460 = term461.
Proof. exact (MK_COMB (@lem3162748) (@lem3162747)). Qed.
Lemma lem3162750 : term462 = term463.
Proof. exact (MK_COMB (@lem3162749) (@lem3162744)). Qed.
Lemma lem3162751 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3162753 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162754 : term188 = term189.
Proof. exact (@lem3162753 (NUMERAL 0) term2). Qed.
Lemma lem3162755 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162756 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162757 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162756 h1) (fun h1 : term189 = True => @lem3162755)). Qed.
Lemma lem3162758 : term189 = True.
Proof. exact (EQ_MP (@lem3162757) (@lem3162755)). Qed.
Lemma lem3162759 : term188 = True.
Proof. exact (TRANS (@lem3162754) (@lem3162758)). Qed.
Lemma lem3162760 : True = term188.
Proof. exact (SYM (@lem3162759)). Qed.
Lemma lem3162761 : term188.
Proof. exact (EQ_MP (@lem3162760) (@lem0)). Qed.
Lemma lem3162762 : term465.
Proof. exact (@lem3162751 (@lem3162761)). Qed.
Lemma lem3162764 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162765 : term188 = term189.
Proof. exact (@lem3162764 (NUMERAL 0) term2). Qed.
Lemma lem3162766 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162767 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162768 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162767 h1) (fun h1 : term189 = True => @lem3162766)). Qed.
Lemma lem3162769 : term189 = True.
Proof. exact (EQ_MP (@lem3162768) (@lem3162766)). Qed.
Lemma lem3162770 : term188 = True.
Proof. exact (TRANS (@lem3162765) (@lem3162769)). Qed.
Lemma lem3162771 : True = term188.
Proof. exact (SYM (@lem3162770)). Qed.
Lemma lem3162772 : term188.
Proof. exact (EQ_MP (@lem3162771) (@lem0)). Qed.
Lemma lem3162773 : term466.
Proof. exact (@lem3162762 (@lem3162772)). Qed.
Lemma lem3162775 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162776 : term188 = term189.
Proof. exact (@lem3162775 (NUMERAL 0) term2). Qed.
Lemma lem3162777 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162778 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162779 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162778 h1) (fun h1 : term189 = True => @lem3162777)). Qed.
Lemma lem3162780 : term189 = True.
Proof. exact (EQ_MP (@lem3162779) (@lem3162777)). Qed.
Lemma lem3162781 : term188 = True.
Proof. exact (TRANS (@lem3162776) (@lem3162780)). Qed.
Lemma lem3162782 : True = term188.
Proof. exact (SYM (@lem3162781)). Qed.
Lemma lem3162783 : term188.
Proof. exact (EQ_MP (@lem3162782) (@lem0)). Qed.
Lemma lem3162784 : term467.
Proof. exact (@lem3162773 (@lem3162783)). Qed.
Lemma lem3162786 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162787 : term169 = term170.
Proof. exact (@lem3162786 term2 term2). Qed.
Lemma lem3162788 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162789 : term172 = term2.
Proof. exact (EQ_MP (@lem3162788) (@lem940073)). Qed.
Lemma lem3162790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162791 : term170 = term93.
Proof. exact (MK_COMB (@lem3162790) (@lem3162789)). Qed.
Lemma lem3162792 : term169 = term93.
Proof. exact (TRANS (@lem3162787) (@lem3162791)). Qed.
Lemma lem3162794 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162795 : term236 = term239.
Proof. exact (@lem3162794 term2 term2). Qed.
Lemma lem3162796 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162797 : term172 = term2.
Proof. exact (EQ_MP (@lem3162796) (@lem940073)). Qed.
Lemma lem3162798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162799 : term170 = term93.
Proof. exact (MK_COMB (@lem3162798) (@lem3162797)). Qed.
Lemma lem3162800 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162801 : term239 = term160.
Proof. exact (MK_COMB (@lem3162800) (@lem3162799)). Qed.
Lemma lem3162802 : term236 = term160.
Proof. exact (TRANS (@lem3162795) (@lem3162801)). Qed.
Lemma lem3162803 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162804 : term468 = term460.
Proof. exact (MK_COMB (@lem3162803) (@lem3162802)). Qed.
Lemma lem3162805 : term469 = term462.
Proof. exact (MK_COMB (@lem3162804) (@lem3162792)). Qed.
Lemma lem3162807 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3162808 : term462 = term79.
Proof. exact (@lem3162807 term2). Qed.
Lemma lem3162809 : term469 = term79.
Proof. exact (TRANS (@lem3162805) (@lem3162808)). Qed.
Lemma lem3162810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162811 : term471 = term273.
Proof. exact (MK_COMB (@lem3162810) (@lem3162809)). Qed.
Lemma lem3162812 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3162813 : term472 = term275.
Proof. exact (MK_COMB (@lem3162811) (@lem3162812)). Qed.
Lemma lem3162815 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162816 : term275 = term79.
Proof. exact (@lem3162815 term2). Qed.
Lemma lem3162817 : term472 = term79.
Proof. exact (TRANS (@lem3162813) (@lem3162816)). Qed.
Lemma lem3162819 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162820 : term169 = term170.
Proof. exact (@lem3162819 term2 term2). Qed.
Lemma lem3162821 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162822 : term172 = term2.
Proof. exact (EQ_MP (@lem3162821) (@lem940073)). Qed.
Lemma lem3162823 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162824 : term170 = term93.
Proof. exact (MK_COMB (@lem3162823) (@lem3162822)). Qed.
Lemma lem3162825 : term169 = term93.
Proof. exact (TRANS (@lem3162820) (@lem3162824)). Qed.
Lemma lem3162826 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3162827 : term277 = term275.
Proof. exact (MK_COMB (@lem3162826) (@lem3162825)). Qed.
Lemma lem3162829 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3162830 : term275 = term79.
Proof. exact (@lem3162829 term2). Qed.
Lemma lem3162831 : term277 = term79.
Proof. exact (TRANS (@lem3162827) (@lem3162830)). Qed.
Lemma lem3162832 : term79 = term277.
Proof. exact (SYM (@lem3162831)). Qed.
Lemma lem3162833 : term472 = term277.
Proof. exact (TRANS (@lem3162817) (@lem3162832)). Qed.
Lemma lem3162834 : term463 = term157.
Proof. exact (@lem3162784 (@lem3162833)). Qed.
Lemma lem3162835 : term462 = term157.
Proof. exact (TRANS (@lem3162750) (@lem3162834)). Qed.
Lemma lem3162837 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3162838 : term157 = term79.
Proof. exact (@lem3162837 term79). Qed.
Lemma lem3162839 : term462 = term79.
Proof. exact (TRANS (@lem3162835) (@lem3162838)). Qed.
Lemma lem3162840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162841 : term473 = term273.
Proof. exact (MK_COMB (@lem3162840) (@lem3162839)). Qed.
Lemma lem3162842 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3162843 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3162841) (@lem3162842 _32603)). Qed.
Lemma lem3162844 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3162741 _32603) (@lem3162843 _32603)). Qed.
Lemma lem3162845 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3162846 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3162844 _32603) (@lem3162845 _32603)). Qed.
Lemma lem3162847 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162848 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3162847) (@lem3162846 _32603)). Qed.
Lemma lem3162850 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162851 : term223 = term226.
Proof. exact (@lem3162850 term200). Qed.
Lemma lem3162853 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162854 : term93 = term182.
Proof. exact (@lem3162853 term2). Qed.
Lemma lem3162855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162856 : term95 = term183.
Proof. exact (MK_COMB (@lem3162855) (@lem3162854)). Qed.
Lemma lem3162857 : term476 = term477.
Proof. exact (MK_COMB (@lem3162856) (@lem3162851)). Qed.
Lemma lem3162858 : term478.
Proof. exact (@lem1981473 term93 term93 term223 term93 term160 term93). Qed.
Lemma lem3162860 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162861 : term188 = term189.
Proof. exact (@lem3162860 (NUMERAL 0) term2). Qed.
Lemma lem3162862 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162863 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162864 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162863 h1) (fun h1 : term189 = True => @lem3162862)). Qed.
Lemma lem3162865 : term189 = True.
Proof. exact (EQ_MP (@lem3162864) (@lem3162862)). Qed.
Lemma lem3162866 : term188 = True.
Proof. exact (TRANS (@lem3162861) (@lem3162865)). Qed.
Lemma lem3162867 : True = term188.
Proof. exact (SYM (@lem3162866)). Qed.
Lemma lem3162868 : term188.
Proof. exact (EQ_MP (@lem3162867) (@lem0)). Qed.
Lemma lem3162869 : term479.
Proof. exact (@lem3162858 (@lem3162868)). Qed.
Lemma lem3162871 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162872 : term188 = term189.
Proof. exact (@lem3162871 (NUMERAL 0) term2). Qed.
Lemma lem3162873 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162874 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162875 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162874 h1) (fun h1 : term189 = True => @lem3162873)). Qed.
Lemma lem3162876 : term189 = True.
Proof. exact (EQ_MP (@lem3162875) (@lem3162873)). Qed.
Lemma lem3162877 : term188 = True.
Proof. exact (TRANS (@lem3162872) (@lem3162876)). Qed.
Lemma lem3162878 : True = term188.
Proof. exact (SYM (@lem3162877)). Qed.
Lemma lem3162879 : term188.
Proof. exact (EQ_MP (@lem3162878) (@lem0)). Qed.
Lemma lem3162880 : term480.
Proof. exact (@lem3162869 (@lem3162879)). Qed.
Lemma lem3162882 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162883 : term188 = term189.
Proof. exact (@lem3162882 (NUMERAL 0) term2). Qed.
Lemma lem3162884 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162885 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3162886 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162885 h1) (fun h1 : term189 = True => @lem3162884)). Qed.
Lemma lem3162887 : term189 = True.
Proof. exact (EQ_MP (@lem3162886) (@lem3162884)). Qed.
Lemma lem3162888 : term188 = True.
Proof. exact (TRANS (@lem3162883) (@lem3162887)). Qed.
Lemma lem3162889 : True = term188.
Proof. exact (SYM (@lem3162888)). Qed.
Lemma lem3162890 : term188.
Proof. exact (EQ_MP (@lem3162889) (@lem0)). Qed.
Lemma lem3162891 : term481.
Proof. exact (@lem3162880 (@lem3162890)). Qed.
Lemma lem3162893 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162894 : term482 = term483.
Proof. exact (@lem3162893 term200 term2). Qed.
Lemma lem3162895 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3162896 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3162897 : term207 = term200.
Proof. exact (EQ_MP (@lem3162896) (@lem3162895)). Qed.
Lemma lem3162898 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162899 : term205 = term186.
Proof. exact (MK_COMB (@lem3162898) (@lem3162897)). Qed.
Lemma lem3162900 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162901 : term483 = term223.
Proof. exact (MK_COMB (@lem3162900) (@lem3162899)). Qed.
Lemma lem3162902 : term482 = term223.
Proof. exact (TRANS (@lem3162894) (@lem3162901)). Qed.
Lemma lem3162904 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162905 : term169 = term170.
Proof. exact (@lem3162904 term2 term2). Qed.
Lemma lem3162906 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162907 : term172 = term2.
Proof. exact (EQ_MP (@lem3162906) (@lem940073)). Qed.
Lemma lem3162908 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162909 : term170 = term93.
Proof. exact (MK_COMB (@lem3162908) (@lem3162907)). Qed.
Lemma lem3162910 : term169 = term93.
Proof. exact (TRANS (@lem3162905) (@lem3162909)). Qed.
Lemma lem3162911 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3162912 : term194 = term95.
Proof. exact (MK_COMB (@lem3162911) (@lem3162910)). Qed.
Lemma lem3162913 : term484 = term476.
Proof. exact (MK_COMB (@lem3162912) (@lem3162902)). Qed.
Lemma lem3162916 : term485 = term160.
Proof. exact (@lem1367771 term2 term2). Qed.
Lemma lem3162917 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3162918 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3162919 : term199 = term200.
Proof. exact (EQ_MP (@lem3162918) (@lem3162917)). Qed.
Lemma lem3162920 : term200 = term199.
Proof. exact (SYM (@lem3162919)). Qed.
Lemma lem3162921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162922 : term186 = term196.
Proof. exact (MK_COMB (@lem3162921) (@lem3162920)). Qed.
Lemma lem3162923 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162924 : term223 = term486.
Proof. exact (MK_COMB (@lem3162923) (@lem3162922)). Qed.
Lemma lem3162925 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3162926 : term476 = term485.
Proof. exact (MK_COMB (@lem3162925) (@lem3162924)). Qed.
Lemma lem3162927 : term476 = term160.
Proof. exact (TRANS (@lem3162926) (@lem3162916)). Qed.
Lemma lem3162928 : term484 = term160.
Proof. exact (TRANS (@lem3162913) (@lem3162927)). Qed.
Lemma lem3162929 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3162930 : term487 = term162.
Proof. exact (MK_COMB (@lem3162929) (@lem3162928)). Qed.
Lemma lem3162931 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3162932 : term488 = term236.
Proof. exact (MK_COMB (@lem3162930) (@lem3162931)). Qed.
Lemma lem3162934 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162935 : term236 = term239.
Proof. exact (@lem3162934 term2 term2). Qed.
Lemma lem3162936 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162937 : term172 = term2.
Proof. exact (EQ_MP (@lem3162936) (@lem940073)). Qed.
Lemma lem3162938 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162939 : term170 = term93.
Proof. exact (MK_COMB (@lem3162938) (@lem3162937)). Qed.
Lemma lem3162940 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162941 : term239 = term160.
Proof. exact (MK_COMB (@lem3162940) (@lem3162939)). Qed.
Lemma lem3162942 : term236 = term160.
Proof. exact (TRANS (@lem3162935) (@lem3162941)). Qed.
Lemma lem3162943 : term488 = term160.
Proof. exact (TRANS (@lem3162932) (@lem3162942)). Qed.
Lemma lem3162945 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3162946 : term169 = term170.
Proof. exact (@lem3162945 term2 term2). Qed.
Lemma lem3162947 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162948 : term172 = term2.
Proof. exact (EQ_MP (@lem3162947) (@lem940073)). Qed.
Lemma lem3162949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162950 : term170 = term93.
Proof. exact (MK_COMB (@lem3162949) (@lem3162948)). Qed.
Lemma lem3162951 : term169 = term93.
Proof. exact (TRANS (@lem3162946) (@lem3162950)). Qed.
Lemma lem3162952 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem3162953 : term489 = term236.
Proof. exact (MK_COMB (@lem3162952) (@lem3162951)). Qed.
Lemma lem3162955 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3162956 : term236 = term239.
Proof. exact (@lem3162955 term2 term2). Qed.
Lemma lem3162957 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3162958 : term172 = term2.
Proof. exact (EQ_MP (@lem3162957) (@lem940073)). Qed.
Lemma lem3162959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3162960 : term170 = term93.
Proof. exact (MK_COMB (@lem3162959) (@lem3162958)). Qed.
Lemma lem3162961 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3162962 : term239 = term160.
Proof. exact (MK_COMB (@lem3162961) (@lem3162960)). Qed.
Lemma lem3162963 : term236 = term160.
Proof. exact (TRANS (@lem3162956) (@lem3162962)). Qed.
Lemma lem3162964 : term489 = term160.
Proof. exact (TRANS (@lem3162953) (@lem3162963)). Qed.
Lemma lem3162965 : term160 = term489.
Proof. exact (SYM (@lem3162964)). Qed.
Lemma lem3162966 : term488 = term489.
Proof. exact (TRANS (@lem3162943) (@lem3162965)). Qed.
Lemma lem3162967 : term477 = term161.
Proof. exact (@lem3162891 (@lem3162966)). Qed.
Lemma lem3162968 : term476 = term161.
Proof. exact (TRANS (@lem3162857) (@lem3162967)). Qed.
Lemma lem3162970 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3162971 : term161 = term160.
Proof. exact (@lem3162970 term160). Qed.
Lemma lem3162972 : term476 = term160.
Proof. exact (TRANS (@lem3162968) (@lem3162971)). Qed.
Lemma lem3162973 (_32603 : int) : (term457 _32603) = term490.
Proof. exact (MK_COMB (@lem3162848 _32603) (@lem3162972)). Qed.
Lemma lem3162974 (_32603 : int) : (term456 _32603) = term490.
Proof. exact (TRANS (@lem3162740 _32603) (@lem3162973 _32603)). Qed.
Lemma lem3162975 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3162976 (_32603 : int) : (term456 _32603) = term160.
Proof. exact (TRANS (@lem3162974 _32603) (@lem3162975)). Qed.
Lemma lem3162977 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3162978 (_32603 : int) : (term491 _32603) = term492.
Proof. exact (MK_COMB (@lem3162977) (@lem3162976 _32603)). Qed.
Lemma lem3162979 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3162980 (_32603 : int) : (term455 _32603) = term493.
Proof. exact (MK_COMB (@lem3162978 _32603) (@lem3162979)). Qed.
Lemma lem3162981 (_32603 : int) (h1 : term578 _32603) : term493.
Proof. exact (EQ_MP (@lem3162980 _32603) (@lem3162739 _32603 h1)). Qed.
Lemma lem3162983 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3162984 : term493 = term494.
Proof. exact (@lem3162983 term79 term160). Qed.
Lemma lem3162986 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3162987 : term160 = term161.
Proof. exact (@lem3162986 term2). Qed.
Lemma lem3162989 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3162990 : term79 = term157.
Proof. exact (@lem3162989 (NUMERAL 0)). Qed.
Lemma lem3162991 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3162992 : term81 = term495.
Proof. exact (MK_COMB (@lem3162991) (@lem3162990)). Qed.
Lemma lem3162993 : term494 = term496.
Proof. exact (MK_COMB (@lem3162992) (@lem3162987)). Qed.
Lemma lem3162994 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3162996 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3162997 : term188 = term189.
Proof. exact (@lem3162996 (NUMERAL 0) term2). Qed.
Lemma lem3162998 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3162999 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163000 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3162999 h1) (fun h1 : term189 = True => @lem3162998)). Qed.
Lemma lem3163001 : term189 = True.
Proof. exact (EQ_MP (@lem3163000) (@lem3162998)). Qed.
Lemma lem3163002 : term188 = True.
Proof. exact (TRANS (@lem3162997) (@lem3163001)). Qed.
Lemma lem3163003 : True = term188.
Proof. exact (SYM (@lem3163002)). Qed.
Lemma lem3163004 : term188.
Proof. exact (EQ_MP (@lem3163003) (@lem0)). Qed.
Lemma lem3163005 : term498.
Proof. exact (@lem3162994 (@lem3163004)). Qed.
Lemma lem3163007 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163008 : term188 = term189.
Proof. exact (@lem3163007 (NUMERAL 0) term2). Qed.
Lemma lem3163009 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163010 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163011 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163010 h1) (fun h1 : term189 = True => @lem3163009)). Qed.
Lemma lem3163012 : term189 = True.
Proof. exact (EQ_MP (@lem3163011) (@lem3163009)). Qed.
Lemma lem3163013 : term188 = True.
Proof. exact (TRANS (@lem3163008) (@lem3163012)). Qed.
Lemma lem3163014 : True = term188.
Proof. exact (SYM (@lem3163013)). Qed.
Lemma lem3163015 : term188.
Proof. exact (EQ_MP (@lem3163014) (@lem0)). Qed.
Lemma lem3163016 : term496 = term499.
Proof. exact (@lem3163005 (@lem3163015)). Qed.
Lemma lem3163018 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163019 : term236 = term239.
Proof. exact (@lem3163018 term2 term2). Qed.
Lemma lem3163020 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163021 : term172 = term2.
Proof. exact (EQ_MP (@lem3163020) (@lem940073)). Qed.
Lemma lem3163022 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163023 : term170 = term93.
Proof. exact (MK_COMB (@lem3163022) (@lem3163021)). Qed.
Lemma lem3163024 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163025 : term239 = term160.
Proof. exact (MK_COMB (@lem3163024) (@lem3163023)). Qed.
Lemma lem3163026 : term236 = term160.
Proof. exact (TRANS (@lem3163019) (@lem3163025)). Qed.
Lemma lem3163028 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163029 : term275 = term79.
Proof. exact (@lem3163028 term2). Qed.
Lemma lem3163030 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3163031 : term500 = term81.
Proof. exact (MK_COMB (@lem3163030) (@lem3163029)). Qed.
Lemma lem3163032 : term499 = term494.
Proof. exact (MK_COMB (@lem3163031) (@lem3163026)). Qed.
Lemma lem3163034 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3163035 : term494 = term503.
Proof. exact (@lem3163034 (NUMERAL 0) term2). Qed.
Lemma lem3163036 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163037 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3163038 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163037 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3163036)). Qed.
Lemma lem3163039 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3163038) (@lem3163036)). Qed.
Lemma lem3163040 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3163041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3163042 : term504 = (and True).
Proof. exact (MK_COMB (@lem3163041) (@lem3163040)). Qed.
Lemma lem3163043 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3163042) (@lem3163039)). Qed.
Lemma lem3163045 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3163046 : term503 = False.
Proof. exact (TRANS (@lem3163043) (@lem3163045)). Qed.
Lemma lem3163047 : term494 = False.
Proof. exact (TRANS (@lem3163035) (@lem3163046)). Qed.
Lemma lem3163048 : term499 = False.
Proof. exact (TRANS (@lem3163032) (@lem3163047)). Qed.
Lemma lem3163049 : term496 = False.
Proof. exact (TRANS (@lem3163016) (@lem3163048)). Qed.
Lemma lem3163050 : term494 = False.
Proof. exact (TRANS (@lem3162993) (@lem3163049)). Qed.
Lemma lem3163051 : term493 = False.
Proof. exact (TRANS (@lem3162984) (@lem3163050)). Qed.
Lemma lem3163052 (_32603 : int) (h1 : term578 _32603) : False.
Proof. exact (EQ_MP (@lem3163051) (@lem3162981 _32603 h1)). Qed.
Lemma lem3163053 (_32603 : int) (h1 : term387 _32603) : term387 _32603.
Proof. exact (h1). Qed.
Lemma lem3163054 (_32603 : int) (h1 : term382 _32603) : term382 _32603.
Proof. exact (h1). Qed.
Lemma lem3163055 (_32603 : int) (h1 : term594 _32603) : term594 _32603.
Proof. exact (h1). Qed.
Lemma lem3163056 (_32603 : int) (h1 : term594 _32603) : term383 _32603.
Proof. exact (proj2 (@lem3163055 _32603 h1)). Qed.
Lemma lem3163058 (_32603 : int) (h1 : term594 _32603) : (term252 _32603) = term79.
Proof. exact (proj2 (@lem3163056 _32603 h1)). Qed.
Lemma lem3163059 (_32603 : int) (h1 : term594 _32603) : term329 _32603.
Proof. exact (proj1 (@lem3163056 _32603 h1)). Qed.
Lemma lem3163060 (_32603 : int) (h1 : term594 _32603) : term281 _32603.
Proof. exact (proj2 (@lem3163059 _32603 h1)). Qed.
Lemma lem3163063 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3163064 : term433 = term188.
Proof. exact (@lem3163063 term79 term93). Qed.
Lemma lem3163066 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163067 : term93 = term182.
Proof. exact (@lem3163066 term2). Qed.
Lemma lem3163069 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163070 : term79 = term157.
Proof. exact (@lem3163069 (NUMERAL 0)). Qed.
Lemma lem3163071 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3163072 : term434 = term435.
Proof. exact (MK_COMB (@lem3163071) (@lem3163070)). Qed.
Lemma lem3163073 : term188 = term436.
Proof. exact (MK_COMB (@lem3163072) (@lem3163067)). Qed.
Lemma lem3163074 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3163076 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163077 : term188 = term189.
Proof. exact (@lem3163076 (NUMERAL 0) term2). Qed.
Lemma lem3163078 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163079 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163080 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163079 h1) (fun h1 : term189 = True => @lem3163078)). Qed.
Lemma lem3163081 : term189 = True.
Proof. exact (EQ_MP (@lem3163080) (@lem3163078)). Qed.
Lemma lem3163082 : term188 = True.
Proof. exact (TRANS (@lem3163077) (@lem3163081)). Qed.
Lemma lem3163083 : True = term188.
Proof. exact (SYM (@lem3163082)). Qed.
Lemma lem3163084 : term188.
Proof. exact (EQ_MP (@lem3163083) (@lem0)). Qed.
Lemma lem3163085 : term438.
Proof. exact (@lem3163074 (@lem3163084)). Qed.
Lemma lem3163087 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163088 : term188 = term189.
Proof. exact (@lem3163087 (NUMERAL 0) term2). Qed.
Lemma lem3163089 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163090 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163091 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163090 h1) (fun h1 : term189 = True => @lem3163089)). Qed.
Lemma lem3163092 : term189 = True.
Proof. exact (EQ_MP (@lem3163091) (@lem3163089)). Qed.
Lemma lem3163093 : term188 = True.
Proof. exact (TRANS (@lem3163088) (@lem3163092)). Qed.
Lemma lem3163094 : True = term188.
Proof. exact (SYM (@lem3163093)). Qed.
Lemma lem3163095 : term188.
Proof. exact (EQ_MP (@lem3163094) (@lem0)). Qed.
Lemma lem3163096 : term436 = term439.
Proof. exact (@lem3163085 (@lem3163095)). Qed.
Lemma lem3163098 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163099 : term169 = term170.
Proof. exact (@lem3163098 term2 term2). Qed.
Lemma lem3163100 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163101 : term172 = term2.
Proof. exact (EQ_MP (@lem3163100) (@lem940073)). Qed.
Lemma lem3163102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163103 : term170 = term93.
Proof. exact (MK_COMB (@lem3163102) (@lem3163101)). Qed.
Lemma lem3163104 : term169 = term93.
Proof. exact (TRANS (@lem3163099) (@lem3163103)). Qed.
Lemma lem3163106 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163107 : term275 = term79.
Proof. exact (@lem3163106 term2). Qed.
Lemma lem3163108 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3163109 : term440 = term434.
Proof. exact (MK_COMB (@lem3163108) (@lem3163107)). Qed.
Lemma lem3163110 : term439 = term188.
Proof. exact (MK_COMB (@lem3163109) (@lem3163104)). Qed.
Lemma lem3163112 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163113 : term188 = term189.
Proof. exact (@lem3163112 (NUMERAL 0) term2). Qed.
Lemma lem3163114 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163115 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163116 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163115 h1) (fun h1 : term189 = True => @lem3163114)). Qed.
Lemma lem3163117 : term189 = True.
Proof. exact (EQ_MP (@lem3163116) (@lem3163114)). Qed.
Lemma lem3163118 : term188 = True.
Proof. exact (TRANS (@lem3163113) (@lem3163117)). Qed.
Lemma lem3163119 : term439 = True.
Proof. exact (TRANS (@lem3163110) (@lem3163118)). Qed.
Lemma lem3163120 : term436 = True.
Proof. exact (TRANS (@lem3163096) (@lem3163119)). Qed.
Lemma lem3163121 : term188 = True.
Proof. exact (TRANS (@lem3163073) (@lem3163120)). Qed.
Lemma lem3163122 : term433 = True.
Proof. exact (TRANS (@lem3163064) (@lem3163121)). Qed.
Lemma lem3163123 : True = term433.
Proof. exact (SYM (@lem3163122)). Qed.
Lemma lem3163124 : term433.
Proof. exact (EQ_MP (@lem3163123) (@lem0)). Qed.
Lemma lem3163125 (_32603 : int) (h1 : term594 _32603) : term528 _32603.
Proof. exact (conj (@lem3163124) (@lem3163060 _32603 h1)). Qed.
Lemma lem3163127 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3163128 (_32603 : int) : term529 _32603.
Proof. exact (@lem3163127 term93 (term263 _32603)). Qed.
Lemma lem3163129 (_32603 : int) (h1 : term594 _32603) : term530 _32603.
Proof. exact (@lem3163128 _32603 (@lem3163125 _32603 h1)). Qed.
Lemma lem3163130 (_32603 : int) : (term531 _32603) = (term263 _32603).
Proof. exact (@lem1982733 (term263 _32603)). Qed.
Lemma lem3163131 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3163132 (_32603 : int) : (term532 _32603) = (term280 _32603).
Proof. exact (MK_COMB (@lem3163131) (@lem3163130 _32603)). Qed.
Lemma lem3163133 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163134 (_32603 : int) : (term530 _32603) = (term281 _32603).
Proof. exact (MK_COMB (@lem3163132 _32603) (@lem3163133)). Qed.
Lemma lem3163135 (_32603 : int) (h1 : term594 _32603) : term281 _32603.
Proof. exact (EQ_MP (@lem3163134 _32603) (@lem3163129 _32603 h1)). Qed.
Lemma lem3163137 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3163138 (_32603 : int) : term579 _32603.
Proof. exact (@lem3163137 (term252 _32603)). Qed.
Lemma lem3163139 (_32603 : int) (h1 : term594 _32603) : term580 _32603.
Proof. exact (@lem3163138 _32603 (@lem3163058 _32603 h1)). Qed.
Lemma lem3163140 (_32603 : int) (h1 : term594 _32603) : term595 _32603.
Proof. exact (@lem3163139 _32603 h1 term93). Qed.
Lemma lem3163141 (_32603 : int) : (term595 _32603) = ((term526 _32603) = term79).
Proof. exact (eq_refl (term595 _32603)). Qed.
Lemma lem3163142 (_32603 : int) (h1 : term594 _32603) : (term526 _32603) = term79.
Proof. exact (EQ_MP (@lem3163141 _32603) (@lem3163140 _32603 h1)). Qed.
Lemma lem3163143 (_32603 : int) : (term526 _32603) = (term252 _32603).
Proof. exact (@lem1982733 (term252 _32603)). Qed.
Lemma lem3163144 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3163145 (_32603 : int) : (term596 _32603) = (term297 _32603).
Proof. exact (MK_COMB (@lem3163144) (@lem3163143 _32603)). Qed.
Lemma lem3163146 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163147 (_32603 : int) : ((term526 _32603) = term79) = ((term252 _32603) = term79).
Proof. exact (MK_COMB (@lem3163145 _32603) (@lem3163146)). Qed.
Lemma lem3163148 (_32603 : int) (h1 : term594 _32603) : (term252 _32603) = term79.
Proof. exact (EQ_MP (@lem3163147 _32603) (@lem3163142 _32603 h1)). Qed.
Lemma lem3163149 (_32603 : int) (h1 : term594 _32603) : term597 _32603.
Proof. exact (conj (@lem3163148 _32603 h1) (@lem3163135 _32603 h1)). Qed.
Lemma lem3163151 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3163152 (_32603 : int) : term598 _32603.
Proof. exact (@lem3163151 (term252 _32603) (term263 _32603)). Qed.
Lemma lem3163153 (_32603 : int) (h1 : term594 _32603) : term599 _32603.
Proof. exact (@lem3163152 _32603 (@lem3163149 _32603 h1)). Qed.
Lemma lem3163154 (_32603 : int) : (term600 _32603) = (term569 _32603).
Proof. exact (@lem1982759 (real_of_int _32603) (term263 _32603) term160). Qed.
Lemma lem3163155 (_32603 : int) : (term570 _32603) = (term459 _32603).
Proof. exact (@lem1982715 term160 (real_of_int _32603)). Qed.
Lemma lem3163157 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163158 : term93 = term182.
Proof. exact (@lem3163157 term2). Qed.
Lemma lem3163160 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163161 : term160 = term161.
Proof. exact (@lem3163160 term2). Qed.
Lemma lem3163162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163163 : term460 = term461.
Proof. exact (MK_COMB (@lem3163162) (@lem3163161)). Qed.
Lemma lem3163164 : term462 = term463.
Proof. exact (MK_COMB (@lem3163163) (@lem3163158)). Qed.
Lemma lem3163165 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3163167 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163168 : term188 = term189.
Proof. exact (@lem3163167 (NUMERAL 0) term2). Qed.
Lemma lem3163169 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163170 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163171 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163170 h1) (fun h1 : term189 = True => @lem3163169)). Qed.
Lemma lem3163172 : term189 = True.
Proof. exact (EQ_MP (@lem3163171) (@lem3163169)). Qed.
Lemma lem3163173 : term188 = True.
Proof. exact (TRANS (@lem3163168) (@lem3163172)). Qed.
Lemma lem3163174 : True = term188.
Proof. exact (SYM (@lem3163173)). Qed.
Lemma lem3163175 : term188.
Proof. exact (EQ_MP (@lem3163174) (@lem0)). Qed.
Lemma lem3163176 : term465.
Proof. exact (@lem3163165 (@lem3163175)). Qed.
Lemma lem3163178 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163179 : term188 = term189.
Proof. exact (@lem3163178 (NUMERAL 0) term2). Qed.
Lemma lem3163180 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163181 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163182 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163181 h1) (fun h1 : term189 = True => @lem3163180)). Qed.
Lemma lem3163183 : term189 = True.
Proof. exact (EQ_MP (@lem3163182) (@lem3163180)). Qed.
Lemma lem3163184 : term188 = True.
Proof. exact (TRANS (@lem3163179) (@lem3163183)). Qed.
Lemma lem3163185 : True = term188.
Proof. exact (SYM (@lem3163184)). Qed.
Lemma lem3163186 : term188.
Proof. exact (EQ_MP (@lem3163185) (@lem0)). Qed.
Lemma lem3163187 : term466.
Proof. exact (@lem3163176 (@lem3163186)). Qed.
Lemma lem3163189 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163190 : term188 = term189.
Proof. exact (@lem3163189 (NUMERAL 0) term2). Qed.
Lemma lem3163191 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163192 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163193 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163192 h1) (fun h1 : term189 = True => @lem3163191)). Qed.
Lemma lem3163194 : term189 = True.
Proof. exact (EQ_MP (@lem3163193) (@lem3163191)). Qed.
Lemma lem3163195 : term188 = True.
Proof. exact (TRANS (@lem3163190) (@lem3163194)). Qed.
Lemma lem3163196 : True = term188.
Proof. exact (SYM (@lem3163195)). Qed.
Lemma lem3163197 : term188.
Proof. exact (EQ_MP (@lem3163196) (@lem0)). Qed.
Lemma lem3163198 : term467.
Proof. exact (@lem3163187 (@lem3163197)). Qed.
Lemma lem3163200 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163201 : term169 = term170.
Proof. exact (@lem3163200 term2 term2). Qed.
Lemma lem3163202 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163203 : term172 = term2.
Proof. exact (EQ_MP (@lem3163202) (@lem940073)). Qed.
Lemma lem3163204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163205 : term170 = term93.
Proof. exact (MK_COMB (@lem3163204) (@lem3163203)). Qed.
Lemma lem3163206 : term169 = term93.
Proof. exact (TRANS (@lem3163201) (@lem3163205)). Qed.
Lemma lem3163208 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163209 : term236 = term239.
Proof. exact (@lem3163208 term2 term2). Qed.
Lemma lem3163210 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163211 : term172 = term2.
Proof. exact (EQ_MP (@lem3163210) (@lem940073)). Qed.
Lemma lem3163212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163213 : term170 = term93.
Proof. exact (MK_COMB (@lem3163212) (@lem3163211)). Qed.
Lemma lem3163214 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163215 : term239 = term160.
Proof. exact (MK_COMB (@lem3163214) (@lem3163213)). Qed.
Lemma lem3163216 : term236 = term160.
Proof. exact (TRANS (@lem3163209) (@lem3163215)). Qed.
Lemma lem3163217 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163218 : term468 = term460.
Proof. exact (MK_COMB (@lem3163217) (@lem3163216)). Qed.
Lemma lem3163219 : term469 = term462.
Proof. exact (MK_COMB (@lem3163218) (@lem3163206)). Qed.
Lemma lem3163221 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3163222 : term462 = term79.
Proof. exact (@lem3163221 term2). Qed.
Lemma lem3163223 : term469 = term79.
Proof. exact (TRANS (@lem3163219) (@lem3163222)). Qed.
Lemma lem3163224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163225 : term471 = term273.
Proof. exact (MK_COMB (@lem3163224) (@lem3163223)). Qed.
Lemma lem3163226 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3163227 : term472 = term275.
Proof. exact (MK_COMB (@lem3163225) (@lem3163226)). Qed.
Lemma lem3163229 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163230 : term275 = term79.
Proof. exact (@lem3163229 term2). Qed.
Lemma lem3163231 : term472 = term79.
Proof. exact (TRANS (@lem3163227) (@lem3163230)). Qed.
Lemma lem3163233 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163234 : term169 = term170.
Proof. exact (@lem3163233 term2 term2). Qed.
Lemma lem3163235 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163236 : term172 = term2.
Proof. exact (EQ_MP (@lem3163235) (@lem940073)). Qed.
Lemma lem3163237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163238 : term170 = term93.
Proof. exact (MK_COMB (@lem3163237) (@lem3163236)). Qed.
Lemma lem3163239 : term169 = term93.
Proof. exact (TRANS (@lem3163234) (@lem3163238)). Qed.
Lemma lem3163240 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3163241 : term277 = term275.
Proof. exact (MK_COMB (@lem3163240) (@lem3163239)). Qed.
Lemma lem3163243 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163244 : term275 = term79.
Proof. exact (@lem3163243 term2). Qed.
Lemma lem3163245 : term277 = term79.
Proof. exact (TRANS (@lem3163241) (@lem3163244)). Qed.
Lemma lem3163246 : term79 = term277.
Proof. exact (SYM (@lem3163245)). Qed.
Lemma lem3163247 : term472 = term277.
Proof. exact (TRANS (@lem3163231) (@lem3163246)). Qed.
Lemma lem3163248 : term463 = term157.
Proof. exact (@lem3163198 (@lem3163247)). Qed.
Lemma lem3163249 : term462 = term157.
Proof. exact (TRANS (@lem3163164) (@lem3163248)). Qed.
Lemma lem3163251 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3163252 : term157 = term79.
Proof. exact (@lem3163251 term79). Qed.
Lemma lem3163253 : term462 = term79.
Proof. exact (TRANS (@lem3163249) (@lem3163252)). Qed.
Lemma lem3163254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163255 : term473 = term273.
Proof. exact (MK_COMB (@lem3163254) (@lem3163253)). Qed.
Lemma lem3163256 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3163257 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3163255) (@lem3163256 _32603)). Qed.
Lemma lem3163258 (_32603 : int) : (term570 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3163155 _32603) (@lem3163257 _32603)). Qed.
Lemma lem3163259 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3163260 (_32603 : int) : (term570 _32603) = term79.
Proof. exact (TRANS (@lem3163258 _32603) (@lem3163259 _32603)). Qed.
Lemma lem3163261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163262 (_32603 : int) : (term571 _32603) = term121.
Proof. exact (MK_COMB (@lem3163261) (@lem3163260 _32603)). Qed.
Lemma lem3163263 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3163264 (_32603 : int) : (term569 _32603) = term490.
Proof. exact (MK_COMB (@lem3163262 _32603) (@lem3163263)). Qed.
Lemma lem3163265 (_32603 : int) : (term600 _32603) = term490.
Proof. exact (TRANS (@lem3163154 _32603) (@lem3163264 _32603)). Qed.
Lemma lem3163266 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3163267 (_32603 : int) : (term600 _32603) = term160.
Proof. exact (TRANS (@lem3163265 _32603) (@lem3163266)). Qed.
Lemma lem3163268 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3163269 (_32603 : int) : (term601 _32603) = term492.
Proof. exact (MK_COMB (@lem3163268) (@lem3163267 _32603)). Qed.
Lemma lem3163270 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163271 (_32603 : int) : (term599 _32603) = term493.
Proof. exact (MK_COMB (@lem3163269 _32603) (@lem3163270)). Qed.
Lemma lem3163272 (_32603 : int) (h1 : term594 _32603) : term493.
Proof. exact (EQ_MP (@lem3163271 _32603) (@lem3163153 _32603 h1)). Qed.
Lemma lem3163274 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3163275 : term493 = term494.
Proof. exact (@lem3163274 term79 term160). Qed.
Lemma lem3163277 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163278 : term160 = term161.
Proof. exact (@lem3163277 term2). Qed.
Lemma lem3163280 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163281 : term79 = term157.
Proof. exact (@lem3163280 (NUMERAL 0)). Qed.
Lemma lem3163282 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3163283 : term81 = term495.
Proof. exact (MK_COMB (@lem3163282) (@lem3163281)). Qed.
Lemma lem3163284 : term494 = term496.
Proof. exact (MK_COMB (@lem3163283) (@lem3163278)). Qed.
Lemma lem3163285 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3163287 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163288 : term188 = term189.
Proof. exact (@lem3163287 (NUMERAL 0) term2). Qed.
Lemma lem3163289 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163290 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163291 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163290 h1) (fun h1 : term189 = True => @lem3163289)). Qed.
Lemma lem3163292 : term189 = True.
Proof. exact (EQ_MP (@lem3163291) (@lem3163289)). Qed.
Lemma lem3163293 : term188 = True.
Proof. exact (TRANS (@lem3163288) (@lem3163292)). Qed.
Lemma lem3163294 : True = term188.
Proof. exact (SYM (@lem3163293)). Qed.
Lemma lem3163295 : term188.
Proof. exact (EQ_MP (@lem3163294) (@lem0)). Qed.
Lemma lem3163296 : term498.
Proof. exact (@lem3163285 (@lem3163295)). Qed.
Lemma lem3163298 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163299 : term188 = term189.
Proof. exact (@lem3163298 (NUMERAL 0) term2). Qed.
Lemma lem3163300 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163301 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163302 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163301 h1) (fun h1 : term189 = True => @lem3163300)). Qed.
Lemma lem3163303 : term189 = True.
Proof. exact (EQ_MP (@lem3163302) (@lem3163300)). Qed.
Lemma lem3163304 : term188 = True.
Proof. exact (TRANS (@lem3163299) (@lem3163303)). Qed.
Lemma lem3163305 : True = term188.
Proof. exact (SYM (@lem3163304)). Qed.
Lemma lem3163306 : term188.
Proof. exact (EQ_MP (@lem3163305) (@lem0)). Qed.
Lemma lem3163307 : term496 = term499.
Proof. exact (@lem3163296 (@lem3163306)). Qed.
Lemma lem3163309 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163310 : term236 = term239.
Proof. exact (@lem3163309 term2 term2). Qed.
Lemma lem3163311 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163312 : term172 = term2.
Proof. exact (EQ_MP (@lem3163311) (@lem940073)). Qed.
Lemma lem3163313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163314 : term170 = term93.
Proof. exact (MK_COMB (@lem3163313) (@lem3163312)). Qed.
Lemma lem3163315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163316 : term239 = term160.
Proof. exact (MK_COMB (@lem3163315) (@lem3163314)). Qed.
Lemma lem3163317 : term236 = term160.
Proof. exact (TRANS (@lem3163310) (@lem3163316)). Qed.
Lemma lem3163319 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163320 : term275 = term79.
Proof. exact (@lem3163319 term2). Qed.
Lemma lem3163321 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3163322 : term500 = term81.
Proof. exact (MK_COMB (@lem3163321) (@lem3163320)). Qed.
Lemma lem3163323 : term499 = term494.
Proof. exact (MK_COMB (@lem3163322) (@lem3163317)). Qed.
Lemma lem3163325 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3163326 : term494 = term503.
Proof. exact (@lem3163325 (NUMERAL 0) term2). Qed.
Lemma lem3163327 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163328 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3163329 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163328 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3163327)). Qed.
Lemma lem3163330 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3163329) (@lem3163327)). Qed.
Lemma lem3163331 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3163332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3163333 : term504 = (and True).
Proof. exact (MK_COMB (@lem3163332) (@lem3163331)). Qed.
Lemma lem3163334 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3163333) (@lem3163330)). Qed.
Lemma lem3163336 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3163337 : term503 = False.
Proof. exact (TRANS (@lem3163334) (@lem3163336)). Qed.
Lemma lem3163338 : term494 = False.
Proof. exact (TRANS (@lem3163326) (@lem3163337)). Qed.
Lemma lem3163339 : term499 = False.
Proof. exact (TRANS (@lem3163323) (@lem3163338)). Qed.
Lemma lem3163340 : term496 = False.
Proof. exact (TRANS (@lem3163307) (@lem3163339)). Qed.
Lemma lem3163341 : term494 = False.
Proof. exact (TRANS (@lem3163284) (@lem3163340)). Qed.
Lemma lem3163342 : term493 = False.
Proof. exact (TRANS (@lem3163275) (@lem3163341)). Qed.
Lemma lem3163343 (_32603 : int) (h1 : term594 _32603) : False.
Proof. exact (EQ_MP (@lem3163342) (@lem3163272 _32603 h1)). Qed.
Lemma lem3163344 (_32603 : int) (h1 : term602 _32603) : term602 _32603.
Proof. exact (h1). Qed.
Lemma lem3163345 (_32603 : int) (h1 : term602 _32603) : term384 _32603.
Proof. exact (proj2 (@lem3163344 _32603 h1)). Qed.
Lemma lem3163347 (_32603 : int) (h1 : term602 _32603) : (term252 _32603) = term79.
Proof. exact (proj2 (@lem3163345 _32603 h1)). Qed.
Lemma lem3163348 (_32603 : int) (h1 : term602 _32603) : term330 _32603.
Proof. exact (proj1 (@lem3163345 _32603 h1)). Qed.
Lemma lem3163349 (_32603 : int) (h1 : term602 _32603) : term281 _32603.
Proof. exact (proj2 (@lem3163348 _32603 h1)). Qed.
Lemma lem3163352 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3163353 : term433 = term188.
Proof. exact (@lem3163352 term79 term93). Qed.
Lemma lem3163355 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163356 : term93 = term182.
Proof. exact (@lem3163355 term2). Qed.
Lemma lem3163358 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163359 : term79 = term157.
Proof. exact (@lem3163358 (NUMERAL 0)). Qed.
Lemma lem3163360 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3163361 : term434 = term435.
Proof. exact (MK_COMB (@lem3163360) (@lem3163359)). Qed.
Lemma lem3163362 : term188 = term436.
Proof. exact (MK_COMB (@lem3163361) (@lem3163356)). Qed.
Lemma lem3163363 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3163365 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163366 : term188 = term189.
Proof. exact (@lem3163365 (NUMERAL 0) term2). Qed.
Lemma lem3163367 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163368 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163369 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163368 h1) (fun h1 : term189 = True => @lem3163367)). Qed.
Lemma lem3163370 : term189 = True.
Proof. exact (EQ_MP (@lem3163369) (@lem3163367)). Qed.
Lemma lem3163371 : term188 = True.
Proof. exact (TRANS (@lem3163366) (@lem3163370)). Qed.
Lemma lem3163372 : True = term188.
Proof. exact (SYM (@lem3163371)). Qed.
Lemma lem3163373 : term188.
Proof. exact (EQ_MP (@lem3163372) (@lem0)). Qed.
Lemma lem3163374 : term438.
Proof. exact (@lem3163363 (@lem3163373)). Qed.
Lemma lem3163376 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163377 : term188 = term189.
Proof. exact (@lem3163376 (NUMERAL 0) term2). Qed.
Lemma lem3163378 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163379 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163380 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163379 h1) (fun h1 : term189 = True => @lem3163378)). Qed.
Lemma lem3163381 : term189 = True.
Proof. exact (EQ_MP (@lem3163380) (@lem3163378)). Qed.
Lemma lem3163382 : term188 = True.
Proof. exact (TRANS (@lem3163377) (@lem3163381)). Qed.
Lemma lem3163383 : True = term188.
Proof. exact (SYM (@lem3163382)). Qed.
Lemma lem3163384 : term188.
Proof. exact (EQ_MP (@lem3163383) (@lem0)). Qed.
Lemma lem3163385 : term436 = term439.
Proof. exact (@lem3163374 (@lem3163384)). Qed.
Lemma lem3163387 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163388 : term169 = term170.
Proof. exact (@lem3163387 term2 term2). Qed.
Lemma lem3163389 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163390 : term172 = term2.
Proof. exact (EQ_MP (@lem3163389) (@lem940073)). Qed.
Lemma lem3163391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163392 : term170 = term93.
Proof. exact (MK_COMB (@lem3163391) (@lem3163390)). Qed.
Lemma lem3163393 : term169 = term93.
Proof. exact (TRANS (@lem3163388) (@lem3163392)). Qed.
Lemma lem3163395 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163396 : term275 = term79.
Proof. exact (@lem3163395 term2). Qed.
Lemma lem3163397 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3163398 : term440 = term434.
Proof. exact (MK_COMB (@lem3163397) (@lem3163396)). Qed.
Lemma lem3163399 : term439 = term188.
Proof. exact (MK_COMB (@lem3163398) (@lem3163393)). Qed.
Lemma lem3163401 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163402 : term188 = term189.
Proof. exact (@lem3163401 (NUMERAL 0) term2). Qed.
Lemma lem3163403 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163404 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163405 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163404 h1) (fun h1 : term189 = True => @lem3163403)). Qed.
Lemma lem3163406 : term189 = True.
Proof. exact (EQ_MP (@lem3163405) (@lem3163403)). Qed.
Lemma lem3163407 : term188 = True.
Proof. exact (TRANS (@lem3163402) (@lem3163406)). Qed.
Lemma lem3163408 : term439 = True.
Proof. exact (TRANS (@lem3163399) (@lem3163407)). Qed.
Lemma lem3163409 : term436 = True.
Proof. exact (TRANS (@lem3163385) (@lem3163408)). Qed.
Lemma lem3163410 : term188 = True.
Proof. exact (TRANS (@lem3163362) (@lem3163409)). Qed.
Lemma lem3163411 : term433 = True.
Proof. exact (TRANS (@lem3163353) (@lem3163410)). Qed.
Lemma lem3163412 : True = term433.
Proof. exact (SYM (@lem3163411)). Qed.
Lemma lem3163413 : term433.
Proof. exact (EQ_MP (@lem3163412) (@lem0)). Qed.
Lemma lem3163414 (_32603 : int) (h1 : term602 _32603) : term528 _32603.
Proof. exact (conj (@lem3163413) (@lem3163349 _32603 h1)). Qed.
Lemma lem3163416 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3163417 (_32603 : int) : term529 _32603.
Proof. exact (@lem3163416 term93 (term263 _32603)). Qed.
Lemma lem3163418 (_32603 : int) (h1 : term602 _32603) : term530 _32603.
Proof. exact (@lem3163417 _32603 (@lem3163414 _32603 h1)). Qed.
Lemma lem3163419 (_32603 : int) : (term531 _32603) = (term263 _32603).
Proof. exact (@lem1982733 (term263 _32603)). Qed.
Lemma lem3163420 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3163421 (_32603 : int) : (term532 _32603) = (term280 _32603).
Proof. exact (MK_COMB (@lem3163420) (@lem3163419 _32603)). Qed.
Lemma lem3163422 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163423 (_32603 : int) : (term530 _32603) = (term281 _32603).
Proof. exact (MK_COMB (@lem3163421 _32603) (@lem3163422)). Qed.
Lemma lem3163424 (_32603 : int) (h1 : term602 _32603) : term281 _32603.
Proof. exact (EQ_MP (@lem3163423 _32603) (@lem3163418 _32603 h1)). Qed.
Lemma lem3163426 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3163427 (_32603 : int) : term579 _32603.
Proof. exact (@lem3163426 (term252 _32603)). Qed.
Lemma lem3163428 (_32603 : int) (h1 : term602 _32603) : term580 _32603.
Proof. exact (@lem3163427 _32603 (@lem3163347 _32603 h1)). Qed.
Lemma lem3163429 (_32603 : int) (h1 : term602 _32603) : term595 _32603.
Proof. exact (@lem3163428 _32603 h1 term93). Qed.
Lemma lem3163430 (_32603 : int) : (term595 _32603) = ((term526 _32603) = term79).
Proof. exact (eq_refl (term595 _32603)). Qed.
Lemma lem3163431 (_32603 : int) (h1 : term602 _32603) : (term526 _32603) = term79.
Proof. exact (EQ_MP (@lem3163430 _32603) (@lem3163429 _32603 h1)). Qed.
Lemma lem3163432 (_32603 : int) : (term526 _32603) = (term252 _32603).
Proof. exact (@lem1982733 (term252 _32603)). Qed.
Lemma lem3163433 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3163434 (_32603 : int) : (term596 _32603) = (term297 _32603).
Proof. exact (MK_COMB (@lem3163433) (@lem3163432 _32603)). Qed.
Lemma lem3163435 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163436 (_32603 : int) : ((term526 _32603) = term79) = ((term252 _32603) = term79).
Proof. exact (MK_COMB (@lem3163434 _32603) (@lem3163435)). Qed.
Lemma lem3163437 (_32603 : int) (h1 : term602 _32603) : (term252 _32603) = term79.
Proof. exact (EQ_MP (@lem3163436 _32603) (@lem3163431 _32603 h1)). Qed.
Lemma lem3163438 (_32603 : int) (h1 : term602 _32603) : term597 _32603.
Proof. exact (conj (@lem3163437 _32603 h1) (@lem3163424 _32603 h1)). Qed.
Lemma lem3163440 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3163441 (_32603 : int) : term598 _32603.
Proof. exact (@lem3163440 (term252 _32603) (term263 _32603)). Qed.
Lemma lem3163442 (_32603 : int) (h1 : term602 _32603) : term599 _32603.
Proof. exact (@lem3163441 _32603 (@lem3163438 _32603 h1)). Qed.
Lemma lem3163443 (_32603 : int) : (term600 _32603) = (term569 _32603).
Proof. exact (@lem1982759 (real_of_int _32603) (term263 _32603) term160). Qed.
Lemma lem3163444 (_32603 : int) : (term570 _32603) = (term459 _32603).
Proof. exact (@lem1982715 term160 (real_of_int _32603)). Qed.
Lemma lem3163446 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163447 : term93 = term182.
Proof. exact (@lem3163446 term2). Qed.
Lemma lem3163449 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163450 : term160 = term161.
Proof. exact (@lem3163449 term2). Qed.
Lemma lem3163451 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163452 : term460 = term461.
Proof. exact (MK_COMB (@lem3163451) (@lem3163450)). Qed.
Lemma lem3163453 : term462 = term463.
Proof. exact (MK_COMB (@lem3163452) (@lem3163447)). Qed.
Lemma lem3163454 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3163456 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163457 : term188 = term189.
Proof. exact (@lem3163456 (NUMERAL 0) term2). Qed.
Lemma lem3163458 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163459 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163460 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163459 h1) (fun h1 : term189 = True => @lem3163458)). Qed.
Lemma lem3163461 : term189 = True.
Proof. exact (EQ_MP (@lem3163460) (@lem3163458)). Qed.
Lemma lem3163462 : term188 = True.
Proof. exact (TRANS (@lem3163457) (@lem3163461)). Qed.
Lemma lem3163463 : True = term188.
Proof. exact (SYM (@lem3163462)). Qed.
Lemma lem3163464 : term188.
Proof. exact (EQ_MP (@lem3163463) (@lem0)). Qed.
Lemma lem3163465 : term465.
Proof. exact (@lem3163454 (@lem3163464)). Qed.
Lemma lem3163467 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163468 : term188 = term189.
Proof. exact (@lem3163467 (NUMERAL 0) term2). Qed.
Lemma lem3163469 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163470 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163471 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163470 h1) (fun h1 : term189 = True => @lem3163469)). Qed.
Lemma lem3163472 : term189 = True.
Proof. exact (EQ_MP (@lem3163471) (@lem3163469)). Qed.
Lemma lem3163473 : term188 = True.
Proof. exact (TRANS (@lem3163468) (@lem3163472)). Qed.
Lemma lem3163474 : True = term188.
Proof. exact (SYM (@lem3163473)). Qed.
Lemma lem3163475 : term188.
Proof. exact (EQ_MP (@lem3163474) (@lem0)). Qed.
Lemma lem3163476 : term466.
Proof. exact (@lem3163465 (@lem3163475)). Qed.
Lemma lem3163478 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163479 : term188 = term189.
Proof. exact (@lem3163478 (NUMERAL 0) term2). Qed.
Lemma lem3163480 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163481 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163482 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163481 h1) (fun h1 : term189 = True => @lem3163480)). Qed.
Lemma lem3163483 : term189 = True.
Proof. exact (EQ_MP (@lem3163482) (@lem3163480)). Qed.
Lemma lem3163484 : term188 = True.
Proof. exact (TRANS (@lem3163479) (@lem3163483)). Qed.
Lemma lem3163485 : True = term188.
Proof. exact (SYM (@lem3163484)). Qed.
Lemma lem3163486 : term188.
Proof. exact (EQ_MP (@lem3163485) (@lem0)). Qed.
Lemma lem3163487 : term467.
Proof. exact (@lem3163476 (@lem3163486)). Qed.
Lemma lem3163489 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163490 : term169 = term170.
Proof. exact (@lem3163489 term2 term2). Qed.
Lemma lem3163491 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163492 : term172 = term2.
Proof. exact (EQ_MP (@lem3163491) (@lem940073)). Qed.
Lemma lem3163493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163494 : term170 = term93.
Proof. exact (MK_COMB (@lem3163493) (@lem3163492)). Qed.
Lemma lem3163495 : term169 = term93.
Proof. exact (TRANS (@lem3163490) (@lem3163494)). Qed.
Lemma lem3163497 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163498 : term236 = term239.
Proof. exact (@lem3163497 term2 term2). Qed.
Lemma lem3163499 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163500 : term172 = term2.
Proof. exact (EQ_MP (@lem3163499) (@lem940073)). Qed.
Lemma lem3163501 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163502 : term170 = term93.
Proof. exact (MK_COMB (@lem3163501) (@lem3163500)). Qed.
Lemma lem3163503 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163504 : term239 = term160.
Proof. exact (MK_COMB (@lem3163503) (@lem3163502)). Qed.
Lemma lem3163505 : term236 = term160.
Proof. exact (TRANS (@lem3163498) (@lem3163504)). Qed.
Lemma lem3163506 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163507 : term468 = term460.
Proof. exact (MK_COMB (@lem3163506) (@lem3163505)). Qed.
Lemma lem3163508 : term469 = term462.
Proof. exact (MK_COMB (@lem3163507) (@lem3163495)). Qed.
Lemma lem3163510 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3163511 : term462 = term79.
Proof. exact (@lem3163510 term2). Qed.
Lemma lem3163512 : term469 = term79.
Proof. exact (TRANS (@lem3163508) (@lem3163511)). Qed.
Lemma lem3163513 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163514 : term471 = term273.
Proof. exact (MK_COMB (@lem3163513) (@lem3163512)). Qed.
Lemma lem3163515 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3163516 : term472 = term275.
Proof. exact (MK_COMB (@lem3163514) (@lem3163515)). Qed.
Lemma lem3163518 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163519 : term275 = term79.
Proof. exact (@lem3163518 term2). Qed.
Lemma lem3163520 : term472 = term79.
Proof. exact (TRANS (@lem3163516) (@lem3163519)). Qed.
Lemma lem3163522 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163523 : term169 = term170.
Proof. exact (@lem3163522 term2 term2). Qed.
Lemma lem3163524 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163525 : term172 = term2.
Proof. exact (EQ_MP (@lem3163524) (@lem940073)). Qed.
Lemma lem3163526 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163527 : term170 = term93.
Proof. exact (MK_COMB (@lem3163526) (@lem3163525)). Qed.
Lemma lem3163528 : term169 = term93.
Proof. exact (TRANS (@lem3163523) (@lem3163527)). Qed.
Lemma lem3163529 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3163530 : term277 = term275.
Proof. exact (MK_COMB (@lem3163529) (@lem3163528)). Qed.
Lemma lem3163532 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163533 : term275 = term79.
Proof. exact (@lem3163532 term2). Qed.
Lemma lem3163534 : term277 = term79.
Proof. exact (TRANS (@lem3163530) (@lem3163533)). Qed.
Lemma lem3163535 : term79 = term277.
Proof. exact (SYM (@lem3163534)). Qed.
Lemma lem3163536 : term472 = term277.
Proof. exact (TRANS (@lem3163520) (@lem3163535)). Qed.
Lemma lem3163537 : term463 = term157.
Proof. exact (@lem3163487 (@lem3163536)). Qed.
Lemma lem3163538 : term462 = term157.
Proof. exact (TRANS (@lem3163453) (@lem3163537)). Qed.
Lemma lem3163540 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3163541 : term157 = term79.
Proof. exact (@lem3163540 term79). Qed.
Lemma lem3163542 : term462 = term79.
Proof. exact (TRANS (@lem3163538) (@lem3163541)). Qed.
Lemma lem3163543 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163544 : term473 = term273.
Proof. exact (MK_COMB (@lem3163543) (@lem3163542)). Qed.
Lemma lem3163545 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3163546 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3163544) (@lem3163545 _32603)). Qed.
Lemma lem3163547 (_32603 : int) : (term570 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3163444 _32603) (@lem3163546 _32603)). Qed.
Lemma lem3163548 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3163549 (_32603 : int) : (term570 _32603) = term79.
Proof. exact (TRANS (@lem3163547 _32603) (@lem3163548 _32603)). Qed.
Lemma lem3163550 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163551 (_32603 : int) : (term571 _32603) = term121.
Proof. exact (MK_COMB (@lem3163550) (@lem3163549 _32603)). Qed.
Lemma lem3163552 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3163553 (_32603 : int) : (term569 _32603) = term490.
Proof. exact (MK_COMB (@lem3163551 _32603) (@lem3163552)). Qed.
Lemma lem3163554 (_32603 : int) : (term600 _32603) = term490.
Proof. exact (TRANS (@lem3163443 _32603) (@lem3163553 _32603)). Qed.
Lemma lem3163555 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3163556 (_32603 : int) : (term600 _32603) = term160.
Proof. exact (TRANS (@lem3163554 _32603) (@lem3163555)). Qed.
Lemma lem3163557 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3163558 (_32603 : int) : (term601 _32603) = term492.
Proof. exact (MK_COMB (@lem3163557) (@lem3163556 _32603)). Qed.
Lemma lem3163559 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163560 (_32603 : int) : (term599 _32603) = term493.
Proof. exact (MK_COMB (@lem3163558 _32603) (@lem3163559)). Qed.
Lemma lem3163561 (_32603 : int) (h1 : term602 _32603) : term493.
Proof. exact (EQ_MP (@lem3163560 _32603) (@lem3163442 _32603 h1)). Qed.
Lemma lem3163563 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3163564 : term493 = term494.
Proof. exact (@lem3163563 term79 term160). Qed.
Lemma lem3163566 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163567 : term160 = term161.
Proof. exact (@lem3163566 term2). Qed.
Lemma lem3163569 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163570 : term79 = term157.
Proof. exact (@lem3163569 (NUMERAL 0)). Qed.
Lemma lem3163571 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3163572 : term81 = term495.
Proof. exact (MK_COMB (@lem3163571) (@lem3163570)). Qed.
Lemma lem3163573 : term494 = term496.
Proof. exact (MK_COMB (@lem3163572) (@lem3163567)). Qed.
Lemma lem3163574 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3163576 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163577 : term188 = term189.
Proof. exact (@lem3163576 (NUMERAL 0) term2). Qed.
Lemma lem3163578 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163579 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163580 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163579 h1) (fun h1 : term189 = True => @lem3163578)). Qed.
Lemma lem3163581 : term189 = True.
Proof. exact (EQ_MP (@lem3163580) (@lem3163578)). Qed.
Lemma lem3163582 : term188 = True.
Proof. exact (TRANS (@lem3163577) (@lem3163581)). Qed.
Lemma lem3163583 : True = term188.
Proof. exact (SYM (@lem3163582)). Qed.
Lemma lem3163584 : term188.
Proof. exact (EQ_MP (@lem3163583) (@lem0)). Qed.
Lemma lem3163585 : term498.
Proof. exact (@lem3163574 (@lem3163584)). Qed.
Lemma lem3163587 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163588 : term188 = term189.
Proof. exact (@lem3163587 (NUMERAL 0) term2). Qed.
Lemma lem3163589 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163590 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163591 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163590 h1) (fun h1 : term189 = True => @lem3163589)). Qed.
Lemma lem3163592 : term189 = True.
Proof. exact (EQ_MP (@lem3163591) (@lem3163589)). Qed.
Lemma lem3163593 : term188 = True.
Proof. exact (TRANS (@lem3163588) (@lem3163592)). Qed.
Lemma lem3163594 : True = term188.
Proof. exact (SYM (@lem3163593)). Qed.
Lemma lem3163595 : term188.
Proof. exact (EQ_MP (@lem3163594) (@lem0)). Qed.
Lemma lem3163596 : term496 = term499.
Proof. exact (@lem3163585 (@lem3163595)). Qed.
Lemma lem3163598 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163599 : term236 = term239.
Proof. exact (@lem3163598 term2 term2). Qed.
Lemma lem3163600 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163601 : term172 = term2.
Proof. exact (EQ_MP (@lem3163600) (@lem940073)). Qed.
Lemma lem3163602 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163603 : term170 = term93.
Proof. exact (MK_COMB (@lem3163602) (@lem3163601)). Qed.
Lemma lem3163604 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163605 : term239 = term160.
Proof. exact (MK_COMB (@lem3163604) (@lem3163603)). Qed.
Lemma lem3163606 : term236 = term160.
Proof. exact (TRANS (@lem3163599) (@lem3163605)). Qed.
Lemma lem3163608 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163609 : term275 = term79.
Proof. exact (@lem3163608 term2). Qed.
Lemma lem3163610 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3163611 : term500 = term81.
Proof. exact (MK_COMB (@lem3163610) (@lem3163609)). Qed.
Lemma lem3163612 : term499 = term494.
Proof. exact (MK_COMB (@lem3163611) (@lem3163606)). Qed.
Lemma lem3163614 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3163615 : term494 = term503.
Proof. exact (@lem3163614 (NUMERAL 0) term2). Qed.
Lemma lem3163616 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163617 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3163618 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163617 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3163616)). Qed.
Lemma lem3163619 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3163618) (@lem3163616)). Qed.
Lemma lem3163620 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3163621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3163622 : term504 = (and True).
Proof. exact (MK_COMB (@lem3163621) (@lem3163620)). Qed.
Lemma lem3163623 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3163622) (@lem3163619)). Qed.
Lemma lem3163625 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3163626 : term503 = False.
Proof. exact (TRANS (@lem3163623) (@lem3163625)). Qed.
Lemma lem3163627 : term494 = False.
Proof. exact (TRANS (@lem3163615) (@lem3163626)). Qed.
Lemma lem3163628 : term499 = False.
Proof. exact (TRANS (@lem3163612) (@lem3163627)). Qed.
Lemma lem3163629 : term496 = False.
Proof. exact (TRANS (@lem3163596) (@lem3163628)). Qed.
Lemma lem3163630 : term494 = False.
Proof. exact (TRANS (@lem3163573) (@lem3163629)). Qed.
Lemma lem3163631 : term493 = False.
Proof. exact (TRANS (@lem3163564) (@lem3163630)). Qed.
Lemma lem3163632 (_32603 : int) (h1 : term602 _32603) : False.
Proof. exact (EQ_MP (@lem3163631) (@lem3163561 _32603 h1)). Qed.
Lemma lem3163633 (_32603 : int) (h1 : term382 _32603) : False.
Proof. exact (or_elim (@lem3163054 _32603 h1) (fun h0 : term594 _32603 => @lem3163343 _32603 h0) (fun h0 : term602 _32603 => @lem3163632 _32603 h0)). Qed.
Lemma lem3163634 (_32603 : int) (h1 : term378 _32603) : term378 _32603.
Proof. exact (h1). Qed.
Lemma lem3163635 (_32603 : int) (h1 : term603 _32603) : term603 _32603.
Proof. exact (h1). Qed.
Lemma lem3163636 (_32603 : int) (h1 : term603 _32603) : term379 _32603.
Proof. exact (proj2 (@lem3163635 _32603 h1)). Qed.
Lemma lem3163638 (_32603 : int) (h1 : term603 _32603) : (term252 _32603) = term79.
Proof. exact (proj2 (@lem3163636 _32603 h1)). Qed.
Lemma lem3163639 (_32603 : int) (h1 : term603 _32603) : term325 _32603.
Proof. exact (proj1 (@lem3163636 _32603 h1)). Qed.
Lemma lem3163640 (_32603 : int) (h1 : term603 _32603) : term230 _32603.
Proof. exact (proj2 (@lem3163639 _32603 h1)). Qed.
Lemma lem3163643 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3163644 : term433 = term188.
Proof. exact (@lem3163643 term79 term93). Qed.
Lemma lem3163646 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163647 : term93 = term182.
Proof. exact (@lem3163646 term2). Qed.
Lemma lem3163649 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163650 : term79 = term157.
Proof. exact (@lem3163649 (NUMERAL 0)). Qed.
Lemma lem3163651 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3163652 : term434 = term435.
Proof. exact (MK_COMB (@lem3163651) (@lem3163650)). Qed.
Lemma lem3163653 : term188 = term436.
Proof. exact (MK_COMB (@lem3163652) (@lem3163647)). Qed.
Lemma lem3163654 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3163656 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163657 : term188 = term189.
Proof. exact (@lem3163656 (NUMERAL 0) term2). Qed.
Lemma lem3163658 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163659 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163660 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163659 h1) (fun h1 : term189 = True => @lem3163658)). Qed.
Lemma lem3163661 : term189 = True.
Proof. exact (EQ_MP (@lem3163660) (@lem3163658)). Qed.
Lemma lem3163662 : term188 = True.
Proof. exact (TRANS (@lem3163657) (@lem3163661)). Qed.
Lemma lem3163663 : True = term188.
Proof. exact (SYM (@lem3163662)). Qed.
Lemma lem3163664 : term188.
Proof. exact (EQ_MP (@lem3163663) (@lem0)). Qed.
Lemma lem3163665 : term438.
Proof. exact (@lem3163654 (@lem3163664)). Qed.
Lemma lem3163667 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163668 : term188 = term189.
Proof. exact (@lem3163667 (NUMERAL 0) term2). Qed.
Lemma lem3163669 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163670 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163671 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163670 h1) (fun h1 : term189 = True => @lem3163669)). Qed.
Lemma lem3163672 : term189 = True.
Proof. exact (EQ_MP (@lem3163671) (@lem3163669)). Qed.
Lemma lem3163673 : term188 = True.
Proof. exact (TRANS (@lem3163668) (@lem3163672)). Qed.
Lemma lem3163674 : True = term188.
Proof. exact (SYM (@lem3163673)). Qed.
Lemma lem3163675 : term188.
Proof. exact (EQ_MP (@lem3163674) (@lem0)). Qed.
Lemma lem3163676 : term436 = term439.
Proof. exact (@lem3163665 (@lem3163675)). Qed.
Lemma lem3163678 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163679 : term169 = term170.
Proof. exact (@lem3163678 term2 term2). Qed.
Lemma lem3163680 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163681 : term172 = term2.
Proof. exact (EQ_MP (@lem3163680) (@lem940073)). Qed.
Lemma lem3163682 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163683 : term170 = term93.
Proof. exact (MK_COMB (@lem3163682) (@lem3163681)). Qed.
Lemma lem3163684 : term169 = term93.
Proof. exact (TRANS (@lem3163679) (@lem3163683)). Qed.
Lemma lem3163686 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163687 : term275 = term79.
Proof. exact (@lem3163686 term2). Qed.
Lemma lem3163688 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3163689 : term440 = term434.
Proof. exact (MK_COMB (@lem3163688) (@lem3163687)). Qed.
Lemma lem3163690 : term439 = term188.
Proof. exact (MK_COMB (@lem3163689) (@lem3163684)). Qed.
Lemma lem3163692 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163693 : term188 = term189.
Proof. exact (@lem3163692 (NUMERAL 0) term2). Qed.
Lemma lem3163694 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163695 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163696 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163695 h1) (fun h1 : term189 = True => @lem3163694)). Qed.
Lemma lem3163697 : term189 = True.
Proof. exact (EQ_MP (@lem3163696) (@lem3163694)). Qed.
Lemma lem3163698 : term188 = True.
Proof. exact (TRANS (@lem3163693) (@lem3163697)). Qed.
Lemma lem3163699 : term439 = True.
Proof. exact (TRANS (@lem3163690) (@lem3163698)). Qed.
Lemma lem3163700 : term436 = True.
Proof. exact (TRANS (@lem3163676) (@lem3163699)). Qed.
Lemma lem3163701 : term188 = True.
Proof. exact (TRANS (@lem3163653) (@lem3163700)). Qed.
Lemma lem3163702 : term433 = True.
Proof. exact (TRANS (@lem3163644) (@lem3163701)). Qed.
Lemma lem3163703 : True = term433.
Proof. exact (SYM (@lem3163702)). Qed.
Lemma lem3163704 : term433.
Proof. exact (EQ_MP (@lem3163703) (@lem0)). Qed.
Lemma lem3163705 (_32603 : int) (h1 : term603 _32603) : term441 _32603.
Proof. exact (conj (@lem3163704) (@lem3163640 _32603 h1)). Qed.
Lemma lem3163707 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3163708 (_32603 : int) : term443 _32603.
Proof. exact (@lem3163707 term93 (term227 _32603)). Qed.
Lemma lem3163709 (_32603 : int) (h1 : term603 _32603) : term444 _32603.
Proof. exact (@lem3163708 _32603 (@lem3163705 _32603 h1)). Qed.
Lemma lem3163710 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3163711 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3163712 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3163711) (@lem3163710 _32603)). Qed.
Lemma lem3163713 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163714 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3163712 _32603) (@lem3163713)). Qed.
Lemma lem3163715 (_32603 : int) (h1 : term603 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3163714 _32603) (@lem3163709 _32603 h1)). Qed.
Lemma lem3163717 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3163718 (_32603 : int) : term579 _32603.
Proof. exact (@lem3163717 (term252 _32603)). Qed.
Lemma lem3163719 (_32603 : int) (h1 : term603 _32603) : term580 _32603.
Proof. exact (@lem3163718 _32603 (@lem3163638 _32603 h1)). Qed.
Lemma lem3163720 (_32603 : int) (h1 : term603 _32603) : term581 _32603.
Proof. exact (@lem3163719 _32603 h1 term160). Qed.
Lemma lem3163721 (_32603 : int) : (term581 _32603) = ((term582 _32603) = term79).
Proof. exact (eq_refl (term581 _32603)). Qed.
Lemma lem3163722 (_32603 : int) (h1 : term603 _32603) : (term582 _32603) = term79.
Proof. exact (EQ_MP (@lem3163721 _32603) (@lem3163720 _32603 h1)). Qed.
Lemma lem3163723 (_32603 : int) : (term582 _32603) = (term583 _32603).
Proof. exact (@lem1982781 (real_of_int _32603) term160 term160). Qed.
Lemma lem3163725 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163726 : term160 = term161.
Proof. exact (@lem3163725 term2). Qed.
Lemma lem3163728 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163729 : term160 = term161.
Proof. exact (@lem3163728 term2). Qed.
Lemma lem3163730 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163731 : term162 = term163.
Proof. exact (MK_COMB (@lem3163730) (@lem3163729)). Qed.
Lemma lem3163732 : term584 = term585.
Proof. exact (MK_COMB (@lem3163731) (@lem3163726)). Qed.
Lemma lem3163733 : term585 = term586.
Proof. exact (@lem1981613 term160 term160 term93 term93). Qed.
Lemma lem3163735 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163736 : term169 = term170.
Proof. exact (@lem3163735 term2 term2). Qed.
Lemma lem3163737 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163738 : term172 = term2.
Proof. exact (EQ_MP (@lem3163737) (@lem940073)). Qed.
Lemma lem3163739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163740 : term170 = term93.
Proof. exact (MK_COMB (@lem3163739) (@lem3163738)). Qed.
Lemma lem3163741 : term169 = term93.
Proof. exact (TRANS (@lem3163736) (@lem3163740)). Qed.
Lemma lem3163743 (m : nat) (n : nat) : (term587 m n) = (term168 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3163744 : term584 = term170.
Proof. exact (@lem3163743 term2 term2). Qed.
Lemma lem3163745 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163746 : term172 = term2.
Proof. exact (EQ_MP (@lem3163745) (@lem940073)). Qed.
Lemma lem3163747 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163748 : term170 = term93.
Proof. exact (MK_COMB (@lem3163747) (@lem3163746)). Qed.
Lemma lem3163749 : term584 = term93.
Proof. exact (TRANS (@lem3163744) (@lem3163748)). Qed.
Lemma lem3163750 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3163751 : term588 = term589.
Proof. exact (MK_COMB (@lem3163750) (@lem3163749)). Qed.
Lemma lem3163752 : term586 = term182.
Proof. exact (MK_COMB (@lem3163751) (@lem3163741)). Qed.
Lemma lem3163753 : term585 = term182.
Proof. exact (TRANS (@lem3163733) (@lem3163752)). Qed.
Lemma lem3163754 : term584 = term182.
Proof. exact (TRANS (@lem3163732) (@lem3163753)). Qed.
Lemma lem3163756 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3163757 : term182 = term93.
Proof. exact (@lem3163756 term93). Qed.
Lemma lem3163758 : term584 = term93.
Proof. exact (TRANS (@lem3163754) (@lem3163757)). Qed.
Lemma lem3163761 (_32603 : int) : (term242 _32603) = (term242 _32603).
Proof. exact (eq_refl (term242 _32603)). Qed.
Lemma lem3163762 (_32603 : int) : (term583 _32603) = (term291 _32603).
Proof. exact (MK_COMB (@lem3163761 _32603) (@lem3163758)). Qed.
Lemma lem3163763 (_32603 : int) : (term582 _32603) = (term291 _32603).
Proof. exact (TRANS (@lem3163723 _32603) (@lem3163762 _32603)). Qed.
Lemma lem3163764 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3163765 (_32603 : int) : (term590 _32603) = (term591 _32603).
Proof. exact (MK_COMB (@lem3163764) (@lem3163763 _32603)). Qed.
Lemma lem3163766 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3163767 (_32603 : int) : ((term582 _32603) = term79) = ((term291 _32603) = term79).
Proof. exact (MK_COMB (@lem3163765 _32603) (@lem3163766)). Qed.
Lemma lem3163768 (_32603 : int) (h1 : term603 _32603) : (term291 _32603) = term79.
Proof. exact (EQ_MP (@lem3163767 _32603) (@lem3163722 _32603 h1)). Qed.
Lemma lem3163769 (_32603 : int) (h1 : term603 _32603) : term592 _32603.
Proof. exact (conj (@lem3163768 _32603 h1) (@lem3163715 _32603 h1)). Qed.
Lemma lem3163771 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3163772 (_32603 : int) : term593 _32603.
Proof. exact (@lem3163771 (term291 _32603) (term227 _32603)). Qed.
Lemma lem3163773 (_32603 : int) (h1 : term603 _32603) : term455 _32603.
Proof. exact (@lem3163772 _32603 (@lem3163769 _32603 h1)). Qed.
Lemma lem3163774 (_32603 : int) : (term456 _32603) = (term457 _32603).
Proof. exact (@lem1982753 (term263 _32603) (real_of_int _32603) term93 term223). Qed.
Lemma lem3163775 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3163777 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163778 : term93 = term182.
Proof. exact (@lem3163777 term2). Qed.
Lemma lem3163780 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163781 : term160 = term161.
Proof. exact (@lem3163780 term2). Qed.
Lemma lem3163782 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163783 : term460 = term461.
Proof. exact (MK_COMB (@lem3163782) (@lem3163781)). Qed.
Lemma lem3163784 : term462 = term463.
Proof. exact (MK_COMB (@lem3163783) (@lem3163778)). Qed.
Lemma lem3163785 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3163787 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163788 : term188 = term189.
Proof. exact (@lem3163787 (NUMERAL 0) term2). Qed.
Lemma lem3163789 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163790 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163791 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163790 h1) (fun h1 : term189 = True => @lem3163789)). Qed.
Lemma lem3163792 : term189 = True.
Proof. exact (EQ_MP (@lem3163791) (@lem3163789)). Qed.
Lemma lem3163793 : term188 = True.
Proof. exact (TRANS (@lem3163788) (@lem3163792)). Qed.
Lemma lem3163794 : True = term188.
Proof. exact (SYM (@lem3163793)). Qed.
Lemma lem3163795 : term188.
Proof. exact (EQ_MP (@lem3163794) (@lem0)). Qed.
Lemma lem3163796 : term465.
Proof. exact (@lem3163785 (@lem3163795)). Qed.
Lemma lem3163798 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163799 : term188 = term189.
Proof. exact (@lem3163798 (NUMERAL 0) term2). Qed.
Lemma lem3163800 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163801 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163802 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163801 h1) (fun h1 : term189 = True => @lem3163800)). Qed.
Lemma lem3163803 : term189 = True.
Proof. exact (EQ_MP (@lem3163802) (@lem3163800)). Qed.
Lemma lem3163804 : term188 = True.
Proof. exact (TRANS (@lem3163799) (@lem3163803)). Qed.
Lemma lem3163805 : True = term188.
Proof. exact (SYM (@lem3163804)). Qed.
Lemma lem3163806 : term188.
Proof. exact (EQ_MP (@lem3163805) (@lem0)). Qed.
Lemma lem3163807 : term466.
Proof. exact (@lem3163796 (@lem3163806)). Qed.
Lemma lem3163809 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163810 : term188 = term189.
Proof. exact (@lem3163809 (NUMERAL 0) term2). Qed.
Lemma lem3163811 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163812 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163813 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163812 h1) (fun h1 : term189 = True => @lem3163811)). Qed.
Lemma lem3163814 : term189 = True.
Proof. exact (EQ_MP (@lem3163813) (@lem3163811)). Qed.
Lemma lem3163815 : term188 = True.
Proof. exact (TRANS (@lem3163810) (@lem3163814)). Qed.
Lemma lem3163816 : True = term188.
Proof. exact (SYM (@lem3163815)). Qed.
Lemma lem3163817 : term188.
Proof. exact (EQ_MP (@lem3163816) (@lem0)). Qed.
Lemma lem3163818 : term467.
Proof. exact (@lem3163807 (@lem3163817)). Qed.
Lemma lem3163820 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163821 : term169 = term170.
Proof. exact (@lem3163820 term2 term2). Qed.
Lemma lem3163822 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163823 : term172 = term2.
Proof. exact (EQ_MP (@lem3163822) (@lem940073)). Qed.
Lemma lem3163824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163825 : term170 = term93.
Proof. exact (MK_COMB (@lem3163824) (@lem3163823)). Qed.
Lemma lem3163826 : term169 = term93.
Proof. exact (TRANS (@lem3163821) (@lem3163825)). Qed.
Lemma lem3163828 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163829 : term236 = term239.
Proof. exact (@lem3163828 term2 term2). Qed.
Lemma lem3163830 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163831 : term172 = term2.
Proof. exact (EQ_MP (@lem3163830) (@lem940073)). Qed.
Lemma lem3163832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163833 : term170 = term93.
Proof. exact (MK_COMB (@lem3163832) (@lem3163831)). Qed.
Lemma lem3163834 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163835 : term239 = term160.
Proof. exact (MK_COMB (@lem3163834) (@lem3163833)). Qed.
Lemma lem3163836 : term236 = term160.
Proof. exact (TRANS (@lem3163829) (@lem3163835)). Qed.
Lemma lem3163837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163838 : term468 = term460.
Proof. exact (MK_COMB (@lem3163837) (@lem3163836)). Qed.
Lemma lem3163839 : term469 = term462.
Proof. exact (MK_COMB (@lem3163838) (@lem3163826)). Qed.
Lemma lem3163841 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3163842 : term462 = term79.
Proof. exact (@lem3163841 term2). Qed.
Lemma lem3163843 : term469 = term79.
Proof. exact (TRANS (@lem3163839) (@lem3163842)). Qed.
Lemma lem3163844 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163845 : term471 = term273.
Proof. exact (MK_COMB (@lem3163844) (@lem3163843)). Qed.
Lemma lem3163846 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3163847 : term472 = term275.
Proof. exact (MK_COMB (@lem3163845) (@lem3163846)). Qed.
Lemma lem3163849 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163850 : term275 = term79.
Proof. exact (@lem3163849 term2). Qed.
Lemma lem3163851 : term472 = term79.
Proof. exact (TRANS (@lem3163847) (@lem3163850)). Qed.
Lemma lem3163853 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163854 : term169 = term170.
Proof. exact (@lem3163853 term2 term2). Qed.
Lemma lem3163855 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163856 : term172 = term2.
Proof. exact (EQ_MP (@lem3163855) (@lem940073)). Qed.
Lemma lem3163857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163858 : term170 = term93.
Proof. exact (MK_COMB (@lem3163857) (@lem3163856)). Qed.
Lemma lem3163859 : term169 = term93.
Proof. exact (TRANS (@lem3163854) (@lem3163858)). Qed.
Lemma lem3163860 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3163861 : term277 = term275.
Proof. exact (MK_COMB (@lem3163860) (@lem3163859)). Qed.
Lemma lem3163863 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3163864 : term275 = term79.
Proof. exact (@lem3163863 term2). Qed.
Lemma lem3163865 : term277 = term79.
Proof. exact (TRANS (@lem3163861) (@lem3163864)). Qed.
Lemma lem3163866 : term79 = term277.
Proof. exact (SYM (@lem3163865)). Qed.
Lemma lem3163867 : term472 = term277.
Proof. exact (TRANS (@lem3163851) (@lem3163866)). Qed.
Lemma lem3163868 : term463 = term157.
Proof. exact (@lem3163818 (@lem3163867)). Qed.
Lemma lem3163869 : term462 = term157.
Proof. exact (TRANS (@lem3163784) (@lem3163868)). Qed.
Lemma lem3163871 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3163872 : term157 = term79.
Proof. exact (@lem3163871 term79). Qed.
Lemma lem3163873 : term462 = term79.
Proof. exact (TRANS (@lem3163869) (@lem3163872)). Qed.
Lemma lem3163874 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163875 : term473 = term273.
Proof. exact (MK_COMB (@lem3163874) (@lem3163873)). Qed.
Lemma lem3163876 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3163877 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3163875) (@lem3163876 _32603)). Qed.
Lemma lem3163878 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3163775 _32603) (@lem3163877 _32603)). Qed.
Lemma lem3163879 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3163880 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3163878 _32603) (@lem3163879 _32603)). Qed.
Lemma lem3163881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163882 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3163881) (@lem3163880 _32603)). Qed.
Lemma lem3163884 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3163885 : term223 = term226.
Proof. exact (@lem3163884 term200). Qed.
Lemma lem3163887 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3163888 : term93 = term182.
Proof. exact (@lem3163887 term2). Qed.
Lemma lem3163889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163890 : term95 = term183.
Proof. exact (MK_COMB (@lem3163889) (@lem3163888)). Qed.
Lemma lem3163891 : term476 = term477.
Proof. exact (MK_COMB (@lem3163890) (@lem3163885)). Qed.
Lemma lem3163892 : term478.
Proof. exact (@lem1981473 term93 term93 term223 term93 term160 term93). Qed.
Lemma lem3163894 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163895 : term188 = term189.
Proof. exact (@lem3163894 (NUMERAL 0) term2). Qed.
Lemma lem3163896 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163897 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163898 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163897 h1) (fun h1 : term189 = True => @lem3163896)). Qed.
Lemma lem3163899 : term189 = True.
Proof. exact (EQ_MP (@lem3163898) (@lem3163896)). Qed.
Lemma lem3163900 : term188 = True.
Proof. exact (TRANS (@lem3163895) (@lem3163899)). Qed.
Lemma lem3163901 : True = term188.
Proof. exact (SYM (@lem3163900)). Qed.
Lemma lem3163902 : term188.
Proof. exact (EQ_MP (@lem3163901) (@lem0)). Qed.
Lemma lem3163903 : term479.
Proof. exact (@lem3163892 (@lem3163902)). Qed.
Lemma lem3163905 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163906 : term188 = term189.
Proof. exact (@lem3163905 (NUMERAL 0) term2). Qed.
Lemma lem3163907 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163908 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163909 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163908 h1) (fun h1 : term189 = True => @lem3163907)). Qed.
Lemma lem3163910 : term189 = True.
Proof. exact (EQ_MP (@lem3163909) (@lem3163907)). Qed.
Lemma lem3163911 : term188 = True.
Proof. exact (TRANS (@lem3163906) (@lem3163910)). Qed.
Lemma lem3163912 : True = term188.
Proof. exact (SYM (@lem3163911)). Qed.
Lemma lem3163913 : term188.
Proof. exact (EQ_MP (@lem3163912) (@lem0)). Qed.
Lemma lem3163914 : term480.
Proof. exact (@lem3163903 (@lem3163913)). Qed.
Lemma lem3163916 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3163917 : term188 = term189.
Proof. exact (@lem3163916 (NUMERAL 0) term2). Qed.
Lemma lem3163918 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3163919 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3163920 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3163919 h1) (fun h1 : term189 = True => @lem3163918)). Qed.
Lemma lem3163921 : term189 = True.
Proof. exact (EQ_MP (@lem3163920) (@lem3163918)). Qed.
Lemma lem3163922 : term188 = True.
Proof. exact (TRANS (@lem3163917) (@lem3163921)). Qed.
Lemma lem3163923 : True = term188.
Proof. exact (SYM (@lem3163922)). Qed.
Lemma lem3163924 : term188.
Proof. exact (EQ_MP (@lem3163923) (@lem0)). Qed.
Lemma lem3163925 : term481.
Proof. exact (@lem3163914 (@lem3163924)). Qed.
Lemma lem3163927 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163928 : term482 = term483.
Proof. exact (@lem3163927 term200 term2). Qed.
Lemma lem3163929 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3163930 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3163931 : term207 = term200.
Proof. exact (EQ_MP (@lem3163930) (@lem3163929)). Qed.
Lemma lem3163932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163933 : term205 = term186.
Proof. exact (MK_COMB (@lem3163932) (@lem3163931)). Qed.
Lemma lem3163934 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163935 : term483 = term223.
Proof. exact (MK_COMB (@lem3163934) (@lem3163933)). Qed.
Lemma lem3163936 : term482 = term223.
Proof. exact (TRANS (@lem3163928) (@lem3163935)). Qed.
Lemma lem3163938 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163939 : term169 = term170.
Proof. exact (@lem3163938 term2 term2). Qed.
Lemma lem3163940 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163941 : term172 = term2.
Proof. exact (EQ_MP (@lem3163940) (@lem940073)). Qed.
Lemma lem3163942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163943 : term170 = term93.
Proof. exact (MK_COMB (@lem3163942) (@lem3163941)). Qed.
Lemma lem3163944 : term169 = term93.
Proof. exact (TRANS (@lem3163939) (@lem3163943)). Qed.
Lemma lem3163945 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3163946 : term194 = term95.
Proof. exact (MK_COMB (@lem3163945) (@lem3163944)). Qed.
Lemma lem3163947 : term484 = term476.
Proof. exact (MK_COMB (@lem3163946) (@lem3163936)). Qed.
Lemma lem3163950 : term485 = term160.
Proof. exact (@lem1367771 term2 term2). Qed.
Lemma lem3163951 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3163952 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3163953 : term199 = term200.
Proof. exact (EQ_MP (@lem3163952) (@lem3163951)). Qed.
Lemma lem3163954 : term200 = term199.
Proof. exact (SYM (@lem3163953)). Qed.
Lemma lem3163955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163956 : term186 = term196.
Proof. exact (MK_COMB (@lem3163955) (@lem3163954)). Qed.
Lemma lem3163957 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163958 : term223 = term486.
Proof. exact (MK_COMB (@lem3163957) (@lem3163956)). Qed.
Lemma lem3163959 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3163960 : term476 = term485.
Proof. exact (MK_COMB (@lem3163959) (@lem3163958)). Qed.
Lemma lem3163961 : term476 = term160.
Proof. exact (TRANS (@lem3163960) (@lem3163950)). Qed.
Lemma lem3163962 : term484 = term160.
Proof. exact (TRANS (@lem3163947) (@lem3163961)). Qed.
Lemma lem3163963 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3163964 : term487 = term162.
Proof. exact (MK_COMB (@lem3163963) (@lem3163962)). Qed.
Lemma lem3163965 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3163966 : term488 = term236.
Proof. exact (MK_COMB (@lem3163964) (@lem3163965)). Qed.
Lemma lem3163968 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163969 : term236 = term239.
Proof. exact (@lem3163968 term2 term2). Qed.
Lemma lem3163970 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163971 : term172 = term2.
Proof. exact (EQ_MP (@lem3163970) (@lem940073)). Qed.
Lemma lem3163972 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163973 : term170 = term93.
Proof. exact (MK_COMB (@lem3163972) (@lem3163971)). Qed.
Lemma lem3163974 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163975 : term239 = term160.
Proof. exact (MK_COMB (@lem3163974) (@lem3163973)). Qed.
Lemma lem3163976 : term236 = term160.
Proof. exact (TRANS (@lem3163969) (@lem3163975)). Qed.
Lemma lem3163977 : term488 = term160.
Proof. exact (TRANS (@lem3163966) (@lem3163976)). Qed.
Lemma lem3163979 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3163980 : term169 = term170.
Proof. exact (@lem3163979 term2 term2). Qed.
Lemma lem3163981 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163982 : term172 = term2.
Proof. exact (EQ_MP (@lem3163981) (@lem940073)). Qed.
Lemma lem3163983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163984 : term170 = term93.
Proof. exact (MK_COMB (@lem3163983) (@lem3163982)). Qed.
Lemma lem3163985 : term169 = term93.
Proof. exact (TRANS (@lem3163980) (@lem3163984)). Qed.
Lemma lem3163986 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem3163987 : term489 = term236.
Proof. exact (MK_COMB (@lem3163986) (@lem3163985)). Qed.
Lemma lem3163989 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3163990 : term236 = term239.
Proof. exact (@lem3163989 term2 term2). Qed.
Lemma lem3163991 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3163992 : term172 = term2.
Proof. exact (EQ_MP (@lem3163991) (@lem940073)). Qed.
Lemma lem3163993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3163994 : term170 = term93.
Proof. exact (MK_COMB (@lem3163993) (@lem3163992)). Qed.
Lemma lem3163995 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3163996 : term239 = term160.
Proof. exact (MK_COMB (@lem3163995) (@lem3163994)). Qed.
Lemma lem3163997 : term236 = term160.
Proof. exact (TRANS (@lem3163990) (@lem3163996)). Qed.
Lemma lem3163998 : term489 = term160.
Proof. exact (TRANS (@lem3163987) (@lem3163997)). Qed.
Lemma lem3163999 : term160 = term489.
Proof. exact (SYM (@lem3163998)). Qed.
Lemma lem3164000 : term488 = term489.
Proof. exact (TRANS (@lem3163977) (@lem3163999)). Qed.
Lemma lem3164001 : term477 = term161.
Proof. exact (@lem3163925 (@lem3164000)). Qed.
Lemma lem3164002 : term476 = term161.
Proof. exact (TRANS (@lem3163891) (@lem3164001)). Qed.
Lemma lem3164004 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3164005 : term161 = term160.
Proof. exact (@lem3164004 term160). Qed.
Lemma lem3164006 : term476 = term160.
Proof. exact (TRANS (@lem3164002) (@lem3164005)). Qed.
Lemma lem3164007 (_32603 : int) : (term457 _32603) = term490.
Proof. exact (MK_COMB (@lem3163882 _32603) (@lem3164006)). Qed.
Lemma lem3164008 (_32603 : int) : (term456 _32603) = term490.
Proof. exact (TRANS (@lem3163774 _32603) (@lem3164007 _32603)). Qed.
Lemma lem3164009 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3164010 (_32603 : int) : (term456 _32603) = term160.
Proof. exact (TRANS (@lem3164008 _32603) (@lem3164009)). Qed.
Lemma lem3164011 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3164012 (_32603 : int) : (term491 _32603) = term492.
Proof. exact (MK_COMB (@lem3164011) (@lem3164010 _32603)). Qed.
Lemma lem3164013 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3164014 (_32603 : int) : (term455 _32603) = term493.
Proof. exact (MK_COMB (@lem3164012 _32603) (@lem3164013)). Qed.
Lemma lem3164015 (_32603 : int) (h1 : term603 _32603) : term493.
Proof. exact (EQ_MP (@lem3164014 _32603) (@lem3163773 _32603 h1)). Qed.
Lemma lem3164017 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3164018 : term493 = term494.
Proof. exact (@lem3164017 term79 term160). Qed.
Lemma lem3164020 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164021 : term160 = term161.
Proof. exact (@lem3164020 term2). Qed.
Lemma lem3164023 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164024 : term79 = term157.
Proof. exact (@lem3164023 (NUMERAL 0)). Qed.
Lemma lem3164025 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164026 : term81 = term495.
Proof. exact (MK_COMB (@lem3164025) (@lem3164024)). Qed.
Lemma lem3164027 : term494 = term496.
Proof. exact (MK_COMB (@lem3164026) (@lem3164021)). Qed.
Lemma lem3164028 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3164030 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164031 : term188 = term189.
Proof. exact (@lem3164030 (NUMERAL 0) term2). Qed.
Lemma lem3164032 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164033 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164034 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164033 h1) (fun h1 : term189 = True => @lem3164032)). Qed.
Lemma lem3164035 : term189 = True.
Proof. exact (EQ_MP (@lem3164034) (@lem3164032)). Qed.
Lemma lem3164036 : term188 = True.
Proof. exact (TRANS (@lem3164031) (@lem3164035)). Qed.
Lemma lem3164037 : True = term188.
Proof. exact (SYM (@lem3164036)). Qed.
Lemma lem3164038 : term188.
Proof. exact (EQ_MP (@lem3164037) (@lem0)). Qed.
Lemma lem3164039 : term498.
Proof. exact (@lem3164028 (@lem3164038)). Qed.
Lemma lem3164041 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164042 : term188 = term189.
Proof. exact (@lem3164041 (NUMERAL 0) term2). Qed.
Lemma lem3164043 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164044 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164045 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164044 h1) (fun h1 : term189 = True => @lem3164043)). Qed.
Lemma lem3164046 : term189 = True.
Proof. exact (EQ_MP (@lem3164045) (@lem3164043)). Qed.
Lemma lem3164047 : term188 = True.
Proof. exact (TRANS (@lem3164042) (@lem3164046)). Qed.
Lemma lem3164048 : True = term188.
Proof. exact (SYM (@lem3164047)). Qed.
Lemma lem3164049 : term188.
Proof. exact (EQ_MP (@lem3164048) (@lem0)). Qed.
Lemma lem3164050 : term496 = term499.
Proof. exact (@lem3164039 (@lem3164049)). Qed.
Lemma lem3164052 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3164053 : term236 = term239.
Proof. exact (@lem3164052 term2 term2). Qed.
Lemma lem3164054 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164055 : term172 = term2.
Proof. exact (EQ_MP (@lem3164054) (@lem940073)). Qed.
Lemma lem3164056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164057 : term170 = term93.
Proof. exact (MK_COMB (@lem3164056) (@lem3164055)). Qed.
Lemma lem3164058 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164059 : term239 = term160.
Proof. exact (MK_COMB (@lem3164058) (@lem3164057)). Qed.
Lemma lem3164060 : term236 = term160.
Proof. exact (TRANS (@lem3164053) (@lem3164059)). Qed.
Lemma lem3164062 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3164063 : term275 = term79.
Proof. exact (@lem3164062 term2). Qed.
Lemma lem3164064 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164065 : term500 = term81.
Proof. exact (MK_COMB (@lem3164064) (@lem3164063)). Qed.
Lemma lem3164066 : term499 = term494.
Proof. exact (MK_COMB (@lem3164065) (@lem3164060)). Qed.
Lemma lem3164068 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3164069 : term494 = term503.
Proof. exact (@lem3164068 (NUMERAL 0) term2). Qed.
Lemma lem3164070 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164071 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3164072 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164071 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3164070)). Qed.
Lemma lem3164073 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3164072) (@lem3164070)). Qed.
Lemma lem3164074 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3164075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164076 : term504 = (and True).
Proof. exact (MK_COMB (@lem3164075) (@lem3164074)). Qed.
Lemma lem3164077 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3164076) (@lem3164073)). Qed.
Lemma lem3164079 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3164080 : term503 = False.
Proof. exact (TRANS (@lem3164077) (@lem3164079)). Qed.
Lemma lem3164081 : term494 = False.
Proof. exact (TRANS (@lem3164069) (@lem3164080)). Qed.
Lemma lem3164082 : term499 = False.
Proof. exact (TRANS (@lem3164066) (@lem3164081)). Qed.
Lemma lem3164083 : term496 = False.
Proof. exact (TRANS (@lem3164050) (@lem3164082)). Qed.
Lemma lem3164084 : term494 = False.
Proof. exact (TRANS (@lem3164027) (@lem3164083)). Qed.
Lemma lem3164085 : term493 = False.
Proof. exact (TRANS (@lem3164018) (@lem3164084)). Qed.
Lemma lem3164086 (_32603 : int) (h1 : term603 _32603) : False.
Proof. exact (EQ_MP (@lem3164085) (@lem3164015 _32603 h1)). Qed.
Lemma lem3164087 (_32603 : int) (h1 : term604 _32603) : term604 _32603.
Proof. exact (h1). Qed.
Lemma lem3164088 (_32603 : int) (h1 : term604 _32603) : term380 _32603.
Proof. exact (proj2 (@lem3164087 _32603 h1)). Qed.
Lemma lem3164090 (_32603 : int) (h1 : term604 _32603) : (term252 _32603) = term79.
Proof. exact (proj2 (@lem3164088 _32603 h1)). Qed.
Lemma lem3164091 (_32603 : int) (h1 : term604 _32603) : term326 _32603.
Proof. exact (proj1 (@lem3164088 _32603 h1)). Qed.
Lemma lem3164092 (_32603 : int) (h1 : term604 _32603) : term230 _32603.
Proof. exact (proj2 (@lem3164091 _32603 h1)). Qed.
Lemma lem3164095 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3164096 : term433 = term188.
Proof. exact (@lem3164095 term79 term93). Qed.
Lemma lem3164098 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164099 : term93 = term182.
Proof. exact (@lem3164098 term2). Qed.
Lemma lem3164101 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164102 : term79 = term157.
Proof. exact (@lem3164101 (NUMERAL 0)). Qed.
Lemma lem3164103 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3164104 : term434 = term435.
Proof. exact (MK_COMB (@lem3164103) (@lem3164102)). Qed.
Lemma lem3164105 : term188 = term436.
Proof. exact (MK_COMB (@lem3164104) (@lem3164099)). Qed.
Lemma lem3164106 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3164108 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164109 : term188 = term189.
Proof. exact (@lem3164108 (NUMERAL 0) term2). Qed.
Lemma lem3164110 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164111 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164112 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164111 h1) (fun h1 : term189 = True => @lem3164110)). Qed.
Lemma lem3164113 : term189 = True.
Proof. exact (EQ_MP (@lem3164112) (@lem3164110)). Qed.
Lemma lem3164114 : term188 = True.
Proof. exact (TRANS (@lem3164109) (@lem3164113)). Qed.
Lemma lem3164115 : True = term188.
Proof. exact (SYM (@lem3164114)). Qed.
Lemma lem3164116 : term188.
Proof. exact (EQ_MP (@lem3164115) (@lem0)). Qed.
Lemma lem3164117 : term438.
Proof. exact (@lem3164106 (@lem3164116)). Qed.
Lemma lem3164119 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164120 : term188 = term189.
Proof. exact (@lem3164119 (NUMERAL 0) term2). Qed.
Lemma lem3164121 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164122 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164123 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164122 h1) (fun h1 : term189 = True => @lem3164121)). Qed.
Lemma lem3164124 : term189 = True.
Proof. exact (EQ_MP (@lem3164123) (@lem3164121)). Qed.
Lemma lem3164125 : term188 = True.
Proof. exact (TRANS (@lem3164120) (@lem3164124)). Qed.
Lemma lem3164126 : True = term188.
Proof. exact (SYM (@lem3164125)). Qed.
Lemma lem3164127 : term188.
Proof. exact (EQ_MP (@lem3164126) (@lem0)). Qed.
Lemma lem3164128 : term436 = term439.
Proof. exact (@lem3164117 (@lem3164127)). Qed.
Lemma lem3164130 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164131 : term169 = term170.
Proof. exact (@lem3164130 term2 term2). Qed.
Lemma lem3164132 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164133 : term172 = term2.
Proof. exact (EQ_MP (@lem3164132) (@lem940073)). Qed.
Lemma lem3164134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164135 : term170 = term93.
Proof. exact (MK_COMB (@lem3164134) (@lem3164133)). Qed.
Lemma lem3164136 : term169 = term93.
Proof. exact (TRANS (@lem3164131) (@lem3164135)). Qed.
Lemma lem3164138 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3164139 : term275 = term79.
Proof. exact (@lem3164138 term2). Qed.
Lemma lem3164140 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3164141 : term440 = term434.
Proof. exact (MK_COMB (@lem3164140) (@lem3164139)). Qed.
Lemma lem3164142 : term439 = term188.
Proof. exact (MK_COMB (@lem3164141) (@lem3164136)). Qed.
Lemma lem3164144 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164145 : term188 = term189.
Proof. exact (@lem3164144 (NUMERAL 0) term2). Qed.
Lemma lem3164146 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164147 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164148 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164147 h1) (fun h1 : term189 = True => @lem3164146)). Qed.
Lemma lem3164149 : term189 = True.
Proof. exact (EQ_MP (@lem3164148) (@lem3164146)). Qed.
Lemma lem3164150 : term188 = True.
Proof. exact (TRANS (@lem3164145) (@lem3164149)). Qed.
Lemma lem3164151 : term439 = True.
Proof. exact (TRANS (@lem3164142) (@lem3164150)). Qed.
Lemma lem3164152 : term436 = True.
Proof. exact (TRANS (@lem3164128) (@lem3164151)). Qed.
Lemma lem3164153 : term188 = True.
Proof. exact (TRANS (@lem3164105) (@lem3164152)). Qed.
Lemma lem3164154 : term433 = True.
Proof. exact (TRANS (@lem3164096) (@lem3164153)). Qed.
Lemma lem3164155 : True = term433.
Proof. exact (SYM (@lem3164154)). Qed.
Lemma lem3164156 : term433.
Proof. exact (EQ_MP (@lem3164155) (@lem0)). Qed.
Lemma lem3164157 (_32603 : int) (h1 : term604 _32603) : term441 _32603.
Proof. exact (conj (@lem3164156) (@lem3164092 _32603 h1)). Qed.
Lemma lem3164159 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3164160 (_32603 : int) : term443 _32603.
Proof. exact (@lem3164159 term93 (term227 _32603)). Qed.
Lemma lem3164161 (_32603 : int) (h1 : term604 _32603) : term444 _32603.
Proof. exact (@lem3164160 _32603 (@lem3164157 _32603 h1)). Qed.
Lemma lem3164162 (_32603 : int) : (term445 _32603) = (term227 _32603).
Proof. exact (@lem1982733 (term227 _32603)). Qed.
Lemma lem3164163 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3164164 (_32603 : int) : (term446 _32603) = (term229 _32603).
Proof. exact (MK_COMB (@lem3164163) (@lem3164162 _32603)). Qed.
Lemma lem3164165 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3164166 (_32603 : int) : (term444 _32603) = (term230 _32603).
Proof. exact (MK_COMB (@lem3164164 _32603) (@lem3164165)). Qed.
Lemma lem3164167 (_32603 : int) (h1 : term604 _32603) : term230 _32603.
Proof. exact (EQ_MP (@lem3164166 _32603) (@lem3164161 _32603 h1)). Qed.
Lemma lem3164169 (y : real) : term541 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3164170 (_32603 : int) : term579 _32603.
Proof. exact (@lem3164169 (term252 _32603)). Qed.
Lemma lem3164171 (_32603 : int) (h1 : term604 _32603) : term580 _32603.
Proof. exact (@lem3164170 _32603 (@lem3164090 _32603 h1)). Qed.
Lemma lem3164172 (_32603 : int) (h1 : term604 _32603) : term581 _32603.
Proof. exact (@lem3164171 _32603 h1 term160). Qed.
Lemma lem3164173 (_32603 : int) : (term581 _32603) = ((term582 _32603) = term79).
Proof. exact (eq_refl (term581 _32603)). Qed.
Lemma lem3164174 (_32603 : int) (h1 : term604 _32603) : (term582 _32603) = term79.
Proof. exact (EQ_MP (@lem3164173 _32603) (@lem3164172 _32603 h1)). Qed.
Lemma lem3164175 (_32603 : int) : (term582 _32603) = (term583 _32603).
Proof. exact (@lem1982781 (real_of_int _32603) term160 term160). Qed.
Lemma lem3164177 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164178 : term160 = term161.
Proof. exact (@lem3164177 term2). Qed.
Lemma lem3164180 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164181 : term160 = term161.
Proof. exact (@lem3164180 term2). Qed.
Lemma lem3164182 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3164183 : term162 = term163.
Proof. exact (MK_COMB (@lem3164182) (@lem3164181)). Qed.
Lemma lem3164184 : term584 = term585.
Proof. exact (MK_COMB (@lem3164183) (@lem3164178)). Qed.
Lemma lem3164185 : term585 = term586.
Proof. exact (@lem1981613 term160 term160 term93 term93). Qed.
Lemma lem3164187 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164188 : term169 = term170.
Proof. exact (@lem3164187 term2 term2). Qed.
Lemma lem3164189 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164190 : term172 = term2.
Proof. exact (EQ_MP (@lem3164189) (@lem940073)). Qed.
Lemma lem3164191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164192 : term170 = term93.
Proof. exact (MK_COMB (@lem3164191) (@lem3164190)). Qed.
Lemma lem3164193 : term169 = term93.
Proof. exact (TRANS (@lem3164188) (@lem3164192)). Qed.
Lemma lem3164195 (m : nat) (n : nat) : (term587 m n) = (term168 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3164196 : term584 = term170.
Proof. exact (@lem3164195 term2 term2). Qed.
Lemma lem3164197 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164198 : term172 = term2.
Proof. exact (EQ_MP (@lem3164197) (@lem940073)). Qed.
Lemma lem3164199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164200 : term170 = term93.
Proof. exact (MK_COMB (@lem3164199) (@lem3164198)). Qed.
Lemma lem3164201 : term584 = term93.
Proof. exact (TRANS (@lem3164196) (@lem3164200)). Qed.
Lemma lem3164202 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3164203 : term588 = term589.
Proof. exact (MK_COMB (@lem3164202) (@lem3164201)). Qed.
Lemma lem3164204 : term586 = term182.
Proof. exact (MK_COMB (@lem3164203) (@lem3164193)). Qed.
Lemma lem3164205 : term585 = term182.
Proof. exact (TRANS (@lem3164185) (@lem3164204)). Qed.
Lemma lem3164206 : term584 = term182.
Proof. exact (TRANS (@lem3164184) (@lem3164205)). Qed.
Lemma lem3164208 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3164209 : term182 = term93.
Proof. exact (@lem3164208 term93). Qed.
Lemma lem3164210 : term584 = term93.
Proof. exact (TRANS (@lem3164206) (@lem3164209)). Qed.
Lemma lem3164213 (_32603 : int) : (term242 _32603) = (term242 _32603).
Proof. exact (eq_refl (term242 _32603)). Qed.
Lemma lem3164214 (_32603 : int) : (term583 _32603) = (term291 _32603).
Proof. exact (MK_COMB (@lem3164213 _32603) (@lem3164210)). Qed.
Lemma lem3164215 (_32603 : int) : (term582 _32603) = (term291 _32603).
Proof. exact (TRANS (@lem3164175 _32603) (@lem3164214 _32603)). Qed.
Lemma lem3164216 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3164217 (_32603 : int) : (term590 _32603) = (term591 _32603).
Proof. exact (MK_COMB (@lem3164216) (@lem3164215 _32603)). Qed.
Lemma lem3164218 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3164219 (_32603 : int) : ((term582 _32603) = term79) = ((term291 _32603) = term79).
Proof. exact (MK_COMB (@lem3164217 _32603) (@lem3164218)). Qed.
Lemma lem3164220 (_32603 : int) (h1 : term604 _32603) : (term291 _32603) = term79.
Proof. exact (EQ_MP (@lem3164219 _32603) (@lem3164174 _32603 h1)). Qed.
Lemma lem3164221 (_32603 : int) (h1 : term604 _32603) : term592 _32603.
Proof. exact (conj (@lem3164220 _32603 h1) (@lem3164167 _32603 h1)). Qed.
Lemma lem3164223 (x : real) (y : real) : term546 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3164224 (_32603 : int) : term593 _32603.
Proof. exact (@lem3164223 (term291 _32603) (term227 _32603)). Qed.
Lemma lem3164225 (_32603 : int) (h1 : term604 _32603) : term455 _32603.
Proof. exact (@lem3164224 _32603 (@lem3164221 _32603 h1)). Qed.
Lemma lem3164226 (_32603 : int) : (term456 _32603) = (term457 _32603).
Proof. exact (@lem1982753 (term263 _32603) (real_of_int _32603) term93 term223). Qed.
Lemma lem3164227 (_32603 : int) : (term458 _32603) = (term459 _32603).
Proof. exact (@lem1982713 term160 (real_of_int _32603)). Qed.
Lemma lem3164229 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164230 : term93 = term182.
Proof. exact (@lem3164229 term2). Qed.
Lemma lem3164232 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164233 : term160 = term161.
Proof. exact (@lem3164232 term2). Qed.
Lemma lem3164234 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3164235 : term460 = term461.
Proof. exact (MK_COMB (@lem3164234) (@lem3164233)). Qed.
Lemma lem3164236 : term462 = term463.
Proof. exact (MK_COMB (@lem3164235) (@lem3164230)). Qed.
Lemma lem3164237 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3164239 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164240 : term188 = term189.
Proof. exact (@lem3164239 (NUMERAL 0) term2). Qed.
Lemma lem3164241 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164242 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164243 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164242 h1) (fun h1 : term189 = True => @lem3164241)). Qed.
Lemma lem3164244 : term189 = True.
Proof. exact (EQ_MP (@lem3164243) (@lem3164241)). Qed.
Lemma lem3164245 : term188 = True.
Proof. exact (TRANS (@lem3164240) (@lem3164244)). Qed.
Lemma lem3164246 : True = term188.
Proof. exact (SYM (@lem3164245)). Qed.
Lemma lem3164247 : term188.
Proof. exact (EQ_MP (@lem3164246) (@lem0)). Qed.
Lemma lem3164248 : term465.
Proof. exact (@lem3164237 (@lem3164247)). Qed.
Lemma lem3164250 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164251 : term188 = term189.
Proof. exact (@lem3164250 (NUMERAL 0) term2). Qed.
Lemma lem3164252 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164253 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164254 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164253 h1) (fun h1 : term189 = True => @lem3164252)). Qed.
Lemma lem3164255 : term189 = True.
Proof. exact (EQ_MP (@lem3164254) (@lem3164252)). Qed.
Lemma lem3164256 : term188 = True.
Proof. exact (TRANS (@lem3164251) (@lem3164255)). Qed.
Lemma lem3164257 : True = term188.
Proof. exact (SYM (@lem3164256)). Qed.
Lemma lem3164258 : term188.
Proof. exact (EQ_MP (@lem3164257) (@lem0)). Qed.
Lemma lem3164259 : term466.
Proof. exact (@lem3164248 (@lem3164258)). Qed.
Lemma lem3164261 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164262 : term188 = term189.
Proof. exact (@lem3164261 (NUMERAL 0) term2). Qed.
Lemma lem3164263 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164264 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164265 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164264 h1) (fun h1 : term189 = True => @lem3164263)). Qed.
Lemma lem3164266 : term189 = True.
Proof. exact (EQ_MP (@lem3164265) (@lem3164263)). Qed.
Lemma lem3164267 : term188 = True.
Proof. exact (TRANS (@lem3164262) (@lem3164266)). Qed.
Lemma lem3164268 : True = term188.
Proof. exact (SYM (@lem3164267)). Qed.
Lemma lem3164269 : term188.
Proof. exact (EQ_MP (@lem3164268) (@lem0)). Qed.
Lemma lem3164270 : term467.
Proof. exact (@lem3164259 (@lem3164269)). Qed.
Lemma lem3164272 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164273 : term169 = term170.
Proof. exact (@lem3164272 term2 term2). Qed.
Lemma lem3164274 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164275 : term172 = term2.
Proof. exact (EQ_MP (@lem3164274) (@lem940073)). Qed.
Lemma lem3164276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164277 : term170 = term93.
Proof. exact (MK_COMB (@lem3164276) (@lem3164275)). Qed.
Lemma lem3164278 : term169 = term93.
Proof. exact (TRANS (@lem3164273) (@lem3164277)). Qed.
Lemma lem3164280 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3164281 : term236 = term239.
Proof. exact (@lem3164280 term2 term2). Qed.
Lemma lem3164282 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164283 : term172 = term2.
Proof. exact (EQ_MP (@lem3164282) (@lem940073)). Qed.
Lemma lem3164284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164285 : term170 = term93.
Proof. exact (MK_COMB (@lem3164284) (@lem3164283)). Qed.
Lemma lem3164286 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164287 : term239 = term160.
Proof. exact (MK_COMB (@lem3164286) (@lem3164285)). Qed.
Lemma lem3164288 : term236 = term160.
Proof. exact (TRANS (@lem3164281) (@lem3164287)). Qed.
Lemma lem3164289 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3164290 : term468 = term460.
Proof. exact (MK_COMB (@lem3164289) (@lem3164288)). Qed.
Lemma lem3164291 : term469 = term462.
Proof. exact (MK_COMB (@lem3164290) (@lem3164278)). Qed.
Lemma lem3164293 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3164294 : term462 = term79.
Proof. exact (@lem3164293 term2). Qed.
Lemma lem3164295 : term469 = term79.
Proof. exact (TRANS (@lem3164291) (@lem3164294)). Qed.
Lemma lem3164296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3164297 : term471 = term273.
Proof. exact (MK_COMB (@lem3164296) (@lem3164295)). Qed.
Lemma lem3164298 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3164299 : term472 = term275.
Proof. exact (MK_COMB (@lem3164297) (@lem3164298)). Qed.
Lemma lem3164301 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3164302 : term275 = term79.
Proof. exact (@lem3164301 term2). Qed.
Lemma lem3164303 : term472 = term79.
Proof. exact (TRANS (@lem3164299) (@lem3164302)). Qed.
Lemma lem3164305 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164306 : term169 = term170.
Proof. exact (@lem3164305 term2 term2). Qed.
Lemma lem3164307 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164308 : term172 = term2.
Proof. exact (EQ_MP (@lem3164307) (@lem940073)). Qed.
Lemma lem3164309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164310 : term170 = term93.
Proof. exact (MK_COMB (@lem3164309) (@lem3164308)). Qed.
Lemma lem3164311 : term169 = term93.
Proof. exact (TRANS (@lem3164306) (@lem3164310)). Qed.
Lemma lem3164312 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3164313 : term277 = term275.
Proof. exact (MK_COMB (@lem3164312) (@lem3164311)). Qed.
Lemma lem3164315 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3164316 : term275 = term79.
Proof. exact (@lem3164315 term2). Qed.
Lemma lem3164317 : term277 = term79.
Proof. exact (TRANS (@lem3164313) (@lem3164316)). Qed.
Lemma lem3164318 : term79 = term277.
Proof. exact (SYM (@lem3164317)). Qed.
Lemma lem3164319 : term472 = term277.
Proof. exact (TRANS (@lem3164303) (@lem3164318)). Qed.
Lemma lem3164320 : term463 = term157.
Proof. exact (@lem3164270 (@lem3164319)). Qed.
Lemma lem3164321 : term462 = term157.
Proof. exact (TRANS (@lem3164236) (@lem3164320)). Qed.
Lemma lem3164323 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3164324 : term157 = term79.
Proof. exact (@lem3164323 term79). Qed.
Lemma lem3164325 : term462 = term79.
Proof. exact (TRANS (@lem3164321) (@lem3164324)). Qed.
Lemma lem3164326 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3164327 : term473 = term273.
Proof. exact (MK_COMB (@lem3164326) (@lem3164325)). Qed.
Lemma lem3164328 (_32603 : int) : (real_of_int _32603) = (real_of_int _32603).
Proof. exact (eq_refl (real_of_int _32603)). Qed.
Lemma lem3164329 (_32603 : int) : (term459 _32603) = (term474 _32603).
Proof. exact (MK_COMB (@lem3164327) (@lem3164328 _32603)). Qed.
Lemma lem3164330 (_32603 : int) : (term458 _32603) = (term474 _32603).
Proof. exact (TRANS (@lem3164227 _32603) (@lem3164329 _32603)). Qed.
Lemma lem3164331 (_32603 : int) : (term474 _32603) = term79.
Proof. exact (@lem1982719 (real_of_int _32603)). Qed.
Lemma lem3164332 (_32603 : int) : (term458 _32603) = term79.
Proof. exact (TRANS (@lem3164330 _32603) (@lem3164331 _32603)). Qed.
Lemma lem3164333 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3164334 (_32603 : int) : (term475 _32603) = term121.
Proof. exact (MK_COMB (@lem3164333) (@lem3164332 _32603)). Qed.
Lemma lem3164336 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164337 : term223 = term226.
Proof. exact (@lem3164336 term200). Qed.
Lemma lem3164339 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164340 : term93 = term182.
Proof. exact (@lem3164339 term2). Qed.
Lemma lem3164341 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3164342 : term95 = term183.
Proof. exact (MK_COMB (@lem3164341) (@lem3164340)). Qed.
Lemma lem3164343 : term476 = term477.
Proof. exact (MK_COMB (@lem3164342) (@lem3164337)). Qed.
Lemma lem3164344 : term478.
Proof. exact (@lem1981473 term93 term93 term223 term93 term160 term93). Qed.
Lemma lem3164346 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164347 : term188 = term189.
Proof. exact (@lem3164346 (NUMERAL 0) term2). Qed.
Lemma lem3164348 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164349 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164350 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164349 h1) (fun h1 : term189 = True => @lem3164348)). Qed.
Lemma lem3164351 : term189 = True.
Proof. exact (EQ_MP (@lem3164350) (@lem3164348)). Qed.
Lemma lem3164352 : term188 = True.
Proof. exact (TRANS (@lem3164347) (@lem3164351)). Qed.
Lemma lem3164353 : True = term188.
Proof. exact (SYM (@lem3164352)). Qed.
Lemma lem3164354 : term188.
Proof. exact (EQ_MP (@lem3164353) (@lem0)). Qed.
Lemma lem3164355 : term479.
Proof. exact (@lem3164344 (@lem3164354)). Qed.
Lemma lem3164357 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164358 : term188 = term189.
Proof. exact (@lem3164357 (NUMERAL 0) term2). Qed.
Lemma lem3164359 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164360 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164361 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164360 h1) (fun h1 : term189 = True => @lem3164359)). Qed.
Lemma lem3164362 : term189 = True.
Proof. exact (EQ_MP (@lem3164361) (@lem3164359)). Qed.
Lemma lem3164363 : term188 = True.
Proof. exact (TRANS (@lem3164358) (@lem3164362)). Qed.
Lemma lem3164364 : True = term188.
Proof. exact (SYM (@lem3164363)). Qed.
Lemma lem3164365 : term188.
Proof. exact (EQ_MP (@lem3164364) (@lem0)). Qed.
Lemma lem3164366 : term480.
Proof. exact (@lem3164355 (@lem3164365)). Qed.
Lemma lem3164368 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164369 : term188 = term189.
Proof. exact (@lem3164368 (NUMERAL 0) term2). Qed.
Lemma lem3164370 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164371 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164372 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164371 h1) (fun h1 : term189 = True => @lem3164370)). Qed.
Lemma lem3164373 : term189 = True.
Proof. exact (EQ_MP (@lem3164372) (@lem3164370)). Qed.
Lemma lem3164374 : term188 = True.
Proof. exact (TRANS (@lem3164369) (@lem3164373)). Qed.
Lemma lem3164375 : True = term188.
Proof. exact (SYM (@lem3164374)). Qed.
Lemma lem3164376 : term188.
Proof. exact (EQ_MP (@lem3164375) (@lem0)). Qed.
Lemma lem3164377 : term481.
Proof. exact (@lem3164366 (@lem3164376)). Qed.
Lemma lem3164379 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3164380 : term482 = term483.
Proof. exact (@lem3164379 term200 term2). Qed.
Lemma lem3164381 : term206 = term198.
Proof. exact (@lem996237 term198). Qed.
Lemma lem3164382 : (term206 = term198) = (term207 = term200).
Proof. exact (@lem1007663 term198 (BIT1 0) term198). Qed.
Lemma lem3164383 : term207 = term200.
Proof. exact (EQ_MP (@lem3164382) (@lem3164381)). Qed.
Lemma lem3164384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164385 : term205 = term186.
Proof. exact (MK_COMB (@lem3164384) (@lem3164383)). Qed.
Lemma lem3164386 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164387 : term483 = term223.
Proof. exact (MK_COMB (@lem3164386) (@lem3164385)). Qed.
Lemma lem3164388 : term482 = term223.
Proof. exact (TRANS (@lem3164380) (@lem3164387)). Qed.
Lemma lem3164390 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164391 : term169 = term170.
Proof. exact (@lem3164390 term2 term2). Qed.
Lemma lem3164392 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164393 : term172 = term2.
Proof. exact (EQ_MP (@lem3164392) (@lem940073)). Qed.
Lemma lem3164394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164395 : term170 = term93.
Proof. exact (MK_COMB (@lem3164394) (@lem3164393)). Qed.
Lemma lem3164396 : term169 = term93.
Proof. exact (TRANS (@lem3164391) (@lem3164395)). Qed.
Lemma lem3164397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3164398 : term194 = term95.
Proof. exact (MK_COMB (@lem3164397) (@lem3164396)). Qed.
Lemma lem3164399 : term484 = term476.
Proof. exact (MK_COMB (@lem3164398) (@lem3164388)). Qed.
Lemma lem3164402 : term485 = term160.
Proof. exact (@lem1367771 term2 term2). Qed.
Lemma lem3164403 : term197 = term198.
Proof. exact (@lem706885). Qed.
Lemma lem3164404 : (term197 = term198) = (term199 = term200).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term198). Qed.
Lemma lem3164405 : term199 = term200.
Proof. exact (EQ_MP (@lem3164404) (@lem3164403)). Qed.
Lemma lem3164406 : term200 = term199.
Proof. exact (SYM (@lem3164405)). Qed.
Lemma lem3164407 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164408 : term186 = term196.
Proof. exact (MK_COMB (@lem3164407) (@lem3164406)). Qed.
Lemma lem3164409 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164410 : term223 = term486.
Proof. exact (MK_COMB (@lem3164409) (@lem3164408)). Qed.
Lemma lem3164411 : term95 = term95.
Proof. exact (eq_refl term95). Qed.
Lemma lem3164412 : term476 = term485.
Proof. exact (MK_COMB (@lem3164411) (@lem3164410)). Qed.
Lemma lem3164413 : term476 = term160.
Proof. exact (TRANS (@lem3164412) (@lem3164402)). Qed.
Lemma lem3164414 : term484 = term160.
Proof. exact (TRANS (@lem3164399) (@lem3164413)). Qed.
Lemma lem3164415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3164416 : term487 = term162.
Proof. exact (MK_COMB (@lem3164415) (@lem3164414)). Qed.
Lemma lem3164417 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3164418 : term488 = term236.
Proof. exact (MK_COMB (@lem3164416) (@lem3164417)). Qed.
Lemma lem3164420 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3164421 : term236 = term239.
Proof. exact (@lem3164420 term2 term2). Qed.
Lemma lem3164422 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164423 : term172 = term2.
Proof. exact (EQ_MP (@lem3164422) (@lem940073)). Qed.
Lemma lem3164424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164425 : term170 = term93.
Proof. exact (MK_COMB (@lem3164424) (@lem3164423)). Qed.
Lemma lem3164426 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164427 : term239 = term160.
Proof. exact (MK_COMB (@lem3164426) (@lem3164425)). Qed.
Lemma lem3164428 : term236 = term160.
Proof. exact (TRANS (@lem3164421) (@lem3164427)). Qed.
Lemma lem3164429 : term488 = term160.
Proof. exact (TRANS (@lem3164418) (@lem3164428)). Qed.
Lemma lem3164431 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164432 : term169 = term170.
Proof. exact (@lem3164431 term2 term2). Qed.
Lemma lem3164433 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164434 : term172 = term2.
Proof. exact (EQ_MP (@lem3164433) (@lem940073)). Qed.
Lemma lem3164435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164436 : term170 = term93.
Proof. exact (MK_COMB (@lem3164435) (@lem3164434)). Qed.
Lemma lem3164437 : term169 = term93.
Proof. exact (TRANS (@lem3164432) (@lem3164436)). Qed.
Lemma lem3164438 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem3164439 : term489 = term236.
Proof. exact (MK_COMB (@lem3164438) (@lem3164437)). Qed.
Lemma lem3164441 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3164442 : term236 = term239.
Proof. exact (@lem3164441 term2 term2). Qed.
Lemma lem3164443 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164444 : term172 = term2.
Proof. exact (EQ_MP (@lem3164443) (@lem940073)). Qed.
Lemma lem3164445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164446 : term170 = term93.
Proof. exact (MK_COMB (@lem3164445) (@lem3164444)). Qed.
Lemma lem3164447 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164448 : term239 = term160.
Proof. exact (MK_COMB (@lem3164447) (@lem3164446)). Qed.
Lemma lem3164449 : term236 = term160.
Proof. exact (TRANS (@lem3164442) (@lem3164448)). Qed.
Lemma lem3164450 : term489 = term160.
Proof. exact (TRANS (@lem3164439) (@lem3164449)). Qed.
Lemma lem3164451 : term160 = term489.
Proof. exact (SYM (@lem3164450)). Qed.
Lemma lem3164452 : term488 = term489.
Proof. exact (TRANS (@lem3164429) (@lem3164451)). Qed.
Lemma lem3164453 : term477 = term161.
Proof. exact (@lem3164377 (@lem3164452)). Qed.
Lemma lem3164454 : term476 = term161.
Proof. exact (TRANS (@lem3164343) (@lem3164453)). Qed.
Lemma lem3164456 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3164457 : term161 = term160.
Proof. exact (@lem3164456 term160). Qed.
Lemma lem3164458 : term476 = term160.
Proof. exact (TRANS (@lem3164454) (@lem3164457)). Qed.
Lemma lem3164459 (_32603 : int) : (term457 _32603) = term490.
Proof. exact (MK_COMB (@lem3164334 _32603) (@lem3164458)). Qed.
Lemma lem3164460 (_32603 : int) : (term456 _32603) = term490.
Proof. exact (TRANS (@lem3164226 _32603) (@lem3164459 _32603)). Qed.
Lemma lem3164461 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3164462 (_32603 : int) : (term456 _32603) = term160.
Proof. exact (TRANS (@lem3164460 _32603) (@lem3164461)). Qed.
Lemma lem3164463 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3164464 (_32603 : int) : (term491 _32603) = term492.
Proof. exact (MK_COMB (@lem3164463) (@lem3164462 _32603)). Qed.
Lemma lem3164465 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3164466 (_32603 : int) : (term455 _32603) = term493.
Proof. exact (MK_COMB (@lem3164464 _32603) (@lem3164465)). Qed.
Lemma lem3164467 (_32603 : int) (h1 : term604 _32603) : term493.
Proof. exact (EQ_MP (@lem3164466 _32603) (@lem3164225 _32603 h1)). Qed.
Lemma lem3164469 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3164470 : term493 = term494.
Proof. exact (@lem3164469 term79 term160). Qed.
Lemma lem3164472 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164473 : term160 = term161.
Proof. exact (@lem3164472 term2). Qed.
Lemma lem3164475 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164476 : term79 = term157.
Proof. exact (@lem3164475 (NUMERAL 0)). Qed.
Lemma lem3164477 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164478 : term81 = term495.
Proof. exact (MK_COMB (@lem3164477) (@lem3164476)). Qed.
Lemma lem3164479 : term494 = term496.
Proof. exact (MK_COMB (@lem3164478) (@lem3164473)). Qed.
Lemma lem3164480 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3164482 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164483 : term188 = term189.
Proof. exact (@lem3164482 (NUMERAL 0) term2). Qed.
Lemma lem3164484 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164485 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164486 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164485 h1) (fun h1 : term189 = True => @lem3164484)). Qed.
Lemma lem3164487 : term189 = True.
Proof. exact (EQ_MP (@lem3164486) (@lem3164484)). Qed.
Lemma lem3164488 : term188 = True.
Proof. exact (TRANS (@lem3164483) (@lem3164487)). Qed.
Lemma lem3164489 : True = term188.
Proof. exact (SYM (@lem3164488)). Qed.
Lemma lem3164490 : term188.
Proof. exact (EQ_MP (@lem3164489) (@lem0)). Qed.
Lemma lem3164491 : term498.
Proof. exact (@lem3164480 (@lem3164490)). Qed.
Lemma lem3164493 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3164494 : term188 = term189.
Proof. exact (@lem3164493 (NUMERAL 0) term2). Qed.
Lemma lem3164495 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164496 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3164497 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164496 h1) (fun h1 : term189 = True => @lem3164495)). Qed.
Lemma lem3164498 : term189 = True.
Proof. exact (EQ_MP (@lem3164497) (@lem3164495)). Qed.
Lemma lem3164499 : term188 = True.
Proof. exact (TRANS (@lem3164494) (@lem3164498)). Qed.
Lemma lem3164500 : True = term188.
Proof. exact (SYM (@lem3164499)). Qed.
Lemma lem3164501 : term188.
Proof. exact (EQ_MP (@lem3164500) (@lem0)). Qed.
Lemma lem3164502 : term496 = term499.
Proof. exact (@lem3164491 (@lem3164501)). Qed.
Lemma lem3164504 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3164505 : term236 = term239.
Proof. exact (@lem3164504 term2 term2). Qed.
Lemma lem3164506 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164507 : term172 = term2.
Proof. exact (EQ_MP (@lem3164506) (@lem940073)). Qed.
Lemma lem3164508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164509 : term170 = term93.
Proof. exact (MK_COMB (@lem3164508) (@lem3164507)). Qed.
Lemma lem3164510 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3164511 : term239 = term160.
Proof. exact (MK_COMB (@lem3164510) (@lem3164509)). Qed.
Lemma lem3164512 : term236 = term160.
Proof. exact (TRANS (@lem3164505) (@lem3164511)). Qed.
Lemma lem3164514 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3164515 : term275 = term79.
Proof. exact (@lem3164514 term2). Qed.
Lemma lem3164516 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164517 : term500 = term81.
Proof. exact (MK_COMB (@lem3164516) (@lem3164515)). Qed.
Lemma lem3164518 : term499 = term494.
Proof. exact (MK_COMB (@lem3164517) (@lem3164512)). Qed.
Lemma lem3164520 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3164521 : term494 = term503.
Proof. exact (@lem3164520 (NUMERAL 0) term2). Qed.
Lemma lem3164522 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3164523 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3164524 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3164523 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3164522)). Qed.
Lemma lem3164525 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3164524) (@lem3164522)). Qed.
Lemma lem3164526 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3164527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164528 : term504 = (and True).
Proof. exact (MK_COMB (@lem3164527) (@lem3164526)). Qed.
Lemma lem3164529 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3164528) (@lem3164525)). Qed.
Lemma lem3164531 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3164532 : term503 = False.
Proof. exact (TRANS (@lem3164529) (@lem3164531)). Qed.
Lemma lem3164533 : term494 = False.
Proof. exact (TRANS (@lem3164521) (@lem3164532)). Qed.
Lemma lem3164534 : term499 = False.
Proof. exact (TRANS (@lem3164518) (@lem3164533)). Qed.
Lemma lem3164535 : term496 = False.
Proof. exact (TRANS (@lem3164502) (@lem3164534)). Qed.
Lemma lem3164536 : term494 = False.
Proof. exact (TRANS (@lem3164479) (@lem3164535)). Qed.
Lemma lem3164537 : term493 = False.
Proof. exact (TRANS (@lem3164470) (@lem3164536)). Qed.
Lemma lem3164538 (_32603 : int) (h1 : term604 _32603) : False.
Proof. exact (EQ_MP (@lem3164537) (@lem3164467 _32603 h1)). Qed.
Lemma lem3164539 (_32603 : int) (h1 : term378 _32603) : False.
Proof. exact (or_elim (@lem3163634 _32603 h1) (fun h0 : term603 _32603 => @lem3164086 _32603 h0) (fun h0 : term604 _32603 => @lem3164538 _32603 h0)). Qed.
Lemma lem3164540 (_32603 : int) (h1 : term387 _32603) : False.
Proof. exact (or_elim (@lem3163053 _32603 h1) (fun h0 : term382 _32603 => @lem3163633 _32603 h0) (fun h0 : term378 _32603 => @lem3164539 _32603 h0)). Qed.
Lemma lem3164541 (_32603 : int) (h1 : term389 _32603) : False.
Proof. exact (or_elim (@lem3162602 _32603 h1) (fun h0 : term578 _32603 => @lem3163052 _32603 h0) (fun h0 : term387 _32603 => @lem3164540 _32603 h0)). Qed.
Lemma lem3164542 (_32603 : int) (h1 : term410 _32603) : False.
Proof. exact (or_elim (@lem3161147 _32603 h1) (fun h0 : term407 _32603 => @lem3162601 _32603 h0) (fun h0 : term389 _32603 => @lem3164541 _32603 h0)). Qed.
Lemma lem3164543 (_32603 : int) (h1 : term431 _32603) : False.
Proof. exact (or_elim (@lem3159021 _32603 h1) (fun h0 : term428 _32603 => @lem3161146 _32603 h0) (fun h0 : term410 _32603 => @lem3164542 _32603 h0)). Qed.
Lemma lem3164545 (_32603 : int) (h1 : term431 _32603) : term431 _32603.
Proof. exact (h1). Qed.
Lemma lem3164546 (_32603 : int) (h1 : term431 _32603) : (term431 _32603) = False.
Proof. exact (prop_ext (fun h2 : term431 _32603 => @lem3164543 _32603 h1) (fun h2 : False => @lem3164545 _32603 h1)). Qed.
Lemma lem3164547 (_32603 : int) (h1 : term431 _32603) : False.
Proof. exact (EQ_MP (@lem3164546 _32603 h1) (@lem3164545 _32603 h1)). Qed.
Lemma lem3164548 (_32603 : int) (h1 : term152 _32603) : term152 _32603.
Proof. exact (h1). Qed.
Lemma lem3164549 (_32603 : int) (h1 : term152 _32603) : term431 _32603.
Proof. exact (EQ_MP (@lem3158933 _32603) (@lem3164548 _32603 h1)). Qed.
Lemma lem3164550 (_32603 : int) (h1 : term152 _32603) : (term431 _32603) = False.
Proof. exact (prop_ext (fun h2 : term431 _32603 => @lem3164547 _32603 h2) (fun h2 : False => @lem3164549 _32603 h1)). Qed.
Lemma lem3164551 (_32603 : int) (h1 : term152 _32603) : False.
Proof. exact (EQ_MP (@lem3164550 _32603 h1) (@lem3164549 _32603 h1)). Qed.
Lemma lem3164552 (_32603 : int) : term605 _32603.
Proof. exact (fun h0 : term152 _32603 => @lem3164551 _32603 h0). Qed.
Lemma lem3164553 (_32603 : int) : term606 _32603.
Proof. exact (@lem1386578 (term607 _32603)). Qed.
Lemma lem3164556 (_32603 : int) : term607 _32603.
Proof. exact (@lem3164553 _32603 (@lem3164552 _32603)). Qed.
Lemma lem3164557 (_32603 : int) : (term150 _32603) = (term72 _32603).
Proof. exact (SYM (@lem3157772 _32603)). Qed.
Lemma lem3164558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3164559 (_32603 : int) : (term607 _32603) = (term37 _32603).
Proof. exact (MK_COMB (@lem3164558) (@lem3164557 _32603)). Qed.
Lemma lem3164560 (_32603 : int) : term37 _32603.
Proof. exact (EQ_MP (@lem3164559 _32603) (@lem3164556 _32603)). Qed.
Lemma lem3164561 (_32603 : int) : term38 _32603.
Proof. exact (EQ_MP (@lem3157491 _32603) (@lem3164560 _32603)). Qed.
Lemma lem3164562 (n : nat) : term608 n.
Proof. exact (@lem3164561 (int_of_num n)). Qed.
Lemma lem3164563 (n : nat) : term34 n.
Proof. exact (@lem3164562 n (@lem3157490 n)). Qed.
Lemma lem3164564 (n : nat) : (term34 n) = ((term9 n) = (term10 n)).
Proof. exact (SYM (@lem3157487 n)). Qed.
Lemma lem3164566 (m : nat) : term609 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem3164567 (m : nat) : (term609 m) = (term610 m).
Proof. exact (eq_refl (term609 m)). Qed.
Lemma lem3164568 (m : nat) : term610 m.
Proof. exact (EQ_MP (@lem3164567 m) (@lem3164566 m)). Qed.
Lemma lem3164569 (m : nat) (n : nat) : term611 m n.
Proof. exact (@lem3164568 m n). Qed.
Lemma lem3164570 (m : nat) (n : nat) : (term611 m n) = (term612 m n).
Proof. exact (eq_refl (term611 m n)). Qed.
Lemma lem3164571 (m : nat) (n : nat) : term612 m n.
Proof. exact (EQ_MP (@lem3164570 m n) (@lem3164569 m n)). Qed.
Lemma lem3164572 (m : nat) (n : nat) (p : nat) : term613 m n p.
Proof. exact (@lem3164571 m n p). Qed.
Lemma lem3164573 (m : nat) (n : nat) (p : nat) : (term613 m n p) = ((term614 m n p) = (term615 m n p)).
Proof. exact (eq_refl (term613 m n p)). Qed.
Lemma lem3164575 (m : nat) : term616 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem3164576 (m : nat) : (term616 m) = (term617 m).
Proof. exact (eq_refl (term616 m)). Qed.
Lemma lem3164577 (m : nat) : term617 m.
Proof. exact (EQ_MP (@lem3164576 m) (@lem3164575 m)). Qed.
Lemma lem3164578 (m : nat) (n : nat) : term618 m n.
Proof. exact (@lem3164577 m n). Qed.
Lemma lem3164579 (m : nat) (n : nat) : (term618 m n) = (term619 m n).
Proof. exact (eq_refl (term618 m n)). Qed.
Lemma lem3164580 (m : nat) (n : nat) : term619 m n.
Proof. exact (EQ_MP (@lem3164579 m n) (@lem3164578 m n)). Qed.
Lemma lem3164581 (m : nat) (n : nat) (p : nat) : term620 m n p.
Proof. exact (@lem3164580 m n p). Qed.
Lemma lem3164582 (m : nat) (n : nat) (p : nat) : (term620 m n p) = ((term621 n m p) = (term622 m n p)).
Proof. exact (eq_refl (term620 m n p)). Qed.
Lemma lem3164622 (a : nat) (b : nat) : ((term623 a b) = (term624 a b)) = (term625 a b).
Proof. exact (@lem17500 (term623 a b) (term624 a b)). Qed.
Lemma lem3164629 (b : nat) : (term626 b) = b.
Proof. exact (@lem1032070 b). Qed.
Lemma lem3164638 (a : nat) (b : nat) : (term627 a b) = (term627 a b).
Proof. exact (eq_refl (term627 a b)). Qed.
Lemma lem3164639 (a : nat) (b : nat) : (term624 a b) = (term623 a b).
Proof. exact (MK_COMB (@lem3164638 a b) (@lem3164629 b)). Qed.
Lemma lem3164640 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3164641 (a : nat) (b : nat) : (term628 a b) = (term629 a b).
Proof. exact (MK_COMB (@lem3164640) (@lem3164639 a b)). Qed.
Lemma lem3164656 (a : nat) (b : nat) : (term630 a b) = (term630 a b).
Proof. exact (eq_refl (term630 a b)). Qed.
Lemma lem3164657 (a : nat) (b : nat) : (term631 a b) = (term632 a b).
Proof. exact (MK_COMB (@lem3164656 a b) (@lem3164641 a b)). Qed.
Lemma lem3164664 (b : nat) : (term626 b) = b.
Proof. exact (@lem1032070 b). Qed.
Lemma lem3164673 (a : nat) (b : nat) : (term627 a b) = (term627 a b).
Proof. exact (eq_refl (term627 a b)). Qed.
Lemma lem3164674 (a : nat) (b : nat) : (term624 a b) = (term623 a b).
Proof. exact (MK_COMB (@lem3164673 a b) (@lem3164664 b)). Qed.
Lemma lem3164687 (a : nat) (b : nat) : (term633 a b) = (term633 a b).
Proof. exact (eq_refl (term633 a b)). Qed.
Lemma lem3164688 (a : nat) (b : nat) : (term634 a b) = (term635 a b).
Proof. exact (MK_COMB (@lem3164687 a b) (@lem3164674 a b)). Qed.
Lemma lem3164689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3164690 (a : nat) (b : nat) : (term636 a b) = (term637 a b).
Proof. exact (MK_COMB (@lem3164689) (@lem3164688 a b)). Qed.
Lemma lem3164691 (a : nat) (b : nat) : (term625 a b) = (term638 a b).
Proof. exact (MK_COMB (@lem3164690 a b) (@lem3164657 a b)). Qed.
Lemma lem3164694 (a : nat) (b : nat) : ((term623 a b) = (term624 a b)) = (term638 a b).
Proof. exact (TRANS (@lem3164622 a b) (@lem3164691 a b)). Qed.
Lemma lem3164696 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3164697 (a : nat) (b : nat) : (term623 a b) = (term639 a b).
Proof. exact (@lem3164696 (Nat.mul a b) b). Qed.
Lemma lem3164698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164699 (a : nat) (b : nat) : (term633 a b) = (term640 a b).
Proof. exact (MK_COMB (@lem3164698) (@lem3164697 a b)). Qed.
Lemma lem3164701 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3164702 (a : nat) (b : nat) : (term623 a b) = (term639 a b).
Proof. exact (@lem3164701 (Nat.mul a b) b). Qed.
Lemma lem3164703 (a : nat) (b : nat) : (term635 a b) = (term641 a b).
Proof. exact (MK_COMB (@lem3164699 a b) (@lem3164702 a b)). Qed.
Lemma lem3164704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3164705 (a : nat) (b : nat) : (term637 a b) = (term642 a b).
Proof. exact (MK_COMB (@lem3164704) (@lem3164703 a b)). Qed.
Lemma lem3164707 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3164708 (a : nat) (b : nat) : (term623 a b) = (term639 a b).
Proof. exact (@lem3164707 (Nat.mul a b) b). Qed.
Lemma lem3164709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3164710 (a : nat) (b : nat) : (term629 a b) = (term643 a b).
Proof. exact (MK_COMB (@lem3164709) (@lem3164708 a b)). Qed.
Lemma lem3164711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164712 (a : nat) (b : nat) : (term630 a b) = (term644 a b).
Proof. exact (MK_COMB (@lem3164711) (@lem3164710 a b)). Qed.
Lemma lem3164714 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3164715 (a : nat) (b : nat) : (term623 a b) = (term639 a b).
Proof. exact (@lem3164714 (Nat.mul a b) b). Qed.
Lemma lem3164716 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3164717 (a : nat) (b : nat) : (term629 a b) = (term643 a b).
Proof. exact (MK_COMB (@lem3164716) (@lem3164715 a b)). Qed.
Lemma lem3164718 (a : nat) (b : nat) : (term632 a b) = (term645 a b).
Proof. exact (MK_COMB (@lem3164712 a b) (@lem3164717 a b)). Qed.
Lemma lem3164719 (a : nat) (b : nat) : (term638 a b) = (term646 a b).
Proof. exact (MK_COMB (@lem3164705 a b) (@lem3164718 a b)). Qed.
Lemma lem3164720 (a : nat) (b : nat) : ((term623 a b) = (term624 a b)) = (term646 a b).
Proof. exact (TRANS (@lem3164694 a b) (@lem3164719 a b)). Qed.
Lemma lem3164721 (b : nat) : term35 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem3164722 (b : nat) : (term35 b) = (term36 b).
Proof. exact (eq_refl (term35 b)). Qed.
Lemma lem3164723 (b : nat) : term36 b.
Proof. exact (EQ_MP (@lem3164722 b) (@lem3164721 b)). Qed.
Lemma lem3164724 (a : nat) (b : nat) : term647 a b.
Proof. exact (@lem2307535 (Nat.mul a b)). Qed.
Lemma lem3164725 (a : nat) (b : nat) : (term647 a b) = (term648 a b).
Proof. exact (eq_refl (term647 a b)). Qed.
Lemma lem3164726 (a : nat) (b : nat) : term648 a b.
Proof. exact (EQ_MP (@lem3164725 a b) (@lem3164724 a b)). Qed.
Lemma lem3164727 (_32606 : int) (_32605 : int) : (term649 _32606 _32605) = (term650 _32606 _32605).
Proof. exact (@lem2318604 (term650 _32606 _32605)). Qed.
Lemma lem3164736 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem16496 t)). Qed.
Lemma lem3164737 (_32606 : int) (_32605 : int) : (term651 _32606 _32605) = (int_le _32606 _32605).
Proof. exact (@lem3164736 (int_le _32606 _32605)). Qed.
Lemma lem3164738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3164739 (_32606 : int) (_32605 : int) : (term652 _32606 _32605) = (term653 _32606 _32605).
Proof. exact (MK_COMB (@lem3164738) (@lem3164737 _32606 _32605)). Qed.
Lemma lem3164741 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem16496 t)). Qed.
Lemma lem3164742 (_32606 : int) (_32605 : int) : (term654 _32606 _32605) = (term83 _32606 _32605).
Proof. exact (@lem3164741 (term83 _32606 _32605)). Qed.
Lemma lem3164743 (_32606 : int) (_32605 : int) : (term655 _32606 _32605) = (term656 _32606 _32605).
Proof. exact (MK_COMB (@lem3164739 _32606 _32605) (@lem3164742 _32606 _32605)). Qed.
Lemma lem3164746 (_32606 : int) : (term657 _32606) = (term657 _32606).
Proof. exact (eq_refl (term657 _32606)). Qed.
Lemma lem3164747 (_32606 : int) (_32605 : int) : (term658 _32606 _32605) = (term659 _32606 _32605).
Proof. exact (MK_COMB (@lem3164746 _32606) (@lem3164743 _32606 _32605)). Qed.
Lemma lem3164750 (_32605 : int) : (term657 _32605) = (term657 _32605).
Proof. exact (eq_refl (term657 _32605)). Qed.
Lemma lem3164751 (_32606 : int) (_32605 : int) : (term650 _32606 _32605) = (term660 _32606 _32605).
Proof. exact (MK_COMB (@lem3164750 _32605) (@lem3164747 _32606 _32605)). Qed.
Lemma lem3164754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3164758 (_32606 : int) (_32605 : int) : (term661 _32606 _32605) = (term662 _32606 _32605).
Proof. exact (MK_COMB (@lem3164754) (@lem3164751 _32606 _32605)). Qed.
Lemma lem3164764 (_32606 : int) (_32605 : int) : (term663 _32606 _32605) = (int_le _32606 _32605).
Proof. exact (@lem16933 (int_le _32606 _32605)). Qed.
Lemma lem3164766 (_32606 : int) (_32605 : int) : (term664 _32606 _32605) = (term664 _32606 _32605).
Proof. exact (eq_refl (term664 _32606 _32605)). Qed.
Lemma lem3164767 (_32606 : int) (_32605 : int) : (term665 _32606 _32605) = (term666 _32606 _32605).
Proof. exact (MK_COMB (@lem3164766 _32606 _32605) (@lem3164764 _32606 _32605)). Qed.
Lemma lem3164768 (_32606 : int) (_32605 : int) : (term667 _32606 _32605) = (term665 _32606 _32605).
Proof. exact (@lem17160 (int_le _32606 _32605) (term83 _32606 _32605)). Qed.
Lemma lem3164769 (_32606 : int) (_32605 : int) : (term667 _32606 _32605) = (term666 _32606 _32605).
Proof. exact (TRANS (@lem3164768 _32606 _32605) (@lem3164767 _32606 _32605)). Qed.
Lemma lem3164771 (_32606 : int) : (term69 _32606) = (term69 _32606).
Proof. exact (eq_refl (term69 _32606)). Qed.
Lemma lem3164772 (_32606 : int) (_32605 : int) : (term668 _32606 _32605) = (term669 _32606 _32605).
Proof. exact (MK_COMB (@lem3164771 _32606) (@lem3164769 _32606 _32605)). Qed.
Lemma lem3164773 (_32606 : int) (_32605 : int) : (term670 _32606 _32605) = (term668 _32606 _32605).
Proof. exact (@lem17362 (term73 _32606) (term656 _32606 _32605)). Qed.
Lemma lem3164774 (_32606 : int) (_32605 : int) : (term670 _32606 _32605) = (term669 _32606 _32605).
Proof. exact (TRANS (@lem3164773 _32606 _32605) (@lem3164772 _32606 _32605)). Qed.
Lemma lem3164776 (_32605 : int) : (term69 _32605) = (term69 _32605).
Proof. exact (eq_refl (term69 _32605)). Qed.
Lemma lem3164777 (_32606 : int) (_32605 : int) : (term671 _32606 _32605) = (term672 _32606 _32605).
Proof. exact (MK_COMB (@lem3164776 _32605) (@lem3164774 _32606 _32605)). Qed.
Lemma lem3164778 (_32606 : int) (_32605 : int) : (term662 _32606 _32605) = (term671 _32606 _32605).
Proof. exact (@lem17362 (term73 _32605) (term659 _32606 _32605)). Qed.
Lemma lem3164779 (_32606 : int) (_32605 : int) : (term662 _32606 _32605) = (term672 _32606 _32605).
Proof. exact (TRANS (@lem3164778 _32606 _32605) (@lem3164777 _32606 _32605)). Qed.
Lemma lem3164796 (_32606 : int) (_32605 : int) : (term661 _32606 _32605) = (term672 _32606 _32605).
Proof. exact (TRANS (@lem3164758 _32606 _32605) (@lem3164779 _32606 _32605)). Qed.
Lemma lem3164799 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3164800 (_32605 : int) : (term73 _32605) = (term76 _32605).
Proof. exact (@lem3164799 term15 _32605). Qed.
Lemma lem3164802 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3164803 : term78 = term79.
Proof. exact (@lem3164802 (NUMERAL 0)). Qed.
Lemma lem3164804 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164805 : term80 = term81.
Proof. exact (MK_COMB (@lem3164804) (@lem3164803)). Qed.
Lemma lem3164806 (_32605 : int) : (real_of_int _32605) = (real_of_int _32605).
Proof. exact (eq_refl (real_of_int _32605)). Qed.
Lemma lem3164807 (_32605 : int) : (term76 _32605) = (term82 _32605).
Proof. exact (MK_COMB (@lem3164805) (@lem3164806 _32605)). Qed.
Lemma lem3164809 (_32605 : int) : (term73 _32605) = (term82 _32605).
Proof. exact (TRANS (@lem3164800 _32605) (@lem3164807 _32605)). Qed.
Lemma lem3164812 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3164813 (_32606 : int) : (term73 _32606) = (term76 _32606).
Proof. exact (@lem3164812 term15 _32606). Qed.
Lemma lem3164815 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3164816 : term78 = term79.
Proof. exact (@lem3164815 (NUMERAL 0)). Qed.
Lemma lem3164817 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164818 : term80 = term81.
Proof. exact (MK_COMB (@lem3164817) (@lem3164816)). Qed.
Lemma lem3164819 (_32606 : int) : (real_of_int _32606) = (real_of_int _32606).
Proof. exact (eq_refl (real_of_int _32606)). Qed.
Lemma lem3164820 (_32606 : int) : (term76 _32606) = (term82 _32606).
Proof. exact (MK_COMB (@lem3164818) (@lem3164819 _32606)). Qed.
Lemma lem3164822 (_32606 : int) : (term73 _32606) = (term82 _32606).
Proof. exact (TRANS (@lem3164813 _32606) (@lem3164820 _32606)). Qed.
Lemma lem3164824 (y : int) (x : int) : (term83 x y) = (term84 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3164825 (_32605 : int) (_32606 : int) : (term83 _32606 _32605) = (term84 _32605 _32606).
Proof. exact (@lem3164824 _32605 _32606). Qed.
Lemma lem3164827 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3164828 (_32605 : int) (_32606 : int) : (term84 _32605 _32606) = (term673 _32605 _32606).
Proof. exact (@lem3164827 (term105 _32605) _32606). Qed.
Lemma lem3164830 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3164831 (_32605 : int) : (term106 _32605) = (term107 _32605).
Proof. exact (@lem3164830 _32605 term18). Qed.
Lemma lem3164833 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3164834 : term92 = term93.
Proof. exact (@lem3164833 term2). Qed.
Lemma lem3164835 (_32605 : int) : (term108 _32605) = (term108 _32605).
Proof. exact (eq_refl (term108 _32605)). Qed.
Lemma lem3164836 (_32605 : int) : (term107 _32605) = (term109 _32605).
Proof. exact (MK_COMB (@lem3164835 _32605) (@lem3164834)). Qed.
Lemma lem3164837 (_32605 : int) : (term106 _32605) = (term109 _32605).
Proof. exact (TRANS (@lem3164831 _32605) (@lem3164836 _32605)). Qed.
Lemma lem3164838 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3164839 (_32605 : int) : (term110 _32605) = (term111 _32605).
Proof. exact (MK_COMB (@lem3164838) (@lem3164837 _32605)). Qed.
Lemma lem3164840 (_32606 : int) : (real_of_int _32606) = (real_of_int _32606).
Proof. exact (eq_refl (real_of_int _32606)). Qed.
Lemma lem3164841 (_32605 : int) (_32606 : int) : (term673 _32605 _32606) = (term674 _32605 _32606).
Proof. exact (MK_COMB (@lem3164839 _32605) (@lem3164840 _32606)). Qed.
Lemma lem3164842 (_32605 : int) (_32606 : int) : (term84 _32605 _32606) = (term674 _32605 _32606).
Proof. exact (TRANS (@lem3164828 _32605 _32606) (@lem3164841 _32605 _32606)). Qed.
Lemma lem3164843 (_32605 : int) (_32606 : int) : (term83 _32606 _32605) = (term674 _32605 _32606).
Proof. exact (TRANS (@lem3164825 _32605 _32606) (@lem3164842 _32605 _32606)). Qed.
Lemma lem3164846 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3164848 (_32606 : int) (_32605 : int) : (int_le _32606 _32605) = (term75 _32606 _32605).
Proof. exact (@lem3164846 _32606 _32605). Qed.
Lemma lem3164849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164850 (_32605 : int) (_32606 : int) : (term664 _32606 _32605) = (term675 _32605 _32606).
Proof. exact (MK_COMB (@lem3164849) (@lem3164843 _32605 _32606)). Qed.
Lemma lem3164851 (_32606 : int) (_32605 : int) : (term666 _32606 _32605) = (term676 _32606 _32605).
Proof. exact (MK_COMB (@lem3164850 _32605 _32606) (@lem3164848 _32606 _32605)). Qed.
Lemma lem3164852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164853 (_32606 : int) : (term69 _32606) = (term149 _32606).
Proof. exact (MK_COMB (@lem3164852) (@lem3164822 _32606)). Qed.
Lemma lem3164854 (_32606 : int) (_32605 : int) : (term669 _32606 _32605) = (term677 _32606 _32605).
Proof. exact (MK_COMB (@lem3164853 _32606) (@lem3164851 _32606 _32605)). Qed.
Lemma lem3164855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3164856 (_32605 : int) : (term69 _32605) = (term149 _32605).
Proof. exact (MK_COMB (@lem3164855) (@lem3164809 _32605)). Qed.
Lemma lem3164857 (_32606 : int) (_32605 : int) : (term672 _32606 _32605) = (term678 _32606 _32605).
Proof. exact (MK_COMB (@lem3164856 _32605) (@lem3164854 _32606 _32605)). Qed.
Lemma lem3164858 (_32606 : int) (_32605 : int) : (term661 _32606 _32605) = (term678 _32606 _32605).
Proof. exact (TRANS (@lem3164796 _32606 _32605) (@lem3164857 _32606 _32605)). Qed.
Lemma lem3164862 (t : Prop) : (term151 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3164898 (_32606 : int) (_32605 : int) : (term679 _32606 _32605) = (term678 _32606 _32605).
Proof. exact (@lem3164862 (term678 _32606 _32605)). Qed.
Lemma lem3164899 (_32605 : int) : (term82 _32605) = (term153 _32605).
Proof. exact (@lem1988287 (real_of_int _32605) term79). Qed.
Lemma lem3164905 (_32605 : int) : (term154 _32605) = (term155 _32605).
Proof. exact (@lem1982792 (real_of_int _32605) term79). Qed.
Lemma lem3164907 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164908 : term79 = term157.
Proof. exact (@lem3164907 (NUMERAL 0)). Qed.
Lemma lem3164910 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164911 : term160 = term161.
Proof. exact (@lem3164910 term2). Qed.
Lemma lem3164912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3164913 : term162 = term163.
Proof. exact (MK_COMB (@lem3164912) (@lem3164911)). Qed.
Lemma lem3164914 : term164 = term165.
Proof. exact (MK_COMB (@lem3164913) (@lem3164908)). Qed.
Lemma lem3164915 : term165 = term166.
Proof. exact (@lem1981613 term160 term79 term93 term93). Qed.
Lemma lem3164917 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164918 : term169 = term170.
Proof. exact (@lem3164917 term2 term2). Qed.
Lemma lem3164919 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164920 : term172 = term2.
Proof. exact (EQ_MP (@lem3164919) (@lem940073)). Qed.
Lemma lem3164921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164922 : term170 = term93.
Proof. exact (MK_COMB (@lem3164921) (@lem3164920)). Qed.
Lemma lem3164923 : term169 = term93.
Proof. exact (TRANS (@lem3164918) (@lem3164922)). Qed.
Lemma lem3164925 (x : nat) : (term173 x) = term79.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3164926 : term164 = term79.
Proof. exact (@lem3164925 term2). Qed.
Lemma lem3164927 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3164928 : term174 = term175.
Proof. exact (MK_COMB (@lem3164927) (@lem3164926)). Qed.
Lemma lem3164929 : term166 = term157.
Proof. exact (MK_COMB (@lem3164928) (@lem3164923)). Qed.
Lemma lem3164930 : term165 = term157.
Proof. exact (TRANS (@lem3164915) (@lem3164929)). Qed.
Lemma lem3164931 : term164 = term157.
Proof. exact (TRANS (@lem3164914) (@lem3164930)). Qed.
Lemma lem3164933 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3164934 : term157 = term79.
Proof. exact (@lem3164933 term79). Qed.
Lemma lem3164935 : term164 = term79.
Proof. exact (TRANS (@lem3164931) (@lem3164934)). Qed.
Lemma lem3164936 (_32605 : int) : (term108 _32605) = (term108 _32605).
Proof. exact (eq_refl (term108 _32605)). Qed.
Lemma lem3164937 (_32605 : int) : (term155 _32605) = (term177 _32605).
Proof. exact (MK_COMB (@lem3164936 _32605) (@lem3164935)). Qed.
Lemma lem3164938 (_32605 : int) : (term177 _32605) = (real_of_int _32605).
Proof. exact (@lem1982723 (real_of_int _32605)). Qed.
Lemma lem3164939 (_32605 : int) : (term155 _32605) = (real_of_int _32605).
Proof. exact (TRANS (@lem3164937 _32605) (@lem3164938 _32605)). Qed.
Lemma lem3164941 (_32605 : int) : (term154 _32605) = (real_of_int _32605).
Proof. exact (TRANS (@lem3164905 _32605) (@lem3164939 _32605)). Qed.
Lemma lem3164942 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3164943 (_32605 : int) : (term178 _32605) = (term179 _32605).
Proof. exact (MK_COMB (@lem3164942) (@lem3164941 _32605)). Qed.
Lemma lem3164944 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3164945 (_32605 : int) : (term153 _32605) = (term180 _32605).
Proof. exact (MK_COMB (@lem3164943 _32605) (@lem3164944)). Qed.
Lemma lem3164946 (_32605 : int) : (term82 _32605) = (term180 _32605).
Proof. exact (TRANS (@lem3164899 _32605) (@lem3164945 _32605)). Qed.
Lemma lem3164947 (_32606 : int) : (term82 _32606) = (term153 _32606).
Proof. exact (@lem1988287 (real_of_int _32606) term79). Qed.
Lemma lem3164953 (_32606 : int) : (term154 _32606) = (term155 _32606).
Proof. exact (@lem1982792 (real_of_int _32606) term79). Qed.
Lemma lem3164955 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3164956 : term79 = term157.
Proof. exact (@lem3164955 (NUMERAL 0)). Qed.
Lemma lem3164958 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3164959 : term160 = term161.
Proof. exact (@lem3164958 term2). Qed.
Lemma lem3164960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3164961 : term162 = term163.
Proof. exact (MK_COMB (@lem3164960) (@lem3164959)). Qed.
Lemma lem3164962 : term164 = term165.
Proof. exact (MK_COMB (@lem3164961) (@lem3164956)). Qed.
Lemma lem3164963 : term165 = term166.
Proof. exact (@lem1981613 term160 term79 term93 term93). Qed.
Lemma lem3164965 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3164966 : term169 = term170.
Proof. exact (@lem3164965 term2 term2). Qed.
Lemma lem3164967 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3164968 : term172 = term2.
Proof. exact (EQ_MP (@lem3164967) (@lem940073)). Qed.
Lemma lem3164969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3164970 : term170 = term93.
Proof. exact (MK_COMB (@lem3164969) (@lem3164968)). Qed.
Lemma lem3164971 : term169 = term93.
Proof. exact (TRANS (@lem3164966) (@lem3164970)). Qed.
Lemma lem3164973 (x : nat) : (term173 x) = term79.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3164974 : term164 = term79.
Proof. exact (@lem3164973 term2). Qed.
Lemma lem3164975 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3164976 : term174 = term175.
Proof. exact (MK_COMB (@lem3164975) (@lem3164974)). Qed.
Lemma lem3164977 : term166 = term157.
Proof. exact (MK_COMB (@lem3164976) (@lem3164971)). Qed.
Lemma lem3164978 : term165 = term157.
Proof. exact (TRANS (@lem3164963) (@lem3164977)). Qed.
Lemma lem3164979 : term164 = term157.
Proof. exact (TRANS (@lem3164962) (@lem3164978)). Qed.
Lemma lem3164981 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3164982 : term157 = term79.
Proof. exact (@lem3164981 term79). Qed.
Lemma lem3164983 : term164 = term79.
Proof. exact (TRANS (@lem3164979) (@lem3164982)). Qed.
Lemma lem3164984 (_32606 : int) : (term108 _32606) = (term108 _32606).
Proof. exact (eq_refl (term108 _32606)). Qed.
Lemma lem3164985 (_32606 : int) : (term155 _32606) = (term177 _32606).
Proof. exact (MK_COMB (@lem3164984 _32606) (@lem3164983)). Qed.
Lemma lem3164986 (_32606 : int) : (term177 _32606) = (real_of_int _32606).
Proof. exact (@lem1982723 (real_of_int _32606)). Qed.
Lemma lem3164987 (_32606 : int) : (term155 _32606) = (real_of_int _32606).
Proof. exact (TRANS (@lem3164985 _32606) (@lem3164986 _32606)). Qed.
Lemma lem3164989 (_32606 : int) : (term154 _32606) = (real_of_int _32606).
Proof. exact (TRANS (@lem3164953 _32606) (@lem3164987 _32606)). Qed.
Lemma lem3164990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3164991 (_32606 : int) : (term178 _32606) = (term179 _32606).
Proof. exact (MK_COMB (@lem3164990) (@lem3164989 _32606)). Qed.
Lemma lem3164992 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3164993 (_32606 : int) : (term153 _32606) = (term180 _32606).
Proof. exact (MK_COMB (@lem3164991 _32606) (@lem3164992)). Qed.
Lemma lem3164994 (_32606 : int) : (term82 _32606) = (term180 _32606).
Proof. exact (TRANS (@lem3164947 _32606) (@lem3164993 _32606)). Qed.
Lemma lem3164995 (_32606 : int) (_32605 : int) : (term674 _32605 _32606) = (term680 _32606 _32605).
Proof. exact (@lem1988287 (real_of_int _32606) (term109 _32605)). Qed.
Lemma lem3165007 (_32606 : int) (_32605 : int) : (term681 _32606 _32605) = (term682 _32606 _32605).
Proof. exact (@lem1982792 (real_of_int _32606) (term109 _32605)). Qed.
Lemma lem3165008 (_32605 : int) : (term234 _32605) = (term235 _32605).
Proof. exact (@lem1982781 (real_of_int _32605) term160 term93). Qed.
Lemma lem3165010 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165011 : term93 = term182.
Proof. exact (@lem3165010 term2). Qed.
Lemma lem3165013 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3165014 : term160 = term161.
Proof. exact (@lem3165013 term2). Qed.
Lemma lem3165015 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165016 : term162 = term163.
Proof. exact (MK_COMB (@lem3165015) (@lem3165014)). Qed.
Lemma lem3165017 : term236 = term237.
Proof. exact (MK_COMB (@lem3165016) (@lem3165011)). Qed.
Lemma lem3165018 : term237 = term238.
Proof. exact (@lem1981613 term160 term93 term93 term93). Qed.
Lemma lem3165020 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165021 : term169 = term170.
Proof. exact (@lem3165020 term2 term2). Qed.
Lemma lem3165022 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165023 : term172 = term2.
Proof. exact (EQ_MP (@lem3165022) (@lem940073)). Qed.
Lemma lem3165024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165025 : term170 = term93.
Proof. exact (MK_COMB (@lem3165024) (@lem3165023)). Qed.
Lemma lem3165026 : term169 = term93.
Proof. exact (TRANS (@lem3165021) (@lem3165025)). Qed.
Lemma lem3165028 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3165029 : term236 = term239.
Proof. exact (@lem3165028 term2 term2). Qed.
Lemma lem3165030 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165031 : term172 = term2.
Proof. exact (EQ_MP (@lem3165030) (@lem940073)). Qed.
Lemma lem3165032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165033 : term170 = term93.
Proof. exact (MK_COMB (@lem3165032) (@lem3165031)). Qed.
Lemma lem3165034 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3165035 : term239 = term160.
Proof. exact (MK_COMB (@lem3165034) (@lem3165033)). Qed.
Lemma lem3165036 : term236 = term160.
Proof. exact (TRANS (@lem3165029) (@lem3165035)). Qed.
Lemma lem3165037 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3165038 : term240 = term241.
Proof. exact (MK_COMB (@lem3165037) (@lem3165036)). Qed.
Lemma lem3165039 : term238 = term161.
Proof. exact (MK_COMB (@lem3165038) (@lem3165026)). Qed.
Lemma lem3165040 : term237 = term161.
Proof. exact (TRANS (@lem3165018) (@lem3165039)). Qed.
Lemma lem3165041 : term236 = term161.
Proof. exact (TRANS (@lem3165017) (@lem3165040)). Qed.
Lemma lem3165043 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3165044 : term161 = term160.
Proof. exact (@lem3165043 term160). Qed.
Lemma lem3165045 : term236 = term160.
Proof. exact (TRANS (@lem3165041) (@lem3165044)). Qed.
Lemma lem3165048 (_32605 : int) : (term242 _32605) = (term242 _32605).
Proof. exact (eq_refl (term242 _32605)). Qed.
Lemma lem3165049 (_32605 : int) : (term235 _32605) = (term243 _32605).
Proof. exact (MK_COMB (@lem3165048 _32605) (@lem3165045)). Qed.
Lemma lem3165050 (_32605 : int) : (term234 _32605) = (term243 _32605).
Proof. exact (TRANS (@lem3165008 _32605) (@lem3165049 _32605)). Qed.
Lemma lem3165051 (_32606 : int) : (term108 _32606) = (term108 _32606).
Proof. exact (eq_refl (term108 _32606)). Qed.
Lemma lem3165052 (_32606 : int) (_32605 : int) : (term682 _32606 _32605) = (term683 _32606 _32605).
Proof. exact (MK_COMB (@lem3165051 _32606) (@lem3165050 _32605)). Qed.
Lemma lem3165057 (_32605 : int) (_32606 : int) : (term683 _32606 _32605) = (term684 _32605 _32606).
Proof. exact (@lem1982757 (term263 _32605) (real_of_int _32606) term160). Qed.
Lemma lem3165058 (_32605 : int) (_32606 : int) : (term682 _32606 _32605) = (term684 _32605 _32606).
Proof. exact (TRANS (@lem3165052 _32606 _32605) (@lem3165057 _32605 _32606)). Qed.
Lemma lem3165060 (_32605 : int) (_32606 : int) : (term681 _32606 _32605) = (term684 _32605 _32606).
Proof. exact (TRANS (@lem3165007 _32606 _32605) (@lem3165058 _32605 _32606)). Qed.
Lemma lem3165061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3165062 (_32605 : int) (_32606 : int) : (term685 _32606 _32605) = (term686 _32605 _32606).
Proof. exact (MK_COMB (@lem3165061) (@lem3165060 _32605 _32606)). Qed.
Lemma lem3165063 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3165064 (_32605 : int) (_32606 : int) : (term680 _32606 _32605) = (term687 _32605 _32606).
Proof. exact (MK_COMB (@lem3165062 _32605 _32606) (@lem3165063)). Qed.
Lemma lem3165065 (_32605 : int) (_32606 : int) : (term674 _32605 _32606) = (term687 _32605 _32606).
Proof. exact (TRANS (@lem3164995 _32606 _32605) (@lem3165064 _32605 _32606)). Qed.
Lemma lem3165066 (_32605 : int) (_32606 : int) : (term75 _32606 _32605) = (term688 _32605 _32606).
Proof. exact (@lem1988287 (real_of_int _32605) (real_of_int _32606)). Qed.
Lemma lem3165079 (_32605 : int) (_32606 : int) : (term689 _32605 _32606) = (term690 _32605 _32606).
Proof. exact (@lem1982792 (real_of_int _32605) (real_of_int _32606)). Qed.
Lemma lem3165080 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3165081 (_32605 : int) (_32606 : int) : (term691 _32605 _32606) = (term692 _32605 _32606).
Proof. exact (MK_COMB (@lem3165080) (@lem3165079 _32605 _32606)). Qed.
Lemma lem3165082 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3165083 (_32605 : int) (_32606 : int) : (term688 _32605 _32606) = (term693 _32605 _32606).
Proof. exact (MK_COMB (@lem3165081 _32605 _32606) (@lem3165082)). Qed.
Lemma lem3165084 (_32605 : int) (_32606 : int) : (term75 _32606 _32605) = (term693 _32605 _32606).
Proof. exact (TRANS (@lem3165066 _32605 _32606) (@lem3165083 _32605 _32606)). Qed.
Lemma lem3165085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165086 (_32605 : int) (_32606 : int) : (term675 _32605 _32606) = (term694 _32605 _32606).
Proof. exact (MK_COMB (@lem3165085) (@lem3165065 _32605 _32606)). Qed.
Lemma lem3165087 (_32605 : int) (_32606 : int) : (term676 _32606 _32605) = (term695 _32605 _32606).
Proof. exact (MK_COMB (@lem3165086 _32605 _32606) (@lem3165084 _32605 _32606)). Qed.
Lemma lem3165088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165089 (_32606 : int) : (term149 _32606) = (term303 _32606).
Proof. exact (MK_COMB (@lem3165088) (@lem3164994 _32606)). Qed.
Lemma lem3165090 (_32605 : int) (_32606 : int) : (term677 _32606 _32605) = (term696 _32605 _32606).
Proof. exact (MK_COMB (@lem3165089 _32606) (@lem3165087 _32605 _32606)). Qed.
Lemma lem3165091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165092 (_32605 : int) : (term149 _32605) = (term303 _32605).
Proof. exact (MK_COMB (@lem3165091) (@lem3164946 _32605)). Qed.
Lemma lem3165093 (_32605 : int) (_32606 : int) : (term678 _32606 _32605) = (term697 _32605 _32606).
Proof. exact (MK_COMB (@lem3165092 _32605) (@lem3165090 _32605 _32606)). Qed.
Lemma lem3165120 (_32605 : int) (_32606 : int) : (term679 _32606 _32605) = (term697 _32605 _32606).
Proof. exact (TRANS (@lem3164898 _32606 _32605) (@lem3165093 _32605 _32606)). Qed.
Lemma lem3165124 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term697 _32605 _32606.
Proof. exact (h1). Qed.
Lemma lem3165125 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term696 _32605 _32606.
Proof. exact (proj2 (@lem3165124 _32605 _32606 h1)). Qed.
Lemma lem3165127 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term695 _32605 _32606.
Proof. exact (proj2 (@lem3165125 _32605 _32606 h1)). Qed.
Lemma lem3165129 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term693 _32605 _32606.
Proof. exact (proj2 (@lem3165127 _32605 _32606 h1)). Qed.
Lemma lem3165130 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term687 _32605 _32606.
Proof. exact (proj1 (@lem3165127 _32605 _32606 h1)). Qed.
Lemma lem3165132 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3165133 : term433 = term188.
Proof. exact (@lem3165132 term79 term93). Qed.
Lemma lem3165135 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165136 : term93 = term182.
Proof. exact (@lem3165135 term2). Qed.
Lemma lem3165138 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165139 : term79 = term157.
Proof. exact (@lem3165138 (NUMERAL 0)). Qed.
Lemma lem3165140 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3165141 : term434 = term435.
Proof. exact (MK_COMB (@lem3165140) (@lem3165139)). Qed.
Lemma lem3165142 : term188 = term436.
Proof. exact (MK_COMB (@lem3165141) (@lem3165136)). Qed.
Lemma lem3165143 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3165145 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165146 : term188 = term189.
Proof. exact (@lem3165145 (NUMERAL 0) term2). Qed.
Lemma lem3165147 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165148 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165149 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165148 h1) (fun h1 : term189 = True => @lem3165147)). Qed.
Lemma lem3165150 : term189 = True.
Proof. exact (EQ_MP (@lem3165149) (@lem3165147)). Qed.
Lemma lem3165151 : term188 = True.
Proof. exact (TRANS (@lem3165146) (@lem3165150)). Qed.
Lemma lem3165152 : True = term188.
Proof. exact (SYM (@lem3165151)). Qed.
Lemma lem3165153 : term188.
Proof. exact (EQ_MP (@lem3165152) (@lem0)). Qed.
Lemma lem3165154 : term438.
Proof. exact (@lem3165143 (@lem3165153)). Qed.
Lemma lem3165156 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165157 : term188 = term189.
Proof. exact (@lem3165156 (NUMERAL 0) term2). Qed.
Lemma lem3165158 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165159 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165160 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165159 h1) (fun h1 : term189 = True => @lem3165158)). Qed.
Lemma lem3165161 : term189 = True.
Proof. exact (EQ_MP (@lem3165160) (@lem3165158)). Qed.
Lemma lem3165162 : term188 = True.
Proof. exact (TRANS (@lem3165157) (@lem3165161)). Qed.
Lemma lem3165163 : True = term188.
Proof. exact (SYM (@lem3165162)). Qed.
Lemma lem3165164 : term188.
Proof. exact (EQ_MP (@lem3165163) (@lem0)). Qed.
Lemma lem3165165 : term436 = term439.
Proof. exact (@lem3165154 (@lem3165164)). Qed.
Lemma lem3165167 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165168 : term169 = term170.
Proof. exact (@lem3165167 term2 term2). Qed.
Lemma lem3165169 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165170 : term172 = term2.
Proof. exact (EQ_MP (@lem3165169) (@lem940073)). Qed.
Lemma lem3165171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165172 : term170 = term93.
Proof. exact (MK_COMB (@lem3165171) (@lem3165170)). Qed.
Lemma lem3165173 : term169 = term93.
Proof. exact (TRANS (@lem3165168) (@lem3165172)). Qed.
Lemma lem3165175 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165176 : term275 = term79.
Proof. exact (@lem3165175 term2). Qed.
Lemma lem3165177 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3165178 : term440 = term434.
Proof. exact (MK_COMB (@lem3165177) (@lem3165176)). Qed.
Lemma lem3165179 : term439 = term188.
Proof. exact (MK_COMB (@lem3165178) (@lem3165173)). Qed.
Lemma lem3165181 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165182 : term188 = term189.
Proof. exact (@lem3165181 (NUMERAL 0) term2). Qed.
Lemma lem3165183 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165184 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165185 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165184 h1) (fun h1 : term189 = True => @lem3165183)). Qed.
Lemma lem3165186 : term189 = True.
Proof. exact (EQ_MP (@lem3165185) (@lem3165183)). Qed.
Lemma lem3165187 : term188 = True.
Proof. exact (TRANS (@lem3165182) (@lem3165186)). Qed.
Lemma lem3165188 : term439 = True.
Proof. exact (TRANS (@lem3165179) (@lem3165187)). Qed.
Lemma lem3165189 : term436 = True.
Proof. exact (TRANS (@lem3165165) (@lem3165188)). Qed.
Lemma lem3165190 : term188 = True.
Proof. exact (TRANS (@lem3165142) (@lem3165189)). Qed.
Lemma lem3165191 : term433 = True.
Proof. exact (TRANS (@lem3165133) (@lem3165190)). Qed.
Lemma lem3165192 : True = term433.
Proof. exact (SYM (@lem3165191)). Qed.
Lemma lem3165193 : term433.
Proof. exact (EQ_MP (@lem3165192) (@lem0)). Qed.
Lemma lem3165194 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term698 _32605 _32606.
Proof. exact (conj (@lem3165193) (@lem3165129 _32605 _32606 h1)). Qed.
Lemma lem3165196 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3165197 (_32605 : int) (_32606 : int) : term699 _32605 _32606.
Proof. exact (@lem3165196 term93 (term690 _32605 _32606)). Qed.
Lemma lem3165198 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term700 _32605 _32606.
Proof. exact (@lem3165197 _32605 _32606 (@lem3165194 _32605 _32606 h1)). Qed.
Lemma lem3165199 (_32605 : int) (_32606 : int) : (term701 _32605 _32606) = (term690 _32605 _32606).
Proof. exact (@lem1982733 (term690 _32605 _32606)). Qed.
Lemma lem3165200 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3165201 (_32605 : int) (_32606 : int) : (term702 _32605 _32606) = (term692 _32605 _32606).
Proof. exact (MK_COMB (@lem3165200) (@lem3165199 _32605 _32606)). Qed.
Lemma lem3165202 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3165203 (_32605 : int) (_32606 : int) : (term700 _32605 _32606) = (term693 _32605 _32606).
Proof. exact (MK_COMB (@lem3165201 _32605 _32606) (@lem3165202)). Qed.
Lemma lem3165204 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term693 _32605 _32606.
Proof. exact (EQ_MP (@lem3165203 _32605 _32606) (@lem3165198 _32605 _32606 h1)). Qed.
Lemma lem3165206 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3165207 : term433 = term188.
Proof. exact (@lem3165206 term79 term93). Qed.
Lemma lem3165209 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165210 : term93 = term182.
Proof. exact (@lem3165209 term2). Qed.
Lemma lem3165212 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165213 : term79 = term157.
Proof. exact (@lem3165212 (NUMERAL 0)). Qed.
Lemma lem3165214 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3165215 : term434 = term435.
Proof. exact (MK_COMB (@lem3165214) (@lem3165213)). Qed.
Lemma lem3165216 : term188 = term436.
Proof. exact (MK_COMB (@lem3165215) (@lem3165210)). Qed.
Lemma lem3165217 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3165219 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165220 : term188 = term189.
Proof. exact (@lem3165219 (NUMERAL 0) term2). Qed.
Lemma lem3165221 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165222 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165223 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165222 h1) (fun h1 : term189 = True => @lem3165221)). Qed.
Lemma lem3165224 : term189 = True.
Proof. exact (EQ_MP (@lem3165223) (@lem3165221)). Qed.
Lemma lem3165225 : term188 = True.
Proof. exact (TRANS (@lem3165220) (@lem3165224)). Qed.
Lemma lem3165226 : True = term188.
Proof. exact (SYM (@lem3165225)). Qed.
Lemma lem3165227 : term188.
Proof. exact (EQ_MP (@lem3165226) (@lem0)). Qed.
Lemma lem3165228 : term438.
Proof. exact (@lem3165217 (@lem3165227)). Qed.
Lemma lem3165230 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165231 : term188 = term189.
Proof. exact (@lem3165230 (NUMERAL 0) term2). Qed.
Lemma lem3165232 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165233 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165234 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165233 h1) (fun h1 : term189 = True => @lem3165232)). Qed.
Lemma lem3165235 : term189 = True.
Proof. exact (EQ_MP (@lem3165234) (@lem3165232)). Qed.
Lemma lem3165236 : term188 = True.
Proof. exact (TRANS (@lem3165231) (@lem3165235)). Qed.
Lemma lem3165237 : True = term188.
Proof. exact (SYM (@lem3165236)). Qed.
Lemma lem3165238 : term188.
Proof. exact (EQ_MP (@lem3165237) (@lem0)). Qed.
Lemma lem3165239 : term436 = term439.
Proof. exact (@lem3165228 (@lem3165238)). Qed.
Lemma lem3165241 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165242 : term169 = term170.
Proof. exact (@lem3165241 term2 term2). Qed.
Lemma lem3165243 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165244 : term172 = term2.
Proof. exact (EQ_MP (@lem3165243) (@lem940073)). Qed.
Lemma lem3165245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165246 : term170 = term93.
Proof. exact (MK_COMB (@lem3165245) (@lem3165244)). Qed.
Lemma lem3165247 : term169 = term93.
Proof. exact (TRANS (@lem3165242) (@lem3165246)). Qed.
Lemma lem3165249 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165250 : term275 = term79.
Proof. exact (@lem3165249 term2). Qed.
Lemma lem3165251 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3165252 : term440 = term434.
Proof. exact (MK_COMB (@lem3165251) (@lem3165250)). Qed.
Lemma lem3165253 : term439 = term188.
Proof. exact (MK_COMB (@lem3165252) (@lem3165247)). Qed.
Lemma lem3165255 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165256 : term188 = term189.
Proof. exact (@lem3165255 (NUMERAL 0) term2). Qed.
Lemma lem3165257 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165258 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165259 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165258 h1) (fun h1 : term189 = True => @lem3165257)). Qed.
Lemma lem3165260 : term189 = True.
Proof. exact (EQ_MP (@lem3165259) (@lem3165257)). Qed.
Lemma lem3165261 : term188 = True.
Proof. exact (TRANS (@lem3165256) (@lem3165260)). Qed.
Lemma lem3165262 : term439 = True.
Proof. exact (TRANS (@lem3165253) (@lem3165261)). Qed.
Lemma lem3165263 : term436 = True.
Proof. exact (TRANS (@lem3165239) (@lem3165262)). Qed.
Lemma lem3165264 : term188 = True.
Proof. exact (TRANS (@lem3165216) (@lem3165263)). Qed.
Lemma lem3165265 : term433 = True.
Proof. exact (TRANS (@lem3165207) (@lem3165264)). Qed.
Lemma lem3165266 : True = term433.
Proof. exact (SYM (@lem3165265)). Qed.
Lemma lem3165267 : term433.
Proof. exact (EQ_MP (@lem3165266) (@lem0)). Qed.
Lemma lem3165268 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term703 _32605 _32606.
Proof. exact (conj (@lem3165267) (@lem3165130 _32605 _32606 h1)). Qed.
Lemma lem3165270 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3165271 (_32605 : int) (_32606 : int) : term704 _32605 _32606.
Proof. exact (@lem3165270 term93 (term684 _32605 _32606)). Qed.
Lemma lem3165272 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term705 _32605 _32606.
Proof. exact (@lem3165271 _32605 _32606 (@lem3165268 _32605 _32606 h1)). Qed.
Lemma lem3165273 (_32605 : int) (_32606 : int) : (term706 _32605 _32606) = (term684 _32605 _32606).
Proof. exact (@lem1982733 (term684 _32605 _32606)). Qed.
Lemma lem3165274 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3165275 (_32605 : int) (_32606 : int) : (term707 _32605 _32606) = (term686 _32605 _32606).
Proof. exact (MK_COMB (@lem3165274) (@lem3165273 _32605 _32606)). Qed.
Lemma lem3165276 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3165277 (_32605 : int) (_32606 : int) : (term705 _32605 _32606) = (term687 _32605 _32606).
Proof. exact (MK_COMB (@lem3165275 _32605 _32606) (@lem3165276)). Qed.
Lemma lem3165278 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term687 _32605 _32606.
Proof. exact (EQ_MP (@lem3165277 _32605 _32606) (@lem3165272 _32605 _32606 h1)). Qed.
Lemma lem3165279 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term695 _32605 _32606.
Proof. exact (conj (@lem3165278 _32605 _32606 h1) (@lem3165204 _32605 _32606 h1)). Qed.
Lemma lem3165281 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3165282 (_32605 : int) (_32606 : int) : term708 _32605 _32606.
Proof. exact (@lem3165281 (term684 _32605 _32606) (term690 _32605 _32606)). Qed.
Lemma lem3165283 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term709 _32605 _32606.
Proof. exact (@lem3165282 _32605 _32606 (@lem3165279 _32605 _32606 h1)). Qed.
Lemma lem3165284 (_32605 : int) (_32606 : int) : (term710 _32605 _32606) = (term711 _32605 _32606).
Proof. exact (@lem1982753 (term263 _32605) (real_of_int _32605) (term252 _32606) (term263 _32606)). Qed.
Lemma lem3165285 (_32605 : int) : (term458 _32605) = (term459 _32605).
Proof. exact (@lem1982713 term160 (real_of_int _32605)). Qed.
Lemma lem3165287 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165288 : term93 = term182.
Proof. exact (@lem3165287 term2). Qed.
Lemma lem3165290 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3165291 : term160 = term161.
Proof. exact (@lem3165290 term2). Qed.
Lemma lem3165292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3165293 : term460 = term461.
Proof. exact (MK_COMB (@lem3165292) (@lem3165291)). Qed.
Lemma lem3165294 : term462 = term463.
Proof. exact (MK_COMB (@lem3165293) (@lem3165288)). Qed.
Lemma lem3165295 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3165297 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165298 : term188 = term189.
Proof. exact (@lem3165297 (NUMERAL 0) term2). Qed.
Lemma lem3165299 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165300 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165301 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165300 h1) (fun h1 : term189 = True => @lem3165299)). Qed.
Lemma lem3165302 : term189 = True.
Proof. exact (EQ_MP (@lem3165301) (@lem3165299)). Qed.
Lemma lem3165303 : term188 = True.
Proof. exact (TRANS (@lem3165298) (@lem3165302)). Qed.
Lemma lem3165304 : True = term188.
Proof. exact (SYM (@lem3165303)). Qed.
Lemma lem3165305 : term188.
Proof. exact (EQ_MP (@lem3165304) (@lem0)). Qed.
Lemma lem3165306 : term465.
Proof. exact (@lem3165295 (@lem3165305)). Qed.
Lemma lem3165308 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165309 : term188 = term189.
Proof. exact (@lem3165308 (NUMERAL 0) term2). Qed.
Lemma lem3165310 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165311 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165312 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165311 h1) (fun h1 : term189 = True => @lem3165310)). Qed.
Lemma lem3165313 : term189 = True.
Proof. exact (EQ_MP (@lem3165312) (@lem3165310)). Qed.
Lemma lem3165314 : term188 = True.
Proof. exact (TRANS (@lem3165309) (@lem3165313)). Qed.
Lemma lem3165315 : True = term188.
Proof. exact (SYM (@lem3165314)). Qed.
Lemma lem3165316 : term188.
Proof. exact (EQ_MP (@lem3165315) (@lem0)). Qed.
Lemma lem3165317 : term466.
Proof. exact (@lem3165306 (@lem3165316)). Qed.
Lemma lem3165319 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165320 : term188 = term189.
Proof. exact (@lem3165319 (NUMERAL 0) term2). Qed.
Lemma lem3165321 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165322 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165323 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165322 h1) (fun h1 : term189 = True => @lem3165321)). Qed.
Lemma lem3165324 : term189 = True.
Proof. exact (EQ_MP (@lem3165323) (@lem3165321)). Qed.
Lemma lem3165325 : term188 = True.
Proof. exact (TRANS (@lem3165320) (@lem3165324)). Qed.
Lemma lem3165326 : True = term188.
Proof. exact (SYM (@lem3165325)). Qed.
Lemma lem3165327 : term188.
Proof. exact (EQ_MP (@lem3165326) (@lem0)). Qed.
Lemma lem3165328 : term467.
Proof. exact (@lem3165317 (@lem3165327)). Qed.
Lemma lem3165330 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165331 : term169 = term170.
Proof. exact (@lem3165330 term2 term2). Qed.
Lemma lem3165332 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165333 : term172 = term2.
Proof. exact (EQ_MP (@lem3165332) (@lem940073)). Qed.
Lemma lem3165334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165335 : term170 = term93.
Proof. exact (MK_COMB (@lem3165334) (@lem3165333)). Qed.
Lemma lem3165336 : term169 = term93.
Proof. exact (TRANS (@lem3165331) (@lem3165335)). Qed.
Lemma lem3165338 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3165339 : term236 = term239.
Proof. exact (@lem3165338 term2 term2). Qed.
Lemma lem3165340 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165341 : term172 = term2.
Proof. exact (EQ_MP (@lem3165340) (@lem940073)). Qed.
Lemma lem3165342 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165343 : term170 = term93.
Proof. exact (MK_COMB (@lem3165342) (@lem3165341)). Qed.
Lemma lem3165344 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3165345 : term239 = term160.
Proof. exact (MK_COMB (@lem3165344) (@lem3165343)). Qed.
Lemma lem3165346 : term236 = term160.
Proof. exact (TRANS (@lem3165339) (@lem3165345)). Qed.
Lemma lem3165347 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3165348 : term468 = term460.
Proof. exact (MK_COMB (@lem3165347) (@lem3165346)). Qed.
Lemma lem3165349 : term469 = term462.
Proof. exact (MK_COMB (@lem3165348) (@lem3165336)). Qed.
Lemma lem3165351 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3165352 : term462 = term79.
Proof. exact (@lem3165351 term2). Qed.
Lemma lem3165353 : term469 = term79.
Proof. exact (TRANS (@lem3165349) (@lem3165352)). Qed.
Lemma lem3165354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165355 : term471 = term273.
Proof. exact (MK_COMB (@lem3165354) (@lem3165353)). Qed.
Lemma lem3165356 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3165357 : term472 = term275.
Proof. exact (MK_COMB (@lem3165355) (@lem3165356)). Qed.
Lemma lem3165359 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165360 : term275 = term79.
Proof. exact (@lem3165359 term2). Qed.
Lemma lem3165361 : term472 = term79.
Proof. exact (TRANS (@lem3165357) (@lem3165360)). Qed.
Lemma lem3165363 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165364 : term169 = term170.
Proof. exact (@lem3165363 term2 term2). Qed.
Lemma lem3165365 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165366 : term172 = term2.
Proof. exact (EQ_MP (@lem3165365) (@lem940073)). Qed.
Lemma lem3165367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165368 : term170 = term93.
Proof. exact (MK_COMB (@lem3165367) (@lem3165366)). Qed.
Lemma lem3165369 : term169 = term93.
Proof. exact (TRANS (@lem3165364) (@lem3165368)). Qed.
Lemma lem3165370 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3165371 : term277 = term275.
Proof. exact (MK_COMB (@lem3165370) (@lem3165369)). Qed.
Lemma lem3165373 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165374 : term275 = term79.
Proof. exact (@lem3165373 term2). Qed.
Lemma lem3165375 : term277 = term79.
Proof. exact (TRANS (@lem3165371) (@lem3165374)). Qed.
Lemma lem3165376 : term79 = term277.
Proof. exact (SYM (@lem3165375)). Qed.
Lemma lem3165377 : term472 = term277.
Proof. exact (TRANS (@lem3165361) (@lem3165376)). Qed.
Lemma lem3165378 : term463 = term157.
Proof. exact (@lem3165328 (@lem3165377)). Qed.
Lemma lem3165379 : term462 = term157.
Proof. exact (TRANS (@lem3165294) (@lem3165378)). Qed.
Lemma lem3165381 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3165382 : term157 = term79.
Proof. exact (@lem3165381 term79). Qed.
Lemma lem3165383 : term462 = term79.
Proof. exact (TRANS (@lem3165379) (@lem3165382)). Qed.
Lemma lem3165384 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165385 : term473 = term273.
Proof. exact (MK_COMB (@lem3165384) (@lem3165383)). Qed.
Lemma lem3165386 (_32605 : int) : (real_of_int _32605) = (real_of_int _32605).
Proof. exact (eq_refl (real_of_int _32605)). Qed.
Lemma lem3165387 (_32605 : int) : (term459 _32605) = (term474 _32605).
Proof. exact (MK_COMB (@lem3165385) (@lem3165386 _32605)). Qed.
Lemma lem3165388 (_32605 : int) : (term458 _32605) = (term474 _32605).
Proof. exact (TRANS (@lem3165285 _32605) (@lem3165387 _32605)). Qed.
Lemma lem3165389 (_32605 : int) : (term474 _32605) = term79.
Proof. exact (@lem1982719 (real_of_int _32605)). Qed.
Lemma lem3165390 (_32605 : int) : (term458 _32605) = term79.
Proof. exact (TRANS (@lem3165388 _32605) (@lem3165389 _32605)). Qed.
Lemma lem3165391 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3165392 (_32605 : int) : (term475 _32605) = term121.
Proof. exact (MK_COMB (@lem3165391) (@lem3165390 _32605)). Qed.
Lemma lem3165393 (_32606 : int) : (term600 _32606) = (term569 _32606).
Proof. exact (@lem1982759 (real_of_int _32606) (term263 _32606) term160). Qed.
Lemma lem3165394 (_32606 : int) : (term570 _32606) = (term459 _32606).
Proof. exact (@lem1982715 term160 (real_of_int _32606)). Qed.
Lemma lem3165396 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165397 : term93 = term182.
Proof. exact (@lem3165396 term2). Qed.
Lemma lem3165399 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3165400 : term160 = term161.
Proof. exact (@lem3165399 term2). Qed.
Lemma lem3165401 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3165402 : term460 = term461.
Proof. exact (MK_COMB (@lem3165401) (@lem3165400)). Qed.
Lemma lem3165403 : term462 = term463.
Proof. exact (MK_COMB (@lem3165402) (@lem3165397)). Qed.
Lemma lem3165404 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3165406 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165407 : term188 = term189.
Proof. exact (@lem3165406 (NUMERAL 0) term2). Qed.
Lemma lem3165408 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165409 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165410 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165409 h1) (fun h1 : term189 = True => @lem3165408)). Qed.
Lemma lem3165411 : term189 = True.
Proof. exact (EQ_MP (@lem3165410) (@lem3165408)). Qed.
Lemma lem3165412 : term188 = True.
Proof. exact (TRANS (@lem3165407) (@lem3165411)). Qed.
Lemma lem3165413 : True = term188.
Proof. exact (SYM (@lem3165412)). Qed.
Lemma lem3165414 : term188.
Proof. exact (EQ_MP (@lem3165413) (@lem0)). Qed.
Lemma lem3165415 : term465.
Proof. exact (@lem3165404 (@lem3165414)). Qed.
Lemma lem3165417 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165418 : term188 = term189.
Proof. exact (@lem3165417 (NUMERAL 0) term2). Qed.
Lemma lem3165419 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165420 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165421 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165420 h1) (fun h1 : term189 = True => @lem3165419)). Qed.
Lemma lem3165422 : term189 = True.
Proof. exact (EQ_MP (@lem3165421) (@lem3165419)). Qed.
Lemma lem3165423 : term188 = True.
Proof. exact (TRANS (@lem3165418) (@lem3165422)). Qed.
Lemma lem3165424 : True = term188.
Proof. exact (SYM (@lem3165423)). Qed.
Lemma lem3165425 : term188.
Proof. exact (EQ_MP (@lem3165424) (@lem0)). Qed.
Lemma lem3165426 : term466.
Proof. exact (@lem3165415 (@lem3165425)). Qed.
Lemma lem3165428 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165429 : term188 = term189.
Proof. exact (@lem3165428 (NUMERAL 0) term2). Qed.
Lemma lem3165430 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165431 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165432 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165431 h1) (fun h1 : term189 = True => @lem3165430)). Qed.
Lemma lem3165433 : term189 = True.
Proof. exact (EQ_MP (@lem3165432) (@lem3165430)). Qed.
Lemma lem3165434 : term188 = True.
Proof. exact (TRANS (@lem3165429) (@lem3165433)). Qed.
Lemma lem3165435 : True = term188.
Proof. exact (SYM (@lem3165434)). Qed.
Lemma lem3165436 : term188.
Proof. exact (EQ_MP (@lem3165435) (@lem0)). Qed.
Lemma lem3165437 : term467.
Proof. exact (@lem3165426 (@lem3165436)). Qed.
Lemma lem3165439 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165440 : term169 = term170.
Proof. exact (@lem3165439 term2 term2). Qed.
Lemma lem3165441 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165442 : term172 = term2.
Proof. exact (EQ_MP (@lem3165441) (@lem940073)). Qed.
Lemma lem3165443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165444 : term170 = term93.
Proof. exact (MK_COMB (@lem3165443) (@lem3165442)). Qed.
Lemma lem3165445 : term169 = term93.
Proof. exact (TRANS (@lem3165440) (@lem3165444)). Qed.
Lemma lem3165447 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3165448 : term236 = term239.
Proof. exact (@lem3165447 term2 term2). Qed.
Lemma lem3165449 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165450 : term172 = term2.
Proof. exact (EQ_MP (@lem3165449) (@lem940073)). Qed.
Lemma lem3165451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165452 : term170 = term93.
Proof. exact (MK_COMB (@lem3165451) (@lem3165450)). Qed.
Lemma lem3165453 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3165454 : term239 = term160.
Proof. exact (MK_COMB (@lem3165453) (@lem3165452)). Qed.
Lemma lem3165455 : term236 = term160.
Proof. exact (TRANS (@lem3165448) (@lem3165454)). Qed.
Lemma lem3165456 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3165457 : term468 = term460.
Proof. exact (MK_COMB (@lem3165456) (@lem3165455)). Qed.
Lemma lem3165458 : term469 = term462.
Proof. exact (MK_COMB (@lem3165457) (@lem3165445)). Qed.
Lemma lem3165460 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3165461 : term462 = term79.
Proof. exact (@lem3165460 term2). Qed.
Lemma lem3165462 : term469 = term79.
Proof. exact (TRANS (@lem3165458) (@lem3165461)). Qed.
Lemma lem3165463 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165464 : term471 = term273.
Proof. exact (MK_COMB (@lem3165463) (@lem3165462)). Qed.
Lemma lem3165465 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3165466 : term472 = term275.
Proof. exact (MK_COMB (@lem3165464) (@lem3165465)). Qed.
Lemma lem3165468 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165469 : term275 = term79.
Proof. exact (@lem3165468 term2). Qed.
Lemma lem3165470 : term472 = term79.
Proof. exact (TRANS (@lem3165466) (@lem3165469)). Qed.
Lemma lem3165472 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165473 : term169 = term170.
Proof. exact (@lem3165472 term2 term2). Qed.
Lemma lem3165474 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165475 : term172 = term2.
Proof. exact (EQ_MP (@lem3165474) (@lem940073)). Qed.
Lemma lem3165476 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165477 : term170 = term93.
Proof. exact (MK_COMB (@lem3165476) (@lem3165475)). Qed.
Lemma lem3165478 : term169 = term93.
Proof. exact (TRANS (@lem3165473) (@lem3165477)). Qed.
Lemma lem3165479 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3165480 : term277 = term275.
Proof. exact (MK_COMB (@lem3165479) (@lem3165478)). Qed.
Lemma lem3165482 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165483 : term275 = term79.
Proof. exact (@lem3165482 term2). Qed.
Lemma lem3165484 : term277 = term79.
Proof. exact (TRANS (@lem3165480) (@lem3165483)). Qed.
Lemma lem3165485 : term79 = term277.
Proof. exact (SYM (@lem3165484)). Qed.
Lemma lem3165486 : term472 = term277.
Proof. exact (TRANS (@lem3165470) (@lem3165485)). Qed.
Lemma lem3165487 : term463 = term157.
Proof. exact (@lem3165437 (@lem3165486)). Qed.
Lemma lem3165488 : term462 = term157.
Proof. exact (TRANS (@lem3165403) (@lem3165487)). Qed.
Lemma lem3165490 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3165491 : term157 = term79.
Proof. exact (@lem3165490 term79). Qed.
Lemma lem3165492 : term462 = term79.
Proof. exact (TRANS (@lem3165488) (@lem3165491)). Qed.
Lemma lem3165493 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165494 : term473 = term273.
Proof. exact (MK_COMB (@lem3165493) (@lem3165492)). Qed.
Lemma lem3165495 (_32606 : int) : (real_of_int _32606) = (real_of_int _32606).
Proof. exact (eq_refl (real_of_int _32606)). Qed.
Lemma lem3165496 (_32606 : int) : (term459 _32606) = (term474 _32606).
Proof. exact (MK_COMB (@lem3165494) (@lem3165495 _32606)). Qed.
Lemma lem3165497 (_32606 : int) : (term570 _32606) = (term474 _32606).
Proof. exact (TRANS (@lem3165394 _32606) (@lem3165496 _32606)). Qed.
Lemma lem3165498 (_32606 : int) : (term474 _32606) = term79.
Proof. exact (@lem1982719 (real_of_int _32606)). Qed.
Lemma lem3165499 (_32606 : int) : (term570 _32606) = term79.
Proof. exact (TRANS (@lem3165497 _32606) (@lem3165498 _32606)). Qed.
Lemma lem3165500 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3165501 (_32606 : int) : (term571 _32606) = term121.
Proof. exact (MK_COMB (@lem3165500) (@lem3165499 _32606)). Qed.
Lemma lem3165502 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3165503 (_32606 : int) : (term569 _32606) = term490.
Proof. exact (MK_COMB (@lem3165501 _32606) (@lem3165502)). Qed.
Lemma lem3165504 (_32606 : int) : (term600 _32606) = term490.
Proof. exact (TRANS (@lem3165393 _32606) (@lem3165503 _32606)). Qed.
Lemma lem3165505 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3165506 (_32606 : int) : (term600 _32606) = term160.
Proof. exact (TRANS (@lem3165504 _32606) (@lem3165505)). Qed.
Lemma lem3165507 (_32605 : int) (_32606 : int) : (term711 _32605 _32606) = term490.
Proof. exact (MK_COMB (@lem3165392 _32605) (@lem3165506 _32606)). Qed.
Lemma lem3165508 (_32605 : int) (_32606 : int) : (term710 _32605 _32606) = term490.
Proof. exact (TRANS (@lem3165284 _32605 _32606) (@lem3165507 _32605 _32606)). Qed.
Lemma lem3165509 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3165510 (_32605 : int) (_32606 : int) : (term710 _32605 _32606) = term160.
Proof. exact (TRANS (@lem3165508 _32605 _32606) (@lem3165509)). Qed.
Lemma lem3165511 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3165512 (_32605 : int) (_32606 : int) : (term712 _32605 _32606) = term492.
Proof. exact (MK_COMB (@lem3165511) (@lem3165510 _32605 _32606)). Qed.
Lemma lem3165513 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3165514 (_32605 : int) (_32606 : int) : (term709 _32605 _32606) = term493.
Proof. exact (MK_COMB (@lem3165512 _32605 _32606) (@lem3165513)). Qed.
Lemma lem3165515 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term493.
Proof. exact (EQ_MP (@lem3165514 _32605 _32606) (@lem3165283 _32605 _32606 h1)). Qed.
Lemma lem3165517 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3165518 : term493 = term494.
Proof. exact (@lem3165517 term79 term160). Qed.
Lemma lem3165520 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3165521 : term160 = term161.
Proof. exact (@lem3165520 term2). Qed.
Lemma lem3165523 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165524 : term79 = term157.
Proof. exact (@lem3165523 (NUMERAL 0)). Qed.
Lemma lem3165525 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3165526 : term81 = term495.
Proof. exact (MK_COMB (@lem3165525) (@lem3165524)). Qed.
Lemma lem3165527 : term494 = term496.
Proof. exact (MK_COMB (@lem3165526) (@lem3165521)). Qed.
Lemma lem3165528 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3165530 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165531 : term188 = term189.
Proof. exact (@lem3165530 (NUMERAL 0) term2). Qed.
Lemma lem3165532 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165533 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165534 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165533 h1) (fun h1 : term189 = True => @lem3165532)). Qed.
Lemma lem3165535 : term189 = True.
Proof. exact (EQ_MP (@lem3165534) (@lem3165532)). Qed.
Lemma lem3165536 : term188 = True.
Proof. exact (TRANS (@lem3165531) (@lem3165535)). Qed.
Lemma lem3165537 : True = term188.
Proof. exact (SYM (@lem3165536)). Qed.
Lemma lem3165538 : term188.
Proof. exact (EQ_MP (@lem3165537) (@lem0)). Qed.
Lemma lem3165539 : term498.
Proof. exact (@lem3165528 (@lem3165538)). Qed.
Lemma lem3165541 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3165542 : term188 = term189.
Proof. exact (@lem3165541 (NUMERAL 0) term2). Qed.
Lemma lem3165543 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165544 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3165545 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165544 h1) (fun h1 : term189 = True => @lem3165543)). Qed.
Lemma lem3165546 : term189 = True.
Proof. exact (EQ_MP (@lem3165545) (@lem3165543)). Qed.
Lemma lem3165547 : term188 = True.
Proof. exact (TRANS (@lem3165542) (@lem3165546)). Qed.
Lemma lem3165548 : True = term188.
Proof. exact (SYM (@lem3165547)). Qed.
Lemma lem3165549 : term188.
Proof. exact (EQ_MP (@lem3165548) (@lem0)). Qed.
Lemma lem3165550 : term496 = term499.
Proof. exact (@lem3165539 (@lem3165549)). Qed.
Lemma lem3165552 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3165553 : term236 = term239.
Proof. exact (@lem3165552 term2 term2). Qed.
Lemma lem3165554 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165555 : term172 = term2.
Proof. exact (EQ_MP (@lem3165554) (@lem940073)). Qed.
Lemma lem3165556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165557 : term170 = term93.
Proof. exact (MK_COMB (@lem3165556) (@lem3165555)). Qed.
Lemma lem3165558 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3165559 : term239 = term160.
Proof. exact (MK_COMB (@lem3165558) (@lem3165557)). Qed.
Lemma lem3165560 : term236 = term160.
Proof. exact (TRANS (@lem3165553) (@lem3165559)). Qed.
Lemma lem3165562 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3165563 : term275 = term79.
Proof. exact (@lem3165562 term2). Qed.
Lemma lem3165564 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3165565 : term500 = term81.
Proof. exact (MK_COMB (@lem3165564) (@lem3165563)). Qed.
Lemma lem3165566 : term499 = term494.
Proof. exact (MK_COMB (@lem3165565) (@lem3165560)). Qed.
Lemma lem3165568 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3165569 : term494 = term503.
Proof. exact (@lem3165568 (NUMERAL 0) term2). Qed.
Lemma lem3165570 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3165571 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3165572 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3165571 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3165570)). Qed.
Lemma lem3165573 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3165572) (@lem3165570)). Qed.
Lemma lem3165574 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3165575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165576 : term504 = (and True).
Proof. exact (MK_COMB (@lem3165575) (@lem3165574)). Qed.
Lemma lem3165577 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3165576) (@lem3165573)). Qed.
Lemma lem3165579 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3165580 : term503 = False.
Proof. exact (TRANS (@lem3165577) (@lem3165579)). Qed.
Lemma lem3165581 : term494 = False.
Proof. exact (TRANS (@lem3165569) (@lem3165580)). Qed.
Lemma lem3165582 : term499 = False.
Proof. exact (TRANS (@lem3165566) (@lem3165581)). Qed.
Lemma lem3165583 : term496 = False.
Proof. exact (TRANS (@lem3165550) (@lem3165582)). Qed.
Lemma lem3165584 : term494 = False.
Proof. exact (TRANS (@lem3165527) (@lem3165583)). Qed.
Lemma lem3165585 : term493 = False.
Proof. exact (TRANS (@lem3165518) (@lem3165584)). Qed.
Lemma lem3165586 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : False.
Proof. exact (EQ_MP (@lem3165585) (@lem3165515 _32605 _32606 h1)). Qed.
Lemma lem3165588 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : term697 _32605 _32606.
Proof. exact (h1). Qed.
Lemma lem3165589 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : (term697 _32605 _32606) = False.
Proof. exact (prop_ext (fun h2 : term697 _32605 _32606 => @lem3165586 _32605 _32606 h1) (fun h2 : False => @lem3165588 _32605 _32606 h1)). Qed.
Lemma lem3165590 (_32605 : int) (_32606 : int) (h1 : term697 _32605 _32606) : False.
Proof. exact (EQ_MP (@lem3165589 _32605 _32606 h1) (@lem3165588 _32605 _32606 h1)). Qed.
Lemma lem3165591 (_32606 : int) (_32605 : int) (h1 : term679 _32606 _32605) : term679 _32606 _32605.
Proof. exact (h1). Qed.
Lemma lem3165592 (_32606 : int) (_32605 : int) (h1 : term679 _32606 _32605) : term697 _32605 _32606.
Proof. exact (EQ_MP (@lem3165120 _32605 _32606) (@lem3165591 _32606 _32605 h1)). Qed.
Lemma lem3165593 (_32606 : int) (_32605 : int) (h1 : term679 _32606 _32605) : (term697 _32605 _32606) = False.
Proof. exact (prop_ext (fun h2 : term697 _32605 _32606 => @lem3165590 _32605 _32606 h2) (fun h2 : False => @lem3165592 _32606 _32605 h1)). Qed.
Lemma lem3165594 (_32606 : int) (_32605 : int) (h1 : term679 _32606 _32605) : False.
Proof. exact (EQ_MP (@lem3165593 _32606 _32605 h1) (@lem3165592 _32606 _32605 h1)). Qed.
Lemma lem3165595 (_32606 : int) (_32605 : int) : term713 _32606 _32605.
Proof. exact (fun h0 : term679 _32606 _32605 => @lem3165594 _32606 _32605 h0). Qed.
Lemma lem3165596 (_32606 : int) (_32605 : int) : term714 _32606 _32605.
Proof. exact (@lem1386578 (term715 _32606 _32605)). Qed.
Lemma lem3165599 (_32606 : int) (_32605 : int) : term715 _32606 _32605.
Proof. exact (@lem3165596 _32606 _32605 (@lem3165595 _32606 _32605)). Qed.
Lemma lem3165600 (_32606 : int) (_32605 : int) : (term678 _32606 _32605) = (term661 _32606 _32605).
Proof. exact (SYM (@lem3164858 _32606 _32605)). Qed.
Lemma lem3165601 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3165602 (_32606 : int) (_32605 : int) : (term715 _32606 _32605) = (term649 _32606 _32605).
Proof. exact (MK_COMB (@lem3165601) (@lem3165600 _32606 _32605)). Qed.
Lemma lem3165603 (_32606 : int) (_32605 : int) : term649 _32606 _32605.
Proof. exact (EQ_MP (@lem3165602 _32606 _32605) (@lem3165599 _32606 _32605)). Qed.
Lemma lem3165604 (_32606 : int) (_32605 : int) : term650 _32606 _32605.
Proof. exact (EQ_MP (@lem3164727 _32606 _32605) (@lem3165603 _32606 _32605)). Qed.
Lemma lem3165605 (a : nat) (b : nat) : term716 a b.
Proof. exact (@lem3165604 (term717 a b) (int_of_num b)). Qed.
Lemma lem3165606 (a : nat) (b : nat) : term718 a b.
Proof. exact (@lem3165605 a b (@lem3164723 b)). Qed.
Lemma lem3165607 (a : nat) (b : nat) : term646 a b.
Proof. exact (@lem3165606 a b (@lem3164726 a b)). Qed.
Lemma lem3165608 (a : nat) (b : nat) : (term646 a b) = ((term623 a b) = (term624 a b)).
Proof. exact (SYM (@lem3164720 a b)). Qed.
Lemma lem3165648 (b : nat) (a : nat) : ((term719 b a) = (term720 b a)) = (term721 b a).
Proof. exact (@lem17500 (term719 b a) (term720 b a)). Qed.
Lemma lem3165655 (a : nat) : (term722 a) = a.
Proof. exact (@lem1032072 a). Qed.
Lemma lem3165664 (a : nat) (b : nat) : (term627 a b) = (term627 a b).
Proof. exact (eq_refl (term627 a b)). Qed.
Lemma lem3165665 (b : nat) (a : nat) : (term720 b a) = (term719 b a).
Proof. exact (MK_COMB (@lem3165664 a b) (@lem3165655 a)). Qed.
Lemma lem3165666 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3165667 (b : nat) (a : nat) : (term723 b a) = (term724 b a).
Proof. exact (MK_COMB (@lem3165666) (@lem3165665 b a)). Qed.
Lemma lem3165682 (b : nat) (a : nat) : (term725 b a) = (term725 b a).
Proof. exact (eq_refl (term725 b a)). Qed.
Lemma lem3165683 (b : nat) (a : nat) : (term726 b a) = (term727 b a).
Proof. exact (MK_COMB (@lem3165682 b a) (@lem3165667 b a)). Qed.
Lemma lem3165690 (a : nat) : (term722 a) = a.
Proof. exact (@lem1032072 a). Qed.
Lemma lem3165699 (a : nat) (b : nat) : (term627 a b) = (term627 a b).
Proof. exact (eq_refl (term627 a b)). Qed.
Lemma lem3165700 (b : nat) (a : nat) : (term720 b a) = (term719 b a).
Proof. exact (MK_COMB (@lem3165699 a b) (@lem3165690 a)). Qed.
Lemma lem3165713 (b : nat) (a : nat) : (term728 b a) = (term728 b a).
Proof. exact (eq_refl (term728 b a)). Qed.
Lemma lem3165714 (b : nat) (a : nat) : (term729 b a) = (term730 b a).
Proof. exact (MK_COMB (@lem3165713 b a) (@lem3165700 b a)). Qed.
Lemma lem3165715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3165716 (b : nat) (a : nat) : (term731 b a) = (term732 b a).
Proof. exact (MK_COMB (@lem3165715) (@lem3165714 b a)). Qed.
Lemma lem3165717 (b : nat) (a : nat) : (term721 b a) = (term733 b a).
Proof. exact (MK_COMB (@lem3165716 b a) (@lem3165683 b a)). Qed.
Lemma lem3165720 (b : nat) (a : nat) : ((term719 b a) = (term720 b a)) = (term733 b a).
Proof. exact (TRANS (@lem3165648 b a) (@lem3165717 b a)). Qed.
Lemma lem3165722 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3165723 (b : nat) (a : nat) : (term719 b a) = (term734 b a).
Proof. exact (@lem3165722 (Nat.mul a b) a). Qed.
Lemma lem3165724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165725 (b : nat) (a : nat) : (term728 b a) = (term735 b a).
Proof. exact (MK_COMB (@lem3165724) (@lem3165723 b a)). Qed.
Lemma lem3165727 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3165728 (b : nat) (a : nat) : (term719 b a) = (term734 b a).
Proof. exact (@lem3165727 (Nat.mul a b) a). Qed.
Lemma lem3165729 (b : nat) (a : nat) : (term730 b a) = (term736 b a).
Proof. exact (MK_COMB (@lem3165725 b a) (@lem3165728 b a)). Qed.
Lemma lem3165730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3165731 (b : nat) (a : nat) : (term732 b a) = (term737 b a).
Proof. exact (MK_COMB (@lem3165730) (@lem3165729 b a)). Qed.
Lemma lem3165733 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3165734 (b : nat) (a : nat) : (term719 b a) = (term734 b a).
Proof. exact (@lem3165733 (Nat.mul a b) a). Qed.
Lemma lem3165735 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3165736 (b : nat) (a : nat) : (term724 b a) = (term738 b a).
Proof. exact (MK_COMB (@lem3165735) (@lem3165734 b a)). Qed.
Lemma lem3165737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165738 (b : nat) (a : nat) : (term725 b a) = (term739 b a).
Proof. exact (MK_COMB (@lem3165737) (@lem3165736 b a)). Qed.
Lemma lem3165740 (m : nat) (n : nat) : (Peano.le m n) = (term11 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3165741 (b : nat) (a : nat) : (term719 b a) = (term734 b a).
Proof. exact (@lem3165740 (Nat.mul a b) a). Qed.
Lemma lem3165742 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3165743 (b : nat) (a : nat) : (term724 b a) = (term738 b a).
Proof. exact (MK_COMB (@lem3165742) (@lem3165741 b a)). Qed.
Lemma lem3165744 (b : nat) (a : nat) : (term727 b a) = (term740 b a).
Proof. exact (MK_COMB (@lem3165738 b a) (@lem3165743 b a)). Qed.
Lemma lem3165745 (b : nat) (a : nat) : (term733 b a) = (term741 b a).
Proof. exact (MK_COMB (@lem3165731 b a) (@lem3165744 b a)). Qed.
Lemma lem3165746 (b : nat) (a : nat) : ((term719 b a) = (term720 b a)) = (term741 b a).
Proof. exact (TRANS (@lem3165720 b a) (@lem3165745 b a)). Qed.
Lemma lem3165747 (a : nat) : term35 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem3165748 (a : nat) : (term35 a) = (term36 a).
Proof. exact (eq_refl (term35 a)). Qed.
Lemma lem3165749 (a : nat) : term36 a.
Proof. exact (EQ_MP (@lem3165748 a) (@lem3165747 a)). Qed.
Lemma lem3165750 (a : nat) (b : nat) : term647 a b.
Proof. exact (@lem2307535 (Nat.mul a b)). Qed.
Lemma lem3165751 (a : nat) (b : nat) : (term647 a b) = (term648 a b).
Proof. exact (eq_refl (term647 a b)). Qed.
Lemma lem3165752 (a : nat) (b : nat) : term648 a b.
Proof. exact (EQ_MP (@lem3165751 a b) (@lem3165750 a b)). Qed.
Lemma lem3165753 (_32610 : int) (_32609 : int) : (term649 _32610 _32609) = (term650 _32610 _32609).
Proof. exact (@lem2318604 (term650 _32610 _32609)). Qed.
Lemma lem3165762 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem16496 t)). Qed.
Lemma lem3165763 (_32610 : int) (_32609 : int) : (term651 _32610 _32609) = (int_le _32610 _32609).
Proof. exact (@lem3165762 (int_le _32610 _32609)). Qed.
Lemma lem3165764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3165765 (_32610 : int) (_32609 : int) : (term652 _32610 _32609) = (term653 _32610 _32609).
Proof. exact (MK_COMB (@lem3165764) (@lem3165763 _32610 _32609)). Qed.
Lemma lem3165767 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem16496 t)). Qed.
Lemma lem3165768 (_32610 : int) (_32609 : int) : (term654 _32610 _32609) = (term83 _32610 _32609).
Proof. exact (@lem3165767 (term83 _32610 _32609)). Qed.
Lemma lem3165769 (_32610 : int) (_32609 : int) : (term655 _32610 _32609) = (term656 _32610 _32609).
Proof. exact (MK_COMB (@lem3165765 _32610 _32609) (@lem3165768 _32610 _32609)). Qed.
Lemma lem3165772 (_32610 : int) : (term657 _32610) = (term657 _32610).
Proof. exact (eq_refl (term657 _32610)). Qed.
Lemma lem3165773 (_32610 : int) (_32609 : int) : (term658 _32610 _32609) = (term659 _32610 _32609).
Proof. exact (MK_COMB (@lem3165772 _32610) (@lem3165769 _32610 _32609)). Qed.
Lemma lem3165776 (_32609 : int) : (term657 _32609) = (term657 _32609).
Proof. exact (eq_refl (term657 _32609)). Qed.
Lemma lem3165777 (_32610 : int) (_32609 : int) : (term650 _32610 _32609) = (term660 _32610 _32609).
Proof. exact (MK_COMB (@lem3165776 _32609) (@lem3165773 _32610 _32609)). Qed.
Lemma lem3165780 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3165784 (_32610 : int) (_32609 : int) : (term661 _32610 _32609) = (term662 _32610 _32609).
Proof. exact (MK_COMB (@lem3165780) (@lem3165777 _32610 _32609)). Qed.
Lemma lem3165790 (_32610 : int) (_32609 : int) : (term663 _32610 _32609) = (int_le _32610 _32609).
Proof. exact (@lem16933 (int_le _32610 _32609)). Qed.
Lemma lem3165792 (_32610 : int) (_32609 : int) : (term664 _32610 _32609) = (term664 _32610 _32609).
Proof. exact (eq_refl (term664 _32610 _32609)). Qed.
Lemma lem3165793 (_32610 : int) (_32609 : int) : (term665 _32610 _32609) = (term666 _32610 _32609).
Proof. exact (MK_COMB (@lem3165792 _32610 _32609) (@lem3165790 _32610 _32609)). Qed.
Lemma lem3165794 (_32610 : int) (_32609 : int) : (term667 _32610 _32609) = (term665 _32610 _32609).
Proof. exact (@lem17160 (int_le _32610 _32609) (term83 _32610 _32609)). Qed.
Lemma lem3165795 (_32610 : int) (_32609 : int) : (term667 _32610 _32609) = (term666 _32610 _32609).
Proof. exact (TRANS (@lem3165794 _32610 _32609) (@lem3165793 _32610 _32609)). Qed.
Lemma lem3165797 (_32610 : int) : (term69 _32610) = (term69 _32610).
Proof. exact (eq_refl (term69 _32610)). Qed.
Lemma lem3165798 (_32610 : int) (_32609 : int) : (term668 _32610 _32609) = (term669 _32610 _32609).
Proof. exact (MK_COMB (@lem3165797 _32610) (@lem3165795 _32610 _32609)). Qed.
Lemma lem3165799 (_32610 : int) (_32609 : int) : (term670 _32610 _32609) = (term668 _32610 _32609).
Proof. exact (@lem17362 (term73 _32610) (term656 _32610 _32609)). Qed.
Lemma lem3165800 (_32610 : int) (_32609 : int) : (term670 _32610 _32609) = (term669 _32610 _32609).
Proof. exact (TRANS (@lem3165799 _32610 _32609) (@lem3165798 _32610 _32609)). Qed.
Lemma lem3165802 (_32609 : int) : (term69 _32609) = (term69 _32609).
Proof. exact (eq_refl (term69 _32609)). Qed.
Lemma lem3165803 (_32610 : int) (_32609 : int) : (term671 _32610 _32609) = (term672 _32610 _32609).
Proof. exact (MK_COMB (@lem3165802 _32609) (@lem3165800 _32610 _32609)). Qed.
Lemma lem3165804 (_32610 : int) (_32609 : int) : (term662 _32610 _32609) = (term671 _32610 _32609).
Proof. exact (@lem17362 (term73 _32609) (term659 _32610 _32609)). Qed.
Lemma lem3165805 (_32610 : int) (_32609 : int) : (term662 _32610 _32609) = (term672 _32610 _32609).
Proof. exact (TRANS (@lem3165804 _32610 _32609) (@lem3165803 _32610 _32609)). Qed.
Lemma lem3165822 (_32610 : int) (_32609 : int) : (term661 _32610 _32609) = (term672 _32610 _32609).
Proof. exact (TRANS (@lem3165784 _32610 _32609) (@lem3165805 _32610 _32609)). Qed.
Lemma lem3165825 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3165826 (_32609 : int) : (term73 _32609) = (term76 _32609).
Proof. exact (@lem3165825 term15 _32609). Qed.
Lemma lem3165828 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3165829 : term78 = term79.
Proof. exact (@lem3165828 (NUMERAL 0)). Qed.
Lemma lem3165830 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3165831 : term80 = term81.
Proof. exact (MK_COMB (@lem3165830) (@lem3165829)). Qed.
Lemma lem3165832 (_32609 : int) : (real_of_int _32609) = (real_of_int _32609).
Proof. exact (eq_refl (real_of_int _32609)). Qed.
Lemma lem3165833 (_32609 : int) : (term76 _32609) = (term82 _32609).
Proof. exact (MK_COMB (@lem3165831) (@lem3165832 _32609)). Qed.
Lemma lem3165835 (_32609 : int) : (term73 _32609) = (term82 _32609).
Proof. exact (TRANS (@lem3165826 _32609) (@lem3165833 _32609)). Qed.
Lemma lem3165838 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3165839 (_32610 : int) : (term73 _32610) = (term76 _32610).
Proof. exact (@lem3165838 term15 _32610). Qed.
Lemma lem3165841 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3165842 : term78 = term79.
Proof. exact (@lem3165841 (NUMERAL 0)). Qed.
Lemma lem3165843 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3165844 : term80 = term81.
Proof. exact (MK_COMB (@lem3165843) (@lem3165842)). Qed.
Lemma lem3165845 (_32610 : int) : (real_of_int _32610) = (real_of_int _32610).
Proof. exact (eq_refl (real_of_int _32610)). Qed.
Lemma lem3165846 (_32610 : int) : (term76 _32610) = (term82 _32610).
Proof. exact (MK_COMB (@lem3165844) (@lem3165845 _32610)). Qed.
Lemma lem3165848 (_32610 : int) : (term73 _32610) = (term82 _32610).
Proof. exact (TRANS (@lem3165839 _32610) (@lem3165846 _32610)). Qed.
Lemma lem3165850 (y : int) (x : int) : (term83 x y) = (term84 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem3165851 (_32609 : int) (_32610 : int) : (term83 _32610 _32609) = (term84 _32609 _32610).
Proof. exact (@lem3165850 _32609 _32610). Qed.
Lemma lem3165853 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3165854 (_32609 : int) (_32610 : int) : (term84 _32609 _32610) = (term673 _32609 _32610).
Proof. exact (@lem3165853 (term105 _32609) _32610). Qed.
Lemma lem3165856 (x : int) (y : int) : (term88 x y) = (term89 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3165857 (_32609 : int) : (term106 _32609) = (term107 _32609).
Proof. exact (@lem3165856 _32609 term18). Qed.
Lemma lem3165859 (n : nat) : (term77 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3165860 : term92 = term93.
Proof. exact (@lem3165859 term2). Qed.
Lemma lem3165861 (_32609 : int) : (term108 _32609) = (term108 _32609).
Proof. exact (eq_refl (term108 _32609)). Qed.
Lemma lem3165862 (_32609 : int) : (term107 _32609) = (term109 _32609).
Proof. exact (MK_COMB (@lem3165861 _32609) (@lem3165860)). Qed.
Lemma lem3165863 (_32609 : int) : (term106 _32609) = (term109 _32609).
Proof. exact (TRANS (@lem3165857 _32609) (@lem3165862 _32609)). Qed.
Lemma lem3165864 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3165865 (_32609 : int) : (term110 _32609) = (term111 _32609).
Proof. exact (MK_COMB (@lem3165864) (@lem3165863 _32609)). Qed.
Lemma lem3165866 (_32610 : int) : (real_of_int _32610) = (real_of_int _32610).
Proof. exact (eq_refl (real_of_int _32610)). Qed.
Lemma lem3165867 (_32609 : int) (_32610 : int) : (term673 _32609 _32610) = (term674 _32609 _32610).
Proof. exact (MK_COMB (@lem3165865 _32609) (@lem3165866 _32610)). Qed.
Lemma lem3165868 (_32609 : int) (_32610 : int) : (term84 _32609 _32610) = (term674 _32609 _32610).
Proof. exact (TRANS (@lem3165854 _32609 _32610) (@lem3165867 _32609 _32610)). Qed.
Lemma lem3165869 (_32609 : int) (_32610 : int) : (term83 _32610 _32609) = (term674 _32609 _32610).
Proof. exact (TRANS (@lem3165851 _32609 _32610) (@lem3165868 _32609 _32610)). Qed.
Lemma lem3165872 (x : int) (y : int) : (int_le x y) = (term75 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3165874 (_32610 : int) (_32609 : int) : (int_le _32610 _32609) = (term75 _32610 _32609).
Proof. exact (@lem3165872 _32610 _32609). Qed.
Lemma lem3165875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165876 (_32609 : int) (_32610 : int) : (term664 _32610 _32609) = (term675 _32609 _32610).
Proof. exact (MK_COMB (@lem3165875) (@lem3165869 _32609 _32610)). Qed.
Lemma lem3165877 (_32610 : int) (_32609 : int) : (term666 _32610 _32609) = (term676 _32610 _32609).
Proof. exact (MK_COMB (@lem3165876 _32609 _32610) (@lem3165874 _32610 _32609)). Qed.
Lemma lem3165878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165879 (_32610 : int) : (term69 _32610) = (term149 _32610).
Proof. exact (MK_COMB (@lem3165878) (@lem3165848 _32610)). Qed.
Lemma lem3165880 (_32610 : int) (_32609 : int) : (term669 _32610 _32609) = (term677 _32610 _32609).
Proof. exact (MK_COMB (@lem3165879 _32610) (@lem3165877 _32610 _32609)). Qed.
Lemma lem3165881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3165882 (_32609 : int) : (term69 _32609) = (term149 _32609).
Proof. exact (MK_COMB (@lem3165881) (@lem3165835 _32609)). Qed.
Lemma lem3165883 (_32610 : int) (_32609 : int) : (term672 _32610 _32609) = (term678 _32610 _32609).
Proof. exact (MK_COMB (@lem3165882 _32609) (@lem3165880 _32610 _32609)). Qed.
Lemma lem3165884 (_32610 : int) (_32609 : int) : (term661 _32610 _32609) = (term678 _32610 _32609).
Proof. exact (TRANS (@lem3165822 _32610 _32609) (@lem3165883 _32610 _32609)). Qed.
Lemma lem3165888 (t : Prop) : (term151 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3165924 (_32610 : int) (_32609 : int) : (term679 _32610 _32609) = (term678 _32610 _32609).
Proof. exact (@lem3165888 (term678 _32610 _32609)). Qed.
Lemma lem3165925 (_32609 : int) : (term82 _32609) = (term153 _32609).
Proof. exact (@lem1988287 (real_of_int _32609) term79). Qed.
Lemma lem3165931 (_32609 : int) : (term154 _32609) = (term155 _32609).
Proof. exact (@lem1982792 (real_of_int _32609) term79). Qed.
Lemma lem3165933 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165934 : term79 = term157.
Proof. exact (@lem3165933 (NUMERAL 0)). Qed.
Lemma lem3165936 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3165937 : term160 = term161.
Proof. exact (@lem3165936 term2). Qed.
Lemma lem3165938 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165939 : term162 = term163.
Proof. exact (MK_COMB (@lem3165938) (@lem3165937)). Qed.
Lemma lem3165940 : term164 = term165.
Proof. exact (MK_COMB (@lem3165939) (@lem3165934)). Qed.
Lemma lem3165941 : term165 = term166.
Proof. exact (@lem1981613 term160 term79 term93 term93). Qed.
Lemma lem3165943 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165944 : term169 = term170.
Proof. exact (@lem3165943 term2 term2). Qed.
Lemma lem3165945 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165946 : term172 = term2.
Proof. exact (EQ_MP (@lem3165945) (@lem940073)). Qed.
Lemma lem3165947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165948 : term170 = term93.
Proof. exact (MK_COMB (@lem3165947) (@lem3165946)). Qed.
Lemma lem3165949 : term169 = term93.
Proof. exact (TRANS (@lem3165944) (@lem3165948)). Qed.
Lemma lem3165951 (x : nat) : (term173 x) = term79.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3165952 : term164 = term79.
Proof. exact (@lem3165951 term2). Qed.
Lemma lem3165953 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3165954 : term174 = term175.
Proof. exact (MK_COMB (@lem3165953) (@lem3165952)). Qed.
Lemma lem3165955 : term166 = term157.
Proof. exact (MK_COMB (@lem3165954) (@lem3165949)). Qed.
Lemma lem3165956 : term165 = term157.
Proof. exact (TRANS (@lem3165941) (@lem3165955)). Qed.
Lemma lem3165957 : term164 = term157.
Proof. exact (TRANS (@lem3165940) (@lem3165956)). Qed.
Lemma lem3165959 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3165960 : term157 = term79.
Proof. exact (@lem3165959 term79). Qed.
Lemma lem3165961 : term164 = term79.
Proof. exact (TRANS (@lem3165957) (@lem3165960)). Qed.
Lemma lem3165962 (_32609 : int) : (term108 _32609) = (term108 _32609).
Proof. exact (eq_refl (term108 _32609)). Qed.
Lemma lem3165963 (_32609 : int) : (term155 _32609) = (term177 _32609).
Proof. exact (MK_COMB (@lem3165962 _32609) (@lem3165961)). Qed.
Lemma lem3165964 (_32609 : int) : (term177 _32609) = (real_of_int _32609).
Proof. exact (@lem1982723 (real_of_int _32609)). Qed.
Lemma lem3165965 (_32609 : int) : (term155 _32609) = (real_of_int _32609).
Proof. exact (TRANS (@lem3165963 _32609) (@lem3165964 _32609)). Qed.
Lemma lem3165967 (_32609 : int) : (term154 _32609) = (real_of_int _32609).
Proof. exact (TRANS (@lem3165931 _32609) (@lem3165965 _32609)). Qed.
Lemma lem3165968 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3165969 (_32609 : int) : (term178 _32609) = (term179 _32609).
Proof. exact (MK_COMB (@lem3165968) (@lem3165967 _32609)). Qed.
Lemma lem3165970 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3165971 (_32609 : int) : (term153 _32609) = (term180 _32609).
Proof. exact (MK_COMB (@lem3165969 _32609) (@lem3165970)). Qed.
Lemma lem3165972 (_32609 : int) : (term82 _32609) = (term180 _32609).
Proof. exact (TRANS (@lem3165925 _32609) (@lem3165971 _32609)). Qed.
Lemma lem3165973 (_32610 : int) : (term82 _32610) = (term153 _32610).
Proof. exact (@lem1988287 (real_of_int _32610) term79). Qed.
Lemma lem3165979 (_32610 : int) : (term154 _32610) = (term155 _32610).
Proof. exact (@lem1982792 (real_of_int _32610) term79). Qed.
Lemma lem3165981 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3165982 : term79 = term157.
Proof. exact (@lem3165981 (NUMERAL 0)). Qed.
Lemma lem3165984 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3165985 : term160 = term161.
Proof. exact (@lem3165984 term2). Qed.
Lemma lem3165986 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3165987 : term162 = term163.
Proof. exact (MK_COMB (@lem3165986) (@lem3165985)). Qed.
Lemma lem3165988 : term164 = term165.
Proof. exact (MK_COMB (@lem3165987) (@lem3165982)). Qed.
Lemma lem3165989 : term165 = term166.
Proof. exact (@lem1981613 term160 term79 term93 term93). Qed.
Lemma lem3165991 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3165992 : term169 = term170.
Proof. exact (@lem3165991 term2 term2). Qed.
Lemma lem3165993 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3165994 : term172 = term2.
Proof. exact (EQ_MP (@lem3165993) (@lem940073)). Qed.
Lemma lem3165995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3165996 : term170 = term93.
Proof. exact (MK_COMB (@lem3165995) (@lem3165994)). Qed.
Lemma lem3165997 : term169 = term93.
Proof. exact (TRANS (@lem3165992) (@lem3165996)). Qed.
Lemma lem3165999 (x : nat) : (term173 x) = term79.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3166000 : term164 = term79.
Proof. exact (@lem3165999 term2). Qed.
Lemma lem3166001 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3166002 : term174 = term175.
Proof. exact (MK_COMB (@lem3166001) (@lem3166000)). Qed.
Lemma lem3166003 : term166 = term157.
Proof. exact (MK_COMB (@lem3166002) (@lem3165997)). Qed.
Lemma lem3166004 : term165 = term157.
Proof. exact (TRANS (@lem3165989) (@lem3166003)). Qed.
Lemma lem3166005 : term164 = term157.
Proof. exact (TRANS (@lem3165988) (@lem3166004)). Qed.
Lemma lem3166007 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3166008 : term157 = term79.
Proof. exact (@lem3166007 term79). Qed.
Lemma lem3166009 : term164 = term79.
Proof. exact (TRANS (@lem3166005) (@lem3166008)). Qed.
Lemma lem3166010 (_32610 : int) : (term108 _32610) = (term108 _32610).
Proof. exact (eq_refl (term108 _32610)). Qed.
Lemma lem3166011 (_32610 : int) : (term155 _32610) = (term177 _32610).
Proof. exact (MK_COMB (@lem3166010 _32610) (@lem3166009)). Qed.
Lemma lem3166012 (_32610 : int) : (term177 _32610) = (real_of_int _32610).
Proof. exact (@lem1982723 (real_of_int _32610)). Qed.
Lemma lem3166013 (_32610 : int) : (term155 _32610) = (real_of_int _32610).
Proof. exact (TRANS (@lem3166011 _32610) (@lem3166012 _32610)). Qed.
Lemma lem3166015 (_32610 : int) : (term154 _32610) = (real_of_int _32610).
Proof. exact (TRANS (@lem3165979 _32610) (@lem3166013 _32610)). Qed.
Lemma lem3166016 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3166017 (_32610 : int) : (term178 _32610) = (term179 _32610).
Proof. exact (MK_COMB (@lem3166016) (@lem3166015 _32610)). Qed.
Lemma lem3166018 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3166019 (_32610 : int) : (term153 _32610) = (term180 _32610).
Proof. exact (MK_COMB (@lem3166017 _32610) (@lem3166018)). Qed.
Lemma lem3166020 (_32610 : int) : (term82 _32610) = (term180 _32610).
Proof. exact (TRANS (@lem3165973 _32610) (@lem3166019 _32610)). Qed.
Lemma lem3166021 (_32610 : int) (_32609 : int) : (term674 _32609 _32610) = (term680 _32610 _32609).
Proof. exact (@lem1988287 (real_of_int _32610) (term109 _32609)). Qed.
Lemma lem3166033 (_32610 : int) (_32609 : int) : (term681 _32610 _32609) = (term682 _32610 _32609).
Proof. exact (@lem1982792 (real_of_int _32610) (term109 _32609)). Qed.
Lemma lem3166034 (_32609 : int) : (term234 _32609) = (term235 _32609).
Proof. exact (@lem1982781 (real_of_int _32609) term160 term93). Qed.
Lemma lem3166036 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166037 : term93 = term182.
Proof. exact (@lem3166036 term2). Qed.
Lemma lem3166039 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3166040 : term160 = term161.
Proof. exact (@lem3166039 term2). Qed.
Lemma lem3166041 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3166042 : term162 = term163.
Proof. exact (MK_COMB (@lem3166041) (@lem3166040)). Qed.
Lemma lem3166043 : term236 = term237.
Proof. exact (MK_COMB (@lem3166042) (@lem3166037)). Qed.
Lemma lem3166044 : term237 = term238.
Proof. exact (@lem1981613 term160 term93 term93 term93). Qed.
Lemma lem3166046 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166047 : term169 = term170.
Proof. exact (@lem3166046 term2 term2). Qed.
Lemma lem3166048 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166049 : term172 = term2.
Proof. exact (EQ_MP (@lem3166048) (@lem940073)). Qed.
Lemma lem3166050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166051 : term170 = term93.
Proof. exact (MK_COMB (@lem3166050) (@lem3166049)). Qed.
Lemma lem3166052 : term169 = term93.
Proof. exact (TRANS (@lem3166047) (@lem3166051)). Qed.
Lemma lem3166054 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3166055 : term236 = term239.
Proof. exact (@lem3166054 term2 term2). Qed.
Lemma lem3166056 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166057 : term172 = term2.
Proof. exact (EQ_MP (@lem3166056) (@lem940073)). Qed.
Lemma lem3166058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166059 : term170 = term93.
Proof. exact (MK_COMB (@lem3166058) (@lem3166057)). Qed.
Lemma lem3166060 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3166061 : term239 = term160.
Proof. exact (MK_COMB (@lem3166060) (@lem3166059)). Qed.
Lemma lem3166062 : term236 = term160.
Proof. exact (TRANS (@lem3166055) (@lem3166061)). Qed.
Lemma lem3166063 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3166064 : term240 = term241.
Proof. exact (MK_COMB (@lem3166063) (@lem3166062)). Qed.
Lemma lem3166065 : term238 = term161.
Proof. exact (MK_COMB (@lem3166064) (@lem3166052)). Qed.
Lemma lem3166066 : term237 = term161.
Proof. exact (TRANS (@lem3166044) (@lem3166065)). Qed.
Lemma lem3166067 : term236 = term161.
Proof. exact (TRANS (@lem3166043) (@lem3166066)). Qed.
Lemma lem3166069 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3166070 : term161 = term160.
Proof. exact (@lem3166069 term160). Qed.
Lemma lem3166071 : term236 = term160.
Proof. exact (TRANS (@lem3166067) (@lem3166070)). Qed.
Lemma lem3166074 (_32609 : int) : (term242 _32609) = (term242 _32609).
Proof. exact (eq_refl (term242 _32609)). Qed.
Lemma lem3166075 (_32609 : int) : (term235 _32609) = (term243 _32609).
Proof. exact (MK_COMB (@lem3166074 _32609) (@lem3166071)). Qed.
Lemma lem3166076 (_32609 : int) : (term234 _32609) = (term243 _32609).
Proof. exact (TRANS (@lem3166034 _32609) (@lem3166075 _32609)). Qed.
Lemma lem3166077 (_32610 : int) : (term108 _32610) = (term108 _32610).
Proof. exact (eq_refl (term108 _32610)). Qed.
Lemma lem3166078 (_32610 : int) (_32609 : int) : (term682 _32610 _32609) = (term683 _32610 _32609).
Proof. exact (MK_COMB (@lem3166077 _32610) (@lem3166076 _32609)). Qed.
Lemma lem3166083 (_32609 : int) (_32610 : int) : (term683 _32610 _32609) = (term684 _32609 _32610).
Proof. exact (@lem1982757 (term263 _32609) (real_of_int _32610) term160). Qed.
Lemma lem3166084 (_32609 : int) (_32610 : int) : (term682 _32610 _32609) = (term684 _32609 _32610).
Proof. exact (TRANS (@lem3166078 _32610 _32609) (@lem3166083 _32609 _32610)). Qed.
Lemma lem3166086 (_32609 : int) (_32610 : int) : (term681 _32610 _32609) = (term684 _32609 _32610).
Proof. exact (TRANS (@lem3166033 _32610 _32609) (@lem3166084 _32609 _32610)). Qed.
Lemma lem3166087 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3166088 (_32609 : int) (_32610 : int) : (term685 _32610 _32609) = (term686 _32609 _32610).
Proof. exact (MK_COMB (@lem3166087) (@lem3166086 _32609 _32610)). Qed.
Lemma lem3166089 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3166090 (_32609 : int) (_32610 : int) : (term680 _32610 _32609) = (term687 _32609 _32610).
Proof. exact (MK_COMB (@lem3166088 _32609 _32610) (@lem3166089)). Qed.
Lemma lem3166091 (_32609 : int) (_32610 : int) : (term674 _32609 _32610) = (term687 _32609 _32610).
Proof. exact (TRANS (@lem3166021 _32610 _32609) (@lem3166090 _32609 _32610)). Qed.
Lemma lem3166092 (_32609 : int) (_32610 : int) : (term75 _32610 _32609) = (term688 _32609 _32610).
Proof. exact (@lem1988287 (real_of_int _32609) (real_of_int _32610)). Qed.
Lemma lem3166105 (_32609 : int) (_32610 : int) : (term689 _32609 _32610) = (term690 _32609 _32610).
Proof. exact (@lem1982792 (real_of_int _32609) (real_of_int _32610)). Qed.
Lemma lem3166106 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3166107 (_32609 : int) (_32610 : int) : (term691 _32609 _32610) = (term692 _32609 _32610).
Proof. exact (MK_COMB (@lem3166106) (@lem3166105 _32609 _32610)). Qed.
Lemma lem3166108 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3166109 (_32609 : int) (_32610 : int) : (term688 _32609 _32610) = (term693 _32609 _32610).
Proof. exact (MK_COMB (@lem3166107 _32609 _32610) (@lem3166108)). Qed.
Lemma lem3166110 (_32609 : int) (_32610 : int) : (term75 _32610 _32609) = (term693 _32609 _32610).
Proof. exact (TRANS (@lem3166092 _32609 _32610) (@lem3166109 _32609 _32610)). Qed.
Lemma lem3166111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3166112 (_32609 : int) (_32610 : int) : (term675 _32609 _32610) = (term694 _32609 _32610).
Proof. exact (MK_COMB (@lem3166111) (@lem3166091 _32609 _32610)). Qed.
Lemma lem3166113 (_32609 : int) (_32610 : int) : (term676 _32610 _32609) = (term695 _32609 _32610).
Proof. exact (MK_COMB (@lem3166112 _32609 _32610) (@lem3166110 _32609 _32610)). Qed.
Lemma lem3166114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3166115 (_32610 : int) : (term149 _32610) = (term303 _32610).
Proof. exact (MK_COMB (@lem3166114) (@lem3166020 _32610)). Qed.
Lemma lem3166116 (_32609 : int) (_32610 : int) : (term677 _32610 _32609) = (term696 _32609 _32610).
Proof. exact (MK_COMB (@lem3166115 _32610) (@lem3166113 _32609 _32610)). Qed.
Lemma lem3166117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3166118 (_32609 : int) : (term149 _32609) = (term303 _32609).
Proof. exact (MK_COMB (@lem3166117) (@lem3165972 _32609)). Qed.
Lemma lem3166119 (_32609 : int) (_32610 : int) : (term678 _32610 _32609) = (term697 _32609 _32610).
Proof. exact (MK_COMB (@lem3166118 _32609) (@lem3166116 _32609 _32610)). Qed.
Lemma lem3166146 (_32609 : int) (_32610 : int) : (term679 _32610 _32609) = (term697 _32609 _32610).
Proof. exact (TRANS (@lem3165924 _32610 _32609) (@lem3166119 _32609 _32610)). Qed.
Lemma lem3166150 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term697 _32609 _32610.
Proof. exact (h1). Qed.
Lemma lem3166151 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term696 _32609 _32610.
Proof. exact (proj2 (@lem3166150 _32609 _32610 h1)). Qed.
Lemma lem3166153 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term695 _32609 _32610.
Proof. exact (proj2 (@lem3166151 _32609 _32610 h1)). Qed.
Lemma lem3166155 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term693 _32609 _32610.
Proof. exact (proj2 (@lem3166153 _32609 _32610 h1)). Qed.
Lemma lem3166156 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term687 _32609 _32610.
Proof. exact (proj1 (@lem3166153 _32609 _32610 h1)). Qed.
Lemma lem3166158 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3166159 : term433 = term188.
Proof. exact (@lem3166158 term79 term93). Qed.
Lemma lem3166161 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166162 : term93 = term182.
Proof. exact (@lem3166161 term2). Qed.
Lemma lem3166164 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166165 : term79 = term157.
Proof. exact (@lem3166164 (NUMERAL 0)). Qed.
Lemma lem3166166 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3166167 : term434 = term435.
Proof. exact (MK_COMB (@lem3166166) (@lem3166165)). Qed.
Lemma lem3166168 : term188 = term436.
Proof. exact (MK_COMB (@lem3166167) (@lem3166162)). Qed.
Lemma lem3166169 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3166171 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166172 : term188 = term189.
Proof. exact (@lem3166171 (NUMERAL 0) term2). Qed.
Lemma lem3166173 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166174 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166175 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166174 h1) (fun h1 : term189 = True => @lem3166173)). Qed.
Lemma lem3166176 : term189 = True.
Proof. exact (EQ_MP (@lem3166175) (@lem3166173)). Qed.
Lemma lem3166177 : term188 = True.
Proof. exact (TRANS (@lem3166172) (@lem3166176)). Qed.
Lemma lem3166178 : True = term188.
Proof. exact (SYM (@lem3166177)). Qed.
Lemma lem3166179 : term188.
Proof. exact (EQ_MP (@lem3166178) (@lem0)). Qed.
Lemma lem3166180 : term438.
Proof. exact (@lem3166169 (@lem3166179)). Qed.
Lemma lem3166182 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166183 : term188 = term189.
Proof. exact (@lem3166182 (NUMERAL 0) term2). Qed.
Lemma lem3166184 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166185 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166186 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166185 h1) (fun h1 : term189 = True => @lem3166184)). Qed.
Lemma lem3166187 : term189 = True.
Proof. exact (EQ_MP (@lem3166186) (@lem3166184)). Qed.
Lemma lem3166188 : term188 = True.
Proof. exact (TRANS (@lem3166183) (@lem3166187)). Qed.
Lemma lem3166189 : True = term188.
Proof. exact (SYM (@lem3166188)). Qed.
Lemma lem3166190 : term188.
Proof. exact (EQ_MP (@lem3166189) (@lem0)). Qed.
Lemma lem3166191 : term436 = term439.
Proof. exact (@lem3166180 (@lem3166190)). Qed.
Lemma lem3166193 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166194 : term169 = term170.
Proof. exact (@lem3166193 term2 term2). Qed.
Lemma lem3166195 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166196 : term172 = term2.
Proof. exact (EQ_MP (@lem3166195) (@lem940073)). Qed.
Lemma lem3166197 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166198 : term170 = term93.
Proof. exact (MK_COMB (@lem3166197) (@lem3166196)). Qed.
Lemma lem3166199 : term169 = term93.
Proof. exact (TRANS (@lem3166194) (@lem3166198)). Qed.
Lemma lem3166201 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166202 : term275 = term79.
Proof. exact (@lem3166201 term2). Qed.
Lemma lem3166203 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3166204 : term440 = term434.
Proof. exact (MK_COMB (@lem3166203) (@lem3166202)). Qed.
Lemma lem3166205 : term439 = term188.
Proof. exact (MK_COMB (@lem3166204) (@lem3166199)). Qed.
Lemma lem3166207 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166208 : term188 = term189.
Proof. exact (@lem3166207 (NUMERAL 0) term2). Qed.
Lemma lem3166209 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166210 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166211 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166210 h1) (fun h1 : term189 = True => @lem3166209)). Qed.
Lemma lem3166212 : term189 = True.
Proof. exact (EQ_MP (@lem3166211) (@lem3166209)). Qed.
Lemma lem3166213 : term188 = True.
Proof. exact (TRANS (@lem3166208) (@lem3166212)). Qed.
Lemma lem3166214 : term439 = True.
Proof. exact (TRANS (@lem3166205) (@lem3166213)). Qed.
Lemma lem3166215 : term436 = True.
Proof. exact (TRANS (@lem3166191) (@lem3166214)). Qed.
Lemma lem3166216 : term188 = True.
Proof. exact (TRANS (@lem3166168) (@lem3166215)). Qed.
Lemma lem3166217 : term433 = True.
Proof. exact (TRANS (@lem3166159) (@lem3166216)). Qed.
Lemma lem3166218 : True = term433.
Proof. exact (SYM (@lem3166217)). Qed.
Lemma lem3166219 : term433.
Proof. exact (EQ_MP (@lem3166218) (@lem0)). Qed.
Lemma lem3166220 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term698 _32609 _32610.
Proof. exact (conj (@lem3166219) (@lem3166155 _32609 _32610 h1)). Qed.
Lemma lem3166222 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3166223 (_32609 : int) (_32610 : int) : term699 _32609 _32610.
Proof. exact (@lem3166222 term93 (term690 _32609 _32610)). Qed.
Lemma lem3166224 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term700 _32609 _32610.
Proof. exact (@lem3166223 _32609 _32610 (@lem3166220 _32609 _32610 h1)). Qed.
Lemma lem3166225 (_32609 : int) (_32610 : int) : (term701 _32609 _32610) = (term690 _32609 _32610).
Proof. exact (@lem1982733 (term690 _32609 _32610)). Qed.
Lemma lem3166226 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3166227 (_32609 : int) (_32610 : int) : (term702 _32609 _32610) = (term692 _32609 _32610).
Proof. exact (MK_COMB (@lem3166226) (@lem3166225 _32609 _32610)). Qed.
Lemma lem3166228 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3166229 (_32609 : int) (_32610 : int) : (term700 _32609 _32610) = (term693 _32609 _32610).
Proof. exact (MK_COMB (@lem3166227 _32609 _32610) (@lem3166228)). Qed.
Lemma lem3166230 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term693 _32609 _32610.
Proof. exact (EQ_MP (@lem3166229 _32609 _32610) (@lem3166224 _32609 _32610 h1)). Qed.
Lemma lem3166232 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3166233 : term433 = term188.
Proof. exact (@lem3166232 term79 term93). Qed.
Lemma lem3166235 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166236 : term93 = term182.
Proof. exact (@lem3166235 term2). Qed.
Lemma lem3166238 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166239 : term79 = term157.
Proof. exact (@lem3166238 (NUMERAL 0)). Qed.
Lemma lem3166240 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3166241 : term434 = term435.
Proof. exact (MK_COMB (@lem3166240) (@lem3166239)). Qed.
Lemma lem3166242 : term188 = term436.
Proof. exact (MK_COMB (@lem3166241) (@lem3166236)). Qed.
Lemma lem3166243 : term437.
Proof. exact (@lem1980255 term79 term93 term93 term93). Qed.
Lemma lem3166245 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166246 : term188 = term189.
Proof. exact (@lem3166245 (NUMERAL 0) term2). Qed.
Lemma lem3166247 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166248 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166249 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166248 h1) (fun h1 : term189 = True => @lem3166247)). Qed.
Lemma lem3166250 : term189 = True.
Proof. exact (EQ_MP (@lem3166249) (@lem3166247)). Qed.
Lemma lem3166251 : term188 = True.
Proof. exact (TRANS (@lem3166246) (@lem3166250)). Qed.
Lemma lem3166252 : True = term188.
Proof. exact (SYM (@lem3166251)). Qed.
Lemma lem3166253 : term188.
Proof. exact (EQ_MP (@lem3166252) (@lem0)). Qed.
Lemma lem3166254 : term438.
Proof. exact (@lem3166243 (@lem3166253)). Qed.
Lemma lem3166256 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166257 : term188 = term189.
Proof. exact (@lem3166256 (NUMERAL 0) term2). Qed.
Lemma lem3166258 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166259 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166260 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166259 h1) (fun h1 : term189 = True => @lem3166258)). Qed.
Lemma lem3166261 : term189 = True.
Proof. exact (EQ_MP (@lem3166260) (@lem3166258)). Qed.
Lemma lem3166262 : term188 = True.
Proof. exact (TRANS (@lem3166257) (@lem3166261)). Qed.
Lemma lem3166263 : True = term188.
Proof. exact (SYM (@lem3166262)). Qed.
Lemma lem3166264 : term188.
Proof. exact (EQ_MP (@lem3166263) (@lem0)). Qed.
Lemma lem3166265 : term436 = term439.
Proof. exact (@lem3166254 (@lem3166264)). Qed.
Lemma lem3166267 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166268 : term169 = term170.
Proof. exact (@lem3166267 term2 term2). Qed.
Lemma lem3166269 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166270 : term172 = term2.
Proof. exact (EQ_MP (@lem3166269) (@lem940073)). Qed.
Lemma lem3166271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166272 : term170 = term93.
Proof. exact (MK_COMB (@lem3166271) (@lem3166270)). Qed.
Lemma lem3166273 : term169 = term93.
Proof. exact (TRANS (@lem3166268) (@lem3166272)). Qed.
Lemma lem3166275 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166276 : term275 = term79.
Proof. exact (@lem3166275 term2). Qed.
Lemma lem3166277 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3166278 : term440 = term434.
Proof. exact (MK_COMB (@lem3166277) (@lem3166276)). Qed.
Lemma lem3166279 : term439 = term188.
Proof. exact (MK_COMB (@lem3166278) (@lem3166273)). Qed.
Lemma lem3166281 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166282 : term188 = term189.
Proof. exact (@lem3166281 (NUMERAL 0) term2). Qed.
Lemma lem3166283 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166284 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166285 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166284 h1) (fun h1 : term189 = True => @lem3166283)). Qed.
Lemma lem3166286 : term189 = True.
Proof. exact (EQ_MP (@lem3166285) (@lem3166283)). Qed.
Lemma lem3166287 : term188 = True.
Proof. exact (TRANS (@lem3166282) (@lem3166286)). Qed.
Lemma lem3166288 : term439 = True.
Proof. exact (TRANS (@lem3166279) (@lem3166287)). Qed.
Lemma lem3166289 : term436 = True.
Proof. exact (TRANS (@lem3166265) (@lem3166288)). Qed.
Lemma lem3166290 : term188 = True.
Proof. exact (TRANS (@lem3166242) (@lem3166289)). Qed.
Lemma lem3166291 : term433 = True.
Proof. exact (TRANS (@lem3166233) (@lem3166290)). Qed.
Lemma lem3166292 : True = term433.
Proof. exact (SYM (@lem3166291)). Qed.
Lemma lem3166293 : term433.
Proof. exact (EQ_MP (@lem3166292) (@lem0)). Qed.
Lemma lem3166294 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term703 _32609 _32610.
Proof. exact (conj (@lem3166293) (@lem3166156 _32609 _32610 h1)). Qed.
Lemma lem3166296 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3166297 (_32609 : int) (_32610 : int) : term704 _32609 _32610.
Proof. exact (@lem3166296 term93 (term684 _32609 _32610)). Qed.
Lemma lem3166298 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term705 _32609 _32610.
Proof. exact (@lem3166297 _32609 _32610 (@lem3166294 _32609 _32610 h1)). Qed.
Lemma lem3166299 (_32609 : int) (_32610 : int) : (term706 _32609 _32610) = (term684 _32609 _32610).
Proof. exact (@lem1982733 (term684 _32609 _32610)). Qed.
Lemma lem3166300 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3166301 (_32609 : int) (_32610 : int) : (term707 _32609 _32610) = (term686 _32609 _32610).
Proof. exact (MK_COMB (@lem3166300) (@lem3166299 _32609 _32610)). Qed.
Lemma lem3166302 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3166303 (_32609 : int) (_32610 : int) : (term705 _32609 _32610) = (term687 _32609 _32610).
Proof. exact (MK_COMB (@lem3166301 _32609 _32610) (@lem3166302)). Qed.
Lemma lem3166304 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term687 _32609 _32610.
Proof. exact (EQ_MP (@lem3166303 _32609 _32610) (@lem3166298 _32609 _32610 h1)). Qed.
Lemma lem3166305 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term695 _32609 _32610.
Proof. exact (conj (@lem3166304 _32609 _32610 h1) (@lem3166230 _32609 _32610 h1)). Qed.
Lemma lem3166307 (x : real) (y : real) : term453 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3166308 (_32609 : int) (_32610 : int) : term708 _32609 _32610.
Proof. exact (@lem3166307 (term684 _32609 _32610) (term690 _32609 _32610)). Qed.
Lemma lem3166309 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term709 _32609 _32610.
Proof. exact (@lem3166308 _32609 _32610 (@lem3166305 _32609 _32610 h1)). Qed.
Lemma lem3166310 (_32609 : int) (_32610 : int) : (term710 _32609 _32610) = (term711 _32609 _32610).
Proof. exact (@lem1982753 (term263 _32609) (real_of_int _32609) (term252 _32610) (term263 _32610)). Qed.
Lemma lem3166311 (_32609 : int) : (term458 _32609) = (term459 _32609).
Proof. exact (@lem1982713 term160 (real_of_int _32609)). Qed.
Lemma lem3166313 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166314 : term93 = term182.
Proof. exact (@lem3166313 term2). Qed.
Lemma lem3166316 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3166317 : term160 = term161.
Proof. exact (@lem3166316 term2). Qed.
Lemma lem3166318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3166319 : term460 = term461.
Proof. exact (MK_COMB (@lem3166318) (@lem3166317)). Qed.
Lemma lem3166320 : term462 = term463.
Proof. exact (MK_COMB (@lem3166319) (@lem3166314)). Qed.
Lemma lem3166321 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3166323 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166324 : term188 = term189.
Proof. exact (@lem3166323 (NUMERAL 0) term2). Qed.
Lemma lem3166325 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166326 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166327 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166326 h1) (fun h1 : term189 = True => @lem3166325)). Qed.
Lemma lem3166328 : term189 = True.
Proof. exact (EQ_MP (@lem3166327) (@lem3166325)). Qed.
Lemma lem3166329 : term188 = True.
Proof. exact (TRANS (@lem3166324) (@lem3166328)). Qed.
Lemma lem3166330 : True = term188.
Proof. exact (SYM (@lem3166329)). Qed.
Lemma lem3166331 : term188.
Proof. exact (EQ_MP (@lem3166330) (@lem0)). Qed.
Lemma lem3166332 : term465.
Proof. exact (@lem3166321 (@lem3166331)). Qed.
Lemma lem3166334 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166335 : term188 = term189.
Proof. exact (@lem3166334 (NUMERAL 0) term2). Qed.
Lemma lem3166336 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166337 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166338 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166337 h1) (fun h1 : term189 = True => @lem3166336)). Qed.
Lemma lem3166339 : term189 = True.
Proof. exact (EQ_MP (@lem3166338) (@lem3166336)). Qed.
Lemma lem3166340 : term188 = True.
Proof. exact (TRANS (@lem3166335) (@lem3166339)). Qed.
Lemma lem3166341 : True = term188.
Proof. exact (SYM (@lem3166340)). Qed.
Lemma lem3166342 : term188.
Proof. exact (EQ_MP (@lem3166341) (@lem0)). Qed.
Lemma lem3166343 : term466.
Proof. exact (@lem3166332 (@lem3166342)). Qed.
Lemma lem3166345 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166346 : term188 = term189.
Proof. exact (@lem3166345 (NUMERAL 0) term2). Qed.
Lemma lem3166347 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166348 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166349 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166348 h1) (fun h1 : term189 = True => @lem3166347)). Qed.
Lemma lem3166350 : term189 = True.
Proof. exact (EQ_MP (@lem3166349) (@lem3166347)). Qed.
Lemma lem3166351 : term188 = True.
Proof. exact (TRANS (@lem3166346) (@lem3166350)). Qed.
Lemma lem3166352 : True = term188.
Proof. exact (SYM (@lem3166351)). Qed.
Lemma lem3166353 : term188.
Proof. exact (EQ_MP (@lem3166352) (@lem0)). Qed.
Lemma lem3166354 : term467.
Proof. exact (@lem3166343 (@lem3166353)). Qed.
Lemma lem3166356 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166357 : term169 = term170.
Proof. exact (@lem3166356 term2 term2). Qed.
Lemma lem3166358 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166359 : term172 = term2.
Proof. exact (EQ_MP (@lem3166358) (@lem940073)). Qed.
Lemma lem3166360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166361 : term170 = term93.
Proof. exact (MK_COMB (@lem3166360) (@lem3166359)). Qed.
Lemma lem3166362 : term169 = term93.
Proof. exact (TRANS (@lem3166357) (@lem3166361)). Qed.
Lemma lem3166364 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3166365 : term236 = term239.
Proof. exact (@lem3166364 term2 term2). Qed.
Lemma lem3166366 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166367 : term172 = term2.
Proof. exact (EQ_MP (@lem3166366) (@lem940073)). Qed.
Lemma lem3166368 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166369 : term170 = term93.
Proof. exact (MK_COMB (@lem3166368) (@lem3166367)). Qed.
Lemma lem3166370 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3166371 : term239 = term160.
Proof. exact (MK_COMB (@lem3166370) (@lem3166369)). Qed.
Lemma lem3166372 : term236 = term160.
Proof. exact (TRANS (@lem3166365) (@lem3166371)). Qed.
Lemma lem3166373 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3166374 : term468 = term460.
Proof. exact (MK_COMB (@lem3166373) (@lem3166372)). Qed.
Lemma lem3166375 : term469 = term462.
Proof. exact (MK_COMB (@lem3166374) (@lem3166362)). Qed.
Lemma lem3166377 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3166378 : term462 = term79.
Proof. exact (@lem3166377 term2). Qed.
Lemma lem3166379 : term469 = term79.
Proof. exact (TRANS (@lem3166375) (@lem3166378)). Qed.
Lemma lem3166380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3166381 : term471 = term273.
Proof. exact (MK_COMB (@lem3166380) (@lem3166379)). Qed.
Lemma lem3166382 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3166383 : term472 = term275.
Proof. exact (MK_COMB (@lem3166381) (@lem3166382)). Qed.
Lemma lem3166385 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166386 : term275 = term79.
Proof. exact (@lem3166385 term2). Qed.
Lemma lem3166387 : term472 = term79.
Proof. exact (TRANS (@lem3166383) (@lem3166386)). Qed.
Lemma lem3166389 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166390 : term169 = term170.
Proof. exact (@lem3166389 term2 term2). Qed.
Lemma lem3166391 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166392 : term172 = term2.
Proof. exact (EQ_MP (@lem3166391) (@lem940073)). Qed.
Lemma lem3166393 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166394 : term170 = term93.
Proof. exact (MK_COMB (@lem3166393) (@lem3166392)). Qed.
Lemma lem3166395 : term169 = term93.
Proof. exact (TRANS (@lem3166390) (@lem3166394)). Qed.
Lemma lem3166396 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3166397 : term277 = term275.
Proof. exact (MK_COMB (@lem3166396) (@lem3166395)). Qed.
Lemma lem3166399 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166400 : term275 = term79.
Proof. exact (@lem3166399 term2). Qed.
Lemma lem3166401 : term277 = term79.
Proof. exact (TRANS (@lem3166397) (@lem3166400)). Qed.
Lemma lem3166402 : term79 = term277.
Proof. exact (SYM (@lem3166401)). Qed.
Lemma lem3166403 : term472 = term277.
Proof. exact (TRANS (@lem3166387) (@lem3166402)). Qed.
Lemma lem3166404 : term463 = term157.
Proof. exact (@lem3166354 (@lem3166403)). Qed.
Lemma lem3166405 : term462 = term157.
Proof. exact (TRANS (@lem3166320) (@lem3166404)). Qed.
Lemma lem3166407 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3166408 : term157 = term79.
Proof. exact (@lem3166407 term79). Qed.
Lemma lem3166409 : term462 = term79.
Proof. exact (TRANS (@lem3166405) (@lem3166408)). Qed.
Lemma lem3166410 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3166411 : term473 = term273.
Proof. exact (MK_COMB (@lem3166410) (@lem3166409)). Qed.
Lemma lem3166412 (_32609 : int) : (real_of_int _32609) = (real_of_int _32609).
Proof. exact (eq_refl (real_of_int _32609)). Qed.
Lemma lem3166413 (_32609 : int) : (term459 _32609) = (term474 _32609).
Proof. exact (MK_COMB (@lem3166411) (@lem3166412 _32609)). Qed.
Lemma lem3166414 (_32609 : int) : (term458 _32609) = (term474 _32609).
Proof. exact (TRANS (@lem3166311 _32609) (@lem3166413 _32609)). Qed.
Lemma lem3166415 (_32609 : int) : (term474 _32609) = term79.
Proof. exact (@lem1982719 (real_of_int _32609)). Qed.
Lemma lem3166416 (_32609 : int) : (term458 _32609) = term79.
Proof. exact (TRANS (@lem3166414 _32609) (@lem3166415 _32609)). Qed.
Lemma lem3166417 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3166418 (_32609 : int) : (term475 _32609) = term121.
Proof. exact (MK_COMB (@lem3166417) (@lem3166416 _32609)). Qed.
Lemma lem3166419 (_32610 : int) : (term600 _32610) = (term569 _32610).
Proof. exact (@lem1982759 (real_of_int _32610) (term263 _32610) term160). Qed.
Lemma lem3166420 (_32610 : int) : (term570 _32610) = (term459 _32610).
Proof. exact (@lem1982715 term160 (real_of_int _32610)). Qed.
Lemma lem3166422 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166423 : term93 = term182.
Proof. exact (@lem3166422 term2). Qed.
Lemma lem3166425 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3166426 : term160 = term161.
Proof. exact (@lem3166425 term2). Qed.
Lemma lem3166427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3166428 : term460 = term461.
Proof. exact (MK_COMB (@lem3166427) (@lem3166426)). Qed.
Lemma lem3166429 : term462 = term463.
Proof. exact (MK_COMB (@lem3166428) (@lem3166423)). Qed.
Lemma lem3166430 : term464.
Proof. exact (@lem1981473 term160 term93 term93 term93 term79 term93). Qed.
Lemma lem3166432 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166433 : term188 = term189.
Proof. exact (@lem3166432 (NUMERAL 0) term2). Qed.
Lemma lem3166434 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166435 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166436 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166435 h1) (fun h1 : term189 = True => @lem3166434)). Qed.
Lemma lem3166437 : term189 = True.
Proof. exact (EQ_MP (@lem3166436) (@lem3166434)). Qed.
Lemma lem3166438 : term188 = True.
Proof. exact (TRANS (@lem3166433) (@lem3166437)). Qed.
Lemma lem3166439 : True = term188.
Proof. exact (SYM (@lem3166438)). Qed.
Lemma lem3166440 : term188.
Proof. exact (EQ_MP (@lem3166439) (@lem0)). Qed.
Lemma lem3166441 : term465.
Proof. exact (@lem3166430 (@lem3166440)). Qed.
Lemma lem3166443 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166444 : term188 = term189.
Proof. exact (@lem3166443 (NUMERAL 0) term2). Qed.
Lemma lem3166445 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166446 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166447 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166446 h1) (fun h1 : term189 = True => @lem3166445)). Qed.
Lemma lem3166448 : term189 = True.
Proof. exact (EQ_MP (@lem3166447) (@lem3166445)). Qed.
Lemma lem3166449 : term188 = True.
Proof. exact (TRANS (@lem3166444) (@lem3166448)). Qed.
Lemma lem3166450 : True = term188.
Proof. exact (SYM (@lem3166449)). Qed.
Lemma lem3166451 : term188.
Proof. exact (EQ_MP (@lem3166450) (@lem0)). Qed.
Lemma lem3166452 : term466.
Proof. exact (@lem3166441 (@lem3166451)). Qed.
Lemma lem3166454 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166455 : term188 = term189.
Proof. exact (@lem3166454 (NUMERAL 0) term2). Qed.
Lemma lem3166456 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166457 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166458 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166457 h1) (fun h1 : term189 = True => @lem3166456)). Qed.
Lemma lem3166459 : term189 = True.
Proof. exact (EQ_MP (@lem3166458) (@lem3166456)). Qed.
Lemma lem3166460 : term188 = True.
Proof. exact (TRANS (@lem3166455) (@lem3166459)). Qed.
Lemma lem3166461 : True = term188.
Proof. exact (SYM (@lem3166460)). Qed.
Lemma lem3166462 : term188.
Proof. exact (EQ_MP (@lem3166461) (@lem0)). Qed.
Lemma lem3166463 : term467.
Proof. exact (@lem3166452 (@lem3166462)). Qed.
Lemma lem3166465 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166466 : term169 = term170.
Proof. exact (@lem3166465 term2 term2). Qed.
Lemma lem3166467 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166468 : term172 = term2.
Proof. exact (EQ_MP (@lem3166467) (@lem940073)). Qed.
Lemma lem3166469 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166470 : term170 = term93.
Proof. exact (MK_COMB (@lem3166469) (@lem3166468)). Qed.
Lemma lem3166471 : term169 = term93.
Proof. exact (TRANS (@lem3166466) (@lem3166470)). Qed.
Lemma lem3166473 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3166474 : term236 = term239.
Proof. exact (@lem3166473 term2 term2). Qed.
Lemma lem3166475 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166476 : term172 = term2.
Proof. exact (EQ_MP (@lem3166475) (@lem940073)). Qed.
Lemma lem3166477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166478 : term170 = term93.
Proof. exact (MK_COMB (@lem3166477) (@lem3166476)). Qed.
Lemma lem3166479 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3166480 : term239 = term160.
Proof. exact (MK_COMB (@lem3166479) (@lem3166478)). Qed.
Lemma lem3166481 : term236 = term160.
Proof. exact (TRANS (@lem3166474) (@lem3166480)). Qed.
Lemma lem3166482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3166483 : term468 = term460.
Proof. exact (MK_COMB (@lem3166482) (@lem3166481)). Qed.
Lemma lem3166484 : term469 = term462.
Proof. exact (MK_COMB (@lem3166483) (@lem3166471)). Qed.
Lemma lem3166486 (m : nat) : (term470 m) = term79.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3166487 : term462 = term79.
Proof. exact (@lem3166486 term2). Qed.
Lemma lem3166488 : term469 = term79.
Proof. exact (TRANS (@lem3166484) (@lem3166487)). Qed.
Lemma lem3166489 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3166490 : term471 = term273.
Proof. exact (MK_COMB (@lem3166489) (@lem3166488)). Qed.
Lemma lem3166491 : term93 = term93.
Proof. exact (eq_refl term93). Qed.
Lemma lem3166492 : term472 = term275.
Proof. exact (MK_COMB (@lem3166490) (@lem3166491)). Qed.
Lemma lem3166494 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166495 : term275 = term79.
Proof. exact (@lem3166494 term2). Qed.
Lemma lem3166496 : term472 = term79.
Proof. exact (TRANS (@lem3166492) (@lem3166495)). Qed.
Lemma lem3166498 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3166499 : term169 = term170.
Proof. exact (@lem3166498 term2 term2). Qed.
Lemma lem3166500 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166501 : term172 = term2.
Proof. exact (EQ_MP (@lem3166500) (@lem940073)). Qed.
Lemma lem3166502 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166503 : term170 = term93.
Proof. exact (MK_COMB (@lem3166502) (@lem3166501)). Qed.
Lemma lem3166504 : term169 = term93.
Proof. exact (TRANS (@lem3166499) (@lem3166503)). Qed.
Lemma lem3166505 : term273 = term273.
Proof. exact (eq_refl term273). Qed.
Lemma lem3166506 : term277 = term275.
Proof. exact (MK_COMB (@lem3166505) (@lem3166504)). Qed.
Lemma lem3166508 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166509 : term275 = term79.
Proof. exact (@lem3166508 term2). Qed.
Lemma lem3166510 : term277 = term79.
Proof. exact (TRANS (@lem3166506) (@lem3166509)). Qed.
Lemma lem3166511 : term79 = term277.
Proof. exact (SYM (@lem3166510)). Qed.
Lemma lem3166512 : term472 = term277.
Proof. exact (TRANS (@lem3166496) (@lem3166511)). Qed.
Lemma lem3166513 : term463 = term157.
Proof. exact (@lem3166463 (@lem3166512)). Qed.
Lemma lem3166514 : term462 = term157.
Proof. exact (TRANS (@lem3166429) (@lem3166513)). Qed.
Lemma lem3166516 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3166517 : term157 = term79.
Proof. exact (@lem3166516 term79). Qed.
Lemma lem3166518 : term462 = term79.
Proof. exact (TRANS (@lem3166514) (@lem3166517)). Qed.
Lemma lem3166519 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3166520 : term473 = term273.
Proof. exact (MK_COMB (@lem3166519) (@lem3166518)). Qed.
Lemma lem3166521 (_32610 : int) : (real_of_int _32610) = (real_of_int _32610).
Proof. exact (eq_refl (real_of_int _32610)). Qed.
Lemma lem3166522 (_32610 : int) : (term459 _32610) = (term474 _32610).
Proof. exact (MK_COMB (@lem3166520) (@lem3166521 _32610)). Qed.
Lemma lem3166523 (_32610 : int) : (term570 _32610) = (term474 _32610).
Proof. exact (TRANS (@lem3166420 _32610) (@lem3166522 _32610)). Qed.
Lemma lem3166524 (_32610 : int) : (term474 _32610) = term79.
Proof. exact (@lem1982719 (real_of_int _32610)). Qed.
Lemma lem3166525 (_32610 : int) : (term570 _32610) = term79.
Proof. exact (TRANS (@lem3166523 _32610) (@lem3166524 _32610)). Qed.
Lemma lem3166526 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3166527 (_32610 : int) : (term571 _32610) = term121.
Proof. exact (MK_COMB (@lem3166526) (@lem3166525 _32610)). Qed.
Lemma lem3166528 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem3166529 (_32610 : int) : (term569 _32610) = term490.
Proof. exact (MK_COMB (@lem3166527 _32610) (@lem3166528)). Qed.
Lemma lem3166530 (_32610 : int) : (term600 _32610) = term490.
Proof. exact (TRANS (@lem3166419 _32610) (@lem3166529 _32610)). Qed.
Lemma lem3166531 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3166532 (_32610 : int) : (term600 _32610) = term160.
Proof. exact (TRANS (@lem3166530 _32610) (@lem3166531)). Qed.
Lemma lem3166533 (_32609 : int) (_32610 : int) : (term711 _32609 _32610) = term490.
Proof. exact (MK_COMB (@lem3166418 _32609) (@lem3166532 _32610)). Qed.
Lemma lem3166534 (_32609 : int) (_32610 : int) : (term710 _32609 _32610) = term490.
Proof. exact (TRANS (@lem3166310 _32609 _32610) (@lem3166533 _32609 _32610)). Qed.
Lemma lem3166535 : term490 = term160.
Proof. exact (@lem1982721 term160). Qed.
Lemma lem3166536 (_32609 : int) (_32610 : int) : (term710 _32609 _32610) = term160.
Proof. exact (TRANS (@lem3166534 _32609 _32610) (@lem3166535)). Qed.
Lemma lem3166537 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3166538 (_32609 : int) (_32610 : int) : (term712 _32609 _32610) = term492.
Proof. exact (MK_COMB (@lem3166537) (@lem3166536 _32609 _32610)). Qed.
Lemma lem3166539 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem3166540 (_32609 : int) (_32610 : int) : (term709 _32609 _32610) = term493.
Proof. exact (MK_COMB (@lem3166538 _32609 _32610) (@lem3166539)). Qed.
Lemma lem3166541 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term493.
Proof. exact (EQ_MP (@lem3166540 _32609 _32610) (@lem3166309 _32609 _32610 h1)). Qed.
Lemma lem3166543 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3166544 : term493 = term494.
Proof. exact (@lem3166543 term79 term160). Qed.
Lemma lem3166546 (x : nat) : (term158 x) = (term159 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3166547 : term160 = term161.
Proof. exact (@lem3166546 term2). Qed.
Lemma lem3166549 (x : nat) : (real_of_num x) = (term156 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3166550 : term79 = term157.
Proof. exact (@lem3166549 (NUMERAL 0)). Qed.
Lemma lem3166551 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3166552 : term81 = term495.
Proof. exact (MK_COMB (@lem3166551) (@lem3166550)). Qed.
Lemma lem3166553 : term494 = term496.
Proof. exact (MK_COMB (@lem3166552) (@lem3166547)). Qed.
Lemma lem3166554 : term497.
Proof. exact (@lem1980026 term79 term93 term160 term93). Qed.
Lemma lem3166556 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166557 : term188 = term189.
Proof. exact (@lem3166556 (NUMERAL 0) term2). Qed.
Lemma lem3166558 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166559 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166560 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166559 h1) (fun h1 : term189 = True => @lem3166558)). Qed.
Lemma lem3166561 : term189 = True.
Proof. exact (EQ_MP (@lem3166560) (@lem3166558)). Qed.
Lemma lem3166562 : term188 = True.
Proof. exact (TRANS (@lem3166557) (@lem3166561)). Qed.
Lemma lem3166563 : True = term188.
Proof. exact (SYM (@lem3166562)). Qed.
Lemma lem3166564 : term188.
Proof. exact (EQ_MP (@lem3166563) (@lem0)). Qed.
Lemma lem3166565 : term498.
Proof. exact (@lem3166554 (@lem3166564)). Qed.
Lemma lem3166567 (m : nat) (n : nat) : (term187 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3166568 : term188 = term189.
Proof. exact (@lem3166567 (NUMERAL 0) term2). Qed.
Lemma lem3166569 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166570 (h1 : term190 = (BIT1 0)) : term189 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3166571 : (term190 = (BIT1 0)) = (term189 = True).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166570 h1) (fun h1 : term189 = True => @lem3166569)). Qed.
Lemma lem3166572 : term189 = True.
Proof. exact (EQ_MP (@lem3166571) (@lem3166569)). Qed.
Lemma lem3166573 : term188 = True.
Proof. exact (TRANS (@lem3166568) (@lem3166572)). Qed.
Lemma lem3166574 : True = term188.
Proof. exact (SYM (@lem3166573)). Qed.
Lemma lem3166575 : term188.
Proof. exact (EQ_MP (@lem3166574) (@lem0)). Qed.
Lemma lem3166576 : term496 = term499.
Proof. exact (@lem3166565 (@lem3166575)). Qed.
Lemma lem3166578 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3166579 : term236 = term239.
Proof. exact (@lem3166578 term2 term2). Qed.
Lemma lem3166580 : (term171 = (BIT1 0)) = (term172 = term2).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3166581 : term172 = term2.
Proof. exact (EQ_MP (@lem3166580) (@lem940073)). Qed.
Lemma lem3166582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3166583 : term170 = term93.
Proof. exact (MK_COMB (@lem3166582) (@lem3166581)). Qed.
Lemma lem3166584 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3166585 : term239 = term160.
Proof. exact (MK_COMB (@lem3166584) (@lem3166583)). Qed.
Lemma lem3166586 : term236 = term160.
Proof. exact (TRANS (@lem3166579) (@lem3166585)). Qed.
Lemma lem3166588 (x : nat) : (term276 x) = term79.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3166589 : term275 = term79.
Proof. exact (@lem3166588 term2). Qed.
Lemma lem3166590 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3166591 : term500 = term81.
Proof. exact (MK_COMB (@lem3166590) (@lem3166589)). Qed.
Lemma lem3166592 : term499 = term494.
Proof. exact (MK_COMB (@lem3166591) (@lem3166586)). Qed.
Lemma lem3166594 (m : nat) (n : nat) : (term501 m n) = (term502 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3166595 : term494 = term503.
Proof. exact (@lem3166594 (NUMERAL 0) term2). Qed.
Lemma lem3166596 : term190 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3166597 (h1 : term190 = (BIT1 0)) : (term2 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3166598 : (term190 = (BIT1 0)) = ((term2 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term190 = (BIT1 0) => @lem3166597 h1) (fun h1 : (term2 = (NUMERAL 0)) = False => @lem3166596)). Qed.
Lemma lem3166599 : (term2 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3166598) (@lem3166596)). Qed.
Lemma lem3166600 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3166601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3166602 : term504 = (and True).
Proof. exact (MK_COMB (@lem3166601) (@lem3166600)). Qed.
Lemma lem3166603 : term503 = (True /\ False).
Proof. exact (MK_COMB (@lem3166602) (@lem3166599)). Qed.
Lemma lem3166605 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3166606 : term503 = False.
Proof. exact (TRANS (@lem3166603) (@lem3166605)). Qed.
Lemma lem3166607 : term494 = False.
Proof. exact (TRANS (@lem3166595) (@lem3166606)). Qed.
Lemma lem3166608 : term499 = False.
Proof. exact (TRANS (@lem3166592) (@lem3166607)). Qed.
Lemma lem3166609 : term496 = False.
Proof. exact (TRANS (@lem3166576) (@lem3166608)). Qed.
Lemma lem3166610 : term494 = False.
Proof. exact (TRANS (@lem3166553) (@lem3166609)). Qed.
Lemma lem3166611 : term493 = False.
Proof. exact (TRANS (@lem3166544) (@lem3166610)). Qed.
Lemma lem3166612 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : False.
Proof. exact (EQ_MP (@lem3166611) (@lem3166541 _32609 _32610 h1)). Qed.
Lemma lem3166614 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : term697 _32609 _32610.
Proof. exact (h1). Qed.
Lemma lem3166615 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : (term697 _32609 _32610) = False.
Proof. exact (prop_ext (fun h2 : term697 _32609 _32610 => @lem3166612 _32609 _32610 h1) (fun h2 : False => @lem3166614 _32609 _32610 h1)). Qed.
Lemma lem3166616 (_32609 : int) (_32610 : int) (h1 : term697 _32609 _32610) : False.
Proof. exact (EQ_MP (@lem3166615 _32609 _32610 h1) (@lem3166614 _32609 _32610 h1)). Qed.
Lemma lem3166617 (_32610 : int) (_32609 : int) (h1 : term679 _32610 _32609) : term679 _32610 _32609.
Proof. exact (h1). Qed.
Lemma lem3166618 (_32610 : int) (_32609 : int) (h1 : term679 _32610 _32609) : term697 _32609 _32610.
Proof. exact (EQ_MP (@lem3166146 _32609 _32610) (@lem3166617 _32610 _32609 h1)). Qed.
Lemma lem3166619 (_32610 : int) (_32609 : int) (h1 : term679 _32610 _32609) : (term697 _32609 _32610) = False.
Proof. exact (prop_ext (fun h2 : term697 _32609 _32610 => @lem3166616 _32609 _32610 h2) (fun h2 : False => @lem3166618 _32610 _32609 h1)). Qed.
Lemma lem3166620 (_32610 : int) (_32609 : int) (h1 : term679 _32610 _32609) : False.
Proof. exact (EQ_MP (@lem3166619 _32610 _32609 h1) (@lem3166618 _32610 _32609 h1)). Qed.
Lemma lem3166621 (_32610 : int) (_32609 : int) : term713 _32610 _32609.
Proof. exact (fun h0 : term679 _32610 _32609 => @lem3166620 _32610 _32609 h0). Qed.
Lemma lem3166622 (_32610 : int) (_32609 : int) : term714 _32610 _32609.
Proof. exact (@lem1386578 (term715 _32610 _32609)). Qed.
Lemma lem3166625 (_32610 : int) (_32609 : int) : term715 _32610 _32609.
Proof. exact (@lem3166622 _32610 _32609 (@lem3166621 _32610 _32609)). Qed.
Lemma lem3166626 (_32610 : int) (_32609 : int) : (term678 _32610 _32609) = (term661 _32610 _32609).
Proof. exact (SYM (@lem3165884 _32610 _32609)). Qed.
Lemma lem3166627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3166628 (_32610 : int) (_32609 : int) : (term715 _32610 _32609) = (term649 _32610 _32609).
Proof. exact (MK_COMB (@lem3166627) (@lem3166626 _32610 _32609)). Qed.
Lemma lem3166629 (_32610 : int) (_32609 : int) : term649 _32610 _32609.
Proof. exact (EQ_MP (@lem3166628 _32610 _32609) (@lem3166625 _32610 _32609)). Qed.
Lemma lem3166630 (_32610 : int) (_32609 : int) : term650 _32610 _32609.
Proof. exact (EQ_MP (@lem3165753 _32610 _32609) (@lem3166629 _32610 _32609)). Qed.
Lemma lem3166631 (b : nat) (a : nat) : term742 b a.
Proof. exact (@lem3166630 (term717 a b) (int_of_num a)). Qed.
Lemma lem3166632 (b : nat) (a : nat) : term743 b a.
Proof. exact (@lem3166631 b a (@lem3165749 a)). Qed.
Lemma lem3166633 (b : nat) (a : nat) : term741 b a.
Proof. exact (@lem3166632 b a (@lem3165752 a b)). Qed.
Lemma lem3166634 (b : nat) (a : nat) : (term741 b a) = ((term719 b a) = (term720 b a)).
Proof. exact (SYM (@lem3165746 b a)). Qed.
Lemma lem3166636 (m : nat) : term744 m.
Proof. exact (@lem3086875 m). Qed.
Lemma lem3166637 (m : nat) : (term744 m) = (term745 m).
Proof. exact (eq_refl (term744 m)). Qed.
Lemma lem3166638 (m : nat) : term745 m.
Proof. exact (EQ_MP (@lem3166637 m) (@lem3166636 m)). Qed.
Lemma lem3166639 (m : nat) (n : nat) : term746 m n.
Proof. exact (@lem3166638 m n). Qed.
Lemma lem3166640 (m : nat) (n : nat) : (term746 m n) = (term747 m n).
Proof. exact (eq_refl (term746 m n)). Qed.
Lemma lem3166645 (a : nat) (b : nat) : (num_divides a b) = (term748 a b).
Proof. exact (EQ_MP (@lem3117508 a b) (@lem3117507 a b)). Qed.
Lemma lem3166646 (n : nat) : (num_divides n n) = (term749 n).
Proof. exact (@lem3166645 n n). Qed.
Lemma lem3166647 : term750 = term751.
Proof. exact (fun_ext (fun n : nat => @lem3166646 n)). Qed.
Lemma lem3166648 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3166649 : term752 = term753.
Proof. exact (MK_COMB (@lem3166648) (@lem3166647)). Qed.
Lemma lem3166651 (P : int -> Prop) : (term754 P) = (term755 P).
Proof. exact (proj1 (@lem3117303 P)). Qed.
Lemma lem3166652 : term756 = term757.
Proof. exact (@lem3166651 term758). Qed.
Lemma lem3166653 (n : nat) : (term759 n) = (term749 n).
Proof. exact (eq_refl (term759 n)). Qed.
Lemma lem3166654 : term760 = term751.
Proof. exact (fun_ext (fun n : nat => @lem3166653 n)). Qed.
Lemma lem3166655 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3166656 : term756 = term753.
Proof. exact (MK_COMB (@lem3166655) (@lem3166654)). Qed.
Lemma lem3166657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3166658 : term761 = term762.
Proof. exact (MK_COMB (@lem3166657) (@lem3166656)). Qed.
Lemma lem3166659 (i : int) : (term763 i) = (int_divides i i).
Proof. exact (eq_refl (term763 i)). Qed.
Lemma lem3166660 (i : int) : (term657 i) = (term657 i).
Proof. exact (eq_refl (term657 i)). Qed.
Lemma lem3166661 (i : int) : (term764 i) = (term765 i).
Proof. exact (MK_COMB (@lem3166660 i) (@lem3166659 i)). Qed.
Lemma lem3166662 : term766 = term767.
Proof. exact (fun_ext (fun i : int => @lem3166661 i)). Qed.
Lemma lem3166663 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3166664 : term757 = term768.
Proof. exact (MK_COMB (@lem3166663) (@lem3166662)). Qed.
Lemma lem3166665 : (term756 = term757) = (term753 = term768).
Proof. exact (MK_COMB (@lem3166658) (@lem3166664)). Qed.
Lemma lem3166666 : term753 = term768.
Proof. exact (EQ_MP (@lem3166665) (@lem3166652)). Qed.
Lemma lem3166669 : term752 = term768.
Proof. exact (TRANS (@lem3166649) (@lem3166666)). Qed.
Lemma lem3166670 : term768 = term752.
Proof. exact (SYM (@lem3166669)). Qed.
Lemma lem3166684 (b : int) (a : int) : (int_divides a b) = (term769 b a).
Proof. exact (EQ_MP (@lem2447298 b a) (@lem2447297 b a)). Qed.
Lemma lem3166685 (i : int) : (int_divides i i) = (term770 i).
Proof. exact (@lem3166684 i i). Qed.
Lemma lem3166692 (i : int) : (term657 i) = (term657 i).
Proof. exact (eq_refl (term657 i)). Qed.
Lemma lem3166693 (i : int) : (term765 i) = (term771 i).
Proof. exact (MK_COMB (@lem3166692 i) (@lem3166685 i)). Qed.
Lemma lem3166696 (i : int) : (term771 i) = (term765 i).
Proof. exact (SYM (@lem3166693 i)). Qed.
Lemma lem3166779 (x : int) (y : int) : (x = y) = ((int_sub x y) = term15).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3166780 (i : int) (x : int) : (i = (int_mul i x)) = ((term772 i x) = term15).
Proof. exact (@lem3166779 i (int_mul i x)). Qed.
Lemma lem3166792 (i : int) (x : int) : (term772 i x) = (term773 i x).
Proof. exact (@lem2416594 i (int_mul i x)). Qed.
Lemma lem3166797 (x : int) (i : int) : (term773 i x) = (term774 x i).
Proof. exact (@lem2416563 (term775 i x) i). Qed.
Lemma lem3166799 (x : int) (i : int) : (term772 i x) = (term774 x i).
Proof. exact (TRANS (@lem3166792 i x) (@lem3166797 x i)). Qed.
Lemma lem3166800 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3166801 (x : int) (i : int) : (term776 i x) = (term777 x i).
Proof. exact (MK_COMB (@lem3166800) (@lem3166799 x i)). Qed.
Lemma lem3166802 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem3166803 (x : int) (i : int) : ((term772 i x) = term15) = ((term774 x i) = term15).
Proof. exact (MK_COMB (@lem3166801 x i) (@lem3166802)). Qed.
Lemma lem3166804 (x : int) (i : int) : (i = (int_mul i x)) = ((term774 x i) = term15).
Proof. exact (TRANS (@lem3166780 i x) (@lem3166803 x i)). Qed.
Lemma lem3166805 (i : int) : (term778 i) = (term779 i).
Proof. exact (fun_ext (fun x : int => @lem3166804 x i)). Qed.
Lemma lem3166806 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3166807 (i : int) : (term770 i) = (term780 i).
Proof. exact (MK_COMB (@lem3166806) (@lem3166805 i)). Qed.
Lemma lem3166808 (i : int) : (term780 i) = (term770 i).
Proof. exact (SYM (@lem3166807 i)). Qed.
Lemma lem3166820 (_32615 : int) (i : int) : ((term774 _32615 i) = term15) = ((term774 _32615 i) = term15).
Proof. exact (eq_refl ((term774 _32615 i) = term15)). Qed.
Lemma lem3166821 (i : int) : (term779 i) = (term779 i).
Proof. exact (fun_ext (fun _32615 : int => @lem3166820 _32615 i)). Qed.
Lemma lem3166822 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3166824 (i : int) : (term780 i) = (term780 i).
Proof. exact (MK_COMB (@lem3166822) (@lem3166821 i)). Qed.
Lemma lem3166825 (i : int) : (term780 i) = (term780 i).
Proof. exact (SYM (@lem3166824 i)). Qed.
Lemma lem3166827 (x : int) (y : int) : (x = y) = ((int_sub x y) = term15).
Proof. exact (EQ_MP (@lem2444031 x y) (@lem2444030 x y)). Qed.
Lemma lem3166828 (_32615 : int) (i : int) : ((term774 _32615 i) = term15) = ((term781 _32615 i) = term15).
Proof. exact (@lem3166827 (term774 _32615 i) term15). Qed.
Lemma lem3166829 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem3166830 (i : int) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem3166837 (_32615 : int) (i : int) : (int_mul i _32615) = (int_mul _32615 i).
Proof. exact (@lem2416549 _32615 i). Qed.
Lemma lem3166840 : term782 = term782.
Proof. exact (eq_refl term782). Qed.
Lemma lem3166843 (_32615 : int) (i : int) : (term775 i _32615) = (term775 _32615 i).
Proof. exact (MK_COMB (@lem3166840) (@lem3166837 _32615 i)). Qed.
Lemma lem3166844 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3166845 (_32615 : int) (i : int) : (term783 i _32615) = (term783 _32615 i).
Proof. exact (MK_COMB (@lem3166844) (@lem3166843 _32615 i)). Qed.
Lemma lem3166848 (_32615 : int) (i : int) : (term774 _32615 i) = (term784 _32615 i).
Proof. exact (MK_COMB (@lem3166845 _32615 i) (@lem3166830 i)). Qed.
Lemma lem3166849 : int_sub = int_sub.
Proof. exact (eq_refl int_sub). Qed.
Lemma lem3166850 (_32615 : int) (i : int) : (term785 _32615 i) = (term786 _32615 i).
Proof. exact (MK_COMB (@lem3166849) (@lem3166848 _32615 i)). Qed.
Lemma lem3166851 (_32615 : int) (i : int) : (term781 _32615 i) = (term787 _32615 i).
Proof. exact (MK_COMB (@lem3166850 _32615 i) (@lem3166829)). Qed.
Lemma lem3166852 (_32615 : int) (i : int) : (term787 _32615 i) = (term788 _32615 i).
Proof. exact (@lem2416594 (term784 _32615 i) term15). Qed.
Lemma lem3166854 (x : nat) : (term789 x) = term15.
Proof. exact (proj2 (@lem2405764 x)). Qed.
Lemma lem3166855 : term790 = term15.
Proof. exact (@lem3166854 term2). Qed.
Lemma lem3166856 (_32615 : int) (i : int) : (term791 _32615 i) = (term791 _32615 i).
Proof. exact (eq_refl (term791 _32615 i)). Qed.
Lemma lem3166857 (_32615 : int) (i : int) : (term788 _32615 i) = (term792 _32615 i).
Proof. exact (MK_COMB (@lem3166856 _32615 i) (@lem3166855)). Qed.
Lemma lem3166858 (_32615 : int) (i : int) : (term792 _32615 i) = (term784 _32615 i).
Proof. exact (@lem2416525 (term784 _32615 i)). Qed.
Lemma lem3166859 (_32615 : int) (i : int) : (term788 _32615 i) = (term784 _32615 i).
Proof. exact (TRANS (@lem3166857 _32615 i) (@lem3166858 _32615 i)). Qed.
Lemma lem3166860 (_32615 : int) (i : int) : (term787 _32615 i) = (term784 _32615 i).
Proof. exact (TRANS (@lem3166852 _32615 i) (@lem3166859 _32615 i)). Qed.
Lemma lem3166861 (_32615 : int) (i : int) : (term781 _32615 i) = (term784 _32615 i).
Proof. exact (TRANS (@lem3166851 _32615 i) (@lem3166860 _32615 i)). Qed.
Lemma lem3166862 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3166863 (_32615 : int) (i : int) : (term793 _32615 i) = (term794 _32615 i).
Proof. exact (MK_COMB (@lem3166862) (@lem3166861 _32615 i)). Qed.
Lemma lem3166864 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem3166865 (_32615 : int) (i : int) : ((term781 _32615 i) = term15) = ((term784 _32615 i) = term15).
Proof. exact (MK_COMB (@lem3166863 _32615 i) (@lem3166864)). Qed.
Lemma lem3166866 (_32615 : int) (i : int) : ((term774 _32615 i) = term15) = ((term784 _32615 i) = term15).
Proof. exact (TRANS (@lem3166828 _32615 i) (@lem3166865 _32615 i)). Qed.
Lemma lem3166867 (i : int) : (term779 i) = (term795 i).
Proof. exact (fun_ext (fun _32615 : int => @lem3166866 _32615 i)). Qed.
Lemma lem3166868 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3166869 (i : int) : (term780 i) = (term796 i).
Proof. exact (MK_COMB (@lem3166868) (@lem3166867 i)). Qed.
Lemma lem3166870 (i : int) : (term796 i) = (term780 i).
Proof. exact (SYM (@lem3166869 i)). Qed.
Lemma lem3166878 (i : int) : ((term797 i) = term15) = ((term797 i) = term15).
Proof. exact (eq_refl ((term797 i) = term15)). Qed.
Lemma lem3166879 : term798 = term798.
Proof. exact (fun_ext (fun i : int => @lem3166878 i)). Qed.
Lemma lem3166880 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3166881 : term799 = term799.
Proof. exact (MK_COMB (@lem3166880) (@lem3166879)). Qed.
Lemma lem3166882 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3166884 : term800 = term800.
Proof. exact (MK_COMB (@lem3166882) (@lem3166881)). Qed.
Lemma lem3166886 (P : int -> Prop) : (term801 P) = (term802 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem3166887 : term800 = term803.
Proof. exact (@lem3166886 term798). Qed.
Lemma lem3166888 (i : int) : (term804 i) = ((term797 i) = term15).
Proof. exact (eq_refl (term804 i)). Qed.
Lemma lem3166889 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3166891 (i : int) : (term805 i) = (term806 i).
Proof. exact (MK_COMB (@lem3166889) (@lem3166888 i)). Qed.
Lemma lem3166892 : term807 = term808.
Proof. exact (fun_ext (fun i : int => @lem3166891 i)). Qed.
Lemma lem3166893 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem3166894 : term803 = term809.
Proof. exact (MK_COMB (@lem3166893) (@lem3166892)). Qed.
Lemma lem3166895 : term800 = term809.
Proof. exact (TRANS (@lem3166887) (@lem3166894)). Qed.
Lemma lem3166900 : term800 = term809.
Proof. exact (TRANS (@lem3166884) (@lem3166895)). Qed.
Lemma lem3166902 (i : int) (h1 : term806 i) : term806 i.
Proof. exact (h1). Qed.
Lemma lem3166903 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem3166904 (i : int) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem3166911 (i : int) : (term810 i) = i.
Proof. exact (@lem2416535 i). Qed.
Lemma lem3166914 : term782 = term782.
Proof. exact (eq_refl term782). Qed.
Lemma lem3166917 (i : int) : (term811 i) = (term812 i).
Proof. exact (MK_COMB (@lem3166914) (@lem3166911 i)). Qed.
Lemma lem3166918 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem3166919 (i : int) : (term813 i) = (term814 i).
Proof. exact (MK_COMB (@lem3166918) (@lem3166917 i)). Qed.
Lemma lem3166920 (i : int) : (term797 i) = (term815 i).
Proof. exact (MK_COMB (@lem3166919 i) (@lem3166904 i)). Qed.
Lemma lem3166921 (i : int) : (term815 i) = (term816 i).
Proof. exact (@lem2416515 term817 i). Qed.
Lemma lem3166923 (m : nat) : (term818 m) = term15.
Proof. exact (proj1 (@lem2405813 m)). Qed.
Lemma lem3166924 : term819 = term15.
Proof. exact (@lem3166923 term2). Qed.
Lemma lem3166925 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3166926 : term820 = term821.
Proof. exact (MK_COMB (@lem3166925) (@lem3166924)). Qed.
Lemma lem3166927 (i : int) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem3166928 (i : int) : (term816 i) = (term822 i).
Proof. exact (MK_COMB (@lem3166926) (@lem3166927 i)). Qed.
Lemma lem3166929 (i : int) : (term815 i) = (term822 i).
Proof. exact (TRANS (@lem3166921 i) (@lem3166928 i)). Qed.
Lemma lem3166930 (i : int) : (term822 i) = term15.
Proof. exact (@lem2416521 i). Qed.
Lemma lem3166931 (i : int) : (term815 i) = term15.
Proof. exact (TRANS (@lem3166929 i) (@lem3166930 i)). Qed.
Lemma lem3166932 (i : int) : (term797 i) = term15.
Proof. exact (TRANS (@lem3166920 i) (@lem3166931 i)). Qed.
Lemma lem3166933 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3166934 (i : int) : (term823 i) = term824.
Proof. exact (MK_COMB (@lem3166933) (@lem3166932 i)). Qed.
Lemma lem3166935 (i : int) : ((term797 i) = term15) = (term15 = term15).
Proof. exact (MK_COMB (@lem3166934 i) (@lem3166903)). Qed.
Lemma lem3166936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3166937 (i : int) : (term806 i) = term825.
Proof. exact (MK_COMB (@lem3166936) (@lem3166935 i)). Qed.
Lemma lem3166938 (i : int) (h1 : term806 i) : term825.
Proof. exact (EQ_MP (@lem3166937 i) (@lem3166902 i h1)). Qed.
Lemma lem3166939 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem3166940 : term826.
Proof. exact (@lem82 (term15 = term15)). Qed.
Lemma lem3166941 (i : int) (h1 : term806 i) : (term15 = term15) = False.
Proof. exact (@lem3166940 (@lem3166938 i h1)). Qed.
Lemma lem3166942 (i : int) (h1 : term806 i) : False.
Proof. exact (EQ_MP (@lem3166941 i h1) (@lem3166939)). Qed.
Lemma lem3166943 (i : int) : term827 i.
Proof. exact (fun h0 : term806 i => @lem3166942 i h0). Qed.
Lemma lem3166944 (i : int) : (term827 i) = (term828 i).
Proof. exact (@lem69 (term806 i)). Qed.
Lemma lem3166945 (i : int) : term828 i.
Proof. exact (EQ_MP (@lem3166944 i) (@lem3166943 i)). Qed.
Lemma lem3166946 (i : int) : term829 i.
Proof. exact (@lem82 (term806 i)). Qed.
Lemma lem3166948 (i : int) : (term806 i) = False.
Proof. exact (@lem3166946 i (@lem3166945 i)). Qed.
Lemma lem3166949 (i : int) : term830 i.
Proof. exact (@lem93 (term806 i)). Qed.
Lemma lem3166950 (i : int) : term828 i.
Proof. exact (@lem3166949 i (@lem3166948 i)). Qed.
Lemma lem3166951 (i : int) : (term828 i) = (term827 i).
Proof. exact (@lem62 (term806 i)). Qed.
Lemma lem3166952 (i : int) : term827 i.
Proof. exact (EQ_MP (@lem3166951 i) (@lem3166950 i)). Qed.
Lemma lem3166953 (i : int) (h1 : term806 i) : term806 i.
Proof. exact (h1). Qed.
Lemma lem3166954 (i : int) (h1 : term806 i) : False.
Proof. exact (@lem3166952 i (@lem3166953 i h1)). Qed.
Lemma lem3166955 (h1 : term809) : term809.
Proof. exact (h1). Qed.
Lemma lem3166956 (h1 : term809) : False.
Proof. exact (ex_elim (@lem3166955 h1) (fun i : int => fun h0 : term808 i => @lem3166954 i h0)). Qed.
Lemma lem3166957 : term831.
Proof. exact (fun h0 : term809 => @lem3166956 h0). Qed.
Lemma lem3166959 (p : Prop) (q : Prop) : term832 p q.
Proof. exact (EQ_MP (@lem1032627 p q) (@lem1032730 p q)). Qed.
Lemma lem3166960 (q : Prop) : term833 q.
Proof. exact (@lem3166959 term809 q). Qed.
Lemma lem3166963 (q : Prop) : term834 q.
Proof. exact (@lem3166960 q (@lem3166957)). Qed.
Lemma lem3166964 : term835.
Proof. exact (@lem3166963 term799). Qed.
Lemma lem3166965 : term799.
Proof. exact (@lem3166964 (@lem3166900)). Qed.
Lemma lem3166966 (i : int) : term804 i.
Proof. exact (@lem3166965 i). Qed.
Lemma lem3166967 (i : int) : (term804 i) = ((term797 i) = term15).
Proof. exact (eq_refl (term804 i)). Qed.
Lemma lem3166968 (i : int) : (term797 i) = term15.
Proof. exact (EQ_MP (@lem3166967 i) (@lem3166966 i)). Qed.
Lemma lem3166969 (i : int) : term796 i.
Proof. exact (ex_intro (term795 i) term18 (@lem3166968 i)). Qed.
Lemma lem3166970 (i : int) : term780 i.
Proof. exact (EQ_MP (@lem3166870 i) (@lem3166969 i)). Qed.
Lemma lem3166972 (i : int) : term780 i.
Proof. exact (EQ_MP (@lem3166825 i) (@lem3166970 i)). Qed.
Lemma lem3166976 (i : int) : term770 i.
Proof. exact (EQ_MP (@lem3166808 i) (@lem3166972 i)). Qed.
Lemma lem3166977 (i : int) : term771 i.
Proof. exact (fun h0 : term73 i => @lem3166976 i). Qed.
Lemma lem3166979 (i : int) : term765 i.
Proof. exact (EQ_MP (@lem3166696 i) (@lem3166977 i)). Qed.
Lemma lem3166985 : term768.
Proof. exact (fun i : int => @lem3166979 i). Qed.
Lemma lem3166986 : term752.
Proof. exact (EQ_MP (@lem3166670) (@lem3166985)). Qed.
Lemma lem3166987 (n : nat) : term836 n.
Proof. exact (@lem3166986 n). Qed.
Lemma lem3166988 (n : nat) : (term836 n) = (num_divides n n).
Proof. exact (eq_refl (term836 n)). Qed.
Lemma lem3166990 (n : nat) : num_divides n n.
Proof. exact (EQ_MP (@lem3166988 n) (@lem3166987 n)). Qed.
Lemma lem3166991 (n : nat) : (num_divides n n) = ((num_divides n n) = True).
Proof. exact (@lem7 (num_divides n n)). Qed.
Lemma lem3166993 (t1 : Prop) : term837 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem3166994 (t1 : Prop) : (term837 t1) = (term838 t1).
Proof. exact (eq_refl (term837 t1)). Qed.
Lemma lem3166995 (t1 : Prop) : term838 t1.
Proof. exact (EQ_MP (@lem3166994 t1) (@lem3166993 t1)). Qed.
Lemma lem3166996 (t1 : Prop) (t2 : Prop) : term839 t1 t2.
Proof. exact (@lem3166995 t1 t2). Qed.
Lemma lem3166997 (t1 : Prop) (t2 : Prop) : (term839 t1 t2) = (term840 t1 t2).
Proof. exact (eq_refl (term839 t1 t2)). Qed.
Lemma lem3166998 (t1 : Prop) (t2 : Prop) : term840 t1 t2.
Proof. exact (EQ_MP (@lem3166997 t1 t2) (@lem3166996 t1 t2)). Qed.
Lemma lem3167007 (m : nat) : term841 m.
Proof. exact (@lem83870 m). Qed.
Lemma lem3167008 (m : nat) : (term841 m) = (term842 m).
Proof. exact (eq_refl (term841 m)). Qed.
Lemma lem3167009 (m : nat) : term842 m.
Proof. exact (EQ_MP (@lem3167008 m) (@lem3167007 m)). Qed.
Lemma lem3167010 (m : nat) (n : nat) : term843 m n.
Proof. exact (@lem3167009 m n). Qed.
Lemma lem3167011 (m : nat) (n : nat) : (term843 m n) = (((Nat.mul m n) = (NUMERAL 0)) = (term844 m n)).
Proof. exact (eq_refl (term843 m n)). Qed.
Lemma lem3167021 (p : Prop) : term845 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem3167022 (p : Prop) : (term845 p) = (term846 p).
Proof. exact (eq_refl (term845 p)). Qed.
Lemma lem3167023 (p : Prop) : term846 p.
Proof. exact (EQ_MP (@lem3167022 p) (@lem3167021 p)). Qed.
Lemma lem3167024 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem3167025 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem3167034 (q : Prop) : (term847 q) = (term847 q).
Proof. exact (eq_refl (term847 q)). Qed.
Lemma lem3167035 (q : Prop) (p : Prop) (h1 : p = True) : (term848 q p) = (term849 q).
Proof. exact (MK_COMB (@lem3167034 q) (@lem3167024 p h1)). Qed.
Lemma lem3167036 (q : Prop) : (term849 q) = ((True \/ q) = (term850 q)).
Proof. exact (eq_refl (term849 q)). Qed.
Lemma lem3167037 (q : Prop) (p : Prop) : (term851 q p) = (term851 q p).
Proof. exact (eq_refl (term851 q p)). Qed.
Lemma lem3167038 (p : Prop) (q : Prop) : ((term848 q p) = (term849 q)) = ((term848 q p) = ((True \/ q) = (term850 q))).
Proof. exact (MK_COMB (@lem3167037 q p) (@lem3167036 q)). Qed.
Lemma lem3167039 (p : Prop) (q : Prop) : (term848 q p) = ((p \/ q) = (term852 p q)).
Proof. exact (eq_refl (term848 q p)). Qed.
Lemma lem3167040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167041 (p : Prop) (q : Prop) : (term851 q p) = (term853 p q).
Proof. exact (MK_COMB (@lem3167040) (@lem3167039 p q)). Qed.
Lemma lem3167042 (q : Prop) : ((True \/ q) = (term850 q)) = ((True \/ q) = (term850 q)).
Proof. exact (eq_refl ((True \/ q) = (term850 q))). Qed.
Lemma lem3167043 (p : Prop) (q : Prop) : ((term848 q p) = ((True \/ q) = (term850 q))) = (((p \/ q) = (term852 p q)) = ((True \/ q) = (term850 q))).
Proof. exact (MK_COMB (@lem3167041 p q) (@lem3167042 q)). Qed.
Lemma lem3167044 (p : Prop) (q : Prop) : ((term848 q p) = (term849 q)) = (((p \/ q) = (term852 p q)) = ((True \/ q) = (term850 q))).
Proof. exact (TRANS (@lem3167038 p q) (@lem3167043 p q)). Qed.
Lemma lem3167045 (q : Prop) (p : Prop) (h1 : p = True) : ((p \/ q) = (term852 p q)) = ((True \/ q) = (term850 q)).
Proof. exact (EQ_MP (@lem3167044 p q) (@lem3167035 q p h1)). Qed.
Lemma lem3167046 (q : Prop) (p : Prop) (h1 : p = True) : ((True \/ q) = (term850 q)) = ((p \/ q) = (term852 p q)).
Proof. exact (SYM (@lem3167045 q p h1)). Qed.
Lemma lem3167047 (q : Prop) : (term847 q) = (term847 q).
Proof. exact (eq_refl (term847 q)). Qed.
Lemma lem3167048 (q : Prop) (p : Prop) (h1 : p = False) : (term848 q p) = (term854 q).
Proof. exact (MK_COMB (@lem3167047 q) (@lem3167025 p h1)). Qed.
Lemma lem3167049 (q : Prop) : (term854 q) = ((False \/ q) = (term855 q)).
Proof. exact (eq_refl (term854 q)). Qed.
Lemma lem3167050 (q : Prop) (p : Prop) : (term851 q p) = (term851 q p).
Proof. exact (eq_refl (term851 q p)). Qed.
Lemma lem3167051 (p : Prop) (q : Prop) : ((term848 q p) = (term854 q)) = ((term848 q p) = ((False \/ q) = (term855 q))).
Proof. exact (MK_COMB (@lem3167050 q p) (@lem3167049 q)). Qed.
Lemma lem3167052 (p : Prop) (q : Prop) : (term848 q p) = ((p \/ q) = (term852 p q)).
Proof. exact (eq_refl (term848 q p)). Qed.
Lemma lem3167053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167054 (p : Prop) (q : Prop) : (term851 q p) = (term853 p q).
Proof. exact (MK_COMB (@lem3167053) (@lem3167052 p q)). Qed.
Lemma lem3167055 (q : Prop) : ((False \/ q) = (term855 q)) = ((False \/ q) = (term855 q)).
Proof. exact (eq_refl ((False \/ q) = (term855 q))). Qed.
Lemma lem3167056 (p : Prop) (q : Prop) : ((term848 q p) = ((False \/ q) = (term855 q))) = (((p \/ q) = (term852 p q)) = ((False \/ q) = (term855 q))).
Proof. exact (MK_COMB (@lem3167054 p q) (@lem3167055 q)). Qed.
Lemma lem3167057 (p : Prop) (q : Prop) : ((term848 q p) = (term854 q)) = (((p \/ q) = (term852 p q)) = ((False \/ q) = (term855 q))).
Proof. exact (TRANS (@lem3167051 p q) (@lem3167056 p q)). Qed.
Lemma lem3167058 (q : Prop) (p : Prop) (h1 : p = False) : ((p \/ q) = (term852 p q)) = ((False \/ q) = (term855 q)).
Proof. exact (EQ_MP (@lem3167057 p q) (@lem3167048 q p h1)). Qed.
Lemma lem3167059 (q : Prop) (p : Prop) (h1 : p = False) : ((False \/ q) = (term855 q)) = ((p \/ q) = (term852 p q)).
Proof. exact (SYM (@lem3167058 q p h1)). Qed.
Lemma lem3167063 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3167064 (q : Prop) : (True \/ q) = True.
Proof. exact (@lem3167063 q). Qed.
Lemma lem3167065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167066 (q : Prop) : (term856 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3167065) (@lem3167064 q)). Qed.
Lemma lem3167070 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3167071 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167072 : term857 = (imp False).
Proof. exact (MK_COMB (@lem3167071) (@lem3167070)). Qed.
Lemma lem3167073 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem3167074 (q : Prop) : (term850 q) = (False -> q).
Proof. exact (MK_COMB (@lem3167072) (@lem3167073 q)). Qed.
Lemma lem3167076 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3167077 (q : Prop) : (False -> q) = True.
Proof. exact (@lem3167076 q). Qed.
Lemma lem3167078 (q : Prop) : (term850 q) = True.
Proof. exact (TRANS (@lem3167074 q) (@lem3167077 q)). Qed.
Lemma lem3167079 (q : Prop) : ((True \/ q) = (term850 q)) = (True = True).
Proof. exact (MK_COMB (@lem3167066 q) (@lem3167078 q)). Qed.
Lemma lem3167081 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3167082 : (True = True) = True.
Proof. exact (@lem3167081 True). Qed.
Lemma lem3167083 (q : Prop) : ((True \/ q) = (term850 q)) = True.
Proof. exact (TRANS (@lem3167079 q) (@lem3167082)). Qed.
Lemma lem3167084 (q : Prop) : True = ((True \/ q) = (term850 q)).
Proof. exact (SYM (@lem3167083 q)). Qed.
Lemma lem3167085 (q : Prop) : (True \/ q) = (term850 q).
Proof. exact (EQ_MP (@lem3167084 q) (@lem0)). Qed.
Lemma lem3167089 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3167090 (q : Prop) : (False \/ q) = q.
Proof. exact (@lem3167089 q). Qed.
Lemma lem3167091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167092 (q : Prop) : (term858 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem3167091) (@lem3167090 q)). Qed.
Lemma lem3167096 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3167097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167098 : term859 = (imp True).
Proof. exact (MK_COMB (@lem3167097) (@lem3167096)). Qed.
Lemma lem3167099 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem3167100 (q : Prop) : (term855 q) = (True -> q).
Proof. exact (MK_COMB (@lem3167098) (@lem3167099 q)). Qed.
Lemma lem3167102 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3167103 (q : Prop) : (True -> q) = q.
Proof. exact (@lem3167102 q). Qed.
Lemma lem3167104 (q : Prop) : (term855 q) = q.
Proof. exact (TRANS (@lem3167100 q) (@lem3167103 q)). Qed.
Lemma lem3167105 (q : Prop) : ((False \/ q) = (term855 q)) = (q = q).
Proof. exact (MK_COMB (@lem3167092 q) (@lem3167104 q)). Qed.
Lemma lem3167107 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3167108 (x : Prop) : (x = x) = True.
Proof. exact (@lem3167107 Prop x). Qed.
Lemma lem3167109 (q : Prop) : (q = q) = True.
Proof. exact (@lem3167108 q). Qed.
Lemma lem3167110 (q : Prop) : ((False \/ q) = (term855 q)) = True.
Proof. exact (TRANS (@lem3167105 q) (@lem3167109 q)). Qed.
Lemma lem3167111 (q : Prop) : True = ((False \/ q) = (term855 q)).
Proof. exact (SYM (@lem3167110 q)). Qed.
Lemma lem3167112 (q : Prop) : (False \/ q) = (term855 q).
Proof. exact (EQ_MP (@lem3167111 q) (@lem0)). Qed.
Lemma lem3167113 (q : Prop) (p : Prop) (h1 : p = False) : (p \/ q) = (term852 p q).
Proof. exact (EQ_MP (@lem3167059 q p h1) (@lem3167112 q)). Qed.
Lemma lem3167114 (q : Prop) (p : Prop) (h1 : p = True) : (p \/ q) = (term852 p q).
Proof. exact (EQ_MP (@lem3167046 q p h1) (@lem3167085 q)). Qed.
Lemma lem3167118 (p : nat) : term860 p.
Proof. exact (@lem3157314 p). Qed.
Lemma lem3167119 (p : nat) : (term860 p) = (term861 p).
Proof. exact (eq_refl (term860 p)). Qed.
Lemma lem3167120 (p : nat) : term861 p.
Proof. exact (EQ_MP (@lem3167119 p) (@lem3167118 p)). Qed.
Lemma lem3167121 (p : nat) (a : nat) : term862 p a.
Proof. exact (@lem3167120 p a). Qed.
Lemma lem3167122 (a : nat) (p : nat) : (term862 p a) = (term863 a p).
Proof. exact (eq_refl (term862 p a)). Qed.
Lemma lem3167123 (a : nat) (p : nat) : term863 a p.
Proof. exact (EQ_MP (@lem3167122 a p) (@lem3167121 p a)). Qed.
Lemma lem3167124 (a : nat) (p : nat) (b : nat) : term864 a p b.
Proof. exact (@lem3167123 a p b). Qed.
Lemma lem3167125 (a : nat) (p : nat) (b : nat) : (term864 a p b) = (term865 a p b).
Proof. exact (eq_refl (term864 a p b)). Qed.
Lemma lem3167126 (a : nat) (p : nat) (b : nat) : term865 a p b.
Proof. exact (EQ_MP (@lem3167125 a p b) (@lem3167124 a p b)). Qed.
Lemma lem3167127 (p : nat) (h1 : term866 p) : term866 p.
Proof. exact (h1). Qed.
Lemma lem3167128 (a : nat) (b : nat) (p : nat) (h1 : term866 p) : (term867 p a b) = (term868 a p b).
Proof. exact (@lem3167126 a p b (@lem3167127 p h1)). Qed.
Lemma lem3167137 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term869 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3167138 (p : Prop) (q : Prop) (p' : Prop) : term870 p q p'.
Proof. exact (fun q' : Prop => @lem3167137 p q p' q'). Qed.
Lemma lem3167139 (p : Prop) (q : Prop) : term871 p q.
Proof. exact (fun p' : Prop => @lem3167138 p q p'). Qed.
Lemma lem3167140 (p : nat) : term872 p.
Proof. exact (@lem3167139 (term866 p) (term873 p)). Qed.
Lemma lem3167141 (p : nat) (p' : Prop) : term874 p p'.
Proof. exact (@lem3167140 p p'). Qed.
Lemma lem3167142 (p : nat) (p' : Prop) : (term874 p p') = (term875 p p').
Proof. exact (eq_refl (term874 p p')). Qed.
Lemma lem3167143 (p : nat) (p' : Prop) : term875 p p'.
Proof. exact (EQ_MP (@lem3167142 p p') (@lem3167141 p p')). Qed.
Lemma lem3167144 (p : nat) (p' : Prop) (q' : Prop) : term876 p p' q'.
Proof. exact (@lem3167143 p p' q'). Qed.
Lemma lem3167145 (p : nat) (p' : Prop) (q' : Prop) : (term876 p p' q') = (term877 p p' q').
Proof. exact (eq_refl (term876 p p' q')). Qed.
Lemma lem3167146 (p : nat) (p' : Prop) (q' : Prop) : term877 p p' q'.
Proof. exact (EQ_MP (@lem3167145 p p' q') (@lem3167144 p p' q')). Qed.
Lemma lem3167155 (p : nat) : (term866 p) = (term866 p).
Proof. exact (eq_refl (term866 p)). Qed.
Lemma lem3167156 (p : nat) (q' : Prop) : term878 p q'.
Proof. exact (@lem3167146 p (term866 p) q'). Qed.
Lemma lem3167157 (p : nat) (q' : Prop) : term879 p q'.
Proof. exact (@lem3167156 p q' (@lem3167155 p)). Qed.
Lemma lem3167158 (p : nat) (h1 : term866 p) : term866 p.
Proof. exact (h1). Qed.
Lemma lem3167159 (p : nat) : (term866 p) = ((term866 p) = True).
Proof. exact (@lem7 (term866 p)). Qed.
Lemma lem3167172 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term869 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3167173 (p : Prop) (q : Prop) (p' : Prop) : term870 p q p'.
Proof. exact (fun q' : Prop => @lem3167172 p q p' q'). Qed.
Lemma lem3167174 (p : Prop) (q : Prop) : term871 p q.
Proof. exact (fun p' : Prop => @lem3167173 p q p'). Qed.
Lemma lem3167175 (a : nat) (p : nat) (b : nat) : term880 a p b.
Proof. exact (@lem3167174 (term867 p a b) (term868 a p b)). Qed.
Lemma lem3167176 (a : nat) (p : nat) (b : nat) (p' : Prop) : term881 a p b p'.
Proof. exact (@lem3167175 a p b p'). Qed.
Lemma lem3167177 (a : nat) (p : nat) (b : nat) (p' : Prop) : (term881 a p b p') = (term882 a p b p').
Proof. exact (eq_refl (term881 a p b p')). Qed.
Lemma lem3167178 (a : nat) (p : nat) (b : nat) (p' : Prop) : term882 a p b p'.
Proof. exact (EQ_MP (@lem3167177 a p b p') (@lem3167176 a p b p')). Qed.
Lemma lem3167179 (a : nat) (p : nat) (b : nat) (p' : Prop) (q' : Prop) : term883 a p b p' q'.
Proof. exact (@lem3167178 a p b p' q'). Qed.
Lemma lem3167180 (a : nat) (p : nat) (b : nat) (p' : Prop) (q' : Prop) : (term883 a p b p' q') = (term884 a p b p' q').
Proof. exact (eq_refl (term883 a p b p' q')). Qed.
Lemma lem3167181 (a : nat) (p : nat) (b : nat) (p' : Prop) (q' : Prop) : term884 a p b p' q'.
Proof. exact (EQ_MP (@lem3167180 a p b p' q') (@lem3167179 a p b p' q')). Qed.
Lemma lem3167183 (a : nat) (p : nat) (b : nat) : term865 a p b.
Proof. exact (fun h0 : term866 p => @lem3167128 a b p h0). Qed.
Lemma lem3167185 (p : nat) (h1 : term866 p) : (term866 p) = True.
Proof. exact (EQ_MP (@lem3167159 p) (@lem3167158 p h1)). Qed.
Lemma lem3167186 (p : nat) (h1 : term866 p) : True = (term866 p).
Proof. exact (SYM (@lem3167185 p h1)). Qed.
Lemma lem3167187 (p : nat) (h1 : term866 p) : term866 p.
Proof. exact (EQ_MP (@lem3167186 p h1) (@lem0)). Qed.
Lemma lem3167188 (a : nat) (b : nat) (p : nat) (h1 : term866 p) : (term867 p a b) = (term868 a p b).
Proof. exact (@lem3167183 a p b (@lem3167187 p h1)). Qed.
Lemma lem3167191 (a : nat) (p : nat) (b : nat) (q' : Prop) : term885 a p b q'.
Proof. exact (@lem3167181 a p b (term868 a p b) q'). Qed.
Lemma lem3167192 (a : nat) (b : nat) (q' : Prop) (p : nat) (h1 : term866 p) : term886 a p b q'.
Proof. exact (@lem3167191 a p b q' (@lem3167188 a b p h1)). Qed.
Lemma lem3167193 (a : nat) (p : nat) (b : nat) (h1 : term868 a p b) : term868 a p b.
Proof. exact (h1). Qed.
Lemma lem3167194 (a : nat) (p : nat) (b : nat) : (term868 a p b) = ((term868 a p b) = True).
Proof. exact (@lem7 (term868 a p b)). Qed.
Lemma lem3167197 (a : nat) (p : nat) (b : nat) (h1 : term868 a p b) : (term868 a p b) = True.
Proof. exact (EQ_MP (@lem3167194 a p b) (@lem3167193 a p b h1)). Qed.
Lemma lem3167198 (a : nat) (p : nat) (b : nat) : term887 a p b.
Proof. exact (fun h0 : term868 a p b => @lem3167197 a p b h0). Qed.
Lemma lem3167199 (a : nat) (b : nat) (p : nat) (h1 : term866 p) : term888 a p b.
Proof. exact (@lem3167192 a b True p h1). Qed.
Lemma lem3167200 (a : nat) (b : nat) (p : nat) (h1 : term866 p) : (term889 a p b) = (term890 a p b).
Proof. exact (@lem3167199 a b p h1 (@lem3167198 a p b)). Qed.
Lemma lem3167202 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3167203 (a : nat) (p : nat) (b : nat) : (term890 a p b) = True.
Proof. exact (@lem3167202 (term868 a p b)). Qed.
Lemma lem3167204 (a : nat) (b : nat) (p : nat) (h1 : term866 p) : (term889 a p b) = True.
Proof. exact (TRANS (@lem3167200 a b p h1) (@lem3167203 a p b)). Qed.
Lemma lem3167205 (a : nat) (p : nat) (h1 : term866 p) : (term891 a p) = term892.
Proof. exact (fun_ext (fun b : nat => @lem3167204 a b p h1)). Qed.
Lemma lem3167206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3167207 (a : nat) (p : nat) (h1 : term866 p) : (term893 a p) = term894.
Proof. exact (MK_COMB (@lem3167206) (@lem3167205 a p h1)). Qed.
Lemma lem3167209 {A : Type'} (t : Prop) : (term895 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3167210 (t : Prop) : (term896 t) = t.
Proof. exact (@lem3167209 nat t). Qed.
Lemma lem3167211 : term894 = True.
Proof. exact (@lem3167210 True). Qed.
Lemma lem3167212 (a : nat) (p : nat) (h1 : term866 p) : (term893 a p) = True.
Proof. exact (TRANS (@lem3167207 a p h1) (@lem3167211)). Qed.
Lemma lem3167213 (p : nat) (h1 : term866 p) : (term897 p) = term892.
Proof. exact (fun_ext (fun a : nat => @lem3167212 a p h1)). Qed.
Lemma lem3167214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3167215 (p : nat) (h1 : term866 p) : (term873 p) = term894.
Proof. exact (MK_COMB (@lem3167214) (@lem3167213 p h1)). Qed.
Lemma lem3167217 {A : Type'} (t : Prop) : (term895 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3167218 (t : Prop) : (term896 t) = t.
Proof. exact (@lem3167217 nat t). Qed.
Lemma lem3167219 : term894 = True.
Proof. exact (@lem3167218 True). Qed.
Lemma lem3167220 (p : nat) (h1 : term866 p) : (term873 p) = True.
Proof. exact (TRANS (@lem3167215 p h1) (@lem3167219)). Qed.
Lemma lem3167221 (p : nat) : term898 p.
Proof. exact (fun h0 : term866 p => @lem3167220 p h0). Qed.
Lemma lem3167222 (p : nat) : term899 p.
Proof. exact (@lem3167157 p True). Qed.
Lemma lem3167223 (p : nat) : (term900 p) = (term901 p).
Proof. exact (@lem3167222 p (@lem3167221 p)). Qed.
Lemma lem3167225 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3167226 (p : nat) : (term901 p) = True.
Proof. exact (@lem3167225 (term866 p)). Qed.
Lemma lem3167227 (p : nat) : (term900 p) = True.
Proof. exact (TRANS (@lem3167223 p) (@lem3167226 p)). Qed.
Lemma lem3167228 (p : nat) : True = (term900 p).
Proof. exact (SYM (@lem3167227 p)). Qed.
Lemma lem3167229 (p : nat) : term900 p.
Proof. exact (EQ_MP (@lem3167228 p) (@lem0)). Qed.
Lemma lem3167402 (p : nat) (h1 : term873 p) : term873 p.
Proof. exact (h1). Qed.
Lemma lem3167406 (p : Prop) (q : Prop) : (p \/ q) = (term852 p q).
Proof. exact (or_elim (@lem3167023 p) (fun h0 : p = True => @lem3167114 q p h0) (fun h0 : p = False => @lem3167113 q p h0)). Qed.
Lemma lem3167407 (p : nat) : (term866 p) = (term902 p).
Proof. exact (@lem3167406 (p = (NUMERAL 0)) (term903 p)). Qed.
Lemma lem3167415 (p : Prop) (q : Prop) : (p \/ q) = (term852 p q).
Proof. exact (or_elim (@lem3167023 p) (fun h0 : p = True => @lem3167114 q p h0) (fun h0 : p = False => @lem3167113 q p h0)). Qed.
Lemma lem3167416 (p : nat) : (term903 p) = (term904 p).
Proof. exact (@lem3167415 (p = term2) (prime p)). Qed.
Lemma lem3167421 (p : nat) : (term905 p) = (term905 p).
Proof. exact (eq_refl (term905 p)). Qed.
Lemma lem3167422 (p : nat) : (term902 p) = (term906 p).
Proof. exact (MK_COMB (@lem3167421 p) (@lem3167416 p)). Qed.
Lemma lem3167425 (p : nat) : (term866 p) = (term906 p).
Proof. exact (TRANS (@lem3167407 p) (@lem3167422 p)). Qed.
Lemma lem3167426 (p : nat) : (term906 p) = (term866 p).
Proof. exact (SYM (@lem3167425 p)). Qed.
Lemma lem3167427 (p : nat) (h1 : term26 p) : term26 p.
Proof. exact (h1). Qed.
Lemma lem3167428 (p : nat) (h1 : term30 p) : term30 p.
Proof. exact (h1). Qed.
Lemma lem3167429 {A : Type'} (P : A -> Prop) : term907 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem3167430 {A : Type'} (P : A -> Prop) : (term907 A P) = (term908 A P).
Proof. exact (eq_refl (term907 A P)). Qed.
Lemma lem3167431 {A : Type'} (P : A -> Prop) : term908 A P.
Proof. exact (EQ_MP (@lem3167430 A P) (@lem3167429 A P)). Qed.
Lemma lem3167432 {A : Type'} (P : A -> Prop) (Q : Prop) : term909 A P Q.
Proof. exact (@lem3167431 A P Q). Qed.
Lemma lem3167433 {A : Type'} (P : A -> Prop) (Q : Prop) : (term909 A P Q) = ((term910 A P Q) = (term911 A P Q)).
Proof. exact (eq_refl (term909 A P Q)). Qed.
Lemma lem3167435 (p : nat) : term912 p.
Proof. exact (@lem3137997 p). Qed.
Lemma lem3167436 (p : nat) : (term912 p) = ((prime p) = (term913 p)).
Proof. exact (eq_refl (term912 p)). Qed.
Lemma lem3167459 (p : nat) : term914 p.
Proof. exact (@lem82 (p = term2)). Qed.
Lemma lem3167473 (p : nat) : (prime p) = (term913 p).
Proof. exact (EQ_MP (@lem3167436 p) (@lem3167435 p)). Qed.
Lemma lem3167477 (p : nat) (h1 : term30 p) : (p = term2) = False.
Proof. exact (@lem3167459 p (@lem3167428 p h1)). Qed.
Lemma lem3167478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3167479 (p : nat) (h1 : term30 p) : (term30 p) = (~ False).
Proof. exact (MK_COMB (@lem3167478) (@lem3167477 p h1)). Qed.
Lemma lem3167481 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3167482 (p : nat) (h1 : term30 p) : (term30 p) = True.
Proof. exact (TRANS (@lem3167479 p h1) (@lem3167481)). Qed.
Lemma lem3167483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3167484 (p : nat) (h1 : term30 p) : (term915 p) = (and True).
Proof. exact (MK_COMB (@lem3167483) (@lem3167482 p h1)). Qed.
Lemma lem3167492 (b : nat) (a : nat) : (num_divides a b) = (term916 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
Lemma lem3167493 (p : nat) (x : nat) : (num_divides x p) = (term916 p x).
Proof. exact (@lem3167492 p x). Qed.
Lemma lem3167500 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167501 (p : nat) (x : nat) : (term917 x p) = (term918 p x).
Proof. exact (MK_COMB (@lem3167500) (@lem3167493 p x)). Qed.
Lemma lem3167508 (x : nat) (p : nat) : (term919 x p) = (term919 x p).
Proof. exact (eq_refl (term919 x p)). Qed.
Lemma lem3167509 (x : nat) (p : nat) : (term920 x p) = (term921 x p).
Proof. exact (MK_COMB (@lem3167501 p x) (@lem3167508 x p)). Qed.
Lemma lem3167511 {A : Type'} (P : A -> Prop) (Q : Prop) : (term910 A P Q) = (term911 A P Q).
Proof. exact (EQ_MP (@lem3167433 A P Q) (@lem3167432 A P Q)). Qed.
Lemma lem3167512 (P : nat -> Prop) (Q : Prop) : (term922 P Q) = (term923 P Q).
Proof. exact (@lem3167511 nat P Q). Qed.
Lemma lem3167513 (x : nat) (p : nat) : (term924 x p) = (term925 x p).
Proof. exact (@lem3167512 (term926 p x) (term919 x p)). Qed.
Lemma lem3167514 (p : nat) (x : nat) (x' : nat) : (term927 p x x') = (p = (Nat.mul x x')).
Proof. exact (eq_refl (term927 p x x')). Qed.
Lemma lem3167515 (p : nat) (x : nat) : (term928 p x) = (term926 p x).
Proof. exact (fun_ext (fun x' : nat => @lem3167514 p x x')). Qed.
Lemma lem3167516 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3167517 (p : nat) (x : nat) : (term929 p x) = (term916 p x).
Proof. exact (MK_COMB (@lem3167516) (@lem3167515 p x)). Qed.
Lemma lem3167518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167519 (p : nat) (x : nat) : (term930 p x) = (term918 p x).
Proof. exact (MK_COMB (@lem3167518) (@lem3167517 p x)). Qed.
Lemma lem3167520 (x : nat) (p : nat) : (term919 x p) = (term919 x p).
Proof. exact (eq_refl (term919 x p)). Qed.
Lemma lem3167521 (x : nat) (p : nat) : (term924 x p) = (term921 x p).
Proof. exact (MK_COMB (@lem3167519 p x) (@lem3167520 x p)). Qed.
Lemma lem3167522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167523 (x : nat) (p : nat) : (term931 x p) = (term932 x p).
Proof. exact (MK_COMB (@lem3167522) (@lem3167521 x p)). Qed.
Lemma lem3167524 (p : nat) (x : nat) (x' : nat) : (term927 p x x') = (p = (Nat.mul x x')).
Proof. exact (eq_refl (term927 p x x')). Qed.
Lemma lem3167525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167526 (p : nat) (x : nat) (x' : nat) : (term933 p x x') = (term934 p x x').
Proof. exact (MK_COMB (@lem3167525) (@lem3167524 p x x')). Qed.
Lemma lem3167527 (x : nat) (p : nat) : (term919 x p) = (term919 x p).
Proof. exact (eq_refl (term919 x p)). Qed.
Lemma lem3167528 (x' : nat) (x : nat) (p : nat) : (term935 x' x p) = (term936 x' x p).
Proof. exact (MK_COMB (@lem3167526 p x x') (@lem3167527 x p)). Qed.
Lemma lem3167529 (x : nat) (p : nat) : (term937 x p) = (term938 x p).
Proof. exact (fun_ext (fun x' : nat => @lem3167528 x' x p)). Qed.
Lemma lem3167530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3167531 (x : nat) (p : nat) : (term925 x p) = (term939 x p).
Proof. exact (MK_COMB (@lem3167530) (@lem3167529 x p)). Qed.
Lemma lem3167532 (x : nat) (p : nat) : ((term924 x p) = (term925 x p)) = ((term921 x p) = (term939 x p)).
Proof. exact (MK_COMB (@lem3167523 x p) (@lem3167531 x p)). Qed.
Lemma lem3167533 (x : nat) (p : nat) : (term921 x p) = (term939 x p).
Proof. exact (EQ_MP (@lem3167532 x p) (@lem3167513 x p)). Qed.
Lemma lem3167550 (x : nat) (p : nat) : (term920 x p) = (term939 x p).
Proof. exact (TRANS (@lem3167509 x p) (@lem3167533 x p)). Qed.
Lemma lem3167551 (p : nat) : (term940 p) = (term941 p).
Proof. exact (fun_ext (fun x : nat => @lem3167550 x p)). Qed.
Lemma lem3167552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3167553 (p : nat) : (term942 p) = (term943 p).
Proof. exact (MK_COMB (@lem3167552) (@lem3167551 p)). Qed.
Lemma lem3167558 (p : nat) (h1 : term30 p) : (term913 p) = (term944 p).
Proof. exact (MK_COMB (@lem3167484 p h1) (@lem3167553 p)). Qed.
Lemma lem3167560 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3167561 (p : nat) : (term944 p) = (term943 p).
Proof. exact (@lem3167560 (term943 p)). Qed.
Lemma lem3167582 (p : nat) (h1 : term30 p) : (term913 p) = (term943 p).
Proof. exact (TRANS (@lem3167558 p h1) (@lem3167561 p)). Qed.
Lemma lem3167583 (p : nat) (h1 : term30 p) : (prime p) = (term943 p).
Proof. exact (TRANS (@lem3167473 p) (@lem3167582 p h1)). Qed.
Lemma lem3167584 (p : nat) (h1 : term30 p) : (term943 p) = (prime p).
Proof. exact (SYM (@lem3167583 p h1)). Qed.
Lemma lem3167587 (a : nat) (p : nat) (h1 : term873 p) : term945 p a.
Proof. exact (@lem3167402 p h1 a). Qed.
Lemma lem3167588 (a : nat) (p : nat) : (term945 p a) = (term893 a p).
Proof. exact (eq_refl (term945 p a)). Qed.
Lemma lem3167589 (a : nat) (p : nat) (h1 : term873 p) : term893 a p.
Proof. exact (EQ_MP (@lem3167588 a p) (@lem3167587 a p h1)). Qed.
Lemma lem3167590 (a : nat) (b : nat) (p : nat) (h1 : term873 p) : term946 a p b.
Proof. exact (@lem3167589 a p h1 b). Qed.
Lemma lem3167591 (a : nat) (p : nat) (b : nat) : (term946 a p b) = (term889 a p b).
Proof. exact (eq_refl (term946 a p b)). Qed.
Lemma lem3167592 (a : nat) (b : nat) (p : nat) (h1 : term873 p) : term889 a p b.
Proof. exact (EQ_MP (@lem3167591 a p b) (@lem3167590 a b p h1)). Qed.
Lemma lem3167593 (p : nat) (a : nat) (b : nat) (h1 : p = (Nat.mul a b)) : p = (Nat.mul a b).
Proof. exact (h1). Qed.
Lemma lem3167594 (b : nat) (a : nat) : (term947 b a) = (term947 b a).
Proof. exact (eq_refl (term947 b a)). Qed.
Lemma lem3167595 (p : nat) (a : nat) (b : nat) (h1 : p = (Nat.mul a b)) : (term948 b a p) = (term949 a b).
Proof. exact (MK_COMB (@lem3167594 b a) (@lem3167593 p a b h1)). Qed.
Lemma lem3167596 (a : nat) (b : nat) : (term949 a b) = (term950 a b).
Proof. exact (eq_refl (term949 a b)). Qed.
Lemma lem3167597 (b : nat) (a : nat) (p : nat) : (term951 b a p) = (term951 b a p).
Proof. exact (eq_refl (term951 b a p)). Qed.
Lemma lem3167598 (p : nat) (a : nat) (b : nat) : ((term948 b a p) = (term949 a b)) = ((term948 b a p) = (term950 a b)).
Proof. exact (MK_COMB (@lem3167597 b a p) (@lem3167596 a b)). Qed.
Lemma lem3167599 (b : nat) (a : nat) (p : nat) : (term948 b a p) = (term952 b a p).
Proof. exact (eq_refl (term948 b a p)). Qed.
Lemma lem3167600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167601 (b : nat) (a : nat) (p : nat) : (term951 b a p) = (term953 b a p).
Proof. exact (MK_COMB (@lem3167600) (@lem3167599 b a p)). Qed.
Lemma lem3167602 (a : nat) (b : nat) : (term950 a b) = (term950 a b).
Proof. exact (eq_refl (term950 a b)). Qed.
Lemma lem3167603 (p : nat) (a : nat) (b : nat) : ((term948 b a p) = (term950 a b)) = ((term952 b a p) = (term950 a b)).
Proof. exact (MK_COMB (@lem3167601 b a p) (@lem3167602 a b)). Qed.
Lemma lem3167604 (p : nat) (a : nat) (b : nat) : ((term948 b a p) = (term949 a b)) = ((term952 b a p) = (term950 a b)).
Proof. exact (TRANS (@lem3167598 p a b) (@lem3167603 p a b)). Qed.
Lemma lem3167605 (p : nat) (a : nat) (b : nat) (h1 : p = (Nat.mul a b)) : (term952 b a p) = (term950 a b).
Proof. exact (EQ_MP (@lem3167604 p a b) (@lem3167595 p a b h1)). Qed.
Lemma lem3167606 (p : nat) (a : nat) (b : nat) (h1 : p = (Nat.mul a b)) : (term950 a b) = (term952 b a p).
Proof. exact (SYM (@lem3167605 p a b h1)). Qed.
Lemma lem3167607 : term954 = term954.
Proof. exact (eq_refl term954). Qed.
Lemma lem3167608 (p : nat) (a : nat) (b : nat) (h1 : p = (Nat.mul a b)) : (term955 p) = (term956 a b).
Proof. exact (MK_COMB (@lem3167607) (@lem3167593 p a b h1)). Qed.
Lemma lem3167609 (a : nat) (b : nat) : (term956 a b) = (term957 a b).
Proof. exact (eq_refl (term956 a b)). Qed.
Lemma lem3167610 (p : nat) : (term958 p) = (term958 p).
Proof. exact (eq_refl (term958 p)). Qed.
Lemma lem3167611 (p : nat) (a : nat) (b : nat) : ((term955 p) = (term956 a b)) = ((term955 p) = (term957 a b)).
Proof. exact (MK_COMB (@lem3167610 p) (@lem3167609 a b)). Qed.
Lemma lem3167612 (p : nat) : (term955 p) = (term26 p).
Proof. exact (eq_refl (term955 p)). Qed.
Lemma lem3167613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3167614 (p : nat) : (term958 p) = (term959 p).
Proof. exact (MK_COMB (@lem3167613) (@lem3167612 p)). Qed.
Lemma lem3167615 (a : nat) (b : nat) : (term957 a b) = (term957 a b).
Proof. exact (eq_refl (term957 a b)). Qed.
Lemma lem3167616 (p : nat) (a : nat) (b : nat) : ((term955 p) = (term957 a b)) = ((term26 p) = (term957 a b)).
Proof. exact (MK_COMB (@lem3167614 p) (@lem3167615 a b)). Qed.
Lemma lem3167617 (p : nat) (a : nat) (b : nat) : ((term955 p) = (term956 a b)) = ((term26 p) = (term957 a b)).
Proof. exact (TRANS (@lem3167611 p a b) (@lem3167616 p a b)). Qed.
Lemma lem3167618 (p : nat) (a : nat) (b : nat) (h1 : p = (Nat.mul a b)) : (term26 p) = (term957 a b).
Proof. exact (EQ_MP (@lem3167617 p a b) (@lem3167608 p a b h1)). Qed.
Lemma lem3167619 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term957 a b.
Proof. exact (EQ_MP (@lem3167618 p a b h2) (@lem3167427 p h1)). Qed.
Lemma lem3167634 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = (term844 m n).
Proof. exact (EQ_MP (@lem3167011 m n) (@lem3167010 m n)). Qed.
Lemma lem3167635 (a : nat) (b : nat) : ((Nat.mul a b) = (NUMERAL 0)) = (term844 a b).
Proof. exact (@lem3167634 a b). Qed.
Lemma lem3167642 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3167643 (a : nat) (b : nat) : (term957 a b) = (term960 a b).
Proof. exact (MK_COMB (@lem3167642) (@lem3167635 a b)). Qed.
Lemma lem3167645 (t1 : Prop) (t2 : Prop) : (term961 t1 t2) = (term962 t1 t2).
Proof. exact (proj2 (@lem3166998 t1 t2)). Qed.
Lemma lem3167646 (a : nat) (b : nat) : (term960 a b) = (term963 a b).
Proof. exact (@lem3167645 (a = (NUMERAL 0)) (b = (NUMERAL 0))). Qed.
Lemma lem3167653 (a : nat) (b : nat) : (term957 a b) = (term963 a b).
Proof. exact (TRANS (@lem3167643 a b) (@lem3167646 a b)). Qed.
Lemma lem3167654 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term963 a b.
Proof. exact (EQ_MP (@lem3167653 a b) (@lem3167619 p a b h1 h2)). Qed.
Lemma lem3167682 (n : nat) : (num_divides n n) = True.
Proof. exact (EQ_MP (@lem3166991 n) (@lem3166990 n)). Qed.
Lemma lem3167683 (a : nat) (b : nat) : (term964 a b) = True.
Proof. exact (@lem3167682 (Nat.mul a b)). Qed.
Lemma lem3167684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167685 (a : nat) (b : nat) : (term965 a b) = (imp True).
Proof. exact (MK_COMB (@lem3167684) (@lem3167683 a b)). Qed.
Lemma lem3167692 (a : nat) (b : nat) : (term966 a b) = (term966 a b).
Proof. exact (eq_refl (term966 a b)). Qed.
Lemma lem3167693 (a : nat) (b : nat) : (term967 a b) = (term968 a b).
Proof. exact (MK_COMB (@lem3167685 a b) (@lem3167692 a b)). Qed.
Lemma lem3167695 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3167696 (a : nat) (b : nat) : (term968 a b) = (term966 a b).
Proof. exact (@lem3167695 (term966 a b)). Qed.
Lemma lem3167703 (a : nat) (b : nat) : (term967 a b) = (term966 a b).
Proof. exact (TRANS (@lem3167693 a b) (@lem3167696 a b)). Qed.
Lemma lem3167704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167705 (a : nat) (b : nat) : (term969 a b) = (term970 a b).
Proof. exact (MK_COMB (@lem3167704) (@lem3167703 a b)). Qed.
Lemma lem3167712 (a : nat) (b : nat) : (term971 a b) = (term971 a b).
Proof. exact (eq_refl (term971 a b)). Qed.
Lemma lem3167713 (a : nat) (b : nat) : (term950 a b) = (term972 a b).
Proof. exact (MK_COMB (@lem3167705 a b) (@lem3167712 a b)). Qed.
Lemma lem3167716 (a : nat) (b : nat) : (term972 a b) = (term950 a b).
Proof. exact (SYM (@lem3167713 a b)). Qed.
Lemma lem3167717 (a : nat) (b : nat) (h1 : term966 a b) : term966 a b.
Proof. exact (h1). Qed.
Lemma lem3167718 (b : nat) (a : nat) (h1 : term973 b a) : term973 b a.
Proof. exact (h1). Qed.
Lemma lem3167719 (a : nat) (b : nat) (h1 : term974 a b) : term974 a b.
Proof. exact (h1). Qed.
Lemma lem3167721 (m : nat) (n : nat) : term747 m n.
Proof. exact (EQ_MP (@lem3166640 m n) (@lem3166639 m n)). Qed.
Lemma lem3167722 (b : nat) (a : nat) : term975 b a.
Proof. exact (@lem3167721 (Nat.mul a b) a). Qed.
Lemma lem3167723 (b : nat) (a : nat) (h1 : term973 b a) : term976 b a.
Proof. exact (@lem3167722 b a (@lem3167718 b a h1)). Qed.
Lemma lem3167725 (m : nat) (n : nat) : term747 m n.
Proof. exact (EQ_MP (@lem3166640 m n) (@lem3166639 m n)). Qed.
Lemma lem3167726 (a : nat) (b : nat) : term977 a b.
Proof. exact (@lem3167725 (Nat.mul a b) b). Qed.
Lemma lem3167727 (a : nat) (b : nat) (h1 : term974 a b) : term978 a b.
Proof. exact (@lem3167726 a b (@lem3167719 a b h1)). Qed.
Lemma lem3167737 (b : nat) (a : nat) : (term719 b a) = (term720 b a).
Proof. exact (EQ_MP (@lem3166634 b a) (@lem3166633 b a)). Qed.
Lemma lem3167738 (a : nat) (b : nat) : (term979 a b) = (term979 a b).
Proof. exact (eq_refl (term979 a b)). Qed.
Lemma lem3167739 (b : nat) (a : nat) : (term980 b a) = (term981 b a).
Proof. exact (MK_COMB (@lem3167738 a b) (@lem3167737 b a)). Qed.
Lemma lem3167740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167741 (b : nat) (a : nat) : (term982 b a) = (term983 b a).
Proof. exact (MK_COMB (@lem3167740) (@lem3167739 b a)). Qed.
Lemma lem3167744 (a : nat) : (a = (NUMERAL 0)) = (a = (NUMERAL 0)).
Proof. exact (eq_refl (a = (NUMERAL 0))). Qed.
Lemma lem3167745 (b : nat) (a : nat) : (term976 b a) = (term984 b a).
Proof. exact (MK_COMB (@lem3167741 b a) (@lem3167744 a)). Qed.
Lemma lem3167746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167747 (b : nat) (a : nat) : (term985 b a) = (term986 b a).
Proof. exact (MK_COMB (@lem3167746) (@lem3167745 b a)). Qed.
Lemma lem3167754 (a : nat) (b : nat) : (term971 a b) = (term971 a b).
Proof. exact (eq_refl (term971 a b)). Qed.
Lemma lem3167755 (a : nat) (b : nat) : (term987 a b) = (term988 a b).
Proof. exact (MK_COMB (@lem3167747 b a) (@lem3167754 a b)). Qed.
Lemma lem3167756 (a : nat) (b : nat) : (term988 a b) = (term987 a b).
Proof. exact (SYM (@lem3167755 a b)). Qed.
Lemma lem3167764 (a : nat) (b : nat) : (term623 a b) = (term624 a b).
Proof. exact (EQ_MP (@lem3165608 a b) (@lem3165607 a b)). Qed.
Lemma lem3167765 (a : nat) (b : nat) : (term979 a b) = (term979 a b).
Proof. exact (eq_refl (term979 a b)). Qed.
Lemma lem3167766 (a : nat) (b : nat) : (term989 a b) = (term990 a b).
Proof. exact (MK_COMB (@lem3167765 a b) (@lem3167764 a b)). Qed.
Lemma lem3167767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167768 (a : nat) (b : nat) : (term991 a b) = (term992 a b).
Proof. exact (MK_COMB (@lem3167767) (@lem3167766 a b)). Qed.
Lemma lem3167771 (b : nat) : (b = (NUMERAL 0)) = (b = (NUMERAL 0)).
Proof. exact (eq_refl (b = (NUMERAL 0))). Qed.
Lemma lem3167772 (a : nat) (b : nat) : (term978 a b) = (term993 a b).
Proof. exact (MK_COMB (@lem3167768 a b) (@lem3167771 b)). Qed.
Lemma lem3167773 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167774 (a : nat) (b : nat) : (term994 a b) = (term995 a b).
Proof. exact (MK_COMB (@lem3167773) (@lem3167772 a b)). Qed.
Lemma lem3167781 (a : nat) (b : nat) : (term971 a b) = (term971 a b).
Proof. exact (eq_refl (term971 a b)). Qed.
Lemma lem3167782 (a : nat) (b : nat) : (term996 a b) = (term997 a b).
Proof. exact (MK_COMB (@lem3167774 a b) (@lem3167781 a b)). Qed.
Lemma lem3167783 (a : nat) (b : nat) : (term997 a b) = (term996 a b).
Proof. exact (SYM (@lem3167782 a b)). Qed.
Lemma lem3167793 (m : nat) (n : nat) (p : nat) : (term621 n m p) = (term622 m n p).
Proof. exact (EQ_MP (@lem3164582 m n p) (@lem3164581 m n p)). Qed.
Lemma lem3167794 (a : nat) (b : nat) : (term720 b a) = (term998 a b).
Proof. exact (@lem3167793 a b term2). Qed.
Lemma lem3167799 (a : nat) (b : nat) : (term979 a b) = (term979 a b).
Proof. exact (eq_refl (term979 a b)). Qed.
Lemma lem3167800 (a : nat) (b : nat) : (term981 b a) = (term999 a b).
Proof. exact (MK_COMB (@lem3167799 a b) (@lem3167794 a b)). Qed.
Lemma lem3167803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167804 (a : nat) (b : nat) : (term983 b a) = (term1000 a b).
Proof. exact (MK_COMB (@lem3167803) (@lem3167800 a b)). Qed.
Lemma lem3167807 (a : nat) : (a = (NUMERAL 0)) = (a = (NUMERAL 0)).
Proof. exact (eq_refl (a = (NUMERAL 0))). Qed.
Lemma lem3167808 (b : nat) (a : nat) : (term984 b a) = (term1001 b a).
Proof. exact (MK_COMB (@lem3167804 a b) (@lem3167807 a)). Qed.
Lemma lem3167811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167812 (b : nat) (a : nat) : (term986 b a) = (term1002 b a).
Proof. exact (MK_COMB (@lem3167811) (@lem3167808 b a)). Qed.
Lemma lem3167819 (a : nat) (b : nat) : (term971 a b) = (term971 a b).
Proof. exact (eq_refl (term971 a b)). Qed.
Lemma lem3167820 (a : nat) (b : nat) : (term988 a b) = (term1003 a b).
Proof. exact (MK_COMB (@lem3167812 b a) (@lem3167819 a b)). Qed.
Lemma lem3167823 (a : nat) (b : nat) : (term1003 a b) = (term988 a b).
Proof. exact (SYM (@lem3167820 a b)). Qed.
Lemma lem3167831 (m : nat) (n : nat) (p : nat) : (term614 m n p) = (term615 m n p).
Proof. exact (EQ_MP (@lem3164573 m n p) (@lem3164572 m n p)). Qed.
Lemma lem3167832 (a : nat) (b : nat) : (term624 a b) = (term1004 a b).
Proof. exact (@lem3167831 a term2 b). Qed.
Lemma lem3167837 (a : nat) (b : nat) : (term979 a b) = (term979 a b).
Proof. exact (eq_refl (term979 a b)). Qed.
Lemma lem3167838 (a : nat) (b : nat) : (term990 a b) = (term1005 a b).
Proof. exact (MK_COMB (@lem3167837 a b) (@lem3167832 a b)). Qed.
Lemma lem3167841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167842 (a : nat) (b : nat) : (term992 a b) = (term1006 a b).
Proof. exact (MK_COMB (@lem3167841) (@lem3167838 a b)). Qed.
Lemma lem3167845 (b : nat) : (b = (NUMERAL 0)) = (b = (NUMERAL 0)).
Proof. exact (eq_refl (b = (NUMERAL 0))). Qed.
Lemma lem3167846 (a : nat) (b : nat) : (term993 a b) = (term1007 a b).
Proof. exact (MK_COMB (@lem3167842 a b) (@lem3167845 b)). Qed.
Lemma lem3167849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3167850 (a : nat) (b : nat) : (term995 a b) = (term1008 a b).
Proof. exact (MK_COMB (@lem3167849) (@lem3167846 a b)). Qed.
Lemma lem3167857 (a : nat) (b : nat) : (term971 a b) = (term971 a b).
Proof. exact (eq_refl (term971 a b)). Qed.
Lemma lem3167858 (a : nat) (b : nat) : (term997 a b) = (term1009 a b).
Proof. exact (MK_COMB (@lem3167850 a b) (@lem3167857 a b)). Qed.
Lemma lem3167861 (a : nat) (b : nat) : (term1009 a b) = (term997 a b).
Proof. exact (SYM (@lem3167858 a b)). Qed.
Lemma lem3167862 : term1010.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem3167863 : term1011.
Proof. exact (proj2 (@lem3167862)). Qed.
Lemma lem3167864 : term1012.
Proof. exact (proj2 (@lem3167863)). Qed.
Lemma lem3167880 : term1013.
Proof. exact (proj1 (@lem3167864)). Qed.
Lemma lem3167881 (m : nat) : term1014 m.
Proof. exact (@lem3167880 m). Qed.
Lemma lem3167882 (m : nat) : (term1014 m) = ((term722 m) = m).
Proof. exact (eq_refl (term1014 m)). Qed.
Lemma lem3167896 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term26 b.
Proof. exact (proj2 (@lem3167654 p a b h1 h2)). Qed.
Lemma lem3167897 (b : nat) : term1015 b.
Proof. exact (@lem82 (b = (NUMERAL 0))). Qed.
Lemma lem3167910 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term26 a.
Proof. exact (proj1 (@lem3167654 p a b h1 h2)). Qed.
Lemma lem3167911 (a : nat) : term1015 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem3167929 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term869 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3167930 (p : Prop) (q : Prop) (p' : Prop) : term870 p q p'.
Proof. exact (fun q' : Prop => @lem3167929 p q p' q'). Qed.
Lemma lem3167931 (p : Prop) (q : Prop) : term871 p q.
Proof. exact (fun p' : Prop => @lem3167930 p q p'). Qed.
Lemma lem3167932 (a : nat) (b : nat) : term1016 a b.
Proof. exact (@lem3167931 (term1001 b a) (term971 a b)). Qed.
Lemma lem3167933 (a : nat) (b : nat) (p' : Prop) : term1017 a b p'.
Proof. exact (@lem3167932 a b p'). Qed.
Lemma lem3167934 (a : nat) (b : nat) (p' : Prop) : (term1017 a b p') = (term1018 a b p').
Proof. exact (eq_refl (term1017 a b p')). Qed.
Lemma lem3167935 (a : nat) (b : nat) (p' : Prop) : term1018 a b p'.
Proof. exact (EQ_MP (@lem3167934 a b p') (@lem3167933 a b p')). Qed.
Lemma lem3167936 (a : nat) (b : nat) (p' : Prop) (q' : Prop) : term1019 a b p' q'.
Proof. exact (@lem3167935 a b p' q'). Qed.
Lemma lem3167937 (a : nat) (b : nat) (p' : Prop) (q' : Prop) : (term1019 a b p' q') = (term1020 a b p' q').
Proof. exact (eq_refl (term1019 a b p' q')). Qed.
Lemma lem3167938 (a : nat) (b : nat) (p' : Prop) (q' : Prop) : term1020 a b p' q'.
Proof. exact (EQ_MP (@lem3167937 a b p' q') (@lem3167936 a b p' q')). Qed.
Lemma lem3167946 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem3167911 a (@lem3167910 p a b h1 h2)). Qed.
Lemma lem3167947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167948 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term16 a) = (or False).
Proof. exact (MK_COMB (@lem3167947) (@lem3167946 p a b h1 h2)). Qed.
Lemma lem3167950 (n : nat) : (term9 n) = (term10 n).
Proof. exact (EQ_MP (@lem3164564 n) (@lem3164563 n)). Qed.
Lemma lem3167951 (b : nat) : (term9 b) = (term10 b).
Proof. exact (@lem3167950 b). Qed.
Lemma lem3167955 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (b = (NUMERAL 0)) = False.
Proof. exact (@lem3167897 b (@lem3167896 p a b h1 h2)). Qed.
Lemma lem3167956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167957 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term16 b) = (or False).
Proof. exact (MK_COMB (@lem3167956) (@lem3167955 p a b h1 h2)). Qed.
Lemma lem3167960 (b : nat) : (b = term2) = (b = term2).
Proof. exact (eq_refl (b = term2)). Qed.
Lemma lem3167961 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term10 b) = (term1021 b).
Proof. exact (MK_COMB (@lem3167957 p a b h1 h2) (@lem3167960 b)). Qed.
Lemma lem3167963 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3167964 (b : nat) : (term1021 b) = (b = term2).
Proof. exact (@lem3167963 (b = term2)). Qed.
Lemma lem3167967 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term10 b) = (b = term2).
Proof. exact (TRANS (@lem3167961 p a b h1 h2) (@lem3167964 b)). Qed.
Lemma lem3167968 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term9 b) = (b = term2).
Proof. exact (TRANS (@lem3167951 b) (@lem3167967 p a b h1 h2)). Qed.
Lemma lem3167969 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term998 a b) = (term1021 b).
Proof. exact (MK_COMB (@lem3167948 p a b h1 h2) (@lem3167968 p a b h1 h2)). Qed.
Lemma lem3167971 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3167972 (b : nat) : (term1021 b) = (b = term2).
Proof. exact (@lem3167971 (b = term2)). Qed.
Lemma lem3167975 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term998 a b) = (b = term2).
Proof. exact (TRANS (@lem3167969 p a b h1 h2) (@lem3167972 b)). Qed.
Lemma lem3167976 (a : nat) (b : nat) : (term979 a b) = (term979 a b).
Proof. exact (eq_refl (term979 a b)). Qed.
Lemma lem3167977 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term999 a b) = (term1022 a b).
Proof. exact (MK_COMB (@lem3167976 a b) (@lem3167975 p a b h1 h2)). Qed.
Lemma lem3167982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3167983 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1000 a b) = (term1023 a b).
Proof. exact (MK_COMB (@lem3167982) (@lem3167977 p a b h1 h2)). Qed.
Lemma lem3167989 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem3167911 a (@lem3167910 p a b h1 h2)). Qed.
Lemma lem3167990 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1001 b a) = (term1024 a b).
Proof. exact (MK_COMB (@lem3167983 p a b h1 h2) (@lem3167989 p a b h1 h2)). Qed.
Lemma lem3167992 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3167993 (a : nat) (b : nat) : (term1024 a b) = (term1022 a b).
Proof. exact (@lem3167992 (term1022 a b)). Qed.
Lemma lem3167998 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1001 b a) = (term1022 a b).
Proof. exact (TRANS (@lem3167990 p a b h1 h2) (@lem3167993 a b)). Qed.
Lemma lem3167999 (a : nat) (b : nat) (q' : Prop) : term1025 a b q'.
Proof. exact (@lem3167938 a b (term1022 a b) q'). Qed.
Lemma lem3168000 (q' : Prop) (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term1026 a b q'.
Proof. exact (@lem3167999 a b q' (@lem3167998 p a b h1 h2)). Qed.
Lemma lem3168001 (a : nat) (b : nat) (h1 : term1022 a b) : term1022 a b.
Proof. exact (h1). Qed.
Lemma lem3168013 (a : nat) (b : nat) (h1 : term1022 a b) : b = term2.
Proof. exact (proj2 (@lem3168001 a b h1)). Qed.
Lemma lem3168014 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem3168015 (a : nat) (b : nat) (h1 : term1022 a b) : (Nat.mul a b) = (term722 a).
Proof. exact (MK_COMB (@lem3168014 a) (@lem3168013 a b h1)). Qed.
Lemma lem3168017 (m : nat) : (term722 m) = m.
Proof. exact (EQ_MP (@lem3167882 m) (@lem3167881 m)). Qed.
Lemma lem3168018 (a : nat) : (term722 a) = a.
Proof. exact (@lem3168017 a). Qed.
Lemma lem3168019 (a : nat) (b : nat) (h1 : term1022 a b) : (Nat.mul a b) = a.
Proof. exact (TRANS (@lem3168015 a b h1) (@lem3168018 a)). Qed.
Lemma lem3168020 (a : nat) : (@eq nat a) = (@eq nat a).
Proof. exact (eq_refl (@eq nat a)). Qed.
Lemma lem3168021 (a : nat) (b : nat) (h1 : term1022 a b) : (a = (Nat.mul a b)) = (a = a).
Proof. exact (MK_COMB (@lem3168020 a) (@lem3168019 a b h1)). Qed.
Lemma lem3168023 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3168024 (x : nat) : (x = x) = True.
Proof. exact (@lem3168023 nat x). Qed.
Lemma lem3168025 (a : nat) : (a = a) = True.
Proof. exact (@lem3168024 a). Qed.
Lemma lem3168026 (a : nat) (b : nat) (h1 : term1022 a b) : (a = (Nat.mul a b)) = True.
Proof. exact (TRANS (@lem3168021 a b h1) (@lem3168025 a)). Qed.
Lemma lem3168027 (a : nat) : (term1027 a) = (term1027 a).
Proof. exact (eq_refl (term1027 a)). Qed.
Lemma lem3168028 (a : nat) (b : nat) (h1 : term1022 a b) : (term971 a b) = (term1028 a).
Proof. exact (MK_COMB (@lem3168027 a) (@lem3168026 a b h1)). Qed.
Lemma lem3168030 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem3168031 (a : nat) : (term1028 a) = True.
Proof. exact (@lem3168030 (a = term2)). Qed.
Lemma lem3168032 (a : nat) (b : nat) (h1 : term1022 a b) : (term971 a b) = True.
Proof. exact (TRANS (@lem3168028 a b h1) (@lem3168031 a)). Qed.
Lemma lem3168033 (a : nat) (b : nat) : term1029 a b.
Proof. exact (fun h0 : term1022 a b => @lem3168032 a b h0). Qed.
Lemma lem3168034 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term1030 a b.
Proof. exact (@lem3168000 True p a b h1 h2). Qed.
Lemma lem3168035 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1003 a b) = (term1031 a b).
Proof. exact (@lem3168034 p a b h1 h2 (@lem3168033 a b)). Qed.
Lemma lem3168037 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3168038 (a : nat) (b : nat) : (term1031 a b) = True.
Proof. exact (@lem3168037 (term1022 a b)). Qed.
Lemma lem3168039 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1003 a b) = True.
Proof. exact (TRANS (@lem3168035 p a b h1 h2) (@lem3168038 a b)). Qed.
Lemma lem3168040 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : True = (term1003 a b).
Proof. exact (SYM (@lem3168039 p a b h1 h2)). Qed.
Lemma lem3168041 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term1003 a b.
Proof. exact (EQ_MP (@lem3168040 p a b h1 h2) (@lem0)). Qed.
Lemma lem3168042 : term1010.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem3168043 : term1011.
Proof. exact (proj2 (@lem3168042)). Qed.
Lemma lem3168064 : term1032.
Proof. exact (proj1 (@lem3168043)). Qed.
Lemma lem3168065 (n : nat) : term1033 n.
Proof. exact (@lem3168064 n). Qed.
Lemma lem3168066 (n : nat) : (term1033 n) = ((term626 n) = n).
Proof. exact (eq_refl (term1033 n)). Qed.
Lemma lem3168076 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term26 b.
Proof. exact (proj2 (@lem3167654 p a b h1 h2)). Qed.
Lemma lem3168077 (b : nat) : term1015 b.
Proof. exact (@lem82 (b = (NUMERAL 0))). Qed.
Lemma lem3168090 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term26 a.
Proof. exact (proj1 (@lem3167654 p a b h1 h2)). Qed.
Lemma lem3168091 (a : nat) : term1015 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem3168109 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term869 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3168110 (p : Prop) (q : Prop) (p' : Prop) : term870 p q p'.
Proof. exact (fun q' : Prop => @lem3168109 p q p' q'). Qed.
Lemma lem3168111 (p : Prop) (q : Prop) : term871 p q.
Proof. exact (fun p' : Prop => @lem3168110 p q p'). Qed.
Lemma lem3168112 (a : nat) (b : nat) : term1034 a b.
Proof. exact (@lem3168111 (term1007 a b) (term971 a b)). Qed.
Lemma lem3168113 (a : nat) (b : nat) (p' : Prop) : term1035 a b p'.
Proof. exact (@lem3168112 a b p'). Qed.
Lemma lem3168114 (a : nat) (b : nat) (p' : Prop) : (term1035 a b p') = (term1036 a b p').
Proof. exact (eq_refl (term1035 a b p')). Qed.
Lemma lem3168115 (a : nat) (b : nat) (p' : Prop) : term1036 a b p'.
Proof. exact (EQ_MP (@lem3168114 a b p') (@lem3168113 a b p')). Qed.
Lemma lem3168116 (a : nat) (b : nat) (p' : Prop) (q' : Prop) : term1037 a b p' q'.
Proof. exact (@lem3168115 a b p' q'). Qed.
Lemma lem3168117 (a : nat) (b : nat) (p' : Prop) (q' : Prop) : (term1037 a b p' q') = (term1038 a b p' q').
Proof. exact (eq_refl (term1037 a b p' q')). Qed.
Lemma lem3168118 (a : nat) (b : nat) (p' : Prop) (q' : Prop) : term1038 a b p' q'.
Proof. exact (EQ_MP (@lem3168117 a b p' q') (@lem3168116 a b p' q')). Qed.
Lemma lem3168126 (n : nat) : (term9 n) = (term10 n).
Proof. exact (EQ_MP (@lem3164564 n) (@lem3164563 n)). Qed.
Lemma lem3168127 (a : nat) : (term9 a) = (term10 a).
Proof. exact (@lem3168126 a). Qed.
Lemma lem3168131 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem3168091 a (@lem3168090 p a b h1 h2)). Qed.
Lemma lem3168132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3168133 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term16 a) = (or False).
Proof. exact (MK_COMB (@lem3168132) (@lem3168131 p a b h1 h2)). Qed.
Lemma lem3168136 (a : nat) : (a = term2) = (a = term2).
Proof. exact (eq_refl (a = term2)). Qed.
Lemma lem3168137 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term10 a) = (term1021 a).
Proof. exact (MK_COMB (@lem3168133 p a b h1 h2) (@lem3168136 a)). Qed.
Lemma lem3168139 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3168140 (a : nat) : (term1021 a) = (a = term2).
Proof. exact (@lem3168139 (a = term2)). Qed.
Lemma lem3168143 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term10 a) = (a = term2).
Proof. exact (TRANS (@lem3168137 p a b h1 h2) (@lem3168140 a)). Qed.
Lemma lem3168144 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term9 a) = (a = term2).
Proof. exact (TRANS (@lem3168127 a) (@lem3168143 p a b h1 h2)). Qed.
Lemma lem3168145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3168146 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1039 a) = (term1027 a).
Proof. exact (MK_COMB (@lem3168145) (@lem3168144 p a b h1 h2)). Qed.
Lemma lem3168150 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (b = (NUMERAL 0)) = False.
Proof. exact (@lem3168077 b (@lem3168076 p a b h1 h2)). Qed.
Lemma lem3168151 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1004 a b) = (term1040 a).
Proof. exact (MK_COMB (@lem3168146 p a b h1 h2) (@lem3168150 p a b h1 h2)). Qed.
Lemma lem3168153 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3168154 (a : nat) : (term1040 a) = (a = term2).
Proof. exact (@lem3168153 (a = term2)). Qed.
Lemma lem3168157 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1004 a b) = (a = term2).
Proof. exact (TRANS (@lem3168151 p a b h1 h2) (@lem3168154 a)). Qed.
Lemma lem3168158 (a : nat) (b : nat) : (term979 a b) = (term979 a b).
Proof. exact (eq_refl (term979 a b)). Qed.
Lemma lem3168159 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1005 a b) = (term1041 b a).
Proof. exact (MK_COMB (@lem3168158 a b) (@lem3168157 p a b h1 h2)). Qed.
Lemma lem3168164 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3168165 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1006 a b) = (term1042 b a).
Proof. exact (MK_COMB (@lem3168164) (@lem3168159 p a b h1 h2)). Qed.
Lemma lem3168171 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (b = (NUMERAL 0)) = False.
Proof. exact (@lem3168077 b (@lem3168076 p a b h1 h2)). Qed.
Lemma lem3168172 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1007 a b) = (term1043 b a).
Proof. exact (MK_COMB (@lem3168165 p a b h1 h2) (@lem3168171 p a b h1 h2)). Qed.
Lemma lem3168174 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3168175 (b : nat) (a : nat) : (term1043 b a) = (term1041 b a).
Proof. exact (@lem3168174 (term1041 b a)). Qed.
Lemma lem3168180 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1007 a b) = (term1041 b a).
Proof. exact (TRANS (@lem3168172 p a b h1 h2) (@lem3168175 b a)). Qed.
Lemma lem3168181 (b : nat) (a : nat) (q' : Prop) : term1044 b a q'.
Proof. exact (@lem3168118 a b (term1041 b a) q'). Qed.
Lemma lem3168182 (q' : Prop) (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term1045 b a q'.
Proof. exact (@lem3168181 b a q' (@lem3168180 p a b h1 h2)). Qed.
Lemma lem3168183 (b : nat) (a : nat) (h1 : term1041 b a) : term1041 b a.
Proof. exact (h1). Qed.
Lemma lem3168193 (b : nat) (a : nat) (h1 : term1041 b a) : a = term2.
Proof. exact (proj2 (@lem3168183 b a h1)). Qed.
Lemma lem3168194 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3168195 (b : nat) (a : nat) (h1 : term1041 b a) : (@eq nat a) = term1046.
Proof. exact (MK_COMB (@lem3168194) (@lem3168193 b a h1)). Qed.
Lemma lem3168196 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem3168197 (b : nat) (a : nat) (h1 : term1041 b a) : (a = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem3168195 b a h1) (@lem3168196)). Qed.
Lemma lem3168199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3168200 (x : nat) : (x = x) = True.
Proof. exact (@lem3168199 nat x). Qed.
Lemma lem3168201 : (term2 = term2) = True.
Proof. exact (@lem3168200 term2). Qed.
Lemma lem3168202 (b : nat) (a : nat) (h1 : term1041 b a) : (a = term2) = True.
Proof. exact (TRANS (@lem3168197 b a h1) (@lem3168201)). Qed.
Lemma lem3168203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3168204 (b : nat) (a : nat) (h1 : term1041 b a) : (term1027 a) = (or True).
Proof. exact (MK_COMB (@lem3168203) (@lem3168202 b a h1)). Qed.
Lemma lem3168208 (b : nat) (a : nat) (h1 : term1041 b a) : a = term2.
Proof. exact (proj2 (@lem3168183 b a h1)). Qed.
Lemma lem3168209 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3168210 (b : nat) (a : nat) (h1 : term1041 b a) : (@eq nat a) = term1046.
Proof. exact (MK_COMB (@lem3168209) (@lem3168208 b a h1)). Qed.
Lemma lem3168212 (b : nat) (a : nat) (h1 : term1041 b a) : a = term2.
Proof. exact (proj2 (@lem3168183 b a h1)). Qed.
Lemma lem3168213 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem3168214 (b : nat) (a : nat) (h1 : term1041 b a) : (Nat.mul a) = term1047.
Proof. exact (MK_COMB (@lem3168213) (@lem3168212 b a h1)). Qed.
Lemma lem3168215 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem3168216 (b : nat) (a : nat) (h1 : term1041 b a) : (Nat.mul a b) = (term626 b).
Proof. exact (MK_COMB (@lem3168214 b a h1) (@lem3168215 b)). Qed.
Lemma lem3168218 (n : nat) : (term626 n) = n.
Proof. exact (EQ_MP (@lem3168066 n) (@lem3168065 n)). Qed.
Lemma lem3168219 (b : nat) : (term626 b) = b.
Proof. exact (@lem3168218 b). Qed.
Lemma lem3168220 (b : nat) (a : nat) (h1 : term1041 b a) : (Nat.mul a b) = b.
Proof. exact (TRANS (@lem3168216 b a h1) (@lem3168219 b)). Qed.
Lemma lem3168221 (b : nat) (a : nat) (h1 : term1041 b a) : (a = (Nat.mul a b)) = (term2 = b).
Proof. exact (MK_COMB (@lem3168210 b a h1) (@lem3168220 b a h1)). Qed.
Lemma lem3168224 (b : nat) (a : nat) (h1 : term1041 b a) : (term971 a b) = (term1048 b).
Proof. exact (MK_COMB (@lem3168204 b a h1) (@lem3168221 b a h1)). Qed.
Lemma lem3168226 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3168227 (b : nat) : (term1048 b) = True.
Proof. exact (@lem3168226 (term2 = b)). Qed.
Lemma lem3168228 (b : nat) (a : nat) (h1 : term1041 b a) : (term971 a b) = True.
Proof. exact (TRANS (@lem3168224 b a h1) (@lem3168227 b)). Qed.
Lemma lem3168229 (a : nat) (b : nat) : term1049 a b.
Proof. exact (fun h0 : term1041 b a => @lem3168228 b a h0). Qed.
Lemma lem3168230 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term1050 b a.
Proof. exact (@lem3168182 True p a b h1 h2). Qed.
Lemma lem3168231 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1009 a b) = (term1051 b a).
Proof. exact (@lem3168230 p a b h1 h2 (@lem3168229 a b)). Qed.
Lemma lem3168233 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3168234 (b : nat) (a : nat) : (term1051 b a) = True.
Proof. exact (@lem3168233 (term1041 b a)). Qed.
Lemma lem3168235 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : (term1009 a b) = True.
Proof. exact (TRANS (@lem3168231 p a b h1 h2) (@lem3168234 b a)). Qed.
Lemma lem3168236 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : True = (term1009 a b).
Proof. exact (SYM (@lem3168235 p a b h1 h2)). Qed.
Lemma lem3168237 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term1009 a b.
Proof. exact (EQ_MP (@lem3168236 p a b h1 h2) (@lem0)). Qed.
Lemma lem3168238 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term997 a b.
Proof. exact (EQ_MP (@lem3167861 a b) (@lem3168237 p a b h1 h2)). Qed.
Lemma lem3168239 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term988 a b.
Proof. exact (EQ_MP (@lem3167823 a b) (@lem3168041 p a b h1 h2)). Qed.
Lemma lem3168240 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term996 a b.
Proof. exact (EQ_MP (@lem3167783 a b) (@lem3168238 p a b h1 h2)). Qed.
Lemma lem3168241 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term987 a b.
Proof. exact (EQ_MP (@lem3167756 a b) (@lem3168239 p a b h1 h2)). Qed.
Lemma lem3168242 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term974 a b) : term971 a b.
Proof. exact (@lem3168240 p a b h1 h2 (@lem3167727 a b h3)). Qed.
Lemma lem3168243 (p : nat) (b : nat) (a : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term973 b a) : term971 a b.
Proof. exact (@lem3168241 p a b h1 h2 (@lem3167723 b a h3)). Qed.
Lemma lem3168244 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term974 a b) : (term974 a b) = (term971 a b).
Proof. exact (prop_ext (fun h4 : term974 a b => @lem3168242 p a b h1 h2 h3) (fun h4 : term971 a b => @lem3167719 a b h3)). Qed.
Lemma lem3168245 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term974 a b) : term971 a b.
Proof. exact (EQ_MP (@lem3168244 p a b h1 h2 h3) (@lem3167719 a b h3)). Qed.
Lemma lem3168246 (p : nat) (b : nat) (a : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term973 b a) : (term973 b a) = (term971 a b).
Proof. exact (prop_ext (fun h4 : term973 b a => @lem3168243 p b a h1 h2 h3) (fun h4 : term971 a b => @lem3167718 b a h3)). Qed.
Lemma lem3168247 (p : nat) (b : nat) (a : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term973 b a) : term971 a b.
Proof. exact (EQ_MP (@lem3168246 p b a h1 h2 h3) (@lem3167718 b a h3)). Qed.
Lemma lem3168248 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) (h3 : term966 a b) : term971 a b.
Proof. exact (or_elim (@lem3167717 a b h3) (fun h0 : term973 b a => @lem3168247 p b a h1 h2 h0) (fun h0 : term974 a b => @lem3168245 p a b h1 h2 h0)). Qed.
Lemma lem3168249 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term972 a b.
Proof. exact (fun h0 : term966 a b => @lem3168248 p a b h1 h2 h0). Qed.
Lemma lem3168250 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term950 a b.
Proof. exact (EQ_MP (@lem3167716 a b) (@lem3168249 p a b h1 h2)). Qed.
Lemma lem3168251 (p : nat) (a : nat) (b : nat) (h1 : term26 p) (h2 : p = (Nat.mul a b)) : term952 b a p.
Proof. exact (EQ_MP (@lem3167606 p a b h2) (@lem3168250 p a b h1 h2)). Qed.
Lemma lem3168252 (p : nat) (a : nat) (b : nat) (h1 : term873 p) (h2 : term26 p) (h3 : p = (Nat.mul a b)) : term919 a p.
Proof. exact (@lem3168251 p a b h2 h3 (@lem3167592 a b p h1)). Qed.
Lemma lem3168253 (b : nat) (a : nat) (p : nat) (h1 : term873 p) (h2 : term26 p) : term936 b a p.
Proof. exact (fun h0 : p = (Nat.mul a b) => @lem3168252 p a b h1 h2 h0). Qed.
Lemma lem3168258 (a : nat) (p : nat) (h1 : term873 p) (h2 : term26 p) : term939 a p.
Proof. exact (fun b : nat => @lem3168253 b a p h1 h2). Qed.
Lemma lem3168263 (p : nat) (h1 : term873 p) (h2 : term26 p) : term943 p.
Proof. exact (fun a : nat => @lem3168258 a p h1 h2). Qed.
Lemma lem3168264 (p : nat) (h1 : term873 p) (h2 : term26 p) (h3 : term30 p) : prime p.
Proof. exact (EQ_MP (@lem3167584 p h3) (@lem3168263 p h1 h2)). Qed.
Lemma lem3168265 (p : nat) (h1 : term873 p) (h2 : term26 p) (h3 : term30 p) : (term30 p) = (prime p).
Proof. exact (prop_ext (fun h4 : term30 p => @lem3168264 p h1 h2 h3) (fun h4 : prime p => @lem3167428 p h3)). Qed.
Lemma lem3168266 (p : nat) (h1 : term873 p) (h2 : term26 p) (h3 : term30 p) : prime p.
Proof. exact (EQ_MP (@lem3168265 p h1 h2 h3) (@lem3167428 p h3)). Qed.
Lemma lem3168267 (p : nat) (h1 : term873 p) (h2 : term26 p) : term904 p.
Proof. exact (fun h0 : term30 p => @lem3168266 p h1 h2 h0). Qed.
Lemma lem3168268 (p : nat) (h1 : term873 p) (h2 : term26 p) : (term26 p) = (term904 p).
Proof. exact (prop_ext (fun h3 : term26 p => @lem3168267 p h1 h2) (fun h3 : term904 p => @lem3167427 p h2)). Qed.
Lemma lem3168269 (p : nat) (h1 : term873 p) (h2 : term26 p) : term904 p.
Proof. exact (EQ_MP (@lem3168268 p h1 h2) (@lem3167427 p h2)). Qed.
Lemma lem3168270 (p : nat) (h1 : term873 p) : term906 p.
Proof. exact (fun h0 : term26 p => @lem3168269 p h1 h0). Qed.
Lemma lem3168271 (p : nat) (h1 : term873 p) : term866 p.
Proof. exact (EQ_MP (@lem3167426 p) (@lem3168270 p h1)). Qed.
Lemma lem3168273 (p : nat) : term1052 p.
Proof. exact (fun h0 : term873 p => @lem3168271 p h0). Qed.
Lemma lem3168274 (p : nat) : term1053 p.
Proof. exact (conj (@lem3167229 p) (@lem3168273 p)). Qed.
Lemma lem3168275 (p : nat) : (term1053 p) = ((term866 p) = (term873 p)).
Proof. exact (@lem32 (term866 p) (term873 p)). Qed.
Lemma lem3168276 (p : nat) : (term866 p) = (term873 p).
Proof. exact (EQ_MP (@lem3168275 p) (@lem3168274 p)). Qed.
Lemma lem3168281 : term1054.
Proof. exact (fun p : nat => @lem3168276 p). Qed.
