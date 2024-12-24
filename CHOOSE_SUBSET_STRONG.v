Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CHOOSE_SUBSET_STRONG_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import CARD_DELETE_spec.
Require Import DISJ_ACI_spec.
Require Import EMPTY_SUBSET_spec.
Require Import FINITE_DELETE_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_INSERT_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import HAS_SIZE_SUC_spec.
Require Import INT_POS_spec.
Require Import LE_SUC_spec.
Require Import SET_PROVE_CASES_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982759_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem4075308 (n : nat) : term0 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem4075309 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem4075311 {_100044 : Type'} (s : _100044 -> Prop) : term2 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4075312 {_100044 : Type'} (s : _100044 -> Prop) : (term2 _100044 s) = (term3 _100044 s).
Proof. exact (eq_refl (term2 _100044 s)). Qed.
Lemma lem4075313 {_100044 : Type'} (s : _100044 -> Prop) : term3 _100044 s.
Proof. exact (EQ_MP (@lem4075312 _100044 s) (@lem4075311 _100044 s)). Qed.
Lemma lem4075314 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term4 _100044 s n.
Proof. exact (@lem4075313 _100044 s n). Qed.
Lemma lem4075315 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term4 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term5 _100044 s n)).
Proof. exact (eq_refl (term4 _100044 s n)). Qed.
Lemma lem4075331 (m : nat) : (S m) = (term6 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4075332 (n : nat) : (S n) = (term6 n).
Proof. exact (@lem4075331 n). Qed.
Lemma lem4075333 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4075334 (n : nat) : (term7 n) = (term8 n).
Proof. exact (MK_COMB (@lem4075333) (@lem4075332 n)). Qed.
Lemma lem4075335 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem4075336 (n : nat) : (term9 n) = (term10 n).
Proof. exact (MK_COMB (@lem4075334 n) (@lem4075335)). Qed.
Lemma lem4075337 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075355 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem4075337) (@lem4075336 n)). Qed.
Lemma lem4075357 (m : nat) (n : nat) : (Peano.le m n) = (term13 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4075358 (n : nat) : (term10 n) = (term14 n).
Proof. exact (@lem4075357 (term6 n) (NUMERAL 0)). Qed.
Lemma lem4075360 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4075361 (n : nat) : (term17 n) = (term18 n).
Proof. exact (@lem4075360 n term19). Qed.
Lemma lem4075362 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem4075363 (n : nat) : (term20 n) = (term21 n).
Proof. exact (MK_COMB (@lem4075362) (@lem4075361 n)). Qed.
Lemma lem4075364 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem4075365 (n : nat) : (term14 n) = (term23 n).
Proof. exact (MK_COMB (@lem4075363 n) (@lem4075364)). Qed.
Lemma lem4075366 (n : nat) : (term10 n) = (term23 n).
Proof. exact (TRANS (@lem4075358 n) (@lem4075365 n)). Qed.
Lemma lem4075367 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075368 (n : nat) : (term12 n) = (term24 n).
Proof. exact (MK_COMB (@lem4075367) (@lem4075366 n)). Qed.
Lemma lem4075369 (n : nat) : (term11 n) = (term24 n).
Proof. exact (TRANS (@lem4075355 n) (@lem4075368 n)). Qed.
Lemma lem4075370 (n : nat) : term25 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem4075371 (n : nat) : (term25 n) = (term26 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem4075372 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem4075371 n) (@lem4075370 n)). Qed.
Lemma lem4075373 (_47867 : int) : (term27 _47867) = (term28 _47867).
Proof. exact (@lem2318604 (term28 _47867)). Qed.
Lemma lem4075384 (_47867 : int) : (term29 _47867) = (term30 _47867).
Proof. exact (@lem16933 (term30 _47867)). Qed.
Lemma lem4075386 (_47867 : int) : (term31 _47867) = (term31 _47867).
Proof. exact (eq_refl (term31 _47867)). Qed.
Lemma lem4075387 (_47867 : int) : (term32 _47867) = (term33 _47867).
Proof. exact (MK_COMB (@lem4075386 _47867) (@lem4075384 _47867)). Qed.
Lemma lem4075388 (_47867 : int) : (term34 _47867) = (term32 _47867).
Proof. exact (@lem17362 (term35 _47867) (term36 _47867)). Qed.
Lemma lem4075396 (_47867 : int) : (term34 _47867) = (term33 _47867).
Proof. exact (TRANS (@lem4075388 _47867) (@lem4075387 _47867)). Qed.
Lemma lem4075399 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4075400 (_47867 : int) : (term35 _47867) = (term38 _47867).
Proof. exact (@lem4075399 term22 _47867). Qed.
Lemma lem4075402 (n : nat) : (term39 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4075403 : term40 = term41.
Proof. exact (@lem4075402 (NUMERAL 0)). Qed.
Lemma lem4075404 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4075405 : term42 = term43.
Proof. exact (MK_COMB (@lem4075404) (@lem4075403)). Qed.
Lemma lem4075406 (_47867 : int) : (real_of_int _47867) = (real_of_int _47867).
Proof. exact (eq_refl (real_of_int _47867)). Qed.
Lemma lem4075407 (_47867 : int) : (term38 _47867) = (term44 _47867).
Proof. exact (MK_COMB (@lem4075405) (@lem4075406 _47867)). Qed.
Lemma lem4075409 (_47867 : int) : (term35 _47867) = (term44 _47867).
Proof. exact (TRANS (@lem4075400 _47867) (@lem4075407 _47867)). Qed.
Lemma lem4075412 (x : int) (y : int) : (int_le x y) = (term37 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4075413 (_47867 : int) : (term30 _47867) = (term45 _47867).
Proof. exact (@lem4075412 (term46 _47867) term22). Qed.
Lemma lem4075415 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4075416 (_47867 : int) : (term49 _47867) = (term50 _47867).
Proof. exact (@lem4075415 _47867 term51). Qed.
Lemma lem4075418 (n : nat) : (term39 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4075419 : term52 = term53.
Proof. exact (@lem4075418 term19). Qed.
Lemma lem4075420 (_47867 : int) : (term54 _47867) = (term54 _47867).
Proof. exact (eq_refl (term54 _47867)). Qed.
Lemma lem4075421 (_47867 : int) : (term50 _47867) = (term55 _47867).
Proof. exact (MK_COMB (@lem4075420 _47867) (@lem4075419)). Qed.
Lemma lem4075422 (_47867 : int) : (term49 _47867) = (term55 _47867).
Proof. exact (TRANS (@lem4075416 _47867) (@lem4075421 _47867)). Qed.
Lemma lem4075423 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4075424 (_47867 : int) : (term56 _47867) = (term57 _47867).
Proof. exact (MK_COMB (@lem4075423) (@lem4075422 _47867)). Qed.
Lemma lem4075426 (n : nat) : (term39 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4075427 : term40 = term41.
Proof. exact (@lem4075426 (NUMERAL 0)). Qed.
Lemma lem4075428 (_47867 : int) : (term45 _47867) = (term58 _47867).
Proof. exact (MK_COMB (@lem4075424 _47867) (@lem4075427)). Qed.
Lemma lem4075430 (_47867 : int) : (term30 _47867) = (term58 _47867).
Proof. exact (TRANS (@lem4075413 _47867) (@lem4075428 _47867)). Qed.
Lemma lem4075431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4075432 (_47867 : int) : (term31 _47867) = (term59 _47867).
Proof. exact (MK_COMB (@lem4075431) (@lem4075409 _47867)). Qed.
Lemma lem4075433 (_47867 : int) : (term33 _47867) = (term60 _47867).
Proof. exact (MK_COMB (@lem4075432 _47867) (@lem4075430 _47867)). Qed.
Lemma lem4075434 (_47867 : int) : (term34 _47867) = (term60 _47867).
Proof. exact (TRANS (@lem4075396 _47867) (@lem4075433 _47867)). Qed.
Lemma lem4075438 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4075454 (_47867 : int) : (term62 _47867) = (term60 _47867).
Proof. exact (@lem4075438 (term60 _47867)). Qed.
Lemma lem4075455 (_47867 : int) : (term44 _47867) = (term63 _47867).
Proof. exact (@lem1988287 (real_of_int _47867) term41). Qed.
Lemma lem4075461 (_47867 : int) : (term64 _47867) = (term65 _47867).
Proof. exact (@lem1982792 (real_of_int _47867) term41). Qed.
Lemma lem4075463 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075464 : term41 = term67.
Proof. exact (@lem4075463 (NUMERAL 0)). Qed.
Lemma lem4075466 (x : nat) : (term68 x) = (term69 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4075467 : term70 = term71.
Proof. exact (@lem4075466 term19). Qed.
Lemma lem4075468 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4075469 : term72 = term73.
Proof. exact (MK_COMB (@lem4075468) (@lem4075467)). Qed.
Lemma lem4075470 : term74 = term75.
Proof. exact (MK_COMB (@lem4075469) (@lem4075464)). Qed.
Lemma lem4075471 : term75 = term76.
Proof. exact (@lem1981613 term70 term41 term53 term53). Qed.
Lemma lem4075473 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4075474 : term79 = term80.
Proof. exact (@lem4075473 term19 term19). Qed.
Lemma lem4075475 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075476 : term82 = term19.
Proof. exact (EQ_MP (@lem4075475) (@lem940073)). Qed.
Lemma lem4075477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075478 : term80 = term53.
Proof. exact (MK_COMB (@lem4075477) (@lem4075476)). Qed.
Lemma lem4075479 : term79 = term53.
Proof. exact (TRANS (@lem4075474) (@lem4075478)). Qed.
Lemma lem4075481 (x : nat) : (term83 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4075482 : term74 = term41.
Proof. exact (@lem4075481 term19). Qed.
Lemma lem4075483 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4075484 : term84 = term85.
Proof. exact (MK_COMB (@lem4075483) (@lem4075482)). Qed.
Lemma lem4075485 : term76 = term67.
Proof. exact (MK_COMB (@lem4075484) (@lem4075479)). Qed.
Lemma lem4075486 : term75 = term67.
Proof. exact (TRANS (@lem4075471) (@lem4075485)). Qed.
Lemma lem4075487 : term74 = term67.
Proof. exact (TRANS (@lem4075470) (@lem4075486)). Qed.
Lemma lem4075489 (x : real) : (term86 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4075490 : term67 = term41.
Proof. exact (@lem4075489 term41). Qed.
Lemma lem4075491 : term74 = term41.
Proof. exact (TRANS (@lem4075487) (@lem4075490)). Qed.
Lemma lem4075492 (_47867 : int) : (term54 _47867) = (term54 _47867).
Proof. exact (eq_refl (term54 _47867)). Qed.
Lemma lem4075493 (_47867 : int) : (term65 _47867) = (term87 _47867).
Proof. exact (MK_COMB (@lem4075492 _47867) (@lem4075491)). Qed.
Lemma lem4075494 (_47867 : int) : (term87 _47867) = (real_of_int _47867).
Proof. exact (@lem1982723 (real_of_int _47867)). Qed.
Lemma lem4075495 (_47867 : int) : (term65 _47867) = (real_of_int _47867).
Proof. exact (TRANS (@lem4075493 _47867) (@lem4075494 _47867)). Qed.
Lemma lem4075497 (_47867 : int) : (term64 _47867) = (real_of_int _47867).
Proof. exact (TRANS (@lem4075461 _47867) (@lem4075495 _47867)). Qed.
Lemma lem4075498 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4075499 (_47867 : int) : (term88 _47867) = (term89 _47867).
Proof. exact (MK_COMB (@lem4075498) (@lem4075497 _47867)). Qed.
Lemma lem4075500 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem4075501 (_47867 : int) : (term63 _47867) = (term90 _47867).
Proof. exact (MK_COMB (@lem4075499 _47867) (@lem4075500)). Qed.
Lemma lem4075502 (_47867 : int) : (term44 _47867) = (term90 _47867).
Proof. exact (TRANS (@lem4075455 _47867) (@lem4075501 _47867)). Qed.
Lemma lem4075503 (_47867 : int) : (term58 _47867) = (term91 _47867).
Proof. exact (@lem1988287 term41 (term55 _47867)). Qed.
Lemma lem4075515 (_47867 : int) : (term92 _47867) = (term93 _47867).
Proof. exact (@lem1982792 term41 (term55 _47867)). Qed.
Lemma lem4075516 (_47867 : int) : (term94 _47867) = (term95 _47867).
Proof. exact (@lem1982781 (real_of_int _47867) term70 term53). Qed.
Lemma lem4075518 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075519 : term53 = term96.
Proof. exact (@lem4075518 term19). Qed.
Lemma lem4075521 (x : nat) : (term68 x) = (term69 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4075522 : term70 = term71.
Proof. exact (@lem4075521 term19). Qed.
Lemma lem4075523 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4075524 : term72 = term73.
Proof. exact (MK_COMB (@lem4075523) (@lem4075522)). Qed.
Lemma lem4075525 : term97 = term98.
Proof. exact (MK_COMB (@lem4075524) (@lem4075519)). Qed.
Lemma lem4075526 : term98 = term99.
Proof. exact (@lem1981613 term70 term53 term53 term53). Qed.
Lemma lem4075528 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4075529 : term79 = term80.
Proof. exact (@lem4075528 term19 term19). Qed.
Lemma lem4075530 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075531 : term82 = term19.
Proof. exact (EQ_MP (@lem4075530) (@lem940073)). Qed.
Lemma lem4075532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075533 : term80 = term53.
Proof. exact (MK_COMB (@lem4075532) (@lem4075531)). Qed.
Lemma lem4075534 : term79 = term53.
Proof. exact (TRANS (@lem4075529) (@lem4075533)). Qed.
Lemma lem4075536 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4075537 : term97 = term102.
Proof. exact (@lem4075536 term19 term19). Qed.
Lemma lem4075538 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075539 : term82 = term19.
Proof. exact (EQ_MP (@lem4075538) (@lem940073)). Qed.
Lemma lem4075540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075541 : term80 = term53.
Proof. exact (MK_COMB (@lem4075540) (@lem4075539)). Qed.
Lemma lem4075542 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4075543 : term102 = term70.
Proof. exact (MK_COMB (@lem4075542) (@lem4075541)). Qed.
Lemma lem4075544 : term97 = term70.
Proof. exact (TRANS (@lem4075537) (@lem4075543)). Qed.
Lemma lem4075545 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4075546 : term103 = term104.
Proof. exact (MK_COMB (@lem4075545) (@lem4075544)). Qed.
Lemma lem4075547 : term99 = term71.
Proof. exact (MK_COMB (@lem4075546) (@lem4075534)). Qed.
Lemma lem4075548 : term98 = term71.
Proof. exact (TRANS (@lem4075526) (@lem4075547)). Qed.
Lemma lem4075549 : term97 = term71.
Proof. exact (TRANS (@lem4075525) (@lem4075548)). Qed.
Lemma lem4075551 (x : real) : (term86 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4075552 : term71 = term70.
Proof. exact (@lem4075551 term70). Qed.
Lemma lem4075553 : term97 = term70.
Proof. exact (TRANS (@lem4075549) (@lem4075552)). Qed.
Lemma lem4075556 (_47867 : int) : (term105 _47867) = (term105 _47867).
Proof. exact (eq_refl (term105 _47867)). Qed.
Lemma lem4075557 (_47867 : int) : (term95 _47867) = (term106 _47867).
Proof. exact (MK_COMB (@lem4075556 _47867) (@lem4075553)). Qed.
Lemma lem4075558 (_47867 : int) : (term94 _47867) = (term106 _47867).
Proof. exact (TRANS (@lem4075516 _47867) (@lem4075557 _47867)). Qed.
Lemma lem4075559 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem4075560 (_47867 : int) : (term93 _47867) = (term108 _47867).
Proof. exact (MK_COMB (@lem4075559) (@lem4075558 _47867)). Qed.
Lemma lem4075561 (_47867 : int) : (term108 _47867) = (term106 _47867).
Proof. exact (@lem1982721 (term106 _47867)). Qed.
Lemma lem4075562 (_47867 : int) : (term93 _47867) = (term106 _47867).
Proof. exact (TRANS (@lem4075560 _47867) (@lem4075561 _47867)). Qed.
Lemma lem4075564 (_47867 : int) : (term92 _47867) = (term106 _47867).
Proof. exact (TRANS (@lem4075515 _47867) (@lem4075562 _47867)). Qed.
Lemma lem4075565 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4075566 (_47867 : int) : (term109 _47867) = (term110 _47867).
Proof. exact (MK_COMB (@lem4075565) (@lem4075564 _47867)). Qed.
Lemma lem4075567 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem4075568 (_47867 : int) : (term91 _47867) = (term111 _47867).
Proof. exact (MK_COMB (@lem4075566 _47867) (@lem4075567)). Qed.
Lemma lem4075569 (_47867 : int) : (term58 _47867) = (term111 _47867).
Proof. exact (TRANS (@lem4075503 _47867) (@lem4075568 _47867)). Qed.
Lemma lem4075570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4075571 (_47867 : int) : (term59 _47867) = (term112 _47867).
Proof. exact (MK_COMB (@lem4075570) (@lem4075502 _47867)). Qed.
Lemma lem4075572 (_47867 : int) : (term60 _47867) = (term113 _47867).
Proof. exact (MK_COMB (@lem4075571 _47867) (@lem4075569 _47867)). Qed.
Lemma lem4075587 (_47867 : int) : (term62 _47867) = (term113 _47867).
Proof. exact (TRANS (@lem4075454 _47867) (@lem4075572 _47867)). Qed.
Lemma lem4075591 (_47867 : int) (h1 : term113 _47867) : term113 _47867.
Proof. exact (h1). Qed.
Lemma lem4075592 (_47867 : int) (h1 : term113 _47867) : term111 _47867.
Proof. exact (proj2 (@lem4075591 _47867 h1)). Qed.
Lemma lem4075593 (_47867 : int) (h1 : term113 _47867) : term90 _47867.
Proof. exact (proj1 (@lem4075591 _47867 h1)). Qed.
Lemma lem4075595 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4075596 : term114 = term115.
Proof. exact (@lem4075595 term41 term53). Qed.
Lemma lem4075598 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075599 : term53 = term96.
Proof. exact (@lem4075598 term19). Qed.
Lemma lem4075601 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075602 : term41 = term67.
Proof. exact (@lem4075601 (NUMERAL 0)). Qed.
Lemma lem4075603 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4075604 : term116 = term117.
Proof. exact (MK_COMB (@lem4075603) (@lem4075602)). Qed.
Lemma lem4075605 : term115 = term118.
Proof. exact (MK_COMB (@lem4075604) (@lem4075599)). Qed.
Lemma lem4075606 : term119.
Proof. exact (@lem1980255 term41 term53 term53 term53). Qed.
Lemma lem4075608 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075609 : term115 = term121.
Proof. exact (@lem4075608 (NUMERAL 0) term19). Qed.
Lemma lem4075610 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075611 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075612 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075611 h1) (fun h1 : term121 = True => @lem4075610)). Qed.
Lemma lem4075613 : term121 = True.
Proof. exact (EQ_MP (@lem4075612) (@lem4075610)). Qed.
Lemma lem4075614 : term115 = True.
Proof. exact (TRANS (@lem4075609) (@lem4075613)). Qed.
Lemma lem4075615 : True = term115.
Proof. exact (SYM (@lem4075614)). Qed.
Lemma lem4075616 : term115.
Proof. exact (EQ_MP (@lem4075615) (@lem0)). Qed.
Lemma lem4075617 : term123.
Proof. exact (@lem4075606 (@lem4075616)). Qed.
Lemma lem4075619 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075620 : term115 = term121.
Proof. exact (@lem4075619 (NUMERAL 0) term19). Qed.
Lemma lem4075621 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075622 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075623 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075622 h1) (fun h1 : term121 = True => @lem4075621)). Qed.
Lemma lem4075624 : term121 = True.
Proof. exact (EQ_MP (@lem4075623) (@lem4075621)). Qed.
Lemma lem4075625 : term115 = True.
Proof. exact (TRANS (@lem4075620) (@lem4075624)). Qed.
Lemma lem4075626 : True = term115.
Proof. exact (SYM (@lem4075625)). Qed.
Lemma lem4075627 : term115.
Proof. exact (EQ_MP (@lem4075626) (@lem0)). Qed.
Lemma lem4075628 : term118 = term124.
Proof. exact (@lem4075617 (@lem4075627)). Qed.
Lemma lem4075630 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4075631 : term79 = term80.
Proof. exact (@lem4075630 term19 term19). Qed.
Lemma lem4075632 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075633 : term82 = term19.
Proof. exact (EQ_MP (@lem4075632) (@lem940073)). Qed.
Lemma lem4075634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075635 : term80 = term53.
Proof. exact (MK_COMB (@lem4075634) (@lem4075633)). Qed.
Lemma lem4075636 : term79 = term53.
Proof. exact (TRANS (@lem4075631) (@lem4075635)). Qed.
Lemma lem4075638 (x : nat) : (term125 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4075639 : term126 = term41.
Proof. exact (@lem4075638 term19). Qed.
Lemma lem4075640 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4075641 : term127 = term116.
Proof. exact (MK_COMB (@lem4075640) (@lem4075639)). Qed.
Lemma lem4075642 : term124 = term115.
Proof. exact (MK_COMB (@lem4075641) (@lem4075636)). Qed.
Lemma lem4075644 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075645 : term115 = term121.
Proof. exact (@lem4075644 (NUMERAL 0) term19). Qed.
Lemma lem4075646 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075647 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075648 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075647 h1) (fun h1 : term121 = True => @lem4075646)). Qed.
Lemma lem4075649 : term121 = True.
Proof. exact (EQ_MP (@lem4075648) (@lem4075646)). Qed.
Lemma lem4075650 : term115 = True.
Proof. exact (TRANS (@lem4075645) (@lem4075649)). Qed.
Lemma lem4075651 : term124 = True.
Proof. exact (TRANS (@lem4075642) (@lem4075650)). Qed.
Lemma lem4075652 : term118 = True.
Proof. exact (TRANS (@lem4075628) (@lem4075651)). Qed.
Lemma lem4075653 : term115 = True.
Proof. exact (TRANS (@lem4075605) (@lem4075652)). Qed.
Lemma lem4075654 : term114 = True.
Proof. exact (TRANS (@lem4075596) (@lem4075653)). Qed.
Lemma lem4075655 : True = term114.
Proof. exact (SYM (@lem4075654)). Qed.
Lemma lem4075656 : term114.
Proof. exact (EQ_MP (@lem4075655) (@lem0)). Qed.
Lemma lem4075657 (_47867 : int) (h1 : term113 _47867) : term128 _47867.
Proof. exact (conj (@lem4075656) (@lem4075593 _47867 h1)). Qed.
Lemma lem4075659 (x : real) (y : real) : term129 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4075660 (_47867 : int) : term130 _47867.
Proof. exact (@lem4075659 term53 (real_of_int _47867)). Qed.
Lemma lem4075661 (_47867 : int) (h1 : term113 _47867) : term131 _47867.
Proof. exact (@lem4075660 _47867 (@lem4075657 _47867 h1)). Qed.
Lemma lem4075662 (_47867 : int) : (term132 _47867) = (real_of_int _47867).
Proof. exact (@lem1982733 (real_of_int _47867)). Qed.
Lemma lem4075663 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4075664 (_47867 : int) : (term133 _47867) = (term89 _47867).
Proof. exact (MK_COMB (@lem4075663) (@lem4075662 _47867)). Qed.
Lemma lem4075665 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem4075666 (_47867 : int) : (term131 _47867) = (term90 _47867).
Proof. exact (MK_COMB (@lem4075664 _47867) (@lem4075665)). Qed.
Lemma lem4075667 (_47867 : int) (h1 : term113 _47867) : term90 _47867.
Proof. exact (EQ_MP (@lem4075666 _47867) (@lem4075661 _47867 h1)). Qed.
Lemma lem4075669 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4075670 : term114 = term115.
Proof. exact (@lem4075669 term41 term53). Qed.
Lemma lem4075672 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075673 : term53 = term96.
Proof. exact (@lem4075672 term19). Qed.
Lemma lem4075675 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075676 : term41 = term67.
Proof. exact (@lem4075675 (NUMERAL 0)). Qed.
Lemma lem4075677 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4075678 : term116 = term117.
Proof. exact (MK_COMB (@lem4075677) (@lem4075676)). Qed.
Lemma lem4075679 : term115 = term118.
Proof. exact (MK_COMB (@lem4075678) (@lem4075673)). Qed.
Lemma lem4075680 : term119.
Proof. exact (@lem1980255 term41 term53 term53 term53). Qed.
Lemma lem4075682 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075683 : term115 = term121.
Proof. exact (@lem4075682 (NUMERAL 0) term19). Qed.
Lemma lem4075684 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075685 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075686 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075685 h1) (fun h1 : term121 = True => @lem4075684)). Qed.
Lemma lem4075687 : term121 = True.
Proof. exact (EQ_MP (@lem4075686) (@lem4075684)). Qed.
Lemma lem4075688 : term115 = True.
Proof. exact (TRANS (@lem4075683) (@lem4075687)). Qed.
Lemma lem4075689 : True = term115.
Proof. exact (SYM (@lem4075688)). Qed.
Lemma lem4075690 : term115.
Proof. exact (EQ_MP (@lem4075689) (@lem0)). Qed.
Lemma lem4075691 : term123.
Proof. exact (@lem4075680 (@lem4075690)). Qed.
Lemma lem4075693 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075694 : term115 = term121.
Proof. exact (@lem4075693 (NUMERAL 0) term19). Qed.
Lemma lem4075695 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075696 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075697 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075696 h1) (fun h1 : term121 = True => @lem4075695)). Qed.
Lemma lem4075698 : term121 = True.
Proof. exact (EQ_MP (@lem4075697) (@lem4075695)). Qed.
Lemma lem4075699 : term115 = True.
Proof. exact (TRANS (@lem4075694) (@lem4075698)). Qed.
Lemma lem4075700 : True = term115.
Proof. exact (SYM (@lem4075699)). Qed.
Lemma lem4075701 : term115.
Proof. exact (EQ_MP (@lem4075700) (@lem0)). Qed.
Lemma lem4075702 : term118 = term124.
Proof. exact (@lem4075691 (@lem4075701)). Qed.
Lemma lem4075704 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4075705 : term79 = term80.
Proof. exact (@lem4075704 term19 term19). Qed.
Lemma lem4075706 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075707 : term82 = term19.
Proof. exact (EQ_MP (@lem4075706) (@lem940073)). Qed.
Lemma lem4075708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075709 : term80 = term53.
Proof. exact (MK_COMB (@lem4075708) (@lem4075707)). Qed.
Lemma lem4075710 : term79 = term53.
Proof. exact (TRANS (@lem4075705) (@lem4075709)). Qed.
Lemma lem4075712 (x : nat) : (term125 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4075713 : term126 = term41.
Proof. exact (@lem4075712 term19). Qed.
Lemma lem4075714 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4075715 : term127 = term116.
Proof. exact (MK_COMB (@lem4075714) (@lem4075713)). Qed.
Lemma lem4075716 : term124 = term115.
Proof. exact (MK_COMB (@lem4075715) (@lem4075710)). Qed.
Lemma lem4075718 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075719 : term115 = term121.
Proof. exact (@lem4075718 (NUMERAL 0) term19). Qed.
Lemma lem4075720 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075721 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075722 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075721 h1) (fun h1 : term121 = True => @lem4075720)). Qed.
Lemma lem4075723 : term121 = True.
Proof. exact (EQ_MP (@lem4075722) (@lem4075720)). Qed.
Lemma lem4075724 : term115 = True.
Proof. exact (TRANS (@lem4075719) (@lem4075723)). Qed.
Lemma lem4075725 : term124 = True.
Proof. exact (TRANS (@lem4075716) (@lem4075724)). Qed.
Lemma lem4075726 : term118 = True.
Proof. exact (TRANS (@lem4075702) (@lem4075725)). Qed.
Lemma lem4075727 : term115 = True.
Proof. exact (TRANS (@lem4075679) (@lem4075726)). Qed.
Lemma lem4075728 : term114 = True.
Proof. exact (TRANS (@lem4075670) (@lem4075727)). Qed.
Lemma lem4075729 : True = term114.
Proof. exact (SYM (@lem4075728)). Qed.
Lemma lem4075730 : term114.
Proof. exact (EQ_MP (@lem4075729) (@lem0)). Qed.
Lemma lem4075731 (_47867 : int) (h1 : term113 _47867) : term134 _47867.
Proof. exact (conj (@lem4075730) (@lem4075592 _47867 h1)). Qed.
Lemma lem4075733 (x : real) (y : real) : term129 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4075734 (_47867 : int) : term135 _47867.
Proof. exact (@lem4075733 term53 (term106 _47867)). Qed.
Lemma lem4075735 (_47867 : int) (h1 : term113 _47867) : term136 _47867.
Proof. exact (@lem4075734 _47867 (@lem4075731 _47867 h1)). Qed.
Lemma lem4075736 (_47867 : int) : (term137 _47867) = (term106 _47867).
Proof. exact (@lem1982733 (term106 _47867)). Qed.
Lemma lem4075737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4075738 (_47867 : int) : (term138 _47867) = (term110 _47867).
Proof. exact (MK_COMB (@lem4075737) (@lem4075736 _47867)). Qed.
Lemma lem4075739 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem4075740 (_47867 : int) : (term136 _47867) = (term111 _47867).
Proof. exact (MK_COMB (@lem4075738 _47867) (@lem4075739)). Qed.
Lemma lem4075741 (_47867 : int) (h1 : term113 _47867) : term111 _47867.
Proof. exact (EQ_MP (@lem4075740 _47867) (@lem4075735 _47867 h1)). Qed.
Lemma lem4075742 (_47867 : int) (h1 : term113 _47867) : term139 _47867.
Proof. exact (conj (@lem4075741 _47867 h1) (@lem4075667 _47867 h1)). Qed.
Lemma lem4075744 (x : real) (y : real) : term140 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4075745 (_47867 : int) : term141 _47867.
Proof. exact (@lem4075744 (term106 _47867) (real_of_int _47867)). Qed.
Lemma lem4075746 (_47867 : int) (h1 : term113 _47867) : term142 _47867.
Proof. exact (@lem4075745 _47867 (@lem4075742 _47867 h1)). Qed.
Lemma lem4075747 (_47867 : int) : (term143 _47867) = (term144 _47867).
Proof. exact (@lem1982759 (term145 _47867) (real_of_int _47867) term70). Qed.
Lemma lem4075748 (_47867 : int) : (term146 _47867) = (term147 _47867).
Proof. exact (@lem1982713 term70 (real_of_int _47867)). Qed.
Lemma lem4075750 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075751 : term53 = term96.
Proof. exact (@lem4075750 term19). Qed.
Lemma lem4075753 (x : nat) : (term68 x) = (term69 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4075754 : term70 = term71.
Proof. exact (@lem4075753 term19). Qed.
Lemma lem4075755 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4075756 : term148 = term149.
Proof. exact (MK_COMB (@lem4075755) (@lem4075754)). Qed.
Lemma lem4075757 : term150 = term151.
Proof. exact (MK_COMB (@lem4075756) (@lem4075751)). Qed.
Lemma lem4075758 : term152.
Proof. exact (@lem1981473 term70 term53 term53 term53 term41 term53). Qed.
Lemma lem4075760 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075761 : term115 = term121.
Proof. exact (@lem4075760 (NUMERAL 0) term19). Qed.
Lemma lem4075762 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075763 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075764 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075763 h1) (fun h1 : term121 = True => @lem4075762)). Qed.
Lemma lem4075765 : term121 = True.
Proof. exact (EQ_MP (@lem4075764) (@lem4075762)). Qed.
Lemma lem4075766 : term115 = True.
Proof. exact (TRANS (@lem4075761) (@lem4075765)). Qed.
Lemma lem4075767 : True = term115.
Proof. exact (SYM (@lem4075766)). Qed.
Lemma lem4075768 : term115.
Proof. exact (EQ_MP (@lem4075767) (@lem0)). Qed.
Lemma lem4075769 : term153.
Proof. exact (@lem4075758 (@lem4075768)). Qed.
Lemma lem4075771 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075772 : term115 = term121.
Proof. exact (@lem4075771 (NUMERAL 0) term19). Qed.
Lemma lem4075773 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075774 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075775 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075774 h1) (fun h1 : term121 = True => @lem4075773)). Qed.
Lemma lem4075776 : term121 = True.
Proof. exact (EQ_MP (@lem4075775) (@lem4075773)). Qed.
Lemma lem4075777 : term115 = True.
Proof. exact (TRANS (@lem4075772) (@lem4075776)). Qed.
Lemma lem4075778 : True = term115.
Proof. exact (SYM (@lem4075777)). Qed.
Lemma lem4075779 : term115.
Proof. exact (EQ_MP (@lem4075778) (@lem0)). Qed.
Lemma lem4075780 : term154.
Proof. exact (@lem4075769 (@lem4075779)). Qed.
Lemma lem4075782 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075783 : term115 = term121.
Proof. exact (@lem4075782 (NUMERAL 0) term19). Qed.
Lemma lem4075784 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075785 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075786 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075785 h1) (fun h1 : term121 = True => @lem4075784)). Qed.
Lemma lem4075787 : term121 = True.
Proof. exact (EQ_MP (@lem4075786) (@lem4075784)). Qed.
Lemma lem4075788 : term115 = True.
Proof. exact (TRANS (@lem4075783) (@lem4075787)). Qed.
Lemma lem4075789 : True = term115.
Proof. exact (SYM (@lem4075788)). Qed.
Lemma lem4075790 : term115.
Proof. exact (EQ_MP (@lem4075789) (@lem0)). Qed.
Lemma lem4075791 : term155.
Proof. exact (@lem4075780 (@lem4075790)). Qed.
Lemma lem4075793 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4075794 : term79 = term80.
Proof. exact (@lem4075793 term19 term19). Qed.
Lemma lem4075795 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075796 : term82 = term19.
Proof. exact (EQ_MP (@lem4075795) (@lem940073)). Qed.
Lemma lem4075797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075798 : term80 = term53.
Proof. exact (MK_COMB (@lem4075797) (@lem4075796)). Qed.
Lemma lem4075799 : term79 = term53.
Proof. exact (TRANS (@lem4075794) (@lem4075798)). Qed.
Lemma lem4075801 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4075802 : term97 = term102.
Proof. exact (@lem4075801 term19 term19). Qed.
Lemma lem4075803 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075804 : term82 = term19.
Proof. exact (EQ_MP (@lem4075803) (@lem940073)). Qed.
Lemma lem4075805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075806 : term80 = term53.
Proof. exact (MK_COMB (@lem4075805) (@lem4075804)). Qed.
Lemma lem4075807 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4075808 : term102 = term70.
Proof. exact (MK_COMB (@lem4075807) (@lem4075806)). Qed.
Lemma lem4075809 : term97 = term70.
Proof. exact (TRANS (@lem4075802) (@lem4075808)). Qed.
Lemma lem4075810 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4075811 : term156 = term148.
Proof. exact (MK_COMB (@lem4075810) (@lem4075809)). Qed.
Lemma lem4075812 : term157 = term150.
Proof. exact (MK_COMB (@lem4075811) (@lem4075799)). Qed.
Lemma lem4075814 (m : nat) : (term158 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4075815 : term150 = term41.
Proof. exact (@lem4075814 term19). Qed.
Lemma lem4075816 : term157 = term41.
Proof. exact (TRANS (@lem4075812) (@lem4075815)). Qed.
Lemma lem4075817 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4075818 : term159 = term160.
Proof. exact (MK_COMB (@lem4075817) (@lem4075816)). Qed.
Lemma lem4075819 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem4075820 : term161 = term126.
Proof. exact (MK_COMB (@lem4075818) (@lem4075819)). Qed.
Lemma lem4075822 (x : nat) : (term125 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4075823 : term126 = term41.
Proof. exact (@lem4075822 term19). Qed.
Lemma lem4075824 : term161 = term41.
Proof. exact (TRANS (@lem4075820) (@lem4075823)). Qed.
Lemma lem4075826 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4075827 : term79 = term80.
Proof. exact (@lem4075826 term19 term19). Qed.
Lemma lem4075828 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075829 : term82 = term19.
Proof. exact (EQ_MP (@lem4075828) (@lem940073)). Qed.
Lemma lem4075830 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075831 : term80 = term53.
Proof. exact (MK_COMB (@lem4075830) (@lem4075829)). Qed.
Lemma lem4075832 : term79 = term53.
Proof. exact (TRANS (@lem4075827) (@lem4075831)). Qed.
Lemma lem4075833 : term160 = term160.
Proof. exact (eq_refl term160). Qed.
Lemma lem4075834 : term162 = term126.
Proof. exact (MK_COMB (@lem4075833) (@lem4075832)). Qed.
Lemma lem4075836 (x : nat) : (term125 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4075837 : term126 = term41.
Proof. exact (@lem4075836 term19). Qed.
Lemma lem4075838 : term162 = term41.
Proof. exact (TRANS (@lem4075834) (@lem4075837)). Qed.
Lemma lem4075839 : term41 = term162.
Proof. exact (SYM (@lem4075838)). Qed.
Lemma lem4075840 : term161 = term162.
Proof. exact (TRANS (@lem4075824) (@lem4075839)). Qed.
Lemma lem4075841 : term151 = term67.
Proof. exact (@lem4075791 (@lem4075840)). Qed.
Lemma lem4075842 : term150 = term67.
Proof. exact (TRANS (@lem4075757) (@lem4075841)). Qed.
Lemma lem4075844 (x : real) : (term86 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4075845 : term67 = term41.
Proof. exact (@lem4075844 term41). Qed.
Lemma lem4075846 : term150 = term41.
Proof. exact (TRANS (@lem4075842) (@lem4075845)). Qed.
Lemma lem4075847 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4075848 : term163 = term160.
Proof. exact (MK_COMB (@lem4075847) (@lem4075846)). Qed.
Lemma lem4075849 (_47867 : int) : (real_of_int _47867) = (real_of_int _47867).
Proof. exact (eq_refl (real_of_int _47867)). Qed.
Lemma lem4075850 (_47867 : int) : (term147 _47867) = (term164 _47867).
Proof. exact (MK_COMB (@lem4075848) (@lem4075849 _47867)). Qed.
Lemma lem4075851 (_47867 : int) : (term146 _47867) = (term164 _47867).
Proof. exact (TRANS (@lem4075748 _47867) (@lem4075850 _47867)). Qed.
Lemma lem4075852 (_47867 : int) : (term164 _47867) = term41.
Proof. exact (@lem1982719 (real_of_int _47867)). Qed.
Lemma lem4075853 (_47867 : int) : (term146 _47867) = term41.
Proof. exact (TRANS (@lem4075851 _47867) (@lem4075852 _47867)). Qed.
Lemma lem4075854 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4075855 (_47867 : int) : (term165 _47867) = term107.
Proof. exact (MK_COMB (@lem4075854) (@lem4075853 _47867)). Qed.
Lemma lem4075856 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem4075857 (_47867 : int) : (term144 _47867) = term166.
Proof. exact (MK_COMB (@lem4075855 _47867) (@lem4075856)). Qed.
Lemma lem4075858 (_47867 : int) : (term143 _47867) = term166.
Proof. exact (TRANS (@lem4075747 _47867) (@lem4075857 _47867)). Qed.
Lemma lem4075859 : term166 = term70.
Proof. exact (@lem1982721 term70). Qed.
Lemma lem4075860 (_47867 : int) : (term143 _47867) = term70.
Proof. exact (TRANS (@lem4075858 _47867) (@lem4075859)). Qed.
Lemma lem4075861 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4075862 (_47867 : int) : (term167 _47867) = term168.
Proof. exact (MK_COMB (@lem4075861) (@lem4075860 _47867)). Qed.
Lemma lem4075863 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem4075864 (_47867 : int) : (term142 _47867) = term169.
Proof. exact (MK_COMB (@lem4075862 _47867) (@lem4075863)). Qed.
Lemma lem4075865 (_47867 : int) (h1 : term113 _47867) : term169.
Proof. exact (EQ_MP (@lem4075864 _47867) (@lem4075746 _47867 h1)). Qed.
Lemma lem4075867 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4075868 : term169 = term170.
Proof. exact (@lem4075867 term41 term70). Qed.
Lemma lem4075870 (x : nat) : (term68 x) = (term69 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4075871 : term70 = term71.
Proof. exact (@lem4075870 term19). Qed.
Lemma lem4075873 (x : nat) : (real_of_num x) = (term66 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4075874 : term41 = term67.
Proof. exact (@lem4075873 (NUMERAL 0)). Qed.
Lemma lem4075875 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4075876 : term43 = term171.
Proof. exact (MK_COMB (@lem4075875) (@lem4075874)). Qed.
Lemma lem4075877 : term170 = term172.
Proof. exact (MK_COMB (@lem4075876) (@lem4075871)). Qed.
Lemma lem4075878 : term173.
Proof. exact (@lem1980026 term41 term53 term70 term53). Qed.
Lemma lem4075880 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075881 : term115 = term121.
Proof. exact (@lem4075880 (NUMERAL 0) term19). Qed.
Lemma lem4075882 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075883 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075884 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075883 h1) (fun h1 : term121 = True => @lem4075882)). Qed.
Lemma lem4075885 : term121 = True.
Proof. exact (EQ_MP (@lem4075884) (@lem4075882)). Qed.
Lemma lem4075886 : term115 = True.
Proof. exact (TRANS (@lem4075881) (@lem4075885)). Qed.
Lemma lem4075887 : True = term115.
Proof. exact (SYM (@lem4075886)). Qed.
Lemma lem4075888 : term115.
Proof. exact (EQ_MP (@lem4075887) (@lem0)). Qed.
Lemma lem4075889 : term174.
Proof. exact (@lem4075878 (@lem4075888)). Qed.
Lemma lem4075891 (m : nat) (n : nat) : (term120 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4075892 : term115 = term121.
Proof. exact (@lem4075891 (NUMERAL 0) term19). Qed.
Lemma lem4075893 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075894 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4075895 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075894 h1) (fun h1 : term121 = True => @lem4075893)). Qed.
Lemma lem4075896 : term121 = True.
Proof. exact (EQ_MP (@lem4075895) (@lem4075893)). Qed.
Lemma lem4075897 : term115 = True.
Proof. exact (TRANS (@lem4075892) (@lem4075896)). Qed.
Lemma lem4075898 : True = term115.
Proof. exact (SYM (@lem4075897)). Qed.
Lemma lem4075899 : term115.
Proof. exact (EQ_MP (@lem4075898) (@lem0)). Qed.
Lemma lem4075900 : term172 = term175.
Proof. exact (@lem4075889 (@lem4075899)). Qed.
Lemma lem4075902 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4075903 : term97 = term102.
Proof. exact (@lem4075902 term19 term19). Qed.
Lemma lem4075904 : (term81 = (BIT1 0)) = (term82 = term19).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4075905 : term82 = term19.
Proof. exact (EQ_MP (@lem4075904) (@lem940073)). Qed.
Lemma lem4075906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4075907 : term80 = term53.
Proof. exact (MK_COMB (@lem4075906) (@lem4075905)). Qed.
Lemma lem4075908 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4075909 : term102 = term70.
Proof. exact (MK_COMB (@lem4075908) (@lem4075907)). Qed.
Lemma lem4075910 : term97 = term70.
Proof. exact (TRANS (@lem4075903) (@lem4075909)). Qed.
Lemma lem4075912 (x : nat) : (term125 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4075913 : term126 = term41.
Proof. exact (@lem4075912 term19). Qed.
Lemma lem4075914 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4075915 : term176 = term43.
Proof. exact (MK_COMB (@lem4075914) (@lem4075913)). Qed.
Lemma lem4075916 : term175 = term170.
Proof. exact (MK_COMB (@lem4075915) (@lem4075910)). Qed.
Lemma lem4075918 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4075919 : term170 = term179.
Proof. exact (@lem4075918 (NUMERAL 0) term19). Qed.
Lemma lem4075920 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4075921 (h1 : term122 = (BIT1 0)) : (term19 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4075922 : (term122 = (BIT1 0)) = ((term19 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem4075921 h1) (fun h1 : (term19 = (NUMERAL 0)) = False => @lem4075920)). Qed.
Lemma lem4075923 : (term19 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4075922) (@lem4075920)). Qed.
Lemma lem4075924 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4075925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4075926 : term180 = (and True).
Proof. exact (MK_COMB (@lem4075925) (@lem4075924)). Qed.
Lemma lem4075927 : term179 = (True /\ False).
Proof. exact (MK_COMB (@lem4075926) (@lem4075923)). Qed.
Lemma lem4075929 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4075930 : term179 = False.
Proof. exact (TRANS (@lem4075927) (@lem4075929)). Qed.
Lemma lem4075931 : term170 = False.
Proof. exact (TRANS (@lem4075919) (@lem4075930)). Qed.
Lemma lem4075932 : term175 = False.
Proof. exact (TRANS (@lem4075916) (@lem4075931)). Qed.
Lemma lem4075933 : term172 = False.
Proof. exact (TRANS (@lem4075900) (@lem4075932)). Qed.
Lemma lem4075934 : term170 = False.
Proof. exact (TRANS (@lem4075877) (@lem4075933)). Qed.
Lemma lem4075935 : term169 = False.
Proof. exact (TRANS (@lem4075868) (@lem4075934)). Qed.
Lemma lem4075936 (_47867 : int) (h1 : term113 _47867) : False.
Proof. exact (EQ_MP (@lem4075935) (@lem4075865 _47867 h1)). Qed.
Lemma lem4075938 (_47867 : int) (h1 : term113 _47867) : term113 _47867.
Proof. exact (h1). Qed.
Lemma lem4075939 (_47867 : int) (h1 : term113 _47867) : (term113 _47867) = False.
Proof. exact (prop_ext (fun h2 : term113 _47867 => @lem4075936 _47867 h1) (fun h2 : False => @lem4075938 _47867 h1)). Qed.
Lemma lem4075940 (_47867 : int) (h1 : term113 _47867) : False.
Proof. exact (EQ_MP (@lem4075939 _47867 h1) (@lem4075938 _47867 h1)). Qed.
Lemma lem4075941 (_47867 : int) (h1 : term62 _47867) : term62 _47867.
Proof. exact (h1). Qed.
Lemma lem4075942 (_47867 : int) (h1 : term62 _47867) : term113 _47867.
Proof. exact (EQ_MP (@lem4075587 _47867) (@lem4075941 _47867 h1)). Qed.
Lemma lem4075943 (_47867 : int) (h1 : term62 _47867) : (term113 _47867) = False.
Proof. exact (prop_ext (fun h2 : term113 _47867 => @lem4075940 _47867 h2) (fun h2 : False => @lem4075942 _47867 h1)). Qed.
Lemma lem4075944 (_47867 : int) (h1 : term62 _47867) : False.
Proof. exact (EQ_MP (@lem4075943 _47867 h1) (@lem4075942 _47867 h1)). Qed.
Lemma lem4075945 (_47867 : int) : term181 _47867.
Proof. exact (fun h0 : term62 _47867 => @lem4075944 _47867 h0). Qed.
Lemma lem4075946 (_47867 : int) : term182 _47867.
Proof. exact (@lem1386578 (term183 _47867)). Qed.
Lemma lem4075949 (_47867 : int) : term183 _47867.
Proof. exact (@lem4075946 _47867 (@lem4075945 _47867)). Qed.
Lemma lem4075950 (_47867 : int) : (term60 _47867) = (term34 _47867).
Proof. exact (SYM (@lem4075434 _47867)). Qed.
Lemma lem4075951 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075952 (_47867 : int) : (term183 _47867) = (term27 _47867).
Proof. exact (MK_COMB (@lem4075951) (@lem4075950 _47867)). Qed.
Lemma lem4075953 (_47867 : int) : term27 _47867.
Proof. exact (EQ_MP (@lem4075952 _47867) (@lem4075949 _47867)). Qed.
Lemma lem4075954 (_47867 : int) : term28 _47867.
Proof. exact (EQ_MP (@lem4075373 _47867) (@lem4075953 _47867)). Qed.
Lemma lem4075955 (n : nat) : term184 n.
Proof. exact (@lem4075954 (int_of_num n)). Qed.
Lemma lem4075956 (n : nat) : term24 n.
Proof. exact (@lem4075955 n (@lem4075372 n)). Qed.
Lemma lem4075957 (n : nat) : (term24 n) = (term11 n).
Proof. exact (SYM (@lem4075369 n)). Qed.
Lemma lem4075958 (n : nat) : term11 n.
Proof. exact (EQ_MP (@lem4075957 n) (@lem4075956 n)). Qed.
Lemma lem4075959 (n : nat) : term185 n.
Proof. exact (@lem82 (term9 n)). Qed.
Lemma lem4075971 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4075973 {A : Type'} (h1 : term186 A) : term186 A.
Proof. exact (h1). Qed.
Lemma lem4075974 {A : Type'} (P : type686 A) (h1 : term186 A) : term187 A P.
Proof. exact (@lem4075973 A h1 P). Qed.
Lemma lem4075975 {A : Type'} (P : type686 A) : (term187 A P) = (term188 A P).
Proof. exact (eq_refl (term187 A P)). Qed.
Lemma lem4075976 {A : Type'} (P : type686 A) (h1 : term186 A) : term188 A P.
Proof. exact (EQ_MP (@lem4075975 A P) (@lem4075974 A P h1)). Qed.
Lemma lem4075977 {A : Type'} (P : type686 A) (h1 : term189 A P) : term189 A P.
Proof. exact (h1). Qed.
Lemma lem4075978 {A : Type'} (P : type686 A) (h1 : term186 A) (h2 : term189 A P) : term190 A P.
Proof. exact (@lem4075976 A P h1 (@lem4075977 A P h2)). Qed.
Lemma lem4075979 {A : Type'} (P : type686 A) (h1 : term189 A P) : term191 A P.
Proof. exact (fun h0 : term186 A => @lem4075978 A P h0 h1). Qed.
Lemma lem4075980 {A : Type'} (h1 : term186 A) : term186 A.
Proof. exact (h1). Qed.
Lemma lem4075981 {A : Type'} (P : type686 A) (h1 : term186 A) (h2 : term189 A P) : term190 A P.
Proof. exact (@lem4075979 A P h2 (@lem4075980 A h1)). Qed.
Lemma lem4075982 {A : Type'} (P : type686 A) (h1 : term186 A) : term188 A P.
Proof. exact (fun h0 : term189 A P => @lem4075981 A P h1 h0). Qed.
Lemma lem4075983 {A : Type'} (h1 : term186 A) : term186 A.
Proof. exact (fun P : type686 A => @lem4075982 A P h1). Qed.
Lemma lem4075984 {A : Type'} : term192 A.
Proof. exact (fun h0 : term186 A => @lem4075983 A h0). Qed.
Lemma lem4075985 {A : Type'} : term186 A.
Proof. exact (@lem4075984 A (@lem3450827 A)). Qed.
Lemma lem4075986 {A : Type'} (P : type686 A) : term187 A P.
Proof. exact (@lem4075985 A P). Qed.
Lemma lem4075987 {A : Type'} (P : type686 A) : (term187 A P) = (term188 A P).
Proof. exact (eq_refl (term187 A P)). Qed.
Lemma lem4075999 {A : Type'} (s : A -> Prop) : term193 A s.
Proof. exact (@lem3867912 A s). Qed.
Lemma lem4076000 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (eq_refl (term193 A s)). Qed.
Lemma lem4076001 {A : Type'} (s : A -> Prop) : term194 A s.
Proof. exact (EQ_MP (@lem4076000 A s) (@lem4075999 A s)). Qed.
Lemma lem4076002 {A : Type'} (s : A -> Prop) (n : nat) : term195 A s n.
Proof. exact (@lem4076001 A s n). Qed.
Lemma lem4076003 {A : Type'} (s : A -> Prop) (n : nat) : (term195 A s n) = ((term196 A s n) = (term197 A s n)).
Proof. exact (eq_refl (term195 A s n)). Qed.
Lemma lem4076005 {A : Type'} (s : A -> Prop) : term198 A s.
Proof. exact (@lem3864294 A s). Qed.
Lemma lem4076006 {A : Type'} (s : A -> Prop) : (term198 A s) = ((term199 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl (term198 A s)). Qed.
Lemma lem4076009 (P : nat -> Prop) : term200 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem4076010 {A : Type'} : term201 A.
Proof. exact (@lem4076009 (term202 A)). Qed.
Lemma lem4076011 {A : Type'} : (term203 A) = (term204 A).
Proof. exact (eq_refl (term203 A)). Qed.
Lemma lem4076012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4076013 {A : Type'} : (term205 A) = (term206 A).
Proof. exact (MK_COMB (@lem4076012) (@lem4076011 A)). Qed.
Lemma lem4076014 {A : Type'} (n : nat) : (term207 A n) = (term208 A n).
Proof. exact (eq_refl (term207 A n)). Qed.
Lemma lem4076015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4076016 {A : Type'} (n : nat) : (term209 A n) = (term210 A n).
Proof. exact (MK_COMB (@lem4076015) (@lem4076014 A n)). Qed.
Lemma lem4076017 {A : Type'} (n : nat) : (term211 A n) = (term212 A n).
Proof. exact (eq_refl (term211 A n)). Qed.
Lemma lem4076018 {A : Type'} (n : nat) : (term213 A n) = (term214 A n).
Proof. exact (MK_COMB (@lem4076016 A n) (@lem4076017 A n)). Qed.
Lemma lem4076019 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (fun_ext (fun n : nat => @lem4076018 A n)). Qed.
Lemma lem4076020 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4076021 {A : Type'} : (term217 A) = (term218 A).
Proof. exact (MK_COMB (@lem4076020) (@lem4076019 A)). Qed.
Lemma lem4076022 {A : Type'} : (term219 A) = (term220 A).
Proof. exact (MK_COMB (@lem4076013 A) (@lem4076021 A)). Qed.
Lemma lem4076023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4076024 {A : Type'} : (term221 A) = (term222 A).
Proof. exact (MK_COMB (@lem4076023) (@lem4076022 A)). Qed.
Lemma lem4076025 {A : Type'} (n : nat) : (term207 A n) = (term208 A n).
Proof. exact (eq_refl (term207 A n)). Qed.
Lemma lem4076026 {A : Type'} : (term223 A) = (term202 A).
Proof. exact (fun_ext (fun n : nat => @lem4076025 A n)). Qed.
Lemma lem4076027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4076028 {A : Type'} : (term224 A) = (term225 A).
Proof. exact (MK_COMB (@lem4076027) (@lem4076026 A)). Qed.
Lemma lem4076029 {A : Type'} : (term201 A) = (term226 A).
Proof. exact (MK_COMB (@lem4076024 A) (@lem4076028 A)). Qed.
Lemma lem4076030 {A : Type'} : term226 A.
Proof. exact (EQ_MP (@lem4076029 A) (@lem4076010 A)). Qed.
Lemma lem4076031 {A : Type'} (n : nat) (h1 : term208 A n) : term208 A n.
Proof. exact (h1). Qed.
Lemma lem4076047 {A : Type'} (s : A -> Prop) : (term199 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4076006 A s) (@lem4076005 A s)). Qed.
Lemma lem4076048 {A : Type'} (s : A -> Prop) : (term199 A s) = (s = (@EMPTY A)).
Proof. exact (@lem4076047 A s). Qed.
Lemma lem4076049 {A : Type'} (t : A -> Prop) : (term199 A t) = (t = (@EMPTY A)).
Proof. exact (@lem4076048 A t). Qed.
Lemma lem4076052 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term227 A t s) = (term227 A t s).
Proof. exact (eq_refl (term227 A t s)). Qed.
Lemma lem4076053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term228 A s t) = (term229 A s t).
Proof. exact (MK_COMB (@lem4076052 A t s) (@lem4076049 A t)). Qed.
Lemma lem4076056 {A : Type'} (s : A -> Prop) : (term230 A s) = (term231 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076053 A s t)). Qed.
Lemma lem4076057 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4076058 {A : Type'} (s : A -> Prop) : (term232 A s) = (term233 A s).
Proof. exact (MK_COMB (@lem4076057 A) (@lem4076056 A s)). Qed.
Lemma lem4076063 {A : Type'} (s : A -> Prop) : (term234 A s) = (term234 A s).
Proof. exact (eq_refl (term234 A s)). Qed.
Lemma lem4076064 {A : Type'} (s : A -> Prop) : (term235 A s) = (term236 A s).
Proof. exact (MK_COMB (@lem4076063 A s) (@lem4076058 A s)). Qed.
Lemma lem4076067 {A : Type'} : (term237 A) = (term238 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076064 A s)). Qed.
Lemma lem4076068 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076069 {A : Type'} : (term204 A) = (term239 A).
Proof. exact (MK_COMB (@lem4076068 A) (@lem4076067 A)). Qed.
Lemma lem4076074 {A : Type'} : (term239 A) = (term204 A).
Proof. exact (SYM (@lem4076069 A)). Qed.
Lemma lem4076090 {A : Type'} (s : A -> Prop) (n : nat) : (term196 A s n) = (term197 A s n).
Proof. exact (EQ_MP (@lem4076003 A s n) (@lem4076002 A s n)). Qed.
Lemma lem4076091 {A : Type'} (s : A -> Prop) (n : nat) : (term196 A s n) = (term197 A s n).
Proof. exact (@lem4076090 A s n). Qed.
Lemma lem4076092 {A : Type'} (t : A -> Prop) (n : nat) : (term196 A t n) = (term197 A t n).
Proof. exact (@lem4076091 A t n). Qed.
Lemma lem4076103 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term227 A t s) = (term227 A t s).
Proof. exact (eq_refl (term227 A t s)). Qed.
Lemma lem4076104 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) : (term240 A s t n) = (term241 A s t n).
Proof. exact (MK_COMB (@lem4076103 A t s) (@lem4076092 A t n)). Qed.
Lemma lem4076107 {A : Type'} (s : A -> Prop) (n : nat) : (term242 A s n) = (term243 A s n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076104 A s t n)). Qed.
Lemma lem4076108 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4076109 {A : Type'} (s : A -> Prop) (n : nat) : (term244 A s n) = (term245 A s n).
Proof. exact (MK_COMB (@lem4076108 A) (@lem4076107 A s n)). Qed.
Lemma lem4076114 {A : Type'} (n : nat) (s : A -> Prop) : (term246 A n s) = (term246 A n s).
Proof. exact (eq_refl (term246 A n s)). Qed.
Lemma lem4076115 {A : Type'} (s : A -> Prop) (n : nat) : (term247 A s n) = (term248 A s n).
Proof. exact (MK_COMB (@lem4076114 A n s) (@lem4076109 A s n)). Qed.
Lemma lem4076118 {A : Type'} (n : nat) : (term249 A n) = (term250 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076115 A s n)). Qed.
Lemma lem4076119 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076120 {A : Type'} (n : nat) : (term212 A n) = (term251 A n).
Proof. exact (MK_COMB (@lem4076119 A) (@lem4076118 A n)). Qed.
Lemma lem4076125 {A : Type'} (n : nat) : (term251 A n) = (term212 A n).
Proof. exact (SYM (@lem4076120 A n)). Qed.
Lemma lem4076127 (p : Prop) : p = (term252 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4076128 {A : Type'} : (term239 A) = (term253 A).
Proof. exact (@lem4076127 (term239 A)). Qed.
Lemma lem4076129 {A : Type'} : (term253 A) = (term239 A).
Proof. exact (SYM (@lem4076128 A)). Qed.
Lemma lem4076130 {A : Type'} (h1 : term254 A) : term254 A.
Proof. exact (h1). Qed.
Lemma lem4076131 {A : Type'} : term255 A.
Proof. exact (@lem3219985 A). Qed.
Lemma lem4076135 {A : Type'} (h1 : term256 A) : term256 A.
Proof. exact (h1). Qed.
Lemma lem4076136 {A : Type'} : term257 A.
Proof. exact (fun h0 : term256 A => @lem4076135 A h0). Qed.
Lemma lem4076137 {A : Type'} (h1 : term257 A) : term257 A.
Proof. exact (h1). Qed.
Lemma lem4076138 {A : Type'} (h1 : term256 A) : term256 A.
Proof. exact (h1). Qed.
Lemma lem4076139 {A : Type'} (h1 : term256 A) (h2 : term257 A) : term256 A.
Proof. exact (@lem4076137 A h2 (@lem4076138 A h1)). Qed.
Lemma lem4076140 {A : Type'} (h1 : term256 A) : term258 A.
Proof. exact (fun h0 : term257 A => @lem4076139 A h1 h0). Qed.
Lemma lem4076141 {A : Type'} (h1 : term257 A) : term257 A.
Proof. exact (h1). Qed.
Lemma lem4076142 {A : Type'} (h1 : term256 A) (h2 : term257 A) : term256 A.
Proof. exact (@lem4076140 A h1 (@lem4076141 A h2)). Qed.
Lemma lem4076143 {A : Type'} (h1 : term257 A) : term257 A.
Proof. exact (fun h0 : term256 A => @lem4076142 A h0 h1). Qed.
Lemma lem4076144 {A : Type'} : term259 A.
Proof. exact (fun h0 : term257 A => @lem4076143 A h0). Qed.
Lemma lem4076147 {A : Type'} : term257 A.
Proof. exact (@lem4076144 A (@lem4076136 A)). Qed.
Lemma lem4076148 {A : Type'} : term257 A.
Proof. exact (@lem4076147 A). Qed.
Lemma lem4076210 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4076211 {A : Type'} : (term260 A) = (term261 A).
Proof. exact (@lem4076210 (term255 A)). Qed.
Lemma lem4076216 {A : Type'} : (term262 A) = (term262 A).
Proof. exact (eq_refl (term262 A)). Qed.
Lemma lem4076223 {A : Type'} : (term256 A) = (term263 A).
Proof. exact (MK_COMB (@lem4076216 A) (@lem4076211 A)). Qed.
Lemma lem4076224 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076225 {A : Type'} : (term264 A) = (term264 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076224 A s)). Qed.
Lemma lem4076226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076227 {A : Type'} : (term255 A) = (term255 A).
Proof. exact (MK_COMB (@lem4076226 A) (@lem4076225 A)). Qed.
Lemma lem4076228 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4076229 {A : Type'} : (term261 A) = (term261 A).
Proof. exact (MK_COMB (@lem4076228) (@lem4076227 A)). Qed.
Lemma lem4076234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term229 A s t) = (term229 A s t).
Proof. exact (eq_refl (term229 A s t)). Qed.
Lemma lem4076235 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076234 A s t)). Qed.
Lemma lem4076236 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4076237 {A : Type'} (s : A -> Prop) : (term233 A s) = (term233 A s).
Proof. exact (MK_COMB (@lem4076236 A) (@lem4076235 A s)). Qed.
Lemma lem4076244 {A : Type'} (s : A -> Prop) : (term234 A s) = (term234 A s).
Proof. exact (eq_refl (term234 A s)). Qed.
Lemma lem4076245 {A : Type'} (s : A -> Prop) : (term236 A s) = (term236 A s).
Proof. exact (MK_COMB (@lem4076244 A s) (@lem4076237 A s)). Qed.
Lemma lem4076246 {A : Type'} : (term238 A) = (term238 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076245 A s)). Qed.
Lemma lem4076247 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076248 {A : Type'} : (term239 A) = (term239 A).
Proof. exact (MK_COMB (@lem4076247 A) (@lem4076246 A)). Qed.
Lemma lem4076249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4076250 {A : Type'} : (term254 A) = (term254 A).
Proof. exact (MK_COMB (@lem4076249) (@lem4076248 A)). Qed.
Lemma lem4076251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4076252 {A : Type'} : (term262 A) = (term262 A).
Proof. exact (MK_COMB (@lem4076251) (@lem4076250 A)). Qed.
Lemma lem4076253 {A : Type'} : (term263 A) = (term263 A).
Proof. exact (MK_COMB (@lem4076252 A) (@lem4076229 A)). Qed.
Lemma lem4076282 {A : Type'} : (term256 A) = (term263 A).
Proof. exact (TRANS (@lem4076223 A) (@lem4076253 A)). Qed.
Lemma lem4076283 {A : Type'} : (term263 A) = (term256 A).
Proof. exact (SYM (@lem4076282 A)). Qed.
Lemma lem4076284 {A : Type'} (h1 : term254 A) : term254 A.
Proof. exact (h1). Qed.
Lemma lem4076285 {A : Type'} (h1 : term255 A) : term255 A.
Proof. exact (h1). Qed.
Lemma lem4076292 {A : Type'} (s : A -> Prop) : (term265 A s) = (term266 A s).
Proof. exact (@lem17265 (@FINITE A s) (term267 A s)). Qed.
Lemma lem4076299 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term268 A s t) = (term269 A s t).
Proof. exact (@lem17045 (@SUBSET A t s) (t = (@EMPTY A))). Qed.
Lemma lem4076300 {A : Type'} (P : type686 A) : (term270 A P) = (term271 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4076301 {A : Type'} (s : A -> Prop) : (term272 A s) = (term273 A s).
Proof. exact (@lem4076300 A (term231 A s)). Qed.
Lemma lem4076302 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term274 A s t) = (term229 A s t).
Proof. exact (eq_refl (term274 A s t)). Qed.
Lemma lem4076303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4076304 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term268 A s t).
Proof. exact (MK_COMB (@lem4076303) (@lem4076302 A s t)). Qed.
Lemma lem4076305 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term275 A s t) = (term269 A s t).
Proof. exact (TRANS (@lem4076304 A s t) (@lem4076299 A s t)). Qed.
Lemma lem4076306 {A : Type'} (s : A -> Prop) : (term276 A s) = (term277 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076305 A s t)). Qed.
Lemma lem4076307 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076308 {A : Type'} (s : A -> Prop) : (term273 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem4076307 A) (@lem4076306 A s)). Qed.
Lemma lem4076309 {A : Type'} (s : A -> Prop) : (term272 A s) = (term278 A s).
Proof. exact (TRANS (@lem4076301 A s) (@lem4076308 A s)). Qed.
Lemma lem4076310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4076311 {A : Type'} (s : A -> Prop) : (term279 A s) = (term280 A s).
Proof. exact (MK_COMB (@lem4076310) (@lem4076292 A s)). Qed.
Lemma lem4076312 {A : Type'} (s : A -> Prop) : (term281 A s) = (term282 A s).
Proof. exact (MK_COMB (@lem4076311 A s) (@lem4076309 A s)). Qed.
Lemma lem4076313 {A : Type'} (s : A -> Prop) : (term283 A s) = (term281 A s).
Proof. exact (@lem17362 (term265 A s) (term233 A s)). Qed.
Lemma lem4076314 {A : Type'} (s : A -> Prop) : (term283 A s) = (term282 A s).
Proof. exact (TRANS (@lem4076313 A s) (@lem4076312 A s)). Qed.
Lemma lem4076315 {A : Type'} (P : type686 A) : (term284 A P) = (term285 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4076316 {A : Type'} : (term254 A) = (term286 A).
Proof. exact (@lem4076315 A (term238 A)). Qed.
Lemma lem4076317 {A : Type'} (s : A -> Prop) : (term287 A s) = (term236 A s).
Proof. exact (eq_refl (term287 A s)). Qed.
Lemma lem4076318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4076319 {A : Type'} (s : A -> Prop) : (term288 A s) = (term283 A s).
Proof. exact (MK_COMB (@lem4076318) (@lem4076317 A s)). Qed.
Lemma lem4076320 {A : Type'} (s : A -> Prop) : (term288 A s) = (term282 A s).
Proof. exact (TRANS (@lem4076319 A s) (@lem4076314 A s)). Qed.
Lemma lem4076321 {A : Type'} : (term289 A) = (term290 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076320 A s)). Qed.
Lemma lem4076322 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4076323 {A : Type'} : (term286 A) = (term291 A).
Proof. exact (MK_COMB (@lem4076322 A) (@lem4076321 A)). Qed.
Lemma lem4076424 {A : Type'} : (term254 A) = (term291 A).
Proof. exact (TRANS (@lem4076316 A) (@lem4076323 A)). Qed.
Lemma lem4076425 {A : Type'} (h1 : term254 A) : term291 A.
Proof. exact (EQ_MP (@lem4076424 A) (@lem4076284 A h1)). Qed.
Lemma lem4076426 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076427 {A : Type'} : (term264 A) = (term264 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076426 A s)). Qed.
Lemma lem4076428 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076437 {A : Type'} : (term255 A) = (term255 A).
Proof. exact (MK_COMB (@lem4076428 A) (@lem4076427 A)). Qed.
Lemma lem4076438 {A : Type'} (h1 : term255 A) : term255 A.
Proof. exact (EQ_MP (@lem4076437 A) (@lem4076285 A h1)). Qed.
Lemma lem4076439 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term282 A s.
Proof. exact (h1). Qed.
Lemma lem4076444 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076445 {A : Type'} : (term264 A) = (term264 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076444 A s)). Qed.
Lemma lem4076446 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076447 {A : Type'} : (term255 A) = (term255 A).
Proof. exact (MK_COMB (@lem4076446 A) (@lem4076445 A)). Qed.
Lemma lem4076448 {A : Type'} (h1 : term255 A) : term255 A.
Proof. exact (EQ_MP (@lem4076447 A) (@lem4076438 A h1)). Qed.
Lemma lem4076465 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term269 A s t) = (term269 A s t).
Proof. exact (eq_refl (term269 A s t)). Qed.
Lemma lem4076466 {A : Type'} (s : A -> Prop) : (term277 A s) = (term277 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076465 A s t)). Qed.
Lemma lem4076467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076468 {A : Type'} (s : A -> Prop) : (term278 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem4076467 A) (@lem4076466 A s)). Qed.
Lemma lem4076487 {A : Type'} (s : A -> Prop) : (term280 A s) = (term280 A s).
Proof. exact (eq_refl (term280 A s)). Qed.
Lemma lem4076488 {A : Type'} (s : A -> Prop) : (term282 A s) = (term282 A s).
Proof. exact (MK_COMB (@lem4076487 A s) (@lem4076468 A s)). Qed.
Lemma lem4076489 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term282 A s.
Proof. exact (EQ_MP (@lem4076488 A s) (@lem4076439 A s h1)). Qed.
Lemma lem4076490 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term278 A s.
Proof. exact (proj2 (@lem4076489 A s h1)). Qed.
Lemma lem4076491 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term266 A s.
Proof. exact (proj1 (@lem4076489 A s h1)). Qed.
Lemma lem4076495 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076496 {A : Type'} : (term264 A) = (term264 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076495 A s)). Qed.
Lemma lem4076497 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076499 {A : Type'} : (term255 A) = (term255 A).
Proof. exact (MK_COMB (@lem4076497 A) (@lem4076496 A)). Qed.
Lemma lem4076500 {A : Type'} (h1 : term255 A) : term255 A.
Proof. exact (EQ_MP (@lem4076499 A) (@lem4076448 A h1)). Qed.
Lemma lem4076508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term269 A s t) = (term269 A s t).
Proof. exact (eq_refl (term269 A s t)). Qed.
Lemma lem4076509 {A : Type'} (s : A -> Prop) : (term277 A s) = (term277 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076508 A s t)). Qed.
Lemma lem4076510 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076512 {A : Type'} (s : A -> Prop) : (term278 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem4076510 A) (@lem4076509 A s)). Qed.
Lemma lem4076513 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term278 A s.
Proof. exact (EQ_MP (@lem4076512 A s) (@lem4076490 A s h1)). Qed.
Lemma lem4076519 {A : Type'} (s : A -> Prop) : (@SUBSET A (@EMPTY A) s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (eq_refl (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076520 {A : Type'} : (term264 A) = (term264 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076519 A s)). Qed.
Lemma lem4076521 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076523 {A : Type'} : (term255 A) = (term255 A).
Proof. exact (MK_COMB (@lem4076521 A) (@lem4076520 A)). Qed.
Lemma lem4076524 {A : Type'} (h1 : term255 A) : term255 A.
Proof. exact (EQ_MP (@lem4076523 A) (@lem4076448 A h1)). Qed.
Lemma lem4076532 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term269 A s t) = (term269 A s t).
Proof. exact (eq_refl (term269 A s t)). Qed.
Lemma lem4076533 {A : Type'} (s : A -> Prop) : (term277 A s) = (term277 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4076532 A s t)). Qed.
Lemma lem4076534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076536 {A : Type'} (s : A -> Prop) : (term278 A s) = (term278 A s).
Proof. exact (MK_COMB (@lem4076534 A) (@lem4076533 A s)). Qed.
Lemma lem4076537 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term278 A s.
Proof. exact (EQ_MP (@lem4076536 A s) (@lem4076490 A s h1)). Qed.
Lemma lem4076542 {A : Type'} (_47869 : A -> Prop) (h1 : term255 A) : term292 A _47869.
Proof. exact (@lem4076500 A h1 _47869). Qed.
Lemma lem4076543 {A : Type'} (_47869 : A -> Prop) : (term292 A _47869) = (@SUBSET A (@EMPTY A) _47869).
Proof. exact (eq_refl (term292 A _47869)). Qed.
Lemma lem4076545 {A : Type'} (_47870 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term293 A s _47870.
Proof. exact (@lem4076513 A s h1 _47870). Qed.
Lemma lem4076546 {A : Type'} (s : A -> Prop) (_47870 : A -> Prop) : (term293 A s _47870) = (term269 A s _47870).
Proof. exact (eq_refl (term293 A s _47870)). Qed.
Lemma lem4076548 {A : Type'} (_47871 : A -> Prop) (h1 : term255 A) : term292 A _47871.
Proof. exact (@lem4076524 A h1 _47871). Qed.
Lemma lem4076549 {A : Type'} (_47871 : A -> Prop) : (term292 A _47871) = (@SUBSET A (@EMPTY A) _47871).
Proof. exact (eq_refl (term292 A _47871)). Qed.
Lemma lem4076551 {A : Type'} (_47872 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term293 A s _47872.
Proof. exact (@lem4076537 A s h1 _47872). Qed.
Lemma lem4076552 {A : Type'} (s : A -> Prop) (_47872 : A -> Prop) : (term293 A s _47872) = (term269 A s _47872).
Proof. exact (eq_refl (term293 A s _47872)). Qed.
Lemma lem4076561 {A : Type'} (_47870 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term269 A s _47870.
Proof. exact (EQ_MP (@lem4076546 A s _47870) (@lem4076545 A _47870 s h1)). Qed.
Lemma lem4076571 {A : Type'} (_47872 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term269 A s _47872.
Proof. exact (EQ_MP (@lem4076552 A s _47872) (@lem4076551 A _47872 s h1)). Qed.
Lemma lem4076608 {A : Type'} (_47869 : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) _47869.
Proof. exact (EQ_MP (@lem4076543 A _47869) (@lem4076542 A _47869 h1)). Qed.
Lemma lem4076609 {A : Type'} (_47869 : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) _47869.
Proof. exact (@lem4076608 A _47869 h1). Qed.
Lemma lem4076610 {A : Type'} (s : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) s.
Proof. exact (@lem4076609 A s h1). Qed.
Lemma lem4076611 {A : Type'} (s : A -> Prop) (h1 : term255 A) : term294 A s.
Proof. exact (fun h0 : term295 A s => @lem4076610 A s h1). Qed.
Lemma lem4076613 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4076614 {A : Type'} (s : A -> Prop) : (term294 A s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (@lem4076613 (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076615 {A : Type'} (s : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) s.
Proof. exact (EQ_MP (@lem4076614 A s) (@lem4076611 A s h1)). Qed.
Lemma lem4076617 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4076618 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4076617 A x). Qed.
Lemma lem4076619 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (@lem4076618 A (@EMPTY A)). Qed.
Lemma lem4076620 {A : Type'} : term297 A.
Proof. exact (fun h0 : term298 A => @lem4076619 A). Qed.
Lemma lem4076622 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4076623 {A : Type'} : (term297 A) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (@lem4076622 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4076624 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4076623 A) (@lem4076620 A)). Qed.
Lemma lem4076626 (a : Prop) (b : Prop) : (term299 a b) = (term300 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4076627 {A : Type'} (s : A -> Prop) (_47870 : A -> Prop) : (term269 A s _47870) = (term268 A s _47870).
Proof. exact (@lem4076626 (@SUBSET A _47870 s) (_47870 = (@EMPTY A))). Qed.
Lemma lem4076629 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4076630 {A : Type'} (s : A -> Prop) (_47870 : A -> Prop) : (term268 A s _47870) = (term301 A s _47870).
Proof. exact (@lem4076629 (term229 A s _47870)). Qed.
Lemma lem4076631 {A : Type'} (s : A -> Prop) (_47870 : A -> Prop) : (term269 A s _47870) = (term301 A s _47870).
Proof. exact (TRANS (@lem4076627 A s _47870) (@lem4076630 A s _47870)). Qed.
Lemma lem4076633 {A : Type'} (s : A -> Prop) (h1 : term255 A) : term302 A s.
Proof. exact (conj (@lem4076615 A s h1) (@lem4076624 A)). Qed.
Lemma lem4076635 {A : Type'} (_47870 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term301 A s _47870.
Proof. exact (EQ_MP (@lem4076631 A s _47870) (@lem4076561 A _47870 s h1)). Qed.
Lemma lem4076636 {A : Type'} (_47870 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term301 A s _47870.
Proof. exact (@lem4076635 A _47870 s h1). Qed.
Lemma lem4076637 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term303 A s.
Proof. exact (@lem4076636 A (@EMPTY A) s h1). Qed.
Lemma lem4076640 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (@lem4076637 A s h2 (@lem4076633 A s h1)). Qed.
Lemma lem4076641 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : term304.
Proof. exact (fun h0 : ~ False => @lem4076640 A s h1 h2). Qed.
Lemma lem4076643 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4076644 : term304 = False.
Proof. exact (@lem4076643 False). Qed.
Lemma lem4076645 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (EQ_MP (@lem4076644) (@lem4076641 A s h1 h2)). Qed.
Lemma lem4076705 {A : Type'} (_47871 : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) _47871.
Proof. exact (EQ_MP (@lem4076549 A _47871) (@lem4076548 A _47871 h1)). Qed.
Lemma lem4076706 {A : Type'} (_47871 : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) _47871.
Proof. exact (@lem4076705 A _47871 h1). Qed.
Lemma lem4076707 {A : Type'} (s : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) s.
Proof. exact (@lem4076706 A s h1). Qed.
Lemma lem4076708 {A : Type'} (s : A -> Prop) (h1 : term255 A) : term294 A s.
Proof. exact (fun h0 : term295 A s => @lem4076707 A s h1). Qed.
Lemma lem4076710 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4076711 {A : Type'} (s : A -> Prop) : (term294 A s) = (@SUBSET A (@EMPTY A) s).
Proof. exact (@lem4076710 (@SUBSET A (@EMPTY A) s)). Qed.
Lemma lem4076712 {A : Type'} (s : A -> Prop) (h1 : term255 A) : @SUBSET A (@EMPTY A) s.
Proof. exact (EQ_MP (@lem4076711 A s) (@lem4076708 A s h1)). Qed.
Lemma lem4076714 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4076715 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4076714 A x). Qed.
Lemma lem4076716 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (@lem4076715 A (@EMPTY A)). Qed.
Lemma lem4076717 {A : Type'} : term297 A.
Proof. exact (fun h0 : term298 A => @lem4076716 A). Qed.
Lemma lem4076719 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4076720 {A : Type'} : (term297 A) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (@lem4076719 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem4076721 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (EQ_MP (@lem4076720 A) (@lem4076717 A)). Qed.
Lemma lem4076723 (a : Prop) (b : Prop) : (term299 a b) = (term300 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4076724 {A : Type'} (s : A -> Prop) (_47872 : A -> Prop) : (term269 A s _47872) = (term268 A s _47872).
Proof. exact (@lem4076723 (@SUBSET A _47872 s) (_47872 = (@EMPTY A))). Qed.
Lemma lem4076726 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4076727 {A : Type'} (s : A -> Prop) (_47872 : A -> Prop) : (term268 A s _47872) = (term301 A s _47872).
Proof. exact (@lem4076726 (term229 A s _47872)). Qed.
Lemma lem4076728 {A : Type'} (s : A -> Prop) (_47872 : A -> Prop) : (term269 A s _47872) = (term301 A s _47872).
Proof. exact (TRANS (@lem4076724 A s _47872) (@lem4076727 A s _47872)). Qed.
Lemma lem4076730 {A : Type'} (s : A -> Prop) (h1 : term255 A) : term302 A s.
Proof. exact (conj (@lem4076712 A s h1) (@lem4076721 A)). Qed.
Lemma lem4076732 {A : Type'} (_47872 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term301 A s _47872.
Proof. exact (EQ_MP (@lem4076728 A s _47872) (@lem4076571 A _47872 s h1)). Qed.
Lemma lem4076733 {A : Type'} (_47872 : A -> Prop) (s : A -> Prop) (h1 : term282 A s) : term301 A s _47872.
Proof. exact (@lem4076732 A _47872 s h1). Qed.
Lemma lem4076734 {A : Type'} (s : A -> Prop) (h1 : term282 A s) : term303 A s.
Proof. exact (@lem4076733 A (@EMPTY A) s h1). Qed.
Lemma lem4076737 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (@lem4076734 A s h2 (@lem4076730 A s h1)). Qed.
Lemma lem4076738 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : term304.
Proof. exact (fun h0 : ~ False => @lem4076737 A s h1 h2). Qed.
Lemma lem4076740 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4076741 : term304 = False.
Proof. exact (@lem4076740 False). Qed.
Lemma lem4076742 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (EQ_MP (@lem4076741) (@lem4076738 A s h1 h2)). Qed.
Lemma lem4076743 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : (term255 A) = False.
Proof. exact (prop_ext (fun h3 : term255 A => @lem4076742 A s h1 h2) (fun h3 : False => @lem4076524 A h1)). Qed.
Lemma lem4076744 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (EQ_MP (@lem4076743 A s h1 h2) (@lem4076524 A h1)). Qed.
Lemma lem4076745 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : (term255 A) = False.
Proof. exact (prop_ext (fun h3 : term255 A => @lem4076645 A s h1 h2) (fun h3 : False => @lem4076500 A h1)). Qed.
Lemma lem4076746 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (EQ_MP (@lem4076745 A s h1 h2) (@lem4076500 A h1)). Qed.
Lemma lem4076747 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (or_elim (@lem4076491 A s h2) (fun h0 : term305 A s => @lem4076746 A s h1 h2) (fun h0 : term267 A s => @lem4076744 A s h1 h2)). Qed.
Lemma lem4076748 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : (term282 A s) = False.
Proof. exact (prop_ext (fun h3 : term282 A s => @lem4076747 A s h1 h2) (fun h3 : False => @lem4076489 A s h2)). Qed.
Lemma lem4076749 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (EQ_MP (@lem4076748 A s h1 h2) (@lem4076489 A s h2)). Qed.
Lemma lem4076750 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : (term255 A) = False.
Proof. exact (prop_ext (fun h3 : term255 A => @lem4076749 A s h1 h2) (fun h3 : False => @lem4076448 A h1)). Qed.
Lemma lem4076751 {A : Type'} (s : A -> Prop) (h1 : term255 A) (h2 : term282 A s) : False.
Proof. exact (EQ_MP (@lem4076750 A s h1 h2) (@lem4076448 A h1)). Qed.
Lemma lem4076752 {A : Type'} (h1 : term255 A) (h2 : term254 A) : False.
Proof. exact (ex_elim (@lem4076425 A h2) (fun s : A -> Prop => fun h0 : term290 A s => @lem4076751 A s h1 h0)). Qed.
Lemma lem4076753 {A : Type'} (h1 : term255 A) (h2 : term254 A) : (term255 A) = False.
Proof. exact (prop_ext (fun h3 : term255 A => @lem4076752 A h1 h2) (fun h3 : False => @lem4076438 A h1)). Qed.
Lemma lem4076754 {A : Type'} (h1 : term255 A) (h2 : term254 A) : False.
Proof. exact (EQ_MP (@lem4076753 A h1 h2) (@lem4076438 A h1)). Qed.
Lemma lem4076755 {A : Type'} (h1 : term254 A) : term260 A.
Proof. exact (fun h0 : term255 A => @lem4076754 A h0 h1). Qed.
Lemma lem4076756 {A : Type'} : (term260 A) = (term261 A).
Proof. exact (@lem69 (term255 A)). Qed.
Lemma lem4076757 {A : Type'} (h1 : term254 A) : term261 A.
Proof. exact (EQ_MP (@lem4076756 A) (@lem4076755 A h1)). Qed.
Lemma lem4076758 {A : Type'} : term263 A.
Proof. exact (fun h0 : term254 A => @lem4076757 A h0). Qed.
Lemma lem4076759 {A : Type'} : term256 A.
Proof. exact (EQ_MP (@lem4076283 A) (@lem4076758 A)). Qed.
Lemma lem4076761 {A : Type'} : term256 A.
Proof. exact (@lem4076148 A (@lem4076759 A)). Qed.
Lemma lem4076762 {A : Type'} (h1 : term254 A) : term260 A.
Proof. exact (@lem4076761 A (@lem4076130 A h1)). Qed.
Lemma lem4076763 {A : Type'} (h1 : term254 A) : False.
Proof. exact (@lem4076762 A h1 (@lem4076131 A)). Qed.
Lemma lem4076764 {A : Type'} (h1 : term254 A) : (term254 A) = False.
Proof. exact (prop_ext (fun h2 : term254 A => @lem4076763 A h1) (fun h2 : False => @lem4076130 A h1)). Qed.
Lemma lem4076765 {A : Type'} (h1 : term254 A) : False.
Proof. exact (EQ_MP (@lem4076764 A h1) (@lem4076130 A h1)). Qed.
Lemma lem4076766 {A : Type'} : term253 A.
Proof. exact (fun h0 : term254 A => @lem4076765 A h0). Qed.
Lemma lem4076767 {A : Type'} : term239 A.
Proof. exact (EQ_MP (@lem4076129 A) (@lem4076766 A)). Qed.
Lemma lem4076769 {A : Type'} (P : type686 A) : term188 A P.
Proof. exact (EQ_MP (@lem4075987 A P) (@lem4075986 A P)). Qed.
Lemma lem4076770 {A : Type'} (P : type686 A) : term188 A P.
Proof. exact (@lem4076769 A P). Qed.
Lemma lem4076771 {A : Type'} (n : nat) : term306 A n.
Proof. exact (@lem4076770 A (term250 A n)). Qed.
Lemma lem4076772 {A : Type'} (n : nat) : (term307 A n) = (term308 A n).
Proof. exact (eq_refl (term307 A n)). Qed.
Lemma lem4076773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4076774 {A : Type'} (n : nat) : (term309 A n) = (term310 A n).
Proof. exact (MK_COMB (@lem4076773) (@lem4076772 A n)). Qed.
Lemma lem4076775 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term311 A n a s) = (term312 A a s n).
Proof. exact (eq_refl (term311 A n a s)). Qed.
Lemma lem4076776 {A : Type'} (a : A) (s : A -> Prop) : (term313 A a s) = (term313 A a s).
Proof. exact (eq_refl (term313 A a s)). Qed.
Lemma lem4076777 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term314 A n a s) = (term315 A a s n).
Proof. exact (MK_COMB (@lem4076776 A a s) (@lem4076775 A a s n)). Qed.
Lemma lem4076778 {A : Type'} (a : A) (n : nat) : (term316 A n a) = (term317 A a n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076777 A a s n)). Qed.
Lemma lem4076779 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076780 {A : Type'} (a : A) (n : nat) : (term318 A n a) = (term319 A a n).
Proof. exact (MK_COMB (@lem4076779 A) (@lem4076778 A a n)). Qed.
Lemma lem4076781 {A : Type'} (n : nat) : (term320 A n) = (term321 A n).
Proof. exact (fun_ext (fun a : A => @lem4076780 A a n)). Qed.
Lemma lem4076782 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4076783 {A : Type'} (n : nat) : (term322 A n) = (term323 A n).
Proof. exact (MK_COMB (@lem4076782 A) (@lem4076781 A n)). Qed.
Lemma lem4076784 {A : Type'} (n : nat) : (term324 A n) = (term325 A n).
Proof. exact (MK_COMB (@lem4076774 A n) (@lem4076783 A n)). Qed.
Lemma lem4076785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4076786 {A : Type'} (n : nat) : (term326 A n) = (term327 A n).
Proof. exact (MK_COMB (@lem4076785) (@lem4076784 A n)). Qed.
Lemma lem4076787 {A : Type'} (s : A -> Prop) (n : nat) : (term328 A n s) = (term248 A s n).
Proof. exact (eq_refl (term328 A n s)). Qed.
Lemma lem4076788 {A : Type'} (n : nat) : (term329 A n) = (term250 A n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4076787 A s n)). Qed.
Lemma lem4076789 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4076790 {A : Type'} (n : nat) : (term330 A n) = (term251 A n).
Proof. exact (MK_COMB (@lem4076789 A) (@lem4076788 A n)). Qed.
Lemma lem4076791 {A : Type'} (n : nat) : (term306 A n) = (term331 A n).
Proof. exact (MK_COMB (@lem4076786 A n) (@lem4076790 A n)). Qed.
Lemma lem4076792 {A : Type'} (n : nat) : term331 A n.
Proof. exact (EQ_MP (@lem4076791 A n) (@lem4076771 A n)). Qed.
Lemma lem4076800 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4075971 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4076801 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem4076800 A). Qed.
Lemma lem4076802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4076803 {A : Type'} : (term332 A) = (imp True).
Proof. exact (MK_COMB (@lem4076802) (@lem4076801 A)). Qed.
Lemma lem4076805 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4076806 (n : nat) : (term7 n) = (term7 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem4076807 {A : Type'} (n : nat) : (term333 A n) = (term9 n).
Proof. exact (MK_COMB (@lem4076806 n) (@lem4076805 A)). Qed.
Lemma lem4076809 (n : nat) : (term9 n) = False.
Proof. exact (@lem4075959 n (@lem4075958 n)). Qed.
Lemma lem4076810 {A : Type'} (n : nat) : (term333 A n) = False.
Proof. exact (TRANS (@lem4076807 A n) (@lem4076809 n)). Qed.
Lemma lem4076811 {A : Type'} (n : nat) : (term334 A n) = (True -> False).
Proof. exact (MK_COMB (@lem4076803 A) (@lem4076810 A n)). Qed.
Lemma lem4076813 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4076814 : (True -> False) = False.
Proof. exact (@lem4076813 False). Qed.
Lemma lem4076815 {A : Type'} (n : nat) : (term334 A n) = False.
Proof. exact (TRANS (@lem4076811 A n) (@lem4076814)). Qed.
Lemma lem4076816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4076817 {A : Type'} (n : nat) : (term335 A n) = (imp False).
Proof. exact (MK_COMB (@lem4076816) (@lem4076815 A n)). Qed.
Lemma lem4076834 {A : Type'} (n : nat) : (term336 A n) = (term336 A n).
Proof. exact (eq_refl (term336 A n)). Qed.
Lemma lem4076835 {A : Type'} (n : nat) : (term308 A n) = (term337 A n).
Proof. exact (MK_COMB (@lem4076817 A n) (@lem4076834 A n)). Qed.
Lemma lem4076837 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4076838 {A : Type'} (n : nat) : (term337 A n) = True.
Proof. exact (@lem4076837 (term336 A n)). Qed.
Lemma lem4076839 {A : Type'} (n : nat) : (term308 A n) = True.
Proof. exact (TRANS (@lem4076835 A n) (@lem4076838 A n)). Qed.
Lemma lem4076840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4076841 {A : Type'} (n : nat) : (term310 A n) = (and True).
Proof. exact (MK_COMB (@lem4076840) (@lem4076839 A n)). Qed.
Lemma lem4076872 {A : Type'} (n : nat) : (term323 A n) = (term323 A n).
Proof. exact (eq_refl (term323 A n)). Qed.
Lemma lem4076873 {A : Type'} (n : nat) : (term325 A n) = (term338 A n).
Proof. exact (MK_COMB (@lem4076841 A n) (@lem4076872 A n)). Qed.
Lemma lem4076875 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4076876 {A : Type'} (n : nat) : (term338 A n) = (term323 A n).
Proof. exact (@lem4076875 (term323 A n)). Qed.
Lemma lem4076907 {A : Type'} (n : nat) : (term325 A n) = (term323 A n).
Proof. exact (TRANS (@lem4076873 A n) (@lem4076876 A n)). Qed.
Lemma lem4076908 {A : Type'} (n : nat) : (term323 A n) = (term325 A n).
Proof. exact (SYM (@lem4076907 A n)). Qed.
Lemma lem4076909 {A : Type'} (a : A) (s : A -> Prop) (h1 : term339 A a s) : term339 A a s.
Proof. exact (h1). Qed.
Lemma lem4076910 (m : nat) : term340 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem4076911 (m : nat) : (term340 m) = (term341 m).
Proof. exact (eq_refl (term340 m)). Qed.
Lemma lem4076912 (m : nat) : term341 m.
Proof. exact (EQ_MP (@lem4076911 m) (@lem4076910 m)). Qed.
Lemma lem4076913 (m : nat) (n : nat) : term342 m n.
Proof. exact (@lem4076912 m n). Qed.
Lemma lem4076914 (m : nat) (n : nat) : (term342 m n) = ((term343 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term342 m n)). Qed.
Lemma lem4076916 {A : Type'} (s : A -> Prop) : term344 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem4076917 {A : Type'} (s : A -> Prop) : (term344 A s) = (term345 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem4076918 {A : Type'} (s : A -> Prop) : term345 A s.
Proof. exact (EQ_MP (@lem4076917 A s) (@lem4076916 A s)). Qed.
Lemma lem4076919 {A : Type'} (s : A -> Prop) (x : A) : term346 A s x.
Proof. exact (@lem4076918 A s x). Qed.
Lemma lem4076920 {A : Type'} (x : A) (s : A -> Prop) : (term346 A s x) = ((term347 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term346 A s x)). Qed.
Lemma lem4076922 {A : Type'} : term348 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4076923 {A : Type'} (x : A) : term349 A x.
Proof. exact (@lem4076922 A x). Qed.
Lemma lem4076924 {A : Type'} (x : A) : (term349 A x) = (term350 A x).
Proof. exact (eq_refl (term349 A x)). Qed.
Lemma lem4076925 {A : Type'} (x : A) : term350 A x.
Proof. exact (EQ_MP (@lem4076924 A x) (@lem4076923 A x)). Qed.
Lemma lem4076926 {A : Type'} (x : A) (s : A -> Prop) : term351 A x s.
Proof. exact (@lem4076925 A x s). Qed.
Lemma lem4076927 {A : Type'} (x : A) (s : A -> Prop) : (term351 A x s) = (term352 A x s).
Proof. exact (eq_refl (term351 A x s)). Qed.
Lemma lem4076928 {A : Type'} (x : A) (s : A -> Prop) : term352 A x s.
Proof. exact (EQ_MP (@lem4076927 A x s) (@lem4076926 A x s)). Qed.
Lemma lem4076929 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4076930 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term353 A x s) = (term354 A x s).
Proof. exact (@lem4076928 A x s (@lem4076929 A s h1)). Qed.
Lemma lem4076949 {A : Type'} (a : A) (s : A -> Prop) : term355 A a s.
Proof. exact (@lem82 (@IN A a s)). Qed.
Lemma lem4076954 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term356 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4076955 (p : Prop) (q : Prop) (p' : Prop) : term357 p q p'.
Proof. exact (fun q' : Prop => @lem4076954 p q p' q'). Qed.
Lemma lem4076956 (p : Prop) (q : Prop) : term358 p q.
Proof. exact (fun p' : Prop => @lem4076955 p q p'). Qed.
Lemma lem4076957 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term359 A a s n.
Proof. exact (@lem4076956 (term360 A n a s) (term361 A a s n)). Qed.
Lemma lem4076958 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (p' : Prop) : term362 A a s n p'.
Proof. exact (@lem4076957 A a s n p'). Qed.
Lemma lem4076959 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (p' : Prop) : (term362 A a s n p') = (term363 A a s n p').
Proof. exact (eq_refl (term362 A a s n p')). Qed.
Lemma lem4076960 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (p' : Prop) : term363 A a s n p'.
Proof. exact (EQ_MP (@lem4076959 A a s n p') (@lem4076958 A a s n p')). Qed.
Lemma lem4076961 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term364 A a s n p' q'.
Proof. exact (@lem4076960 A a s n p' q'). Qed.
Lemma lem4076962 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : (term364 A a s n p' q') = (term365 A a s n p' q').
Proof. exact (eq_refl (term364 A a s n p' q')). Qed.
Lemma lem4076963 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (p' : Prop) (q' : Prop) : term365 A a s n p' q'.
Proof. exact (EQ_MP (@lem4076962 A a s n p' q') (@lem4076961 A a s n p' q')). Qed.
Lemma lem4076967 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term356 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4076968 (p : Prop) (q : Prop) (p' : Prop) : term357 p q p'.
Proof. exact (fun q' : Prop => @lem4076967 p q p' q'). Qed.
Lemma lem4076969 (p : Prop) (q : Prop) : term358 p q.
Proof. exact (fun p' : Prop => @lem4076968 p q p'). Qed.
Lemma lem4076970 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : term366 A n a s.
Proof. exact (@lem4076969 (term347 A a s) (term367 A n a s)). Qed.
Lemma lem4076971 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (p' : Prop) : term368 A n a s p'.
Proof. exact (@lem4076970 A n a s p'). Qed.
Lemma lem4076972 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (p' : Prop) : (term368 A n a s p') = (term369 A n a s p').
Proof. exact (eq_refl (term368 A n a s p')). Qed.
Lemma lem4076973 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (p' : Prop) : term369 A n a s p'.
Proof. exact (EQ_MP (@lem4076972 A n a s p') (@lem4076971 A n a s p')). Qed.
Lemma lem4076974 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term370 A n a s p' q'.
Proof. exact (@lem4076973 A n a s p' q'). Qed.
Lemma lem4076975 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term370 A n a s p' q') = (term371 A n a s p' q').
Proof. exact (eq_refl (term370 A n a s p' q')). Qed.
Lemma lem4076976 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term371 A n a s p' q'.
Proof. exact (EQ_MP (@lem4076975 A n a s p' q') (@lem4076974 A n a s p' q')). Qed.
Lemma lem4076978 {A : Type'} (x : A) (s : A -> Prop) : (term347 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4076920 A x s) (@lem4076919 A s x)). Qed.
Lemma lem4076979 {A : Type'} (x : A) (s : A -> Prop) : (term347 A x s) = (@FINITE A s).
Proof. exact (@lem4076978 A x s). Qed.
Lemma lem4076980 {A : Type'} (a : A) (s : A -> Prop) : (term347 A a s) = (@FINITE A s).
Proof. exact (@lem4076979 A a s). Qed.
Lemma lem4076981 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (q' : Prop) : term372 A n a s q'.
Proof. exact (@lem4076976 A n a s (@FINITE A s) q'). Qed.
Lemma lem4076982 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (q' : Prop) : term373 A n a s q'.
Proof. exact (@lem4076981 A n a s q' (@lem4076980 A a s)). Qed.
Lemma lem4076983 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4076984 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4076987 {A : Type'} (x : A) (s : A -> Prop) : term352 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4076930 A x s h0). Qed.
Lemma lem4076988 {A : Type'} (x : A) (s : A -> Prop) : term352 A x s.
Proof. exact (@lem4076987 A x s). Qed.
Lemma lem4076989 {A : Type'} (a : A) (s : A -> Prop) : term352 A a s.
Proof. exact (@lem4076988 A a s). Qed.
Lemma lem4076991 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4076984 A s) (@lem4076983 A s h1)). Qed.
Lemma lem4076992 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4076991 A s h1)). Qed.
Lemma lem4076993 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4076992 A s h1) (@lem0)). Qed.
Lemma lem4076994 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) : (term353 A a s) = (term354 A a s).
Proof. exact (@lem4076989 A a s (@lem4076993 A s h1)). Qed.
Lemma lem4076996 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term374 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4076997 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term375 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4076996 _2963 g t e g' t' e'). Qed.
Lemma lem4076998 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term376 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4076997 _2963 g t e g' t'). Qed.
Lemma lem4076999 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term377 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4076998 _2963 g t e g'). Qed.
Lemma lem4077000 (g : Prop) (t : nat) (e : nat) : term378 g t e.
Proof. exact (@lem4076999 nat g t e). Qed.
Lemma lem4077001 {A : Type'} (a : A) (s : A -> Prop) : term379 A a s.
Proof. exact (@lem4077000 (@IN A a s) (@CARD A s) (term380 A s)). Qed.
Lemma lem4077002 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) : term381 A a s g'.
Proof. exact (@lem4077001 A a s g'). Qed.
Lemma lem4077003 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) : (term381 A a s g') = (term382 A a s g').
Proof. exact (eq_refl (term381 A a s g')). Qed.
Lemma lem4077004 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) : term382 A a s g'.
Proof. exact (EQ_MP (@lem4077003 A a s g') (@lem4077002 A a s g')). Qed.
Lemma lem4077005 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term383 A a s g' t'.
Proof. exact (@lem4077004 A a s g' t'). Qed.
Lemma lem4077006 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term383 A a s g' t') = (term384 A a s g' t').
Proof. exact (eq_refl (term383 A a s g' t')). Qed.
Lemma lem4077007 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term384 A a s g' t'.
Proof. exact (EQ_MP (@lem4077006 A a s g' t') (@lem4077005 A a s g' t')). Qed.
Lemma lem4077008 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term385 A a s g' t' e'.
Proof. exact (@lem4077007 A a s g' t' e'). Qed.
Lemma lem4077009 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term385 A a s g' t' e') = (term386 A a s g' t' e').
Proof. exact (eq_refl (term385 A a s g' t' e')). Qed.
Lemma lem4077010 {A : Type'} (a : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term386 A a s g' t' e'.
Proof. exact (EQ_MP (@lem4077009 A a s g' t' e') (@lem4077008 A a s g' t' e')). Qed.
Lemma lem4077012 {A : Type'} (a : A) (s : A -> Prop) (h1 : term339 A a s) : (@IN A a s) = False.
Proof. exact (@lem4076949 A a s (@lem4076909 A a s h1)). Qed.
Lemma lem4077013 {A : Type'} (a : A) (s : A -> Prop) (t' : nat) (e' : nat) : term387 A a s t' e'.
Proof. exact (@lem4077010 A a s False t' e'). Qed.
Lemma lem4077014 {A : Type'} (t' : nat) (e' : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : term388 A a s t' e'.
Proof. exact (@lem4077013 A a s t' e' (@lem4077012 A a s h1)). Qed.
Lemma lem4077018 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem4077019 {A : Type'} (s : A -> Prop) : term389 A s.
Proof. exact (fun h0 : False => @lem4077018 A s). Qed.
Lemma lem4077020 {A : Type'} (e' : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : term390 A a s e'.
Proof. exact (@lem4077014 A (@CARD A s) e' a s h1). Qed.
Lemma lem4077021 {A : Type'} (e' : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : term391 A a s e'.
Proof. exact (@lem4077020 A e' a s h1 (@lem4077019 A s)). Qed.
Lemma lem4077027 {A : Type'} (s : A -> Prop) : (term380 A s) = (term380 A s).
Proof. exact (eq_refl (term380 A s)). Qed.
Lemma lem4077028 {A : Type'} (s : A -> Prop) : term392 A s.
Proof. exact (fun h0 : ~ False => @lem4077027 A s). Qed.
Lemma lem4077029 {A : Type'} (a : A) (s : A -> Prop) (h1 : term339 A a s) : term393 A a s.
Proof. exact (@lem4077021 A (term380 A s) a s h1). Qed.
Lemma lem4077030 {A : Type'} (a : A) (s : A -> Prop) (h1 : term339 A a s) : (term354 A a s) = (term394 A s).
Proof. exact (@lem4077029 A a s h1 (@lem4077028 A s)). Qed.
Lemma lem4077032 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4077033 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4077032 nat t1 t2). Qed.
Lemma lem4077034 {A : Type'} (s : A -> Prop) : (term394 A s) = (term380 A s).
Proof. exact (@lem4077033 (@CARD A s) (term380 A s)). Qed.
Lemma lem4077035 {A : Type'} (a : A) (s : A -> Prop) (h1 : term339 A a s) : (term354 A a s) = (term380 A s).
Proof. exact (TRANS (@lem4077030 A a s h1) (@lem4077034 A s)). Qed.
Lemma lem4077036 {A : Type'} (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term339 A a s) : (term353 A a s) = (term380 A s).
Proof. exact (TRANS (@lem4076994 A a s h1) (@lem4077035 A a s h2)). Qed.
Lemma lem4077037 (n : nat) : (term7 n) = (term7 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem4077038 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term339 A a s) : (term367 A n a s) = (term395 A n s).
Proof. exact (MK_COMB (@lem4077037 n) (@lem4077036 A a s h1 h2)). Qed.
Lemma lem4077040 (m : nat) (n : nat) : (term343 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem4076914 m n) (@lem4076913 m n)). Qed.
Lemma lem4077041 {A : Type'} (n : nat) (s : A -> Prop) : (term395 A n s) = (term396 A n s).
Proof. exact (@lem4077040 n (@CARD A s)). Qed.
Lemma lem4077042 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term339 A a s) : (term367 A n a s) = (term396 A n s).
Proof. exact (TRANS (@lem4077038 A n a s h1 h2) (@lem4077041 A n s)). Qed.
Lemma lem4077043 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : term397 A a n s.
Proof. exact (fun h0 : @FINITE A s => @lem4077042 A n a s h0 h1). Qed.
Lemma lem4077044 {A : Type'} (a : A) (n : nat) (s : A -> Prop) : term398 A a n s.
Proof. exact (@lem4076982 A n a s (term396 A n s)). Qed.
Lemma lem4077045 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : (term360 A n a s) = (term399 A n s).
Proof. exact (@lem4077044 A a n s (@lem4077043 A n a s h1)). Qed.
Lemma lem4077069 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (q' : Prop) : term400 A a n s q'.
Proof. exact (@lem4076963 A a s n (term399 A n s) q'). Qed.
Lemma lem4077070 {A : Type'} (n : nat) (q' : Prop) (a : A) (s : A -> Prop) (h1 : term339 A a s) : term401 A a n s q'.
Proof. exact (@lem4077069 A a n s q' (@lem4077045 A n a s h1)). Qed.
Lemma lem4077118 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term361 A a s n) = (term361 A a s n).
Proof. exact (eq_refl (term361 A a s n)). Qed.
Lemma lem4077119 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : term402 A a s n.
Proof. exact (fun h0 : term399 A n s => @lem4077118 A a s n). Qed.
Lemma lem4077120 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : term403 A a s n.
Proof. exact (@lem4077070 A n (term361 A a s n) a s h1). Qed.
Lemma lem4077121 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : (term312 A a s n) = (term404 A a s n).
Proof. exact (@lem4077120 A n a s h1 (@lem4077119 A a s n)). Qed.
Lemma lem4077272 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term339 A a s) : (term404 A a s n) = (term312 A a s n).
Proof. exact (SYM (@lem4077121 A n a s h1)). Qed.
Lemma lem4077273 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : term399 A n s.
Proof. exact (h1). Qed.
Lemma lem4077274 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term208 A n) : term405 A n s.
Proof. exact (@lem4076031 A n h1 s). Qed.
Lemma lem4077275 {A : Type'} (s : A -> Prop) (n : nat) : (term405 A n s) = (term406 A s n).
Proof. exact (eq_refl (term405 A n s)). Qed.
Lemma lem4077276 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term208 A n) : term406 A s n.
Proof. exact (EQ_MP (@lem4077275 A s n) (@lem4077274 A s n h1)). Qed.
Lemma lem4077279 {A : Type'} (n : nat) (s : A -> Prop) : (term399 A n s) = ((term399 A n s) = True).
Proof. exact (@lem7 (term399 A n s)). Qed.
Lemma lem4077286 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term399 A n s) = True.
Proof. exact (EQ_MP (@lem4077279 A n s) (@lem4077273 A n s h1)). Qed.
Lemma lem4077287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077288 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term407 A n s) = (imp True).
Proof. exact (MK_COMB (@lem4077287) (@lem4077286 A n s h1)). Qed.
Lemma lem4077295 {A : Type'} (s : A -> Prop) (n : nat) : (term408 A s n) = (term408 A s n).
Proof. exact (eq_refl (term408 A s n)). Qed.
Lemma lem4077296 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term406 A s n) = (term409 A s n).
Proof. exact (MK_COMB (@lem4077288 A n s h1) (@lem4077295 A s n)). Qed.
Lemma lem4077298 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4077299 {A : Type'} (s : A -> Prop) (n : nat) : (term409 A s n) = (term408 A s n).
Proof. exact (@lem4077298 (term408 A s n)). Qed.
Lemma lem4077306 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term406 A s n) = (term408 A s n).
Proof. exact (TRANS (@lem4077296 A n s h1) (@lem4077299 A s n)). Qed.
Lemma lem4077307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077308 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term410 A s n) = (term411 A s n).
Proof. exact (MK_COMB (@lem4077307) (@lem4077306 A n s h1)). Qed.
Lemma lem4077325 {A : Type'} (a : A) (s : A -> Prop) (n : nat) : (term361 A a s n) = (term361 A a s n).
Proof. exact (eq_refl (term361 A a s n)). Qed.
Lemma lem4077326 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term412 A a s n) = (term413 A a s n).
Proof. exact (MK_COMB (@lem4077308 A n s h1) (@lem4077325 A a s n)). Qed.
Lemma lem4077329 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term399 A n s) : (term413 A a s n) = (term412 A a s n).
Proof. exact (SYM (@lem4077326 A a n s h1)). Qed.
Lemma lem4077330 {A : Type'} (s : A -> Prop) (n : nat) (h1 : term408 A s n) : term408 A s n.
Proof. exact (h1). Qed.
Lemma lem4077331 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term414 A s t n) : term414 A s t n.
Proof. exact (h1). Qed.
Lemma lem4077332 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @HAS_SIZE A t n.
Proof. exact (h1). Qed.
Lemma lem4077333 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4077344 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) : term415 A n a s.
Proof. exact (conj (@lem4077273 A n s h2) (@lem4076909 A a s h1)). Qed.
Lemma lem4077345 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @SUBSET A t s) : term416 A t n a s.
Proof. exact (conj (@lem4077333 A t s h3) (@lem4077344 A a n s h1 h2)). Qed.
Lemma lem4077346 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term417 A t n a s.
Proof. exact (conj (@lem4077332 A t n h3) (@lem4077345 A a n t s h1 h2 h4)). Qed.
Lemma lem4077354 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4077355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (@lem4077354 A s t). Qed.
Lemma lem4077356 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term418 A t s).
Proof. exact (@lem4077355 A t s). Qed.
Lemma lem4077363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4077364 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term227 A t s) = (term419 A t s).
Proof. exact (MK_COMB (@lem4077363) (@lem4077356 A t s)). Qed.
Lemma lem4077369 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term415 A n a s) = (term415 A n a s).
Proof. exact (eq_refl (term415 A n a s)). Qed.
Lemma lem4077370 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term416 A t n a s) = (term420 A t n a s).
Proof. exact (MK_COMB (@lem4077364 A t s) (@lem4077369 A n a s)). Qed.
Lemma lem4077373 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4077374 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term417 A t n a s) = (term422 A t n a s).
Proof. exact (MK_COMB (@lem4077373 A t n) (@lem4077370 A t n a s)). Qed.
Lemma lem4077377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077378 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term423 A t n a s) = (term424 A t n a s).
Proof. exact (MK_COMB (@lem4077377) (@lem4077374 A t n a s)). Qed.
Lemma lem4077380 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4077381 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (@lem4077380 A s t). Qed.
Lemma lem4077382 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term425 A t a s) = (term426 A t a s).
Proof. exact (@lem4077381 A (@INSERT A a t) (@INSERT A a s)). Qed.
Lemma lem4077389 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term427 A n t a s) = (term428 A n t a s).
Proof. exact (MK_COMB (@lem4077378 A t n a s) (@lem4077382 A t a s)). Qed.
Lemma lem4077392 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term428 A n t a s) = (term427 A n t a s).
Proof. exact (SYM (@lem4077389 A n t a s)). Qed.
Lemma lem4077406 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4077407 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4077406 A P x). Qed.
Lemma lem4077408 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4077407 A t x). Qed.
Lemma lem4077409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077410 {A : Type'} (t : A -> Prop) (x : A) : (term429 A x t) = (term430 A t x).
Proof. exact (MK_COMB (@lem4077409) (@lem4077408 A t x)). Qed.
Lemma lem4077412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4077413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4077412 A P x). Qed.
Lemma lem4077414 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4077413 A s x). Qed.
Lemma lem4077415 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term431 A t x s) = (term432 A t s x).
Proof. exact (MK_COMB (@lem4077410 A t x) (@lem4077414 A s x)). Qed.
Lemma lem4077418 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term433 A t s) = (term434 A t s).
Proof. exact (fun_ext (fun x : A => @lem4077415 A t s x)). Qed.
Lemma lem4077419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077420 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term418 A t s) = (term435 A t s).
Proof. exact (MK_COMB (@lem4077419 A) (@lem4077418 A t s)). Qed.
Lemma lem4077425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4077426 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term419 A t s) = (term436 A t s).
Proof. exact (MK_COMB (@lem4077425) (@lem4077420 A t s)). Qed.
Lemma lem4077432 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4077433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4077432 A P x). Qed.
Lemma lem4077434 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem4077433 A s a). Qed.
Lemma lem4077435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4077436 {A : Type'} (s : A -> Prop) (a : A) : (term339 A a s) = (term437 A s a).
Proof. exact (MK_COMB (@lem4077435) (@lem4077434 A s a)). Qed.
Lemma lem4077437 {A : Type'} (n : nat) (s : A -> Prop) : (term438 A n s) = (term438 A n s).
Proof. exact (eq_refl (term438 A n s)). Qed.
Lemma lem4077438 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term415 A n a s) = (term439 A n s a).
Proof. exact (MK_COMB (@lem4077437 A n s) (@lem4077436 A s a)). Qed.
Lemma lem4077441 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term420 A t n a s) = (term440 A t n s a).
Proof. exact (MK_COMB (@lem4077426 A t s) (@lem4077438 A n s a)). Qed.
Lemma lem4077444 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4077445 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term422 A t n a s) = (term441 A t n s a).
Proof. exact (MK_COMB (@lem4077444 A t n) (@lem4077441 A t n s a)). Qed.
Lemma lem4077448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077449 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term424 A t n a s) = (term442 A t n s a).
Proof. exact (MK_COMB (@lem4077448) (@lem4077445 A t n s a)). Qed.
Lemma lem4077457 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4077458 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (@lem4077457 A y x s). Qed.
Lemma lem4077459 {A : Type'} (a : A) (x : A) (t : A -> Prop) : (term443 A x a t) = (term444 A a x t).
Proof. exact (@lem4077458 A a x t). Qed.
Lemma lem4077465 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4077466 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4077465 A P x). Qed.
Lemma lem4077467 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4077466 A t x). Qed.
Lemma lem4077468 {A : Type'} (x : A) (a : A) : (term445 A x a) = (term445 A x a).
Proof. exact (eq_refl (term445 A x a)). Qed.
Lemma lem4077469 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term444 A a x t) = (term446 A a t x).
Proof. exact (MK_COMB (@lem4077468 A x a) (@lem4077467 A t x)). Qed.
Lemma lem4077472 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term443 A x a t) = (term446 A a t x).
Proof. exact (TRANS (@lem4077459 A a x t) (@lem4077469 A a t x)). Qed.
Lemma lem4077473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077474 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term447 A x a t) = (term448 A a t x).
Proof. exact (MK_COMB (@lem4077473) (@lem4077472 A a t x)). Qed.
Lemma lem4077476 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4077477 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (@lem4077476 A y x s). Qed.
Lemma lem4077478 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term443 A x a s) = (term444 A a x s).
Proof. exact (@lem4077477 A a x s). Qed.
Lemma lem4077484 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4077485 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4077484 A P x). Qed.
Lemma lem4077486 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4077485 A s x). Qed.
Lemma lem4077487 {A : Type'} (x : A) (a : A) : (term445 A x a) = (term445 A x a).
Proof. exact (eq_refl (term445 A x a)). Qed.
Lemma lem4077488 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term444 A a x s) = (term446 A a s x).
Proof. exact (MK_COMB (@lem4077487 A x a) (@lem4077486 A s x)). Qed.
Lemma lem4077491 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term443 A x a s) = (term446 A a s x).
Proof. exact (TRANS (@lem4077478 A a x s) (@lem4077488 A a s x)). Qed.
Lemma lem4077492 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (x : A) : (term449 A t x a s) = (term450 A t a s x).
Proof. exact (MK_COMB (@lem4077474 A a t x) (@lem4077491 A a s x)). Qed.
Lemma lem4077495 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term451 A t a s) = (term452 A t a s).
Proof. exact (fun_ext (fun x : A => @lem4077492 A t a s x)). Qed.
Lemma lem4077496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077497 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term426 A t a s) = (term453 A t a s).
Proof. exact (MK_COMB (@lem4077496 A) (@lem4077495 A t a s)). Qed.
Lemma lem4077502 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term428 A n t a s) = (term454 A n t a s).
Proof. exact (MK_COMB (@lem4077449 A t n s a) (@lem4077497 A t a s)). Qed.
Lemma lem4077505 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term454 A n t a s) = (term428 A n t a s).
Proof. exact (SYM (@lem4077502 A n t a s)). Qed.
Lemma lem4077507 (p : Prop) : p = (term252 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4077508 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term454 A n t a s) = (term455 A n t a s).
Proof. exact (@lem4077507 (term454 A n t a s)). Qed.
Lemma lem4077509 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term455 A n t a s) = (term454 A n t a s).
Proof. exact (SYM (@lem4077508 A n t a s)). Qed.
Lemma lem4077510 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term456 A n t a s) : term456 A n t a s.
Proof. exact (h1). Qed.
Lemma lem4077513 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term455 A n t a s) : term455 A n t a s.
Proof. exact (h1). Qed.
Lemma lem4077514 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term457 A n t a s.
Proof. exact (fun h0 : term455 A n t a s => @lem4077513 A n t a s h0). Qed.
Lemma lem4077515 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term457 A n t a s) : term457 A n t a s.
Proof. exact (h1). Qed.
Lemma lem4077516 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term455 A n t a s) : term455 A n t a s.
Proof. exact (h1). Qed.
Lemma lem4077517 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term455 A n t a s) (h2 : term457 A n t a s) : term455 A n t a s.
Proof. exact (@lem4077515 A n t a s h2 (@lem4077516 A n t a s h1)). Qed.
Lemma lem4077518 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term455 A n t a s) : term458 A n t a s.
Proof. exact (fun h0 : term457 A n t a s => @lem4077517 A n t a s h1 h0). Qed.
Lemma lem4077519 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term457 A n t a s) : term457 A n t a s.
Proof. exact (h1). Qed.
Lemma lem4077520 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term455 A n t a s) (h2 : term457 A n t a s) : term455 A n t a s.
Proof. exact (@lem4077518 A n t a s h1 (@lem4077519 A n t a s h2)). Qed.
Lemma lem4077521 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term457 A n t a s) : term457 A n t a s.
Proof. exact (fun h0 : term455 A n t a s => @lem4077520 A n t a s h0 h1). Qed.
Lemma lem4077522 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term459 A n t a s.
Proof. exact (fun h0 : term457 A n t a s => @lem4077521 A n t a s h0). Qed.
Lemma lem4077525 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term457 A n t a s.
Proof. exact (@lem4077522 A n t a s (@lem4077514 A n t a s)). Qed.
Lemma lem4077526 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term457 A n t a s.
Proof. exact (@lem4077525 A n t a s). Qed.
Lemma lem4077544 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4077545 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term455 A n t a s) = (term460 A n t a s).
Proof. exact (@lem4077544 (term456 A n t a s)). Qed.
Lemma lem4077547 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4077548 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term460 A n t a s) = (term454 A n t a s).
Proof. exact (@lem4077547 (term454 A n t a s)). Qed.
Lemma lem4077551 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term455 A n t a s) = (term454 A n t a s).
Proof. exact (TRANS (@lem4077545 A n t a s) (@lem4077548 A n t a s)). Qed.
Lemma lem4077576 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term461 A t a s) = (term462 A t a s).
Proof. exact (fun_ext (fun n : nat => @lem4077551 A n t a s)). Qed.
Lemma lem4077577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4077578 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term463 A t a s) = (term464 A t a s).
Proof. exact (MK_COMB (@lem4077577) (@lem4077576 A t a s)). Qed.
Lemma lem4077583 {A : Type'} (a : A) (s : A -> Prop) : (term465 A a s) = (term466 A a s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4077578 A t a s)). Qed.
Lemma lem4077584 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4077585 {A : Type'} (a : A) (s : A -> Prop) : (term467 A a s) = (term468 A a s).
Proof. exact (MK_COMB (@lem4077584 A) (@lem4077583 A a s)). Qed.
Lemma lem4077590 {A : Type'} (s : A -> Prop) : (term469 A s) = (term470 A s).
Proof. exact (fun_ext (fun a : A => @lem4077585 A a s)). Qed.
Lemma lem4077591 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077592 {A : Type'} (s : A -> Prop) : (term471 A s) = (term472 A s).
Proof. exact (MK_COMB (@lem4077591 A) (@lem4077590 A s)). Qed.
Lemma lem4077597 {A : Type'} : (term473 A) = (term474 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4077592 A s)). Qed.
Lemma lem4077598 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4077607 {A : Type'} : (term475 A) = (term476 A).
Proof. exact (MK_COMB (@lem4077598 A) (@lem4077597 A)). Qed.
Lemma lem4077620 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (x : A) : (term450 A t a s x) = (term450 A t a s x).
Proof. exact (eq_refl (term450 A t a s x)). Qed.
Lemma lem4077621 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term452 A t a s) = (term452 A t a s).
Proof. exact (fun_ext (fun x : A => @lem4077620 A t a s x)). Qed.
Lemma lem4077622 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077623 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term453 A t a s) = (term453 A t a s).
Proof. exact (MK_COMB (@lem4077622 A) (@lem4077621 A t a s)). Qed.
Lemma lem4077634 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term439 A n s a) = (term439 A n s a).
Proof. exact (eq_refl (term439 A n s a)). Qed.
Lemma lem4077639 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term432 A t s x) = (term432 A t s x).
Proof. exact (eq_refl (term432 A t s x)). Qed.
Lemma lem4077640 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term434 A t s) = (term434 A t s).
Proof. exact (fun_ext (fun x : A => @lem4077639 A t s x)). Qed.
Lemma lem4077641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077642 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term435 A t s) = (term435 A t s).
Proof. exact (MK_COMB (@lem4077641 A) (@lem4077640 A t s)). Qed.
Lemma lem4077643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4077644 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term436 A t s) = (term436 A t s).
Proof. exact (MK_COMB (@lem4077643) (@lem4077642 A t s)). Qed.
Lemma lem4077645 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term440 A t n s a) = (term440 A t n s a).
Proof. exact (MK_COMB (@lem4077644 A t s) (@lem4077634 A n s a)). Qed.
Lemma lem4077648 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4077649 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term441 A t n s a) = (term441 A t n s a).
Proof. exact (MK_COMB (@lem4077648 A t n) (@lem4077645 A t n s a)). Qed.
Lemma lem4077650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4077651 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term442 A t n s a) = (term442 A t n s a).
Proof. exact (MK_COMB (@lem4077650) (@lem4077649 A t n s a)). Qed.
Lemma lem4077652 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term454 A n t a s) = (term454 A n t a s).
Proof. exact (MK_COMB (@lem4077651 A t n s a) (@lem4077623 A t a s)). Qed.
Lemma lem4077653 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term462 A t a s) = (term462 A t a s).
Proof. exact (fun_ext (fun n : nat => @lem4077652 A n t a s)). Qed.
Lemma lem4077654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4077655 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term464 A t a s) = (term464 A t a s).
Proof. exact (MK_COMB (@lem4077654) (@lem4077653 A t a s)). Qed.
Lemma lem4077656 {A : Type'} (a : A) (s : A -> Prop) : (term466 A a s) = (term466 A a s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4077655 A t a s)). Qed.
Lemma lem4077657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4077658 {A : Type'} (a : A) (s : A -> Prop) : (term468 A a s) = (term468 A a s).
Proof. exact (MK_COMB (@lem4077657 A) (@lem4077656 A a s)). Qed.
Lemma lem4077659 {A : Type'} (s : A -> Prop) : (term470 A s) = (term470 A s).
Proof. exact (fun_ext (fun a : A => @lem4077658 A a s)). Qed.
Lemma lem4077660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077661 {A : Type'} (s : A -> Prop) : (term472 A s) = (term472 A s).
Proof. exact (MK_COMB (@lem4077660 A) (@lem4077659 A s)). Qed.
Lemma lem4077662 {A : Type'} : (term474 A) = (term474 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4077661 A s)). Qed.
Lemma lem4077663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4077664 {A : Type'} : (term476 A) = (term476 A).
Proof. exact (MK_COMB (@lem4077663 A) (@lem4077662 A)). Qed.
Lemma lem4077721 {A : Type'} : (term475 A) = (term476 A).
Proof. exact (TRANS (@lem4077607 A) (@lem4077664 A)). Qed.
Lemma lem4077722 {A : Type'} : (term476 A) = (term475 A).
Proof. exact (SYM (@lem4077721 A)). Qed.
Lemma lem4077723 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term441 A t n s a.
Proof. exact (h1). Qed.
Lemma lem4077726 (p : Prop) : p = (term252 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4077727 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term446 A a s x) = (term477 A a s x).
Proof. exact (@lem4077726 (term446 A a s x)). Qed.
Lemma lem4077728 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term477 A a s x) = (term446 A a s x).
Proof. exact (SYM (@lem4077727 A a s x)). Qed.
Lemma lem4077729 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term478 A a s x.
Proof. exact (h1). Qed.
Lemma lem4077737 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term432 A t s x) = (term479 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4077738 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term434 A t s) = (term480 A t s).
Proof. exact (fun_ext (fun x : A => @lem4077737 A t s x)). Qed.
Lemma lem4077739 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077740 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term435 A t s) = (term481 A t s).
Proof. exact (MK_COMB (@lem4077739 A) (@lem4077738 A t s)). Qed.
Lemma lem4077747 {A : Type'} (n : nat) (s : A -> Prop) : (term399 A n s) = (term482 A n s).
Proof. exact (@lem17265 (@FINITE A s) (term396 A n s)). Qed.
Lemma lem4077748 {A : Type'} (s : A -> Prop) (a : A) : (term437 A s a) = (term437 A s a).
Proof. exact (eq_refl (term437 A s a)). Qed.
Lemma lem4077749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4077750 {A : Type'} (n : nat) (s : A -> Prop) : (term438 A n s) = (term483 A n s).
Proof. exact (MK_COMB (@lem4077749) (@lem4077747 A n s)). Qed.
Lemma lem4077751 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term439 A n s a) = (term484 A n s a).
Proof. exact (MK_COMB (@lem4077750 A n s) (@lem4077748 A s a)). Qed.
Lemma lem4077752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4077753 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term436 A t s) = (term485 A t s).
Proof. exact (MK_COMB (@lem4077752) (@lem4077740 A t s)). Qed.
Lemma lem4077754 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term440 A t n s a) = (term486 A t n s a).
Proof. exact (MK_COMB (@lem4077753 A t s) (@lem4077751 A n s a)). Qed.
Lemma lem4077756 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4077793 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term441 A t n s a) = (term487 A t n s a).
Proof. exact (MK_COMB (@lem4077756 A t n) (@lem4077754 A t n s a)). Qed.
Lemma lem4077794 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term487 A t n s a.
Proof. exact (EQ_MP (@lem4077793 A t n s a) (@lem4077723 A t n s a h1)). Qed.
Lemma lem4077804 {A : Type'} (a : A) (t : A -> Prop) (x : A) (h1 : term446 A a t x) : term446 A a t x.
Proof. exact (h1). Qed.
Lemma lem4077815 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term478 A a s x) = (term488 A a s x).
Proof. exact (@lem17160 (x = a) (s x)). Qed.
Lemma lem4077816 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term488 A a s x.
Proof. exact (EQ_MP (@lem4077815 A a s x) (@lem4077729 A a s x h1)). Qed.
Lemma lem4077817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4077822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4077823 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4077822 A Prop f x). Qed.
Lemma lem4077825 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4077823 A s a). Qed.
Lemma lem4077826 {A : Type'} (s : A -> Prop) (a : A) : (term437 A s a) = (term489 A s a).
Proof. exact (MK_COMB (@lem4077817) (@lem4077825 A s a)). Qed.
Lemma lem4077843 {A : Type'} (n : nat) (s : A -> Prop) : (term483 A n s) = (term483 A n s).
Proof. exact (eq_refl (term483 A n s)). Qed.
Lemma lem4077844 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term484 A n s a) = (term490 A n s a).
Proof. exact (MK_COMB (@lem4077843 A n s) (@lem4077826 A s a)). Qed.
Lemma lem4077849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4077850 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4077849 A Prop f x). Qed.
Lemma lem4077852 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4077850 A s x). Qed.
Lemma lem4077853 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4077858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4077859 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4077858 A Prop f x). Qed.
Lemma lem4077861 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4077859 A t x). Qed.
Lemma lem4077862 {A : Type'} (t : A -> Prop) (x : A) : (term437 A t x) = (term489 A t x).
Proof. exact (MK_COMB (@lem4077853) (@lem4077861 A t x)). Qed.
Lemma lem4077863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4077864 {A : Type'} (t : A -> Prop) (x : A) : (term491 A t x) = (term492 A t x).
Proof. exact (MK_COMB (@lem4077863) (@lem4077862 A t x)). Qed.
Lemma lem4077865 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term479 A t s x) = (term493 A t s x).
Proof. exact (MK_COMB (@lem4077864 A t x) (@lem4077852 A s x)). Qed.
Lemma lem4077866 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term480 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4077865 A t s x)). Qed.
Lemma lem4077867 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077868 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term481 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4077867 A) (@lem4077866 A t s)). Qed.
Lemma lem4077869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4077870 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term485 A t s) = (term496 A t s).
Proof. exact (MK_COMB (@lem4077869) (@lem4077868 A t s)). Qed.
Lemma lem4077871 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term486 A t n s a) = (term497 A t n s a).
Proof. exact (MK_COMB (@lem4077870 A t s) (@lem4077844 A n s a)). Qed.
Lemma lem4077878 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4077879 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term487 A t n s a) = (term498 A t n s a).
Proof. exact (MK_COMB (@lem4077878 A t n) (@lem4077871 A t n s a)). Qed.
Lemma lem4077880 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term498 A t n s a.
Proof. exact (EQ_MP (@lem4077879 A t n s a) (@lem4077794 A t n s a h1)). Qed.
Lemma lem4077885 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4077886 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4077885 A Prop f x). Qed.
Lemma lem4077888 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4077886 A t x). Qed.
Lemma lem4077895 {A : Type'} (x : A) (a : A) : (term445 A x a) = (term445 A x a).
Proof. exact (eq_refl (term445 A x a)). Qed.
Lemma lem4077896 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term446 A a t x) = (term499 A a t x).
Proof. exact (MK_COMB (@lem4077895 A x a) (@lem4077888 A t x)). Qed.
Lemma lem4077897 {A : Type'} (a : A) (t : A -> Prop) (x : A) (h1 : term446 A a t x) : term499 A a t x.
Proof. exact (EQ_MP (@lem4077896 A a t x) (@lem4077804 A a t x h1)). Qed.
Lemma lem4077898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4077903 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4077904 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4077903 A Prop f x). Qed.
Lemma lem4077906 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4077904 A s x). Qed.
Lemma lem4077907 {A : Type'} (s : A -> Prop) (x : A) : (term437 A s x) = (term489 A s x).
Proof. exact (MK_COMB (@lem4077898) (@lem4077906 A s x)). Qed.
Lemma lem4077916 {A : Type'} (x : A) (a : A) : (term500 A x a) = (term500 A x a).
Proof. exact (eq_refl (term500 A x a)). Qed.
Lemma lem4077917 {A : Type'} (a : A) (s : A -> Prop) (x : A) : (term488 A a s x) = (term501 A a s x).
Proof. exact (MK_COMB (@lem4077916 A x a) (@lem4077907 A s x)). Qed.
Lemma lem4077918 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term501 A a s x.
Proof. exact (EQ_MP (@lem4077917 A a s x) (@lem4077816 A a s x h1)). Qed.
Lemma lem4077921 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term497 A t n s a.
Proof. exact (proj2 (@lem4077880 A t n s a h1)). Qed.
Lemma lem4077923 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term490 A n s a.
Proof. exact (proj2 (@lem4077921 A t n s a h1)). Qed.
Lemma lem4077924 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term495 A t s.
Proof. exact (proj1 (@lem4077921 A t n s a h1)). Qed.
Lemma lem4077926 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term482 A n s.
Proof. exact (proj1 (@lem4077923 A t n s a h1)). Qed.
Lemma lem4077969 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4077989 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term493 A t s x) = (term493 A t s x).
Proof. exact (eq_refl (term493 A t s x)). Qed.
Lemma lem4077990 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4077989 A t s x)). Qed.
Lemma lem4077991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4077993 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term495 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4077991 A) (@lem4077990 A t s)). Qed.
Lemma lem4077994 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term495 A t s.
Proof. exact (EQ_MP (@lem4077993 A t s) (@lem4077924 A t n s a h1)). Qed.
Lemma lem4078006 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem4078043 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4078063 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term493 A t s x) = (term493 A t s x).
Proof. exact (eq_refl (term493 A t s x)). Qed.
Lemma lem4078064 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4078063 A t s x)). Qed.
Lemma lem4078065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4078067 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term495 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4078065 A) (@lem4078064 A t s)). Qed.
Lemma lem4078068 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term495 A t s.
Proof. exact (EQ_MP (@lem4078067 A t s) (@lem4077924 A t n s a h1)). Qed.
Lemma lem4078080 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem4078084 {A : Type'} (_47892 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term502 A t s _47892.
Proof. exact (@lem4077994 A t n s a h1 _47892). Qed.
Lemma lem4078085 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47892 : A) : (term502 A t s _47892) = (term493 A t s _47892).
Proof. exact (eq_refl (term502 A t s _47892)). Qed.
Lemma lem4078090 {A : Type'} (_47894 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term502 A t s _47894.
Proof. exact (@lem4078068 A t n s a h1 _47894). Qed.
Lemma lem4078091 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47894 : A) : (term502 A t s _47894) = (term493 A t s _47894).
Proof. exact (eq_refl (term502 A t s _47894)). Qed.
Lemma lem4078094 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term503 A x a.
Proof. exact (proj1 (@lem4077918 A a s x h1)). Qed.
Lemma lem4078110 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4078114 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term489 A s x.
Proof. exact (proj2 (@lem4077918 A a s x h1)). Qed.
Lemma lem4078122 {A : Type'} (_47892 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term493 A t s _47892.
Proof. exact (EQ_MP (@lem4078085 A t s _47892) (@lem4078084 A _47892 t n s a h1)). Qed.
Lemma lem4078128 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem4078130 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term503 A x a.
Proof. exact (proj1 (@lem4077918 A a s x h1)). Qed.
Lemma lem4078146 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4078150 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term489 A s x.
Proof. exact (proj2 (@lem4077918 A a s x h1)). Qed.
Lemma lem4078158 {A : Type'} (_47894 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term493 A t s _47894.
Proof. exact (EQ_MP (@lem4078091 A t s _47894) (@lem4078090 A _47894 t n s a h1)). Qed.
Lemma lem4078164 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem4078179 {A : Type'} (a : A) : (term504 A a) = (term504 A a).
Proof. exact (eq_refl (term504 A a)). Qed.
Lemma lem4078180 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term505 A a x) = (term506 A a).
Proof. exact (MK_COMB (@lem4078179 A a) (@lem4078110 A x a h1)). Qed.
Lemma lem4078181 {A : Type'} (a : A) : (term506 A a) = (term507 A a).
Proof. exact (eq_refl (term506 A a)). Qed.
Lemma lem4078182 {A : Type'} (a : A) (x : A) : (term508 A a x) = (term508 A a x).
Proof. exact (eq_refl (term508 A a x)). Qed.
Lemma lem4078183 {A : Type'} (x : A) (a : A) : ((term505 A a x) = (term506 A a)) = ((term505 A a x) = (term507 A a)).
Proof. exact (MK_COMB (@lem4078182 A a x) (@lem4078181 A a)). Qed.
Lemma lem4078184 {A : Type'} (x : A) (a : A) : (term505 A a x) = (term503 A x a).
Proof. exact (eq_refl (term505 A a x)). Qed.
Lemma lem4078185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4078186 {A : Type'} (x : A) (a : A) : (term508 A a x) = (term509 A x a).
Proof. exact (MK_COMB (@lem4078185) (@lem4078184 A x a)). Qed.
Lemma lem4078187 {A : Type'} (a : A) : (term507 A a) = (term507 A a).
Proof. exact (eq_refl (term507 A a)). Qed.
Lemma lem4078188 {A : Type'} (x : A) (a : A) : ((term505 A a x) = (term507 A a)) = ((term503 A x a) = (term507 A a)).
Proof. exact (MK_COMB (@lem4078186 A x a) (@lem4078187 A a)). Qed.
Lemma lem4078189 {A : Type'} (x : A) (a : A) : ((term505 A a x) = (term506 A a)) = ((term503 A x a) = (term507 A a)).
Proof. exact (TRANS (@lem4078183 A x a) (@lem4078188 A x a)). Qed.
Lemma lem4078190 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term503 A x a) = (term507 A a).
Proof. exact (EQ_MP (@lem4078189 A x a) (@lem4078180 A x a h1)). Qed.
Lemma lem4078191 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : term507 A a.
Proof. exact (EQ_MP (@lem4078190 A x a h2) (@lem4078094 A a s x h1)). Qed.
Lemma lem4078275 {A : Type'} (a : A) : (term504 A a) = (term504 A a).
Proof. exact (eq_refl (term504 A a)). Qed.
Lemma lem4078276 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term505 A a x) = (term506 A a).
Proof. exact (MK_COMB (@lem4078275 A a) (@lem4078146 A x a h1)). Qed.
Lemma lem4078277 {A : Type'} (a : A) : (term506 A a) = (term507 A a).
Proof. exact (eq_refl (term506 A a)). Qed.
Lemma lem4078278 {A : Type'} (a : A) (x : A) : (term508 A a x) = (term508 A a x).
Proof. exact (eq_refl (term508 A a x)). Qed.
Lemma lem4078279 {A : Type'} (x : A) (a : A) : ((term505 A a x) = (term506 A a)) = ((term505 A a x) = (term507 A a)).
Proof. exact (MK_COMB (@lem4078278 A a x) (@lem4078277 A a)). Qed.
Lemma lem4078280 {A : Type'} (x : A) (a : A) : (term505 A a x) = (term503 A x a).
Proof. exact (eq_refl (term505 A a x)). Qed.
Lemma lem4078281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4078282 {A : Type'} (x : A) (a : A) : (term508 A a x) = (term509 A x a).
Proof. exact (MK_COMB (@lem4078281) (@lem4078280 A x a)). Qed.
Lemma lem4078283 {A : Type'} (a : A) : (term507 A a) = (term507 A a).
Proof. exact (eq_refl (term507 A a)). Qed.
Lemma lem4078284 {A : Type'} (x : A) (a : A) : ((term505 A a x) = (term507 A a)) = ((term503 A x a) = (term507 A a)).
Proof. exact (MK_COMB (@lem4078282 A x a) (@lem4078283 A a)). Qed.
Lemma lem4078285 {A : Type'} (x : A) (a : A) : ((term505 A a x) = (term506 A a)) = ((term503 A x a) = (term507 A a)).
Proof. exact (TRANS (@lem4078279 A x a) (@lem4078284 A x a)). Qed.
Lemma lem4078286 {A : Type'} (x : A) (a : A) (h1 : x = a) : (term503 A x a) = (term507 A a).
Proof. exact (EQ_MP (@lem4078285 A x a) (@lem4078276 A x a h1)). Qed.
Lemma lem4078287 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : term507 A a.
Proof. exact (EQ_MP (@lem4078286 A x a h2) (@lem4078130 A a s x h1)). Qed.
Lemma lem4078414 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4078415 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4078414 A x). Qed.
Lemma lem4078416 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4078415 A a). Qed.
Lemma lem4078417 {A : Type'} (a : A) : term510 A a.
Proof. exact (fun h0 : term507 A a => @lem4078416 A a). Qed.
Lemma lem4078419 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078420 {A : Type'} (a : A) : (term510 A a) = (a = a).
Proof. exact (@lem4078419 (a = a)). Qed.
Lemma lem4078421 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4078420 A a) (@lem4078417 A a)). Qed.
Lemma lem4078424 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4078426 {A : Type'} (a : A) : (term507 A a) = (term511 A a).
Proof. exact (@lem4078424 (a = a)). Qed.
Lemma lem4078429 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : term511 A a.
Proof. exact (EQ_MP (@lem4078426 A a) (@lem4078191 A s x a h1 h2)). Qed.
Lemma lem4078432 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (@lem4078429 A s x a h1 h2 (@lem4078421 A a)). Qed.
Lemma lem4078433 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : term304.
Proof. exact (fun h0 : ~ False => @lem4078432 A s x a h1 h2). Qed.
Lemma lem4078435 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078436 : term304 = False.
Proof. exact (@lem4078435 False). Qed.
Lemma lem4078495 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem4078496 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : term512 A t x.
Proof. exact (fun h0 : term489 A t x => @lem4078495 A t x h1). Qed.
Lemma lem4078498 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078499 {A : Type'} (t : A -> Prop) (x : A) : (term512 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4078498 (@I (A -> Prop) t x)). Qed.
Lemma lem4078500 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4078499 A t x) (@lem4078496 A t x h1)). Qed.
Lemma lem4078506 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4078507 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : (term493 A t s _47892) = (term513 A s t _47892).
Proof. exact (@lem4078506 (@I (A -> Prop) s _47892) (term489 A t _47892)). Qed.
Lemma lem4078513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4078514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : (term514 A t s _47892) = (term515 A s t _47892).
Proof. exact (MK_COMB (@lem4078513) (@lem4078507 A s t _47892)). Qed.
Lemma lem4078520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : (term513 A s t _47892) = (term513 A s t _47892).
Proof. exact (eq_refl (term513 A s t _47892)). Qed.
Lemma lem4078521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : ((term493 A t s _47892) = (term513 A s t _47892)) = ((term513 A s t _47892) = (term513 A s t _47892)).
Proof. exact (MK_COMB (@lem4078514 A s t _47892) (@lem4078520 A s t _47892)). Qed.
Lemma lem4078523 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4078524 (x : Prop) : (x = x) = True.
Proof. exact (@lem4078523 Prop x). Qed.
Lemma lem4078525 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : ((term513 A s t _47892) = (term513 A s t _47892)) = True.
Proof. exact (@lem4078524 (term513 A s t _47892)). Qed.
Lemma lem4078526 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : ((term493 A t s _47892) = (term513 A s t _47892)) = True.
Proof. exact (TRANS (@lem4078521 A s t _47892) (@lem4078525 A s t _47892)). Qed.
Lemma lem4078527 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : True = ((term493 A t s _47892) = (term513 A s t _47892)).
Proof. exact (SYM (@lem4078526 A s t _47892)). Qed.
Lemma lem4078528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47892 : A) : (term493 A t s _47892) = (term513 A s t _47892).
Proof. exact (EQ_MP (@lem4078527 A s t _47892) (@lem0)). Qed.
Lemma lem4078529 {A : Type'} (_47892 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term513 A s t _47892.
Proof. exact (EQ_MP (@lem4078528 A s t _47892) (@lem4078122 A _47892 t n s a h1)). Qed.
Lemma lem4078531 (b : Prop) (a : Prop) : (a \/ b) = (term516 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4078532 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47892 : A) : (term513 A s t _47892) = (term517 A t s _47892).
Proof. exact (@lem4078531 (term489 A t _47892) (@I (A -> Prop) s _47892)). Qed.
Lemma lem4078534 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4078535 {A : Type'} (t : A -> Prop) (_47892 : A) : (term518 A t _47892) = (@I (A -> Prop) t _47892).
Proof. exact (@lem4078534 (@I (A -> Prop) t _47892)). Qed.
Lemma lem4078536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4078537 {A : Type'} (t : A -> Prop) (_47892 : A) : (term519 A t _47892) = (term520 A t _47892).
Proof. exact (MK_COMB (@lem4078536) (@lem4078535 A t _47892)). Qed.
Lemma lem4078538 {A : Type'} (s : A -> Prop) (_47892 : A) : (@I (A -> Prop) s _47892) = (@I (A -> Prop) s _47892).
Proof. exact (eq_refl (@I (A -> Prop) s _47892)). Qed.
Lemma lem4078539 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47892 : A) : (term517 A t s _47892) = (term521 A t s _47892).
Proof. exact (MK_COMB (@lem4078537 A t _47892) (@lem4078538 A s _47892)). Qed.
Lemma lem4078540 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47892 : A) : (term513 A s t _47892) = (term521 A t s _47892).
Proof. exact (TRANS (@lem4078532 A t s _47892) (@lem4078539 A t s _47892)). Qed.
Lemma lem4078543 {A : Type'} (_47892 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term521 A t s _47892.
Proof. exact (EQ_MP (@lem4078540 A t s _47892) (@lem4078529 A _47892 t n s a h1)). Qed.
Lemma lem4078544 {A : Type'} (_47892 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term521 A t s _47892.
Proof. exact (@lem4078543 A _47892 t n s a h1). Qed.
Lemma lem4078545 {A : Type'} (x : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term521 A t s x.
Proof. exact (@lem4078544 A x t n s a h1). Qed.
Lemma lem4078548 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : @I (A -> Prop) t x) : @I (A -> Prop) s x.
Proof. exact (@lem4078545 A x t n s a h1 (@lem4078500 A t x h2)). Qed.
Lemma lem4078549 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : @I (A -> Prop) t x) : term512 A s x.
Proof. exact (fun h0 : term489 A s x => @lem4078548 A n s a t x h1 h2). Qed.
Lemma lem4078551 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078552 {A : Type'} (s : A -> Prop) (x : A) : (term512 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4078551 (@I (A -> Prop) s x)). Qed.
Lemma lem4078553 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : @I (A -> Prop) t x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4078552 A s x) (@lem4078549 A n s a t x h1 h2)). Qed.
Lemma lem4078556 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4078558 {A : Type'} (s : A -> Prop) (x : A) : (term489 A s x) = (term522 A s x).
Proof. exact (@lem4078556 (@I (A -> Prop) s x)). Qed.
Lemma lem4078561 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term522 A s x.
Proof. exact (EQ_MP (@lem4078558 A s x) (@lem4078114 A a s x h1)). Qed.
Lemma lem4078564 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (@lem4078561 A a s x h1 (@lem4078553 A n s a t x h2 h3)). Qed.
Lemma lem4078565 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : term304.
Proof. exact (fun h0 : ~ False => @lem4078564 A n s a t x h1 h2 h3). Qed.
Lemma lem4078567 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078568 : term304 = False.
Proof. exact (@lem4078567 False). Qed.
Lemma lem4078569 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078568) (@lem4078565 A n s a t x h1 h2 h3)). Qed.
Lemma lem4078642 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4078643 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4078642 A x). Qed.
Lemma lem4078644 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4078643 A a). Qed.
Lemma lem4078645 {A : Type'} (a : A) : term510 A a.
Proof. exact (fun h0 : term507 A a => @lem4078644 A a). Qed.
Lemma lem4078647 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078648 {A : Type'} (a : A) : (term510 A a) = (a = a).
Proof. exact (@lem4078647 (a = a)). Qed.
Lemma lem4078649 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4078648 A a) (@lem4078645 A a)). Qed.
Lemma lem4078652 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4078654 {A : Type'} (a : A) : (term507 A a) = (term511 A a).
Proof. exact (@lem4078652 (a = a)). Qed.
Lemma lem4078657 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : term511 A a.
Proof. exact (EQ_MP (@lem4078654 A a) (@lem4078287 A s x a h1 h2)). Qed.
Lemma lem4078660 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (@lem4078657 A s x a h1 h2 (@lem4078649 A a)). Qed.
Lemma lem4078661 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : term304.
Proof. exact (fun h0 : ~ False => @lem4078660 A s x a h1 h2). Qed.
Lemma lem4078663 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078664 : term304 = False.
Proof. exact (@lem4078663 False). Qed.
Lemma lem4078738 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem4078739 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : term512 A t x.
Proof. exact (fun h0 : term489 A t x => @lem4078738 A t x h1). Qed.
Lemma lem4078741 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078742 {A : Type'} (t : A -> Prop) (x : A) : (term512 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4078741 (@I (A -> Prop) t x)). Qed.
Lemma lem4078743 {A : Type'} (t : A -> Prop) (x : A) (h1 : @I (A -> Prop) t x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4078742 A t x) (@lem4078739 A t x h1)). Qed.
Lemma lem4078749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4078750 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : (term493 A t s _47894) = (term513 A s t _47894).
Proof. exact (@lem4078749 (@I (A -> Prop) s _47894) (term489 A t _47894)). Qed.
Lemma lem4078756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4078757 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : (term514 A t s _47894) = (term515 A s t _47894).
Proof. exact (MK_COMB (@lem4078756) (@lem4078750 A s t _47894)). Qed.
Lemma lem4078763 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : (term513 A s t _47894) = (term513 A s t _47894).
Proof. exact (eq_refl (term513 A s t _47894)). Qed.
Lemma lem4078764 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : ((term493 A t s _47894) = (term513 A s t _47894)) = ((term513 A s t _47894) = (term513 A s t _47894)).
Proof. exact (MK_COMB (@lem4078757 A s t _47894) (@lem4078763 A s t _47894)). Qed.
Lemma lem4078766 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4078767 (x : Prop) : (x = x) = True.
Proof. exact (@lem4078766 Prop x). Qed.
Lemma lem4078768 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : ((term513 A s t _47894) = (term513 A s t _47894)) = True.
Proof. exact (@lem4078767 (term513 A s t _47894)). Qed.
Lemma lem4078769 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : ((term493 A t s _47894) = (term513 A s t _47894)) = True.
Proof. exact (TRANS (@lem4078764 A s t _47894) (@lem4078768 A s t _47894)). Qed.
Lemma lem4078770 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : True = ((term493 A t s _47894) = (term513 A s t _47894)).
Proof. exact (SYM (@lem4078769 A s t _47894)). Qed.
Lemma lem4078771 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_47894 : A) : (term493 A t s _47894) = (term513 A s t _47894).
Proof. exact (EQ_MP (@lem4078770 A s t _47894) (@lem0)). Qed.
Lemma lem4078772 {A : Type'} (_47894 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term513 A s t _47894.
Proof. exact (EQ_MP (@lem4078771 A s t _47894) (@lem4078158 A _47894 t n s a h1)). Qed.
Lemma lem4078774 (b : Prop) (a : Prop) : (a \/ b) = (term516 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4078775 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47894 : A) : (term513 A s t _47894) = (term517 A t s _47894).
Proof. exact (@lem4078774 (term489 A t _47894) (@I (A -> Prop) s _47894)). Qed.
Lemma lem4078777 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4078778 {A : Type'} (t : A -> Prop) (_47894 : A) : (term518 A t _47894) = (@I (A -> Prop) t _47894).
Proof. exact (@lem4078777 (@I (A -> Prop) t _47894)). Qed.
Lemma lem4078779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4078780 {A : Type'} (t : A -> Prop) (_47894 : A) : (term519 A t _47894) = (term520 A t _47894).
Proof. exact (MK_COMB (@lem4078779) (@lem4078778 A t _47894)). Qed.
Lemma lem4078781 {A : Type'} (s : A -> Prop) (_47894 : A) : (@I (A -> Prop) s _47894) = (@I (A -> Prop) s _47894).
Proof. exact (eq_refl (@I (A -> Prop) s _47894)). Qed.
Lemma lem4078782 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47894 : A) : (term517 A t s _47894) = (term521 A t s _47894).
Proof. exact (MK_COMB (@lem4078780 A t _47894) (@lem4078781 A s _47894)). Qed.
Lemma lem4078783 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_47894 : A) : (term513 A s t _47894) = (term521 A t s _47894).
Proof. exact (TRANS (@lem4078775 A t s _47894) (@lem4078782 A t s _47894)). Qed.
Lemma lem4078786 {A : Type'} (_47894 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term521 A t s _47894.
Proof. exact (EQ_MP (@lem4078783 A t s _47894) (@lem4078772 A _47894 t n s a h1)). Qed.
Lemma lem4078787 {A : Type'} (_47894 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term521 A t s _47894.
Proof. exact (@lem4078786 A _47894 t n s a h1). Qed.
Lemma lem4078788 {A : Type'} (x : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term521 A t s x.
Proof. exact (@lem4078787 A x t n s a h1). Qed.
Lemma lem4078791 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : @I (A -> Prop) t x) : @I (A -> Prop) s x.
Proof. exact (@lem4078788 A x t n s a h1 (@lem4078743 A t x h2)). Qed.
Lemma lem4078792 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : @I (A -> Prop) t x) : term512 A s x.
Proof. exact (fun h0 : term489 A s x => @lem4078791 A n s a t x h1 h2). Qed.
Lemma lem4078794 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078795 {A : Type'} (s : A -> Prop) (x : A) : (term512 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4078794 (@I (A -> Prop) s x)). Qed.
Lemma lem4078796 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : @I (A -> Prop) t x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4078795 A s x) (@lem4078792 A n s a t x h1 h2)). Qed.
Lemma lem4078799 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4078801 {A : Type'} (s : A -> Prop) (x : A) : (term489 A s x) = (term522 A s x).
Proof. exact (@lem4078799 (@I (A -> Prop) s x)). Qed.
Lemma lem4078804 {A : Type'} (a : A) (s : A -> Prop) (x : A) (h1 : term478 A a s x) : term522 A s x.
Proof. exact (EQ_MP (@lem4078801 A s x) (@lem4078150 A a s x h1)). Qed.
Lemma lem4078807 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (@lem4078804 A a s x h1 (@lem4078796 A n s a t x h2 h3)). Qed.
Lemma lem4078808 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : term304.
Proof. exact (fun h0 : ~ False => @lem4078807 A n s a t x h1 h2 h3). Qed.
Lemma lem4078810 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4078811 : term304 = False.
Proof. exact (@lem4078810 False). Qed.
Lemma lem4078812 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078811) (@lem4078808 A n s a t x h1 h2 h3)). Qed.
Lemma lem4078813 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078664) (@lem4078661 A s x a h1 h2)). Qed.
Lemma lem4078814 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078436) (@lem4078433 A s x a h1 h2)). Qed.
Lemma lem4078815 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : (@I (A -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) t x => @lem4078812 A n s a t x h1 h2 h3) (fun h4 : False => @lem4078164 A t x h3)). Qed.
Lemma lem4078816 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078815 A n s a t x h1 h2 h3) (@lem4078164 A t x h3)). Qed.
Lemma lem4078817 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4078813 A s x a h1 h2) (fun h3 : False => @lem4078146 A x a h2)). Qed.
Lemma lem4078818 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078817 A s x a h1 h2) (@lem4078146 A x a h2)). Qed.
Lemma lem4078819 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : (@I (A -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) t x => @lem4078569 A n s a t x h1 h2 h3) (fun h4 : False => @lem4078128 A t x h3)). Qed.
Lemma lem4078820 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078819 A n s a t x h1 h2 h3) (@lem4078128 A t x h3)). Qed.
Lemma lem4078821 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4078814 A s x a h1 h2) (fun h3 : False => @lem4078110 A x a h2)). Qed.
Lemma lem4078822 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078821 A s x a h1 h2) (@lem4078110 A x a h2)). Qed.
Lemma lem4078823 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : (@I (A -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) t x => @lem4078816 A n s a t x h1 h2 h3) (fun h4 : False => @lem4078080 A t x h3)). Qed.
Lemma lem4078824 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078823 A n s a t x h1 h2 h3) (@lem4078080 A t x h3)). Qed.
Lemma lem4078825 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4078818 A s x a h1 h2) (fun h3 : False => @lem4078043 A x a h2)). Qed.
Lemma lem4078826 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078825 A s x a h1 h2) (@lem4078043 A x a h2)). Qed.
Lemma lem4078827 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : (@I (A -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) t x => @lem4078820 A n s a t x h1 h2 h3) (fun h4 : False => @lem4078006 A t x h3)). Qed.
Lemma lem4078828 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078827 A n s a t x h1 h2 h3) (@lem4078006 A t x h3)). Qed.
Lemma lem4078829 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4078822 A s x a h1 h2) (fun h3 : False => @lem4077969 A x a h2)). Qed.
Lemma lem4078830 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078829 A s x a h1 h2) (@lem4077969 A x a h2)). Qed.
Lemma lem4078831 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : (@I (A -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) t x => @lem4078824 A n s a t x h1 h2 h3) (fun h4 : False => @lem4078080 A t x h3)). Qed.
Lemma lem4078832 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078831 A n s a t x h1 h2 h3) (@lem4078080 A t x h3)). Qed.
Lemma lem4078833 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4078826 A s x a h1 h2) (fun h3 : False => @lem4078043 A x a h2)). Qed.
Lemma lem4078834 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078833 A s x a h1 h2) (@lem4078043 A x a h2)). Qed.
Lemma lem4078835 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : (@I (A -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (A -> Prop) t x => @lem4078828 A n s a t x h1 h2 h3) (fun h4 : False => @lem4078006 A t x h3)). Qed.
Lemma lem4078836 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : @I (A -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem4078835 A n s a t x h1 h2 h3) (@lem4078006 A t x h3)). Qed.
Lemma lem4078837 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem4078830 A s x a h1 h2) (fun h3 : False => @lem4077969 A x a h2)). Qed.
Lemma lem4078838 {A : Type'} (s : A -> Prop) (x : A) (a : A) (h1 : term478 A a s x) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem4078837 A s x a h1 h2) (@lem4077969 A x a h2)). Qed.
Lemma lem4078839 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : False.
Proof. exact (or_elim (@lem4077897 A a t x h3) (fun h0 : x = a => @lem4078834 A s x a h1 h0) (fun h0 : @I (A -> Prop) t x => @lem4078832 A n s a t x h1 h2 h0)). Qed.
Lemma lem4078840 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : False.
Proof. exact (or_elim (@lem4077897 A a t x h3) (fun h0 : x = a => @lem4078838 A s x a h1 h0) (fun h0 : @I (A -> Prop) t x => @lem4078836 A n s a t x h1 h2 h0)). Qed.
Lemma lem4078841 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : False.
Proof. exact (or_elim (@lem4077926 A t n s a h2) (fun h0 : term305 A s => @lem4078840 A n s a t x h1 h2 h3) (fun h0 : term396 A n s => @lem4078839 A n s a t x h1 h2 h3)). Qed.
Lemma lem4078842 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : (term446 A a t x) = False.
Proof. exact (prop_ext (fun h4 : term446 A a t x => @lem4078841 A n s a t x h1 h2 h3) (fun h4 : False => @lem4077804 A a t x h3)). Qed.
Lemma lem4078843 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : False.
Proof. exact (EQ_MP (@lem4078842 A n s a t x h1 h2 h3) (@lem4077804 A a t x h3)). Qed.
Lemma lem4078844 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : (term478 A a s x) = False.
Proof. exact (prop_ext (fun h4 : term478 A a s x => @lem4078843 A n s a t x h1 h2 h3) (fun h4 : False => @lem4077729 A a s x h1)). Qed.
Lemma lem4078845 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term478 A a s x) (h2 : term441 A t n s a) (h3 : term446 A a t x) : False.
Proof. exact (EQ_MP (@lem4078844 A n s a t x h1 h2 h3) (@lem4077729 A a s x h1)). Qed.
Lemma lem4078846 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : term446 A a t x) : term477 A a s x.
Proof. exact (fun h0 : term478 A a s x => @lem4078845 A n s a t x h0 h1 h2). Qed.
Lemma lem4078847 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (x : A) (h1 : term441 A t n s a) (h2 : term446 A a t x) : term446 A a s x.
Proof. exact (EQ_MP (@lem4077728 A a s x) (@lem4078846 A n s a t x h1 h2)). Qed.
Lemma lem4078848 {A : Type'} (x : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term450 A t a s x.
Proof. exact (fun h0 : term446 A a t x => @lem4078847 A n s a t x h1 h0). Qed.
Lemma lem4078853 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term453 A t a s.
Proof. exact (fun x : A => @lem4078848 A x t n s a h1). Qed.
Lemma lem4078854 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term454 A n t a s.
Proof. exact (fun h0 : term441 A t n s a => @lem4078853 A t n s a h0). Qed.
Lemma lem4078859 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : term464 A t a s.
Proof. exact (fun n : nat => @lem4078854 A n t a s). Qed.
Lemma lem4078864 {A : Type'} (a : A) (s : A -> Prop) : term468 A a s.
Proof. exact (fun t : A -> Prop => @lem4078859 A t a s). Qed.
Lemma lem4078869 {A : Type'} (s : A -> Prop) : term472 A s.
Proof. exact (fun a : A => @lem4078864 A a s). Qed.
Lemma lem4078874 {A : Type'} : term476 A.
Proof. exact (fun s : A -> Prop => @lem4078869 A s). Qed.
Lemma lem4078875 {A : Type'} : term475 A.
Proof. exact (EQ_MP (@lem4077722 A) (@lem4078874 A)). Qed.
Lemma lem4078876 {A : Type'} (s : A -> Prop) : term523 A s.
Proof. exact (@lem4078875 A s). Qed.
Lemma lem4078877 {A : Type'} (s : A -> Prop) : (term523 A s) = (term471 A s).
Proof. exact (eq_refl (term523 A s)). Qed.
Lemma lem4078878 {A : Type'} (s : A -> Prop) : term471 A s.
Proof. exact (EQ_MP (@lem4078877 A s) (@lem4078876 A s)). Qed.
Lemma lem4078879 {A : Type'} (s : A -> Prop) (a : A) : term524 A s a.
Proof. exact (@lem4078878 A s a). Qed.
Lemma lem4078880 {A : Type'} (a : A) (s : A -> Prop) : (term524 A s a) = (term467 A a s).
Proof. exact (eq_refl (term524 A s a)). Qed.
Lemma lem4078881 {A : Type'} (a : A) (s : A -> Prop) : term467 A a s.
Proof. exact (EQ_MP (@lem4078880 A a s) (@lem4078879 A s a)). Qed.
Lemma lem4078882 {A : Type'} (a : A) (s : A -> Prop) (t : A -> Prop) : term525 A a s t.
Proof. exact (@lem4078881 A a s t). Qed.
Lemma lem4078883 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : (term525 A a s t) = (term463 A t a s).
Proof. exact (eq_refl (term525 A a s t)). Qed.
Lemma lem4078884 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) : term463 A t a s.
Proof. exact (EQ_MP (@lem4078883 A t a s) (@lem4078882 A a s t)). Qed.
Lemma lem4078885 {A : Type'} (t : A -> Prop) (a : A) (s : A -> Prop) (n : nat) : term526 A t a s n.
Proof. exact (@lem4078884 A t a s n). Qed.
Lemma lem4078886 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : (term526 A t a s n) = (term455 A n t a s).
Proof. exact (eq_refl (term526 A t a s n)). Qed.
Lemma lem4078887 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term455 A n t a s.
Proof. exact (EQ_MP (@lem4078886 A n t a s) (@lem4078885 A t a s n)). Qed.
Lemma lem4078889 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term455 A n t a s.
Proof. exact (@lem4077526 A n t a s (@lem4078887 A n t a s)). Qed.
Lemma lem4078890 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term456 A n t a s) : False.
Proof. exact (@lem4078889 A n t a s (@lem4077510 A n t a s h1)). Qed.
Lemma lem4078891 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term456 A n t a s) : (term456 A n t a s) = False.
Proof. exact (prop_ext (fun h2 : term456 A n t a s => @lem4078890 A n t a s h1) (fun h2 : False => @lem4077510 A n t a s h1)). Qed.
Lemma lem4078892 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) (h1 : term456 A n t a s) : False.
Proof. exact (EQ_MP (@lem4078891 A n t a s h1) (@lem4077510 A n t a s h1)). Qed.
Lemma lem4078893 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term455 A n t a s.
Proof. exact (fun h0 : term456 A n t a s => @lem4078892 A n t a s h0). Qed.
Lemma lem4078894 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term454 A n t a s.
Proof. exact (EQ_MP (@lem4077509 A n t a s) (@lem4078893 A n t a s)). Qed.
Lemma lem4078895 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term428 A n t a s.
Proof. exact (EQ_MP (@lem4077505 A n t a s) (@lem4078894 A n t a s)). Qed.
Lemma lem4078896 {A : Type'} (n : nat) (t : A -> Prop) (a : A) (s : A -> Prop) : term427 A n t a s.
Proof. exact (EQ_MP (@lem4077392 A n t a s) (@lem4078895 A n t a s)). Qed.
Lemma lem4078897 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term425 A t a s.
Proof. exact (@lem4078896 A n t a s (@lem4077346 A a n t s h1 h2 h3 h4)). Qed.
Lemma lem4078908 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) : term415 A n a s.
Proof. exact (conj (@lem4077273 A n s h2) (@lem4076909 A a s h1)). Qed.
Lemma lem4078909 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @SUBSET A t s) : term416 A t n a s.
Proof. exact (conj (@lem4077333 A t s h3) (@lem4078908 A a n s h1 h2)). Qed.
Lemma lem4078910 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term417 A t n a s.
Proof. exact (conj (@lem4077332 A t n h3) (@lem4078909 A a n t s h1 h2 h4)). Qed.
Lemma lem4078918 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4078919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (@lem4078918 A s t). Qed.
Lemma lem4078920 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term418 A t s).
Proof. exact (@lem4078919 A t s). Qed.
Lemma lem4078927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4078928 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term227 A t s) = (term419 A t s).
Proof. exact (MK_COMB (@lem4078927) (@lem4078920 A t s)). Qed.
Lemma lem4078933 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term415 A n a s) = (term415 A n a s).
Proof. exact (eq_refl (term415 A n a s)). Qed.
Lemma lem4078934 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term416 A t n a s) = (term420 A t n a s).
Proof. exact (MK_COMB (@lem4078928 A t s) (@lem4078933 A n a s)). Qed.
Lemma lem4078937 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4078938 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term417 A t n a s) = (term422 A t n a s).
Proof. exact (MK_COMB (@lem4078937 A t n) (@lem4078934 A t n a s)). Qed.
Lemma lem4078941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4078942 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term423 A t n a s) = (term424 A t n a s).
Proof. exact (MK_COMB (@lem4078941) (@lem4078938 A t n a s)). Qed.
Lemma lem4078946 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term527 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4078947 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term527 A s t).
Proof. exact (@lem4078946 A s t). Qed.
Lemma lem4078948 {A : Type'} (a : A) (t : A -> Prop) : ((@INSERT A a t) = (@EMPTY A)) = (term528 A a t).
Proof. exact (@lem4078947 A (@INSERT A a t) (@EMPTY A)). Qed.
Lemma lem4078957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4078958 {A : Type'} (a : A) (t : A -> Prop) : (term529 A a t) = (term530 A a t).
Proof. exact (MK_COMB (@lem4078957) (@lem4078948 A a t)). Qed.
Lemma lem4078959 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term531 A n s a t) = (term532 A n s a t).
Proof. exact (MK_COMB (@lem4078942 A t n a s) (@lem4078958 A a t)). Qed.
Lemma lem4078962 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term532 A n s a t) = (term531 A n s a t).
Proof. exact (SYM (@lem4078959 A n s a t)). Qed.
Lemma lem4078976 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4078977 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4078976 A P x). Qed.
Lemma lem4078978 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4078977 A t x). Qed.
Lemma lem4078979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4078980 {A : Type'} (t : A -> Prop) (x : A) : (term429 A x t) = (term430 A t x).
Proof. exact (MK_COMB (@lem4078979) (@lem4078978 A t x)). Qed.
Lemma lem4078982 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4078983 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4078982 A P x). Qed.
Lemma lem4078984 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4078983 A s x). Qed.
Lemma lem4078985 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term431 A t x s) = (term432 A t s x).
Proof. exact (MK_COMB (@lem4078980 A t x) (@lem4078984 A s x)). Qed.
Lemma lem4078988 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term433 A t s) = (term434 A t s).
Proof. exact (fun_ext (fun x : A => @lem4078985 A t s x)). Qed.
Lemma lem4078989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4078990 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term418 A t s) = (term435 A t s).
Proof. exact (MK_COMB (@lem4078989 A) (@lem4078988 A t s)). Qed.
Lemma lem4078995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4078996 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term419 A t s) = (term436 A t s).
Proof. exact (MK_COMB (@lem4078995) (@lem4078990 A t s)). Qed.
Lemma lem4079002 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4079003 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4079002 A P x). Qed.
Lemma lem4079004 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem4079003 A s a). Qed.
Lemma lem4079005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4079006 {A : Type'} (s : A -> Prop) (a : A) : (term339 A a s) = (term437 A s a).
Proof. exact (MK_COMB (@lem4079005) (@lem4079004 A s a)). Qed.
Lemma lem4079007 {A : Type'} (n : nat) (s : A -> Prop) : (term438 A n s) = (term438 A n s).
Proof. exact (eq_refl (term438 A n s)). Qed.
Lemma lem4079008 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term415 A n a s) = (term439 A n s a).
Proof. exact (MK_COMB (@lem4079007 A n s) (@lem4079006 A s a)). Qed.
Lemma lem4079011 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term420 A t n a s) = (term440 A t n s a).
Proof. exact (MK_COMB (@lem4078996 A t s) (@lem4079008 A n s a)). Qed.
Lemma lem4079014 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4079015 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term422 A t n a s) = (term441 A t n s a).
Proof. exact (MK_COMB (@lem4079014 A t n) (@lem4079011 A t n s a)). Qed.
Lemma lem4079018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4079019 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term424 A t n a s) = (term442 A t n s a).
Proof. exact (MK_COMB (@lem4079018) (@lem4079015 A t n s a)). Qed.
Lemma lem4079027 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4079028 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (@lem4079027 A y x s). Qed.
Lemma lem4079029 {A : Type'} (a : A) (x : A) (t : A -> Prop) : (term443 A x a t) = (term444 A a x t).
Proof. exact (@lem4079028 A a x t). Qed.
Lemma lem4079035 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4079036 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4079035 A P x). Qed.
Lemma lem4079037 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4079036 A t x). Qed.
Lemma lem4079038 {A : Type'} (x : A) (a : A) : (term445 A x a) = (term445 A x a).
Proof. exact (eq_refl (term445 A x a)). Qed.
Lemma lem4079039 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term444 A a x t) = (term446 A a t x).
Proof. exact (MK_COMB (@lem4079038 A x a) (@lem4079037 A t x)). Qed.
Lemma lem4079042 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term443 A x a t) = (term446 A a t x).
Proof. exact (TRANS (@lem4079029 A a x t) (@lem4079039 A a t x)). Qed.
Lemma lem4079043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4079044 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term533 A x a t) = (term534 A a t x).
Proof. exact (MK_COMB (@lem4079043) (@lem4079042 A a t x)). Qed.
Lemma lem4079046 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4079047 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4079046 A x). Qed.
Lemma lem4079048 {A : Type'} (a : A) (t : A -> Prop) (x : A) : ((term443 A x a t) = (@IN A x (@EMPTY A))) = ((term446 A a t x) = False).
Proof. exact (MK_COMB (@lem4079044 A a t x) (@lem4079047 A x)). Qed.
Lemma lem4079050 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4079051 {A : Type'} (a : A) (t : A -> Prop) (x : A) : ((term446 A a t x) = False) = (term478 A a t x).
Proof. exact (@lem4079050 (term446 A a t x)). Qed.
Lemma lem4079056 {A : Type'} (a : A) (t : A -> Prop) (x : A) : ((term443 A x a t) = (@IN A x (@EMPTY A))) = (term478 A a t x).
Proof. exact (TRANS (@lem4079048 A a t x) (@lem4079051 A a t x)). Qed.
Lemma lem4079057 {A : Type'} (a : A) (t : A -> Prop) : (term535 A a t) = (term536 A a t).
Proof. exact (fun_ext (fun x : A => @lem4079056 A a t x)). Qed.
Lemma lem4079058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079059 {A : Type'} (a : A) (t : A -> Prop) : (term528 A a t) = (term537 A a t).
Proof. exact (MK_COMB (@lem4079058 A) (@lem4079057 A a t)). Qed.
Lemma lem4079064 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4079065 {A : Type'} (a : A) (t : A -> Prop) : (term530 A a t) = (term538 A a t).
Proof. exact (MK_COMB (@lem4079064) (@lem4079059 A a t)). Qed.
Lemma lem4079066 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term532 A n s a t) = (term539 A n s a t).
Proof. exact (MK_COMB (@lem4079019 A t n s a) (@lem4079065 A a t)). Qed.
Lemma lem4079069 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term539 A n s a t) = (term532 A n s a t).
Proof. exact (SYM (@lem4079066 A n s a t)). Qed.
Lemma lem4079071 (p : Prop) : p = (term252 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4079072 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term539 A n s a t) = (term540 A n s a t).
Proof. exact (@lem4079071 (term539 A n s a t)). Qed.
Lemma lem4079073 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term540 A n s a t) = (term539 A n s a t).
Proof. exact (SYM (@lem4079072 A n s a t)). Qed.
Lemma lem4079074 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term541 A n s a t) : term541 A n s a t.
Proof. exact (h1). Qed.
Lemma lem4079077 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term540 A n s a t) : term540 A n s a t.
Proof. exact (h1). Qed.
Lemma lem4079078 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term542 A n s a t.
Proof. exact (fun h0 : term540 A n s a t => @lem4079077 A n s a t h0). Qed.
Lemma lem4079079 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term542 A n s a t) : term542 A n s a t.
Proof. exact (h1). Qed.
Lemma lem4079080 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term540 A n s a t) : term540 A n s a t.
Proof. exact (h1). Qed.
Lemma lem4079081 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term540 A n s a t) (h2 : term542 A n s a t) : term540 A n s a t.
Proof. exact (@lem4079079 A n s a t h2 (@lem4079080 A n s a t h1)). Qed.
Lemma lem4079082 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term540 A n s a t) : term543 A n s a t.
Proof. exact (fun h0 : term542 A n s a t => @lem4079081 A n s a t h1 h0). Qed.
Lemma lem4079083 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term542 A n s a t) : term542 A n s a t.
Proof. exact (h1). Qed.
Lemma lem4079084 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term540 A n s a t) (h2 : term542 A n s a t) : term540 A n s a t.
Proof. exact (@lem4079082 A n s a t h1 (@lem4079083 A n s a t h2)). Qed.
Lemma lem4079085 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term542 A n s a t) : term542 A n s a t.
Proof. exact (fun h0 : term540 A n s a t => @lem4079084 A n s a t h0 h1). Qed.
Lemma lem4079086 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term544 A n s a t.
Proof. exact (fun h0 : term542 A n s a t => @lem4079085 A n s a t h0). Qed.
Lemma lem4079089 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term542 A n s a t.
Proof. exact (@lem4079086 A n s a t (@lem4079078 A n s a t)). Qed.
Lemma lem4079090 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term542 A n s a t.
Proof. exact (@lem4079089 A n s a t). Qed.
Lemma lem4079108 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4079109 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term540 A n s a t) = (term545 A n s a t).
Proof. exact (@lem4079108 (term541 A n s a t)). Qed.
Lemma lem4079111 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4079112 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term545 A n s a t) = (term539 A n s a t).
Proof. exact (@lem4079111 (term539 A n s a t)). Qed.
Lemma lem4079115 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term540 A n s a t) = (term539 A n s a t).
Proof. exact (TRANS (@lem4079109 A n s a t) (@lem4079112 A n s a t)). Qed.
Lemma lem4079136 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term546 A s a t) = (term547 A s a t).
Proof. exact (fun_ext (fun n : nat => @lem4079115 A n s a t)). Qed.
Lemma lem4079137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4079138 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term548 A s a t) = (term549 A s a t).
Proof. exact (MK_COMB (@lem4079137) (@lem4079136 A s a t)). Qed.
Lemma lem4079143 {A : Type'} (a : A) (t : A -> Prop) : (term550 A a t) = (term551 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4079138 A s a t)). Qed.
Lemma lem4079144 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4079145 {A : Type'} (a : A) (t : A -> Prop) : (term552 A a t) = (term553 A a t).
Proof. exact (MK_COMB (@lem4079144 A) (@lem4079143 A a t)). Qed.
Lemma lem4079150 {A : Type'} (t : A -> Prop) : (term554 A t) = (term555 A t).
Proof. exact (fun_ext (fun a : A => @lem4079145 A a t)). Qed.
Lemma lem4079151 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079152 {A : Type'} (t : A -> Prop) : (term556 A t) = (term557 A t).
Proof. exact (MK_COMB (@lem4079151 A) (@lem4079150 A t)). Qed.
Lemma lem4079157 {A : Type'} : (term558 A) = (term559 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4079152 A t)). Qed.
Lemma lem4079158 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4079167 {A : Type'} : (term560 A) = (term561 A).
Proof. exact (MK_COMB (@lem4079158 A) (@lem4079157 A)). Qed.
Lemma lem4079174 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term478 A a t x) = (term478 A a t x).
Proof. exact (eq_refl (term478 A a t x)). Qed.
Lemma lem4079175 {A : Type'} (a : A) (t : A -> Prop) : (term536 A a t) = (term536 A a t).
Proof. exact (fun_ext (fun x : A => @lem4079174 A a t x)). Qed.
Lemma lem4079176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079177 {A : Type'} (a : A) (t : A -> Prop) : (term537 A a t) = (term537 A a t).
Proof. exact (MK_COMB (@lem4079176 A) (@lem4079175 A a t)). Qed.
Lemma lem4079178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4079179 {A : Type'} (a : A) (t : A -> Prop) : (term538 A a t) = (term538 A a t).
Proof. exact (MK_COMB (@lem4079178) (@lem4079177 A a t)). Qed.
Lemma lem4079190 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term439 A n s a) = (term439 A n s a).
Proof. exact (eq_refl (term439 A n s a)). Qed.
Lemma lem4079195 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term432 A t s x) = (term432 A t s x).
Proof. exact (eq_refl (term432 A t s x)). Qed.
Lemma lem4079196 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term434 A t s) = (term434 A t s).
Proof. exact (fun_ext (fun x : A => @lem4079195 A t s x)). Qed.
Lemma lem4079197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079198 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term435 A t s) = (term435 A t s).
Proof. exact (MK_COMB (@lem4079197 A) (@lem4079196 A t s)). Qed.
Lemma lem4079199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079200 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term436 A t s) = (term436 A t s).
Proof. exact (MK_COMB (@lem4079199) (@lem4079198 A t s)). Qed.
Lemma lem4079201 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term440 A t n s a) = (term440 A t n s a).
Proof. exact (MK_COMB (@lem4079200 A t s) (@lem4079190 A n s a)). Qed.
Lemma lem4079204 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4079205 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term441 A t n s a) = (term441 A t n s a).
Proof. exact (MK_COMB (@lem4079204 A t n) (@lem4079201 A t n s a)). Qed.
Lemma lem4079206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4079207 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term442 A t n s a) = (term442 A t n s a).
Proof. exact (MK_COMB (@lem4079206) (@lem4079205 A t n s a)). Qed.
Lemma lem4079208 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term539 A n s a t) = (term539 A n s a t).
Proof. exact (MK_COMB (@lem4079207 A t n s a) (@lem4079179 A a t)). Qed.
Lemma lem4079209 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term547 A s a t) = (term547 A s a t).
Proof. exact (fun_ext (fun n : nat => @lem4079208 A n s a t)). Qed.
Lemma lem4079210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4079211 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term549 A s a t) = (term549 A s a t).
Proof. exact (MK_COMB (@lem4079210) (@lem4079209 A s a t)). Qed.
Lemma lem4079212 {A : Type'} (a : A) (t : A -> Prop) : (term551 A a t) = (term551 A a t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4079211 A s a t)). Qed.
Lemma lem4079213 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4079214 {A : Type'} (a : A) (t : A -> Prop) : (term553 A a t) = (term553 A a t).
Proof. exact (MK_COMB (@lem4079213 A) (@lem4079212 A a t)). Qed.
Lemma lem4079215 {A : Type'} (t : A -> Prop) : (term555 A t) = (term555 A t).
Proof. exact (fun_ext (fun a : A => @lem4079214 A a t)). Qed.
Lemma lem4079216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079217 {A : Type'} (t : A -> Prop) : (term557 A t) = (term557 A t).
Proof. exact (MK_COMB (@lem4079216 A) (@lem4079215 A t)). Qed.
Lemma lem4079218 {A : Type'} : (term559 A) = (term559 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4079217 A t)). Qed.
Lemma lem4079219 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4079220 {A : Type'} : (term561 A) = (term561 A).
Proof. exact (MK_COMB (@lem4079219 A) (@lem4079218 A)). Qed.
Lemma lem4079273 {A : Type'} : (term560 A) = (term561 A).
Proof. exact (TRANS (@lem4079167 A) (@lem4079220 A)). Qed.
Lemma lem4079274 {A : Type'} : (term561 A) = (term560 A).
Proof. exact (SYM (@lem4079273 A)). Qed.
Lemma lem4079275 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term441 A t n s a.
Proof. exact (h1). Qed.
Lemma lem4079276 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term537 A a t.
Proof. exact (h1). Qed.
Lemma lem4079284 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term432 A t s x) = (term479 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4079285 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term434 A t s) = (term480 A t s).
Proof. exact (fun_ext (fun x : A => @lem4079284 A t s x)). Qed.
Lemma lem4079286 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079287 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term435 A t s) = (term481 A t s).
Proof. exact (MK_COMB (@lem4079286 A) (@lem4079285 A t s)). Qed.
Lemma lem4079294 {A : Type'} (n : nat) (s : A -> Prop) : (term399 A n s) = (term482 A n s).
Proof. exact (@lem17265 (@FINITE A s) (term396 A n s)). Qed.
Lemma lem4079295 {A : Type'} (s : A -> Prop) (a : A) : (term437 A s a) = (term437 A s a).
Proof. exact (eq_refl (term437 A s a)). Qed.
Lemma lem4079296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079297 {A : Type'} (n : nat) (s : A -> Prop) : (term438 A n s) = (term483 A n s).
Proof. exact (MK_COMB (@lem4079296) (@lem4079294 A n s)). Qed.
Lemma lem4079298 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term439 A n s a) = (term484 A n s a).
Proof. exact (MK_COMB (@lem4079297 A n s) (@lem4079295 A s a)). Qed.
Lemma lem4079299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079300 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term436 A t s) = (term485 A t s).
Proof. exact (MK_COMB (@lem4079299) (@lem4079287 A t s)). Qed.
Lemma lem4079301 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term440 A t n s a) = (term486 A t n s a).
Proof. exact (MK_COMB (@lem4079300 A t s) (@lem4079298 A n s a)). Qed.
Lemma lem4079303 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4079340 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term441 A t n s a) = (term487 A t n s a).
Proof. exact (MK_COMB (@lem4079303 A t n) (@lem4079301 A t n s a)). Qed.
Lemma lem4079341 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term487 A t n s a.
Proof. exact (EQ_MP (@lem4079340 A t n s a) (@lem4079275 A t n s a h1)). Qed.
Lemma lem4079348 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term478 A a t x) = (term488 A a t x).
Proof. exact (@lem17160 (x = a) (t x)). Qed.
Lemma lem4079349 {A : Type'} (a : A) (t : A -> Prop) : (term536 A a t) = (term562 A a t).
Proof. exact (fun_ext (fun x : A => @lem4079348 A a t x)). Qed.
Lemma lem4079350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079351 {A : Type'} (a : A) (t : A -> Prop) : (term537 A a t) = (term563 A a t).
Proof. exact (MK_COMB (@lem4079350 A) (@lem4079349 A a t)). Qed.
Lemma lem4079353 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term564 A P Q) = (term565 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4079354 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term564 A P Q) = (term565 A P Q).
Proof. exact (@lem4079353 A P Q). Qed.
Lemma lem4079355 {A : Type'} (a : A) (t : A -> Prop) : (term566 A a t) = (term567 A a t).
Proof. exact (@lem4079354 A (term504 A a) (term568 A t)). Qed.
Lemma lem4079356 {A : Type'} (x : A) (a : A) : (term505 A a x) = (term503 A x a).
Proof. exact (eq_refl (term505 A a x)). Qed.
Lemma lem4079357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079358 {A : Type'} (x : A) (a : A) : (term569 A a x) = (term500 A x a).
Proof. exact (MK_COMB (@lem4079357) (@lem4079356 A x a)). Qed.
Lemma lem4079359 {A : Type'} (t : A -> Prop) (x : A) : (term570 A t x) = (term437 A t x).
Proof. exact (eq_refl (term570 A t x)). Qed.
Lemma lem4079360 {A : Type'} (a : A) (t : A -> Prop) (x : A) : (term571 A a t x) = (term488 A a t x).
Proof. exact (MK_COMB (@lem4079358 A x a) (@lem4079359 A t x)). Qed.
Lemma lem4079361 {A : Type'} (a : A) (t : A -> Prop) : (term572 A a t) = (term562 A a t).
Proof. exact (fun_ext (fun x : A => @lem4079360 A a t x)). Qed.
Lemma lem4079362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079363 {A : Type'} (a : A) (t : A -> Prop) : (term566 A a t) = (term563 A a t).
Proof. exact (MK_COMB (@lem4079362 A) (@lem4079361 A a t)). Qed.
Lemma lem4079364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4079365 {A : Type'} (a : A) (t : A -> Prop) : (term573 A a t) = (term574 A a t).
Proof. exact (MK_COMB (@lem4079364) (@lem4079363 A a t)). Qed.
Lemma lem4079366 {A : Type'} (x : A) (a : A) : (term505 A a x) = (term503 A x a).
Proof. exact (eq_refl (term505 A a x)). Qed.
Lemma lem4079367 {A : Type'} (a : A) : (term575 A a) = (term504 A a).
Proof. exact (fun_ext (fun x : A => @lem4079366 A x a)). Qed.
Lemma lem4079368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079369 {A : Type'} (a : A) : (term576 A a) = (term577 A a).
Proof. exact (MK_COMB (@lem4079368 A) (@lem4079367 A a)). Qed.
Lemma lem4079370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079371 {A : Type'} (a : A) : (term578 A a) = (term579 A a).
Proof. exact (MK_COMB (@lem4079370) (@lem4079369 A a)). Qed.
Lemma lem4079372 {A : Type'} (t : A -> Prop) (x : A) : (term570 A t x) = (term437 A t x).
Proof. exact (eq_refl (term570 A t x)). Qed.
Lemma lem4079373 {A : Type'} (t : A -> Prop) : (term580 A t) = (term568 A t).
Proof. exact (fun_ext (fun x : A => @lem4079372 A t x)). Qed.
Lemma lem4079374 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079375 {A : Type'} (t : A -> Prop) : (term581 A t) = (term582 A t).
Proof. exact (MK_COMB (@lem4079374 A) (@lem4079373 A t)). Qed.
Lemma lem4079376 {A : Type'} (a : A) (t : A -> Prop) : (term567 A a t) = (term583 A a t).
Proof. exact (MK_COMB (@lem4079371 A a) (@lem4079375 A t)). Qed.
Lemma lem4079377 {A : Type'} (a : A) (t : A -> Prop) : ((term566 A a t) = (term567 A a t)) = ((term563 A a t) = (term583 A a t)).
Proof. exact (MK_COMB (@lem4079365 A a t) (@lem4079376 A a t)). Qed.
Lemma lem4079388 {A : Type'} (a : A) (t : A -> Prop) : (term563 A a t) = (term583 A a t).
Proof. exact (EQ_MP (@lem4079377 A a t) (@lem4079355 A a t)). Qed.
Lemma lem4079389 {A : Type'} (a : A) (t : A -> Prop) : (term537 A a t) = (term583 A a t).
Proof. exact (TRANS (@lem4079351 A a t) (@lem4079388 A a t)). Qed.
Lemma lem4079390 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term583 A a t.
Proof. exact (EQ_MP (@lem4079389 A a t) (@lem4079276 A a t h1)). Qed.
Lemma lem4079391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4079396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4079397 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4079396 A Prop f x). Qed.
Lemma lem4079399 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4079397 A s a). Qed.
Lemma lem4079400 {A : Type'} (s : A -> Prop) (a : A) : (term437 A s a) = (term489 A s a).
Proof. exact (MK_COMB (@lem4079391) (@lem4079399 A s a)). Qed.
Lemma lem4079417 {A : Type'} (n : nat) (s : A -> Prop) : (term483 A n s) = (term483 A n s).
Proof. exact (eq_refl (term483 A n s)). Qed.
Lemma lem4079418 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term484 A n s a) = (term490 A n s a).
Proof. exact (MK_COMB (@lem4079417 A n s) (@lem4079400 A s a)). Qed.
Lemma lem4079423 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4079424 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4079423 A Prop f x). Qed.
Lemma lem4079426 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4079424 A s x). Qed.
Lemma lem4079427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4079432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4079433 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4079432 A Prop f x). Qed.
Lemma lem4079435 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4079433 A t x). Qed.
Lemma lem4079436 {A : Type'} (t : A -> Prop) (x : A) : (term437 A t x) = (term489 A t x).
Proof. exact (MK_COMB (@lem4079427) (@lem4079435 A t x)). Qed.
Lemma lem4079437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4079438 {A : Type'} (t : A -> Prop) (x : A) : (term491 A t x) = (term492 A t x).
Proof. exact (MK_COMB (@lem4079437) (@lem4079436 A t x)). Qed.
Lemma lem4079439 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term479 A t s x) = (term493 A t s x).
Proof. exact (MK_COMB (@lem4079438 A t x) (@lem4079426 A s x)). Qed.
Lemma lem4079440 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term480 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4079439 A t s x)). Qed.
Lemma lem4079441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079442 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term481 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4079441 A) (@lem4079440 A t s)). Qed.
Lemma lem4079443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079444 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term485 A t s) = (term496 A t s).
Proof. exact (MK_COMB (@lem4079443) (@lem4079442 A t s)). Qed.
Lemma lem4079445 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term486 A t n s a) = (term497 A t n s a).
Proof. exact (MK_COMB (@lem4079444 A t s) (@lem4079418 A n s a)). Qed.
Lemma lem4079452 {A : Type'} (t : A -> Prop) (n : nat) : (term421 A t n) = (term421 A t n).
Proof. exact (eq_refl (term421 A t n)). Qed.
Lemma lem4079453 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term487 A t n s a) = (term498 A t n s a).
Proof. exact (MK_COMB (@lem4079452 A t n) (@lem4079445 A t n s a)). Qed.
Lemma lem4079454 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term498 A t n s a.
Proof. exact (EQ_MP (@lem4079453 A t n s a) (@lem4079341 A t n s a h1)). Qed.
Lemma lem4079455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4079460 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4079461 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4079460 A Prop f x). Qed.
Lemma lem4079463 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4079461 A t x). Qed.
Lemma lem4079464 {A : Type'} (t : A -> Prop) (x : A) : (term437 A t x) = (term489 A t x).
Proof. exact (MK_COMB (@lem4079455) (@lem4079463 A t x)). Qed.
Lemma lem4079465 {A : Type'} (t : A -> Prop) : (term568 A t) = (term584 A t).
Proof. exact (fun_ext (fun x : A => @lem4079464 A t x)). Qed.
Lemma lem4079466 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079467 {A : Type'} (t : A -> Prop) : (term582 A t) = (term585 A t).
Proof. exact (MK_COMB (@lem4079466 A) (@lem4079465 A t)). Qed.
Lemma lem4079474 {A : Type'} (x : A) (a : A) : (term503 A x a) = (term503 A x a).
Proof. exact (eq_refl (term503 A x a)). Qed.
Lemma lem4079475 {A : Type'} (a : A) : (term504 A a) = (term504 A a).
Proof. exact (fun_ext (fun x : A => @lem4079474 A x a)). Qed.
Lemma lem4079476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079477 {A : Type'} (a : A) : (term577 A a) = (term577 A a).
Proof. exact (MK_COMB (@lem4079476 A) (@lem4079475 A a)). Qed.
Lemma lem4079478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079479 {A : Type'} (a : A) : (term579 A a) = (term579 A a).
Proof. exact (MK_COMB (@lem4079478) (@lem4079477 A a)). Qed.
Lemma lem4079480 {A : Type'} (a : A) (t : A -> Prop) : (term583 A a t) = (term586 A a t).
Proof. exact (MK_COMB (@lem4079479 A a) (@lem4079467 A t)). Qed.
Lemma lem4079481 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term586 A a t.
Proof. exact (EQ_MP (@lem4079480 A a t) (@lem4079390 A a t h1)). Qed.
Lemma lem4079483 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term577 A a.
Proof. exact (proj1 (@lem4079481 A a t h1)). Qed.
Lemma lem4079484 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term497 A t n s a.
Proof. exact (proj2 (@lem4079454 A t n s a h1)). Qed.
Lemma lem4079486 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term490 A n s a.
Proof. exact (proj2 (@lem4079484 A t n s a h1)). Qed.
Lemma lem4079489 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term482 A n s.
Proof. exact (proj1 (@lem4079486 A t n s a h1)). Qed.
Lemma lem4079493 {A : Type'} (x : A) (a : A) : (term503 A x a) = (term503 A x a).
Proof. exact (eq_refl (term503 A x a)). Qed.
Lemma lem4079494 {A : Type'} (a : A) : (term504 A a) = (term504 A a).
Proof. exact (fun_ext (fun x : A => @lem4079493 A x a)). Qed.
Lemma lem4079495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079497 {A : Type'} (a : A) : (term577 A a) = (term577 A a).
Proof. exact (MK_COMB (@lem4079495 A) (@lem4079494 A a)). Qed.
Lemma lem4079498 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term577 A a.
Proof. exact (EQ_MP (@lem4079497 A a) (@lem4079483 A a t h1)). Qed.
Lemma lem4079532 {A : Type'} (x : A) (a : A) : (term503 A x a) = (term503 A x a).
Proof. exact (eq_refl (term503 A x a)). Qed.
Lemma lem4079533 {A : Type'} (a : A) : (term504 A a) = (term504 A a).
Proof. exact (fun_ext (fun x : A => @lem4079532 A x a)). Qed.
Lemma lem4079534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4079536 {A : Type'} (a : A) : (term577 A a) = (term577 A a).
Proof. exact (MK_COMB (@lem4079534 A) (@lem4079533 A a)). Qed.
Lemma lem4079537 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term577 A a.
Proof. exact (EQ_MP (@lem4079536 A a) (@lem4079483 A a t h1)). Qed.
Lemma lem4079570 {A : Type'} (_47971 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term505 A a _47971.
Proof. exact (@lem4079498 A a t h1 _47971). Qed.
Lemma lem4079571 {A : Type'} (_47971 : A) (a : A) : (term505 A a _47971) = (term503 A _47971 a).
Proof. exact (eq_refl (term505 A a _47971)). Qed.
Lemma lem4079579 {A : Type'} (_47974 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term505 A a _47974.
Proof. exact (@lem4079537 A a t h1 _47974). Qed.
Lemma lem4079580 {A : Type'} (_47974 : A) (a : A) : (term505 A a _47974) = (term503 A _47974 a).
Proof. exact (eq_refl (term505 A a _47974)). Qed.
Lemma lem4079589 {A : Type'} (_47971 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term503 A _47971 a.
Proof. exact (EQ_MP (@lem4079571 A _47971 a) (@lem4079570 A _47971 a t h1)). Qed.
Lemma lem4079605 {A : Type'} (_47974 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term503 A _47974 a.
Proof. exact (EQ_MP (@lem4079580 A _47974 a) (@lem4079579 A _47974 a t h1)). Qed.
Lemma lem4079677 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4079678 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4079677 A x). Qed.
Lemma lem4079679 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4079678 A a). Qed.
Lemma lem4079680 {A : Type'} (a : A) : term510 A a.
Proof. exact (fun h0 : term507 A a => @lem4079679 A a). Qed.
Lemma lem4079682 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4079683 {A : Type'} (a : A) : (term510 A a) = (a = a).
Proof. exact (@lem4079682 (a = a)). Qed.
Lemma lem4079684 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4079683 A a) (@lem4079680 A a)). Qed.
Lemma lem4079687 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4079689 {A : Type'} (_47971 : A) (a : A) : (term503 A _47971 a) = (term587 A _47971 a).
Proof. exact (@lem4079687 (_47971 = a)). Qed.
Lemma lem4079692 {A : Type'} (_47971 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term587 A _47971 a.
Proof. exact (EQ_MP (@lem4079689 A _47971 a) (@lem4079589 A _47971 a t h1)). Qed.
Lemma lem4079693 {A : Type'} (_47971 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term587 A _47971 a.
Proof. exact (@lem4079692 A _47971 a t h1). Qed.
Lemma lem4079694 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term511 A a.
Proof. exact (@lem4079693 A a a t h1). Qed.
Lemma lem4079697 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : False.
Proof. exact (@lem4079694 A a t h1 (@lem4079684 A a)). Qed.
Lemma lem4079698 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term304.
Proof. exact (fun h0 : ~ False => @lem4079697 A a t h1). Qed.
Lemma lem4079700 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4079701 : term304 = False.
Proof. exact (@lem4079700 False). Qed.
Lemma lem4079702 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : False.
Proof. exact (EQ_MP (@lem4079701) (@lem4079698 A a t h1)). Qed.
Lemma lem4079775 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4079776 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4079775 A x). Qed.
Lemma lem4079777 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4079776 A a). Qed.
Lemma lem4079778 {A : Type'} (a : A) : term510 A a.
Proof. exact (fun h0 : term507 A a => @lem4079777 A a). Qed.
Lemma lem4079780 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4079781 {A : Type'} (a : A) : (term510 A a) = (a = a).
Proof. exact (@lem4079780 (a = a)). Qed.
Lemma lem4079782 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4079781 A a) (@lem4079778 A a)). Qed.
Lemma lem4079785 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4079787 {A : Type'} (_47974 : A) (a : A) : (term503 A _47974 a) = (term587 A _47974 a).
Proof. exact (@lem4079785 (_47974 = a)). Qed.
Lemma lem4079790 {A : Type'} (_47974 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term587 A _47974 a.
Proof. exact (EQ_MP (@lem4079787 A _47974 a) (@lem4079605 A _47974 a t h1)). Qed.
Lemma lem4079791 {A : Type'} (_47974 : A) (a : A) (t : A -> Prop) (h1 : term537 A a t) : term587 A _47974 a.
Proof. exact (@lem4079790 A _47974 a t h1). Qed.
Lemma lem4079792 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term511 A a.
Proof. exact (@lem4079791 A a a t h1). Qed.
Lemma lem4079795 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : False.
Proof. exact (@lem4079792 A a t h1 (@lem4079782 A a)). Qed.
Lemma lem4079796 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : term304.
Proof. exact (fun h0 : ~ False => @lem4079795 A a t h1). Qed.
Lemma lem4079798 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4079799 : term304 = False.
Proof. exact (@lem4079798 False). Qed.
Lemma lem4079800 {A : Type'} (a : A) (t : A -> Prop) (h1 : term537 A a t) : False.
Proof. exact (EQ_MP (@lem4079799) (@lem4079796 A a t h1)). Qed.
Lemma lem4079801 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term537 A a t) (h2 : term441 A t n s a) : False.
Proof. exact (or_elim (@lem4079489 A t n s a h2) (fun h0 : term305 A s => @lem4079702 A a t h1) (fun h0 : term396 A n s => @lem4079800 A a t h1)). Qed.
Lemma lem4079802 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term588 A a t.
Proof. exact (fun h0 : term537 A a t => @lem4079801 A t n s a h0 h1). Qed.
Lemma lem4079803 {A : Type'} (a : A) (t : A -> Prop) : (term588 A a t) = (term538 A a t).
Proof. exact (@lem69 (term537 A a t)). Qed.
Lemma lem4079804 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term441 A t n s a) : term538 A a t.
Proof. exact (EQ_MP (@lem4079803 A a t) (@lem4079802 A t n s a h1)). Qed.
Lemma lem4079805 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term539 A n s a t.
Proof. exact (fun h0 : term441 A t n s a => @lem4079804 A t n s a h0). Qed.
Lemma lem4079810 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term549 A s a t.
Proof. exact (fun n : nat => @lem4079805 A n s a t). Qed.
Lemma lem4079815 {A : Type'} (a : A) (t : A -> Prop) : term553 A a t.
Proof. exact (fun s : A -> Prop => @lem4079810 A s a t). Qed.
Lemma lem4079820 {A : Type'} (t : A -> Prop) : term557 A t.
Proof. exact (fun a : A => @lem4079815 A a t). Qed.
Lemma lem4079825 {A : Type'} : term561 A.
Proof. exact (fun t : A -> Prop => @lem4079820 A t). Qed.
Lemma lem4079826 {A : Type'} : term560 A.
Proof. exact (EQ_MP (@lem4079274 A) (@lem4079825 A)). Qed.
Lemma lem4079827 {A : Type'} (t : A -> Prop) : term589 A t.
Proof. exact (@lem4079826 A t). Qed.
Lemma lem4079828 {A : Type'} (t : A -> Prop) : (term589 A t) = (term556 A t).
Proof. exact (eq_refl (term589 A t)). Qed.
Lemma lem4079829 {A : Type'} (t : A -> Prop) : term556 A t.
Proof. exact (EQ_MP (@lem4079828 A t) (@lem4079827 A t)). Qed.
Lemma lem4079830 {A : Type'} (t : A -> Prop) (a : A) : term590 A t a.
Proof. exact (@lem4079829 A t a). Qed.
Lemma lem4079831 {A : Type'} (a : A) (t : A -> Prop) : (term590 A t a) = (term552 A a t).
Proof. exact (eq_refl (term590 A t a)). Qed.
Lemma lem4079832 {A : Type'} (a : A) (t : A -> Prop) : term552 A a t.
Proof. exact (EQ_MP (@lem4079831 A a t) (@lem4079830 A t a)). Qed.
Lemma lem4079833 {A : Type'} (a : A) (t : A -> Prop) (s : A -> Prop) : term591 A a t s.
Proof. exact (@lem4079832 A a t s). Qed.
Lemma lem4079834 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term591 A a t s) = (term548 A s a t).
Proof. exact (eq_refl (term591 A a t s)). Qed.
Lemma lem4079835 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : term548 A s a t.
Proof. exact (EQ_MP (@lem4079834 A s a t) (@lem4079833 A a t s)). Qed.
Lemma lem4079836 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (n : nat) : term592 A s a t n.
Proof. exact (@lem4079835 A s a t n). Qed.
Lemma lem4079837 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : (term592 A s a t n) = (term540 A n s a t).
Proof. exact (eq_refl (term592 A s a t n)). Qed.
Lemma lem4079838 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term540 A n s a t.
Proof. exact (EQ_MP (@lem4079837 A n s a t) (@lem4079836 A s a t n)). Qed.
Lemma lem4079840 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term540 A n s a t.
Proof. exact (@lem4079090 A n s a t (@lem4079838 A n s a t)). Qed.
Lemma lem4079841 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term541 A n s a t) : False.
Proof. exact (@lem4079840 A n s a t (@lem4079074 A n s a t h1)). Qed.
Lemma lem4079842 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term541 A n s a t) : (term541 A n s a t) = False.
Proof. exact (prop_ext (fun h2 : term541 A n s a t => @lem4079841 A n s a t h1) (fun h2 : False => @lem4079074 A n s a t h1)). Qed.
Lemma lem4079843 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (h1 : term541 A n s a t) : False.
Proof. exact (EQ_MP (@lem4079842 A n s a t h1) (@lem4079074 A n s a t h1)). Qed.
Lemma lem4079844 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term540 A n s a t.
Proof. exact (fun h0 : term541 A n s a t => @lem4079843 A n s a t h0). Qed.
Lemma lem4079845 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term539 A n s a t.
Proof. exact (EQ_MP (@lem4079073 A n s a t) (@lem4079844 A n s a t)). Qed.
Lemma lem4079846 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term532 A n s a t.
Proof. exact (EQ_MP (@lem4079069 A n s a t) (@lem4079845 A n s a t)). Qed.
Lemma lem4079847 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) : term531 A n s a t.
Proof. exact (EQ_MP (@lem4078962 A n s a t) (@lem4079846 A n s a t)). Qed.
Lemma lem4079848 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term529 A a t.
Proof. exact (@lem4079847 A n s a t (@lem4078910 A a n t s h1 h2 h3 h4)). Qed.
Lemma lem4079850 {A : Type'} (a : A) (s : A -> Prop) (h1 : term339 A a s) : term339 A a s.
Proof. exact (h1). Qed.
Lemma lem4079854 {A : Type'} (n : nat) (s : A -> Prop) (h1 : term399 A n s) : term399 A n s.
Proof. exact (h1). Qed.
Lemma lem4079856 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @SUBSET A t s) : @SUBSET A t s.
Proof. exact (h1). Qed.
Lemma lem4079858 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term5 _100044 s n).
Proof. exact (EQ_MP (@lem4075315 _100044 s n) (@lem4075314 _100044 s n)). Qed.
Lemma lem4079859 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term5 A s n).
Proof. exact (@lem4079858 A s n). Qed.
Lemma lem4079860 {A : Type'} (t : A -> Prop) (n : nat) : (@HAS_SIZE A t n) = (term5 A t n).
Proof. exact (@lem4079859 A t n). Qed.
Lemma lem4079865 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term5 A t n.
Proof. exact (EQ_MP (@lem4079860 A t n) (@lem4077332 A t n h1)). Qed.
Lemma lem4079866 {A : Type'} : term348 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4079867 {A : Type'} (x : A) : term349 A x.
Proof. exact (@lem4079866 A x). Qed.
Lemma lem4079868 {A : Type'} (x : A) : (term349 A x) = (term350 A x).
Proof. exact (eq_refl (term349 A x)). Qed.
Lemma lem4079869 {A : Type'} (x : A) : term350 A x.
Proof. exact (EQ_MP (@lem4079868 A x) (@lem4079867 A x)). Qed.
Lemma lem4079870 {A : Type'} (x : A) (s : A -> Prop) : term351 A x s.
Proof. exact (@lem4079869 A x s). Qed.
Lemma lem4079871 {A : Type'} (x : A) (s : A -> Prop) : (term351 A x s) = (term352 A x s).
Proof. exact (eq_refl (term351 A x s)). Qed.
Lemma lem4079872 {A : Type'} (x : A) (s : A -> Prop) : term352 A x s.
Proof. exact (EQ_MP (@lem4079871 A x s) (@lem4079870 A x s)). Qed.
Lemma lem4079873 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4079874 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term353 A x s) = (term354 A x s).
Proof. exact (@lem4079872 A x s (@lem4079873 A s h1)). Qed.
Lemma lem4079881 {A : Type'} (s : A -> Prop) : term593 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem4079882 {A : Type'} (s : A -> Prop) : (term593 A s) = (term594 A s).
Proof. exact (eq_refl (term593 A s)). Qed.
Lemma lem4079883 {A : Type'} (s : A -> Prop) : term594 A s.
Proof. exact (EQ_MP (@lem4079882 A s) (@lem4079881 A s)). Qed.
Lemma lem4079884 {A : Type'} (s : A -> Prop) (x : A) : term595 A s x.
Proof. exact (@lem4079883 A s x). Qed.
Lemma lem4079885 {A : Type'} (x : A) (s : A -> Prop) : (term595 A s x) = ((term596 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term595 A s x)). Qed.
Lemma lem4079887 {A : Type'} (s : A -> Prop) : term344 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem4079888 {A : Type'} (s : A -> Prop) : (term344 A s) = (term345 A s).
Proof. exact (eq_refl (term344 A s)). Qed.
Lemma lem4079889 {A : Type'} (s : A -> Prop) : term345 A s.
Proof. exact (EQ_MP (@lem4079888 A s) (@lem4079887 A s)). Qed.
Lemma lem4079890 {A : Type'} (s : A -> Prop) (x : A) : term346 A s x.
Proof. exact (@lem4079889 A s x). Qed.
Lemma lem4079891 {A : Type'} (x : A) (s : A -> Prop) : (term346 A s x) = ((term347 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term346 A s x)). Qed.
Lemma lem4079893 {A : Type'} (x : A) : term597 A x.
Proof. exact (@lem3845383 A x). Qed.
Lemma lem4079894 {A : Type'} (x : A) : (term597 A x) = (term598 A x).
Proof. exact (eq_refl (term597 A x)). Qed.
Lemma lem4079895 {A : Type'} (x : A) : term598 A x.
Proof. exact (EQ_MP (@lem4079894 A x) (@lem4079893 A x)). Qed.
Lemma lem4079896 {A : Type'} (x : A) (s : A -> Prop) : term599 A x s.
Proof. exact (@lem4079895 A x s). Qed.
Lemma lem4079897 {A : Type'} (x : A) (s : A -> Prop) : (term599 A x s) = (term600 A x s).
Proof. exact (eq_refl (term599 A x s)). Qed.
Lemma lem4079898 {A : Type'} (x : A) (s : A -> Prop) : term600 A x s.
Proof. exact (EQ_MP (@lem4079897 A x s) (@lem4079896 A x s)). Qed.
Lemma lem4079899 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4079900 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term601 A s x) = (term602 A x s).
Proof. exact (@lem4079898 A x s (@lem4079899 A s h1)). Qed.
Lemma lem4079906 {_100044 : Type'} (s : _100044 -> Prop) : term2 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4079907 {_100044 : Type'} (s : _100044 -> Prop) : (term2 _100044 s) = (term3 _100044 s).
Proof. exact (eq_refl (term2 _100044 s)). Qed.
Lemma lem4079908 {_100044 : Type'} (s : _100044 -> Prop) : term3 _100044 s.
Proof. exact (EQ_MP (@lem4079907 _100044 s) (@lem4079906 _100044 s)). Qed.
Lemma lem4079909 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term4 _100044 s n.
Proof. exact (@lem4079908 _100044 s n). Qed.
Lemma lem4079910 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term4 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term5 _100044 s n)).
Proof. exact (eq_refl (term4 _100044 s n)). Qed.
Lemma lem4079926 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @FINITE A t.
Proof. exact (proj1 (@lem4079865 A t n h1)). Qed.
Lemma lem4079927 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem4079936 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term356 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4079937 (p : Prop) (q : Prop) (p' : Prop) : term357 p q p'.
Proof. exact (fun q' : Prop => @lem4079936 p q p' q'). Qed.
Lemma lem4079938 (p : Prop) (q : Prop) : term358 p q.
Proof. exact (fun p' : Prop => @lem4079937 p q p'). Qed.
Lemma lem4079939 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : term603 A a t a' n.
Proof. exact (@lem4079938 (term443 A a' a t) (term604 A a t a' n)). Qed.
Lemma lem4079940 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (p' : Prop) : term605 A a t a' n p'.
Proof. exact (@lem4079939 A a t a' n p'). Qed.
Lemma lem4079941 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (p' : Prop) : (term605 A a t a' n p') = (term606 A a t a' n p').
Proof. exact (eq_refl (term605 A a t a' n p')). Qed.
Lemma lem4079942 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (p' : Prop) : term606 A a t a' n p'.
Proof. exact (EQ_MP (@lem4079941 A a t a' n p') (@lem4079940 A a t a' n p')). Qed.
Lemma lem4079943 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (p' : Prop) (q' : Prop) : term607 A a t a' n p' q'.
Proof. exact (@lem4079942 A a t a' n p' q'). Qed.
Lemma lem4079944 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (p' : Prop) (q' : Prop) : (term607 A a t a' n p' q') = (term608 A a t a' n p' q').
Proof. exact (eq_refl (term607 A a t a' n p' q')). Qed.
Lemma lem4079945 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (p' : Prop) (q' : Prop) : term608 A a t a' n p' q'.
Proof. exact (EQ_MP (@lem4079944 A a t a' n p' q') (@lem4079943 A a t a' n p' q')). Qed.
Lemma lem4079946 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : (term443 A a' a t) = (term443 A a' a t).
Proof. exact (eq_refl (term443 A a' a t)). Qed.
Lemma lem4079947 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (q' : Prop) : term609 A n a' a t q'.
Proof. exact (@lem4079945 A a t a' n (term443 A a' a t) q'). Qed.
Lemma lem4079948 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (q' : Prop) : term610 A n a' a t q'.
Proof. exact (@lem4079947 A n a' a t q' (@lem4079946 A a' a t)). Qed.
Lemma lem4079949 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (h1 : term443 A a' a t) : term443 A a' a t.
Proof. exact (h1). Qed.
Lemma lem4079950 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : (term443 A a' a t) = ((term443 A a' a t) = True).
Proof. exact (@lem7 (term443 A a' a t)). Qed.
Lemma lem4079953 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term5 _100044 s n).
Proof. exact (EQ_MP (@lem4079910 _100044 s n) (@lem4079909 _100044 s n)). Qed.
Lemma lem4079954 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term5 A s n).
Proof. exact (@lem4079953 A s n). Qed.
Lemma lem4079955 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term604 A a t a' n) = (term611 A a t a' n).
Proof. exact (@lem4079954 A (term612 A a t a') n). Qed.
Lemma lem4079959 {A : Type'} (x : A) (s : A -> Prop) : (term596 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4079885 A x s) (@lem4079884 A s x)). Qed.
Lemma lem4079960 {A : Type'} (x : A) (s : A -> Prop) : (term596 A s x) = (@FINITE A s).
Proof. exact (@lem4079959 A x s). Qed.
Lemma lem4079961 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : (term613 A a t a') = (term347 A a t).
Proof. exact (@lem4079960 A a' (@INSERT A a t)). Qed.
Lemma lem4079963 {A : Type'} (x : A) (s : A -> Prop) : (term347 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4079891 A x s) (@lem4079890 A s x)). Qed.
Lemma lem4079964 {A : Type'} (x : A) (s : A -> Prop) : (term347 A x s) = (@FINITE A s).
Proof. exact (@lem4079963 A x s). Qed.
Lemma lem4079965 {A : Type'} (a : A) (t : A -> Prop) : (term347 A a t) = (@FINITE A t).
Proof. exact (@lem4079964 A a t). Qed.
Lemma lem4079967 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem4079927 A t) (@lem4079926 A t n h1)). Qed.
Lemma lem4079968 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term347 A a t) = True.
Proof. exact (TRANS (@lem4079965 A a t) (@lem4079967 A t n h1)). Qed.
Lemma lem4079969 {A : Type'} (a : A) (a' : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term613 A a t a') = True.
Proof. exact (TRANS (@lem4079961 A a' a t) (@lem4079968 A a t n h1)). Qed.
Lemma lem4079970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4079971 {A : Type'} (a : A) (a' : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term614 A a t a') = (and True).
Proof. exact (MK_COMB (@lem4079970) (@lem4079969 A a a' t n h1)). Qed.
Lemma lem4079975 {A : Type'} (x : A) (s : A -> Prop) : term600 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4079900 A x s h0). Qed.
Lemma lem4079976 {A : Type'} (x : A) (s : A -> Prop) : term600 A x s.
Proof. exact (@lem4079975 A x s). Qed.
Lemma lem4079977 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : term615 A a' a t.
Proof. exact (@lem4079976 A a' (@INSERT A a t)). Qed.
Lemma lem4079979 {A : Type'} (x : A) (s : A -> Prop) : (term347 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4079891 A x s) (@lem4079890 A s x)). Qed.
Lemma lem4079980 {A : Type'} (x : A) (s : A -> Prop) : (term347 A x s) = (@FINITE A s).
Proof. exact (@lem4079979 A x s). Qed.
Lemma lem4079981 {A : Type'} (a : A) (t : A -> Prop) : (term347 A a t) = (@FINITE A t).
Proof. exact (@lem4079980 A a t). Qed.
Lemma lem4079983 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem4079927 A t) (@lem4079926 A t n h1)). Qed.
Lemma lem4079984 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term347 A a t) = True.
Proof. exact (TRANS (@lem4079981 A a t) (@lem4079983 A t n h1)). Qed.
Lemma lem4079985 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : True = (term347 A a t).
Proof. exact (SYM (@lem4079984 A a t n h1)). Qed.
Lemma lem4079986 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term347 A a t.
Proof. exact (EQ_MP (@lem4079985 A a t n h1) (@lem0)). Qed.
Lemma lem4079987 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term616 A a t a') = (term617 A a' a t).
Proof. exact (@lem4079977 A a' a t (@lem4079986 A a t n h1)). Qed.
Lemma lem4079989 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term374 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4079990 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term375 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4079989 _2963 g t e g' t' e'). Qed.
Lemma lem4079991 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term376 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4079990 _2963 g t e g' t'). Qed.
Lemma lem4079992 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term377 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4079991 _2963 g t e g'). Qed.
Lemma lem4079993 (g : Prop) (t : nat) (e : nat) : term378 g t e.
Proof. exact (@lem4079992 nat g t e). Qed.
Lemma lem4079994 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : term618 A a' a t.
Proof. exact (@lem4079993 (term443 A a' a t) (term619 A a t) (term353 A a t)). Qed.
Lemma lem4079995 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) : term620 A a' a t g'.
Proof. exact (@lem4079994 A a' a t g'). Qed.
Lemma lem4079996 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) : (term620 A a' a t g') = (term621 A a' a t g').
Proof. exact (eq_refl (term620 A a' a t g')). Qed.
Lemma lem4079997 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) : term621 A a' a t g'.
Proof. exact (EQ_MP (@lem4079996 A a' a t g') (@lem4079995 A a' a t g')). Qed.
Lemma lem4079998 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) : term622 A a' a t g' t'.
Proof. exact (@lem4079997 A a' a t g' t'). Qed.
Lemma lem4079999 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) : (term622 A a' a t g' t') = (term623 A a' a t g' t').
Proof. exact (eq_refl (term622 A a' a t g' t')). Qed.
Lemma lem4080000 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) : term623 A a' a t g' t'.
Proof. exact (EQ_MP (@lem4079999 A a' a t g' t') (@lem4079998 A a' a t g' t')). Qed.
Lemma lem4080001 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term624 A a' a t g' t' e'.
Proof. exact (@lem4080000 A a' a t g' t' e'). Qed.
Lemma lem4080002 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term624 A a' a t g' t' e') = (term625 A a' a t g' t' e').
Proof. exact (eq_refl (term624 A a' a t g' t' e')). Qed.
Lemma lem4080003 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term625 A a' a t g' t' e'.
Proof. exact (EQ_MP (@lem4080002 A a' a t g' t' e') (@lem4080001 A a' a t g' t' e')). Qed.
Lemma lem4080005 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (h1 : term443 A a' a t) : (term443 A a' a t) = True.
Proof. exact (EQ_MP (@lem4079950 A a' a t) (@lem4079949 A a' a t h1)). Qed.
Lemma lem4080006 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (t' : nat) (e' : nat) : term626 A a' a t t' e'.
Proof. exact (@lem4080003 A a' a t True t' e'). Qed.
Lemma lem4080007 {A : Type'} (t' : nat) (e' : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : term443 A a' a t) : term627 A a' a t t' e'.
Proof. exact (@lem4080006 A a' a t t' e' (@lem4080005 A a' a t h1)). Qed.
Lemma lem4080014 {A : Type'} (x : A) (s : A -> Prop) : term352 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4079874 A x s h0). Qed.
Lemma lem4080015 {A : Type'} (x : A) (s : A -> Prop) : term352 A x s.
Proof. exact (@lem4080014 A x s). Qed.
Lemma lem4080016 {A : Type'} (a : A) (t : A -> Prop) : term352 A a t.
Proof. exact (@lem4080015 A a t). Qed.
Lemma lem4080018 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem4079927 A t) (@lem4079926 A t n h1)). Qed.
Lemma lem4080021 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : True = (@FINITE A t).
Proof. exact (SYM (@lem4080018 A t n h1)). Qed.
Lemma lem4080022 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : @FINITE A t.
Proof. exact (EQ_MP (@lem4080021 A t n h1) (@lem0)). Qed.
Lemma lem4080023 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term353 A a t) = (term354 A a t).
Proof. exact (@lem4080016 A a t (@lem4080022 A t n h1)). Qed.
Lemma lem4080025 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term374 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4080026 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term375 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4080025 _2963 g t e g' t' e'). Qed.
Lemma lem4080027 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term376 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4080026 _2963 g t e g' t'). Qed.
Lemma lem4080028 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term377 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4080027 _2963 g t e g'). Qed.
Lemma lem4080029 (g : Prop) (t : nat) (e : nat) : term378 g t e.
Proof. exact (@lem4080028 nat g t e). Qed.
Lemma lem4080030 {A : Type'} (a : A) (t : A -> Prop) : term379 A a t.
Proof. exact (@lem4080029 (@IN A a t) (@CARD A t) (term380 A t)). Qed.
Lemma lem4080031 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) : term381 A a t g'.
Proof. exact (@lem4080030 A a t g'). Qed.
Lemma lem4080032 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) : (term381 A a t g') = (term382 A a t g').
Proof. exact (eq_refl (term381 A a t g')). Qed.
Lemma lem4080033 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) : term382 A a t g'.
Proof. exact (EQ_MP (@lem4080032 A a t g') (@lem4080031 A a t g')). Qed.
Lemma lem4080034 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) : term383 A a t g' t'.
Proof. exact (@lem4080033 A a t g' t'). Qed.
Lemma lem4080035 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) : (term383 A a t g' t') = (term384 A a t g' t').
Proof. exact (eq_refl (term383 A a t g' t')). Qed.
Lemma lem4080036 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) : term384 A a t g' t'.
Proof. exact (EQ_MP (@lem4080035 A a t g' t') (@lem4080034 A a t g' t')). Qed.
Lemma lem4080037 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term385 A a t g' t' e'.
Proof. exact (@lem4080036 A a t g' t' e'). Qed.
Lemma lem4080038 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term385 A a t g' t' e') = (term386 A a t g' t' e').
Proof. exact (eq_refl (term385 A a t g' t' e')). Qed.
Lemma lem4080039 {A : Type'} (a : A) (t : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term386 A a t g' t' e'.
Proof. exact (EQ_MP (@lem4080038 A a t g' t' e') (@lem4080037 A a t g' t' e')). Qed.
Lemma lem4080040 {A : Type'} (a : A) (t : A -> Prop) : (@IN A a t) = (@IN A a t).
Proof. exact (eq_refl (@IN A a t)). Qed.
Lemma lem4080041 {A : Type'} (a : A) (t : A -> Prop) (t' : nat) (e' : nat) : term628 A a t t' e'.
Proof. exact (@lem4080039 A a t (@IN A a t) t' e'). Qed.
Lemma lem4080042 {A : Type'} (a : A) (t : A -> Prop) (t' : nat) (e' : nat) : term629 A a t t' e'.
Proof. exact (@lem4080041 A a t t' e' (@lem4080040 A a t)). Qed.
Lemma lem4080047 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (@CARD A t) = n.
Proof. exact (proj2 (@lem4079865 A t n h1)). Qed.
Lemma lem4080048 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term630 A a t n.
Proof. exact (fun h0 : @IN A a t => @lem4080047 A t n h1). Qed.
Lemma lem4080049 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (e' : nat) : term629 A a t n e'.
Proof. exact (@lem4080042 A a t n e'). Qed.
Lemma lem4080050 {A : Type'} (a : A) (e' : nat) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term631 A a t n e'.
Proof. exact (@lem4080049 A a t n e' (@lem4080048 A a t n h1)). Qed.
Lemma lem4080055 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (@CARD A t) = n.
Proof. exact (proj2 (@lem4079865 A t n h1)). Qed.
Lemma lem4080056 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4080057 {A : Type'} (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term380 A t) = (S n).
Proof. exact (MK_COMB (@lem4080056) (@lem4080055 A t n h1)). Qed.
Lemma lem4080058 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term632 A a t n.
Proof. exact (fun h0 : term339 A a t => @lem4080057 A t n h1). Qed.
Lemma lem4080059 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term633 A a t n.
Proof. exact (@lem4080050 A a (S n) t n h1). Qed.
Lemma lem4080060 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term354 A a t) = (term634 A a t n).
Proof. exact (@lem4080059 A a t n h1 (@lem4080058 A a t n h1)). Qed.
Lemma lem4080094 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term353 A a t) = (term634 A a t n).
Proof. exact (TRANS (@lem4080023 A a t n h1) (@lem4080060 A a t n h1)). Qed.
Lemma lem4080095 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem4080096 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term635 A a t) = (term636 A a t n).
Proof. exact (MK_COMB (@lem4080095) (@lem4080094 A a t n h1)). Qed.
Lemma lem4080130 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem4080131 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term619 A a t) = (term637 A a t n).
Proof. exact (MK_COMB (@lem4080096 A a t n h1) (@lem4080130)). Qed.
Lemma lem4080165 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term638 A a t n.
Proof. exact (fun h0 : True => @lem4080131 A a t n h1). Qed.
Lemma lem4080166 {A : Type'} (n : nat) (e' : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : term443 A a' a t) : term639 A a' a t n e'.
Proof. exact (@lem4080007 A (term637 A a t n) e' a' a t h1). Qed.
Lemma lem4080167 {A : Type'} (e' : nat) (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : term640 A a' a t n e'.
Proof. exact (@lem4080166 A n e' a' a t h2 (@lem4080165 A a t n h1)). Qed.
Lemma lem4080181 {A : Type'} (a : A) (t : A -> Prop) : (term353 A a t) = (term353 A a t).
Proof. exact (eq_refl (term353 A a t)). Qed.
Lemma lem4080182 {A : Type'} (a : A) (t : A -> Prop) : term641 A a t.
Proof. exact (fun h0 : ~ True => @lem4080181 A a t). Qed.
Lemma lem4080183 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : term642 A a' n a t.
Proof. exact (@lem4080167 A (term353 A a t) n a' a t h1 h2). Qed.
Lemma lem4080184 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term617 A a' a t) = (term643 A n a t).
Proof. exact (@lem4080183 A n a' a t h1 h2 (@lem4080182 A a t)). Qed.
Lemma lem4080186 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4080187 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem4080186 nat t2 t1). Qed.
Lemma lem4080188 {A : Type'} (a : A) (t : A -> Prop) (n : nat) : (term643 A n a t) = (term637 A a t n).
Proof. exact (@lem4080187 (term353 A a t) (term637 A a t n)). Qed.
Lemma lem4080222 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term617 A a' a t) = (term637 A a t n).
Proof. exact (TRANS (@lem4080184 A n a' a t h1 h2) (@lem4080188 A a t n)). Qed.
Lemma lem4080223 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term616 A a t a') = (term637 A a t n).
Proof. exact (TRANS (@lem4079987 A a' a t n h1) (@lem4080222 A n a' a t h1 h2)). Qed.
Lemma lem4080224 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4080225 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term644 A a t a') = (term645 A a t n).
Proof. exact (MK_COMB (@lem4080224) (@lem4080223 A n a' a t h1 h2)). Qed.
Lemma lem4080259 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4080260 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : ((term616 A a t a') = n) = ((term637 A a t n) = n).
Proof. exact (MK_COMB (@lem4080225 A n a' a t h1 h2) (@lem4080259 n)). Qed.
Lemma lem4080296 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term611 A a t a' n) = (term646 A a t n).
Proof. exact (MK_COMB (@lem4079971 A a a' t n h1) (@lem4080260 A n a' a t h1 h2)). Qed.
Lemma lem4080298 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4080299 {A : Type'} (a : A) (t : A -> Prop) (n : nat) : (term646 A a t n) = ((term637 A a t n) = n).
Proof. exact (@lem4080298 ((term637 A a t n) = n)). Qed.
Lemma lem4080335 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term611 A a t a' n) = ((term637 A a t n) = n).
Proof. exact (TRANS (@lem4080296 A n a' a t h1 h2) (@lem4080299 A a t n)). Qed.
Lemma lem4080336 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) (h1 : @HAS_SIZE A t n) (h2 : term443 A a' a t) : (term604 A a t a' n) = ((term637 A a t n) = n).
Proof. exact (TRANS (@lem4079955 A a t a' n) (@lem4080335 A n a' a t h1 h2)). Qed.
Lemma lem4080337 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : term647 A a' a t n.
Proof. exact (fun h0 : term443 A a' a t => @lem4080336 A n a' a t h1 h0). Qed.
Lemma lem4080338 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : term648 A a' a t n.
Proof. exact (@lem4079948 A n a' a t ((term637 A a t n) = n)). Qed.
Lemma lem4080339 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term649 A a t a' n) = (term650 A a' a t n).
Proof. exact (@lem4080338 A a' a t n (@lem4080337 A a' a t n h1)). Qed.
Lemma lem4080433 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term651 A a t n) = (term652 A a t n).
Proof. exact (fun_ext (fun a' : A => @lem4080339 A a' a t n h1)). Qed.
Lemma lem4080527 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4080528 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term653 A a t n) = (term654 A a t n).
Proof. exact (MK_COMB (@lem4080527 A) (@lem4080433 A a t n h1)). Qed.
Lemma lem4080626 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (h1 : @HAS_SIZE A t n) : (term654 A a t n) = (term653 A a t n).
Proof. exact (SYM (@lem4080528 A a t n h1)). Qed.
Lemma lem4080627 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term655 _476 _475 _474 _477) = (term656 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem4080628 {A : Type'} (_474 : nat) (_475 : Prop) (a' : A) (a : A) (t : A -> Prop) (n : nat) (_477 : nat) : (term657 A a' a t n _475 _474 _477) = (term658 A _474 _475 a' a t n _477).
Proof. exact (@lem4080627 _474 _475 (term659 A a' a t n) _477). Qed.
Lemma lem4080629 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term660 A a' a t n) = (term661 A a' a t n).
Proof. exact (@lem4080628 A n (@IN A a t) a' a t n (S n)). Qed.
Lemma lem4080630 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term662 A a' a t n) = (term663 A a' a t n).
Proof. exact (eq_refl (term662 A a' a t n)). Qed.
Lemma lem4080631 {A : Type'} (a : A) (t : A -> Prop) : (term313 A a t) = (term313 A a t).
Proof. exact (eq_refl (term313 A a t)). Qed.
Lemma lem4080632 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term664 A a' a t n) = (term665 A a' a t n).
Proof. exact (MK_COMB (@lem4080631 A a t) (@lem4080630 A a' a t n)). Qed.
Lemma lem4080633 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term666 A a' a t n) = (term667 A a' a t n).
Proof. exact (eq_refl (term666 A a' a t n)). Qed.
Lemma lem4080634 {A : Type'} (a : A) (t : A -> Prop) : (term429 A a t) = (term429 A a t).
Proof. exact (eq_refl (term429 A a t)). Qed.
Lemma lem4080635 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term668 A a' a t n) = (term669 A a' a t n).
Proof. exact (MK_COMB (@lem4080634 A a t) (@lem4080633 A a' a t n)). Qed.
Lemma lem4080636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4080637 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term670 A a' a t n) = (term671 A a' a t n).
Proof. exact (MK_COMB (@lem4080636) (@lem4080635 A a' a t n)). Qed.
Lemma lem4080638 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term661 A a' a t n) = (term672 A a' a t n).
Proof. exact (MK_COMB (@lem4080637 A a' a t n) (@lem4080632 A a' a t n)). Qed.
Lemma lem4080639 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term660 A a' a t n) = (term650 A a' a t n).
Proof. exact (eq_refl (term660 A a' a t n)). Qed.
Lemma lem4080640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4080641 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term673 A a' a t n) = (term674 A a' a t n).
Proof. exact (MK_COMB (@lem4080640) (@lem4080639 A a' a t n)). Qed.
Lemma lem4080642 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : ((term660 A a' a t n) = (term661 A a' a t n)) = ((term650 A a' a t n) = (term672 A a' a t n)).
Proof. exact (MK_COMB (@lem4080641 A a' a t n) (@lem4080638 A a' a t n)). Qed.
Lemma lem4080643 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term650 A a' a t n) = (term672 A a' a t n).
Proof. exact (EQ_MP (@lem4080642 A a' a t n) (@lem4080629 A a' a t n)). Qed.
Lemma lem4080644 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term672 A a' a t n) = (term650 A a' a t n).
Proof. exact (SYM (@lem4080643 A a' a t n)). Qed.
Lemma lem4080645 {A : Type'} (a : A) (t : A -> Prop) (h1 : @IN A a t) : @IN A a t.
Proof. exact (h1). Qed.
Lemma lem4080690 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem4075309 n) (@lem4075308 n)). Qed.
Lemma lem4080691 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4080692 (n : nat) : (term675 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem4080691) (@lem4080690 n)). Qed.
Lemma lem4080693 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4080694 (n : nat) : ((term1 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem4080692 n) (@lem4080693 n)). Qed.
Lemma lem4080696 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4080697 (x : nat) : (x = x) = True.
Proof. exact (@lem4080696 nat x). Qed.
Lemma lem4080698 (n : nat) : (n = n) = True.
Proof. exact (@lem4080697 n). Qed.
Lemma lem4080699 (n : nat) : ((term1 n) = n) = True.
Proof. exact (TRANS (@lem4080694 n) (@lem4080698 n)). Qed.
Lemma lem4080700 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : (term447 A a' a t) = (term447 A a' a t).
Proof. exact (eq_refl (term447 A a' a t)). Qed.
Lemma lem4080701 {A : Type'} (n : nat) (a' : A) (a : A) (t : A -> Prop) : (term663 A a' a t n) = (term676 A a' a t).
Proof. exact (MK_COMB (@lem4080700 A a' a t) (@lem4080699 n)). Qed.
Lemma lem4080703 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4080704 {A : Type'} (a' : A) (a : A) (t : A -> Prop) : (term676 A a' a t) = True.
Proof. exact (@lem4080703 (term443 A a' a t)). Qed.
Lemma lem4080705 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term663 A a' a t n) = True.
Proof. exact (TRANS (@lem4080701 A n a' a t) (@lem4080704 A a' a t)). Qed.
Lemma lem4080706 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : True = (term663 A a' a t n).
Proof. exact (SYM (@lem4080705 A a' a t n)). Qed.
Lemma lem4080718 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) : term415 A n a s.
Proof. exact (conj (@lem4079854 A n s h2) (@lem4079850 A a s h1)). Qed.
Lemma lem4080719 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @SUBSET A t s) : term416 A t n a s.
Proof. exact (conj (@lem4079856 A t s h3) (@lem4080718 A a n s h1 h2)). Qed.
Lemma lem4080720 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term677 A t n a s.
Proof. exact (conj (@lem4079865 A t n h3) (@lem4080719 A a n t s h1 h2 h4)). Qed.
Lemma lem4080721 {A : Type'} (n : nat) (a : A) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @IN A a t) (h5 : @SUBSET A t s) : term678 A t n a s.
Proof. exact (conj (@lem4080645 A a t h4) (@lem4080720 A a n t s h1 h2 h3 h5)). Qed.
Lemma lem4080737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4080738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term418 A s t).
Proof. exact (@lem4080737 A s t). Qed.
Lemma lem4080739 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term418 A t s).
Proof. exact (@lem4080738 A t s). Qed.
Lemma lem4080746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4080747 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term227 A t s) = (term419 A t s).
Proof. exact (MK_COMB (@lem4080746) (@lem4080739 A t s)). Qed.
Lemma lem4080752 {A : Type'} (n : nat) (a : A) (s : A -> Prop) : (term415 A n a s) = (term415 A n a s).
Proof. exact (eq_refl (term415 A n a s)). Qed.
Lemma lem4080753 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term416 A t n a s) = (term420 A t n a s).
Proof. exact (MK_COMB (@lem4080747 A t s) (@lem4080752 A n a s)). Qed.
Lemma lem4080756 {A : Type'} (t : A -> Prop) (n : nat) : (term679 A t n) = (term679 A t n).
Proof. exact (eq_refl (term679 A t n)). Qed.
Lemma lem4080757 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term677 A t n a s) = (term680 A t n a s).
Proof. exact (MK_COMB (@lem4080756 A t n) (@lem4080753 A t n a s)). Qed.
Lemma lem4080760 {A : Type'} (a : A) (t : A -> Prop) : (term681 A a t) = (term681 A a t).
Proof. exact (eq_refl (term681 A a t)). Qed.
Lemma lem4080761 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term678 A t n a s) = (term682 A t n a s).
Proof. exact (MK_COMB (@lem4080760 A a t) (@lem4080757 A t n a s)). Qed.
Lemma lem4080764 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4080765 {A : Type'} (t : A -> Prop) (n : nat) (a : A) (s : A -> Prop) : (term683 A t n a s) = (term684 A t n a s).
Proof. exact (MK_COMB (@lem4080764) (@lem4080761 A t n a s)). Qed.
Lemma lem4080772 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term667 A a' a t n) = (term667 A a' a t n).
Proof. exact (eq_refl (term667 A a' a t n)). Qed.
Lemma lem4080773 {A : Type'} (s : A -> Prop) (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term685 A s a' a t n) = (term686 A s a' a t n).
Proof. exact (MK_COMB (@lem4080765 A t n a s) (@lem4080772 A a' a t n)). Qed.
Lemma lem4080776 {A : Type'} (s : A -> Prop) (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term686 A s a' a t n) = (term685 A s a' a t n).
Proof. exact (SYM (@lem4080773 A s a' a t n)). Qed.
Lemma lem4080782 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4080783 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4080782 A P x). Qed.
Lemma lem4080784 {A : Type'} (t : A -> Prop) (a : A) : (@IN A a t) = (t a).
Proof. exact (@lem4080783 A t a). Qed.
Lemma lem4080785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4080786 {A : Type'} (t : A -> Prop) (a : A) : (term681 A a t) = (term687 A t a).
Proof. exact (MK_COMB (@lem4080785) (@lem4080784 A t a)). Qed.
Lemma lem4080802 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4080803 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4080802 A P x). Qed.
Lemma lem4080804 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4080803 A t x). Qed.
Lemma lem4080805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4080806 {A : Type'} (t : A -> Prop) (x : A) : (term429 A x t) = (term430 A t x).
Proof. exact (MK_COMB (@lem4080805) (@lem4080804 A t x)). Qed.
Lemma lem4080808 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4080809 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4080808 A P x). Qed.
Lemma lem4080810 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4080809 A s x). Qed.
Lemma lem4080811 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term431 A t x s) = (term432 A t s x).
Proof. exact (MK_COMB (@lem4080806 A t x) (@lem4080810 A s x)). Qed.
Lemma lem4080814 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term433 A t s) = (term434 A t s).
Proof. exact (fun_ext (fun x : A => @lem4080811 A t s x)). Qed.
Lemma lem4080815 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4080816 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term418 A t s) = (term435 A t s).
Proof. exact (MK_COMB (@lem4080815 A) (@lem4080814 A t s)). Qed.
Lemma lem4080821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4080822 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term419 A t s) = (term436 A t s).
Proof. exact (MK_COMB (@lem4080821) (@lem4080816 A t s)). Qed.
Lemma lem4080828 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4080829 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4080828 A P x). Qed.
Lemma lem4080830 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem4080829 A s a). Qed.
Lemma lem4080831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4080832 {A : Type'} (s : A -> Prop) (a : A) : (term339 A a s) = (term437 A s a).
Proof. exact (MK_COMB (@lem4080831) (@lem4080830 A s a)). Qed.
Lemma lem4080833 {A : Type'} (n : nat) (s : A -> Prop) : (term438 A n s) = (term438 A n s).
Proof. exact (eq_refl (term438 A n s)). Qed.
Lemma lem4080834 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term415 A n a s) = (term439 A n s a).
Proof. exact (MK_COMB (@lem4080833 A n s) (@lem4080832 A s a)). Qed.
Lemma lem4080837 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term420 A t n a s) = (term440 A t n s a).
Proof. exact (MK_COMB (@lem4080822 A t s) (@lem4080834 A n s a)). Qed.
Lemma lem4080840 {A : Type'} (t : A -> Prop) (n : nat) : (term679 A t n) = (term679 A t n).
Proof. exact (eq_refl (term679 A t n)). Qed.
Lemma lem4080841 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term680 A t n a s) = (term688 A t n s a).
Proof. exact (MK_COMB (@lem4080840 A t n) (@lem4080837 A t n s a)). Qed.
Lemma lem4080844 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term682 A t n a s) = (term689 A t n s a).
Proof. exact (MK_COMB (@lem4080786 A t a) (@lem4080841 A t n s a)). Qed.
Lemma lem4080847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4080848 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term684 A t n a s) = (term690 A t n s a).
Proof. exact (MK_COMB (@lem4080847) (@lem4080844 A t n s a)). Qed.
Lemma lem4080852 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4080853 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term443 A x y s) = (term444 A y x s).
Proof. exact (@lem4080852 A y x s). Qed.
Lemma lem4080854 {A : Type'} (a : A) (a' : A) (t : A -> Prop) : (term443 A a' a t) = (term444 A a a' t).
Proof. exact (@lem4080853 A a a' t). Qed.
Lemma lem4080860 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4080861 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4080860 A P x). Qed.
Lemma lem4080862 {A : Type'} (t : A -> Prop) (a' : A) : (@IN A a' t) = (t a').
Proof. exact (@lem4080861 A t a'). Qed.
Lemma lem4080863 {A : Type'} (a' : A) (a : A) : (term445 A a' a) = (term445 A a' a).
Proof. exact (eq_refl (term445 A a' a)). Qed.
Lemma lem4080864 {A : Type'} (a : A) (t : A -> Prop) (a' : A) : (term444 A a a' t) = (term446 A a t a').
Proof. exact (MK_COMB (@lem4080863 A a' a) (@lem4080862 A t a')). Qed.
Lemma lem4080867 {A : Type'} (a : A) (t : A -> Prop) (a' : A) : (term443 A a' a t) = (term446 A a t a').
Proof. exact (TRANS (@lem4080854 A a a' t) (@lem4080864 A a t a')). Qed.
Lemma lem4080868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4080869 {A : Type'} (a : A) (t : A -> Prop) (a' : A) : (term447 A a' a t) = (term448 A a t a').
Proof. exact (MK_COMB (@lem4080868) (@lem4080867 A a t a')). Qed.
Lemma lem4080872 (n : nat) : ((term691 n) = n) = ((term691 n) = n).
Proof. exact (eq_refl ((term691 n) = n)). Qed.
Lemma lem4080873 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term667 A a' a t n) = (term692 A a t a' n).
Proof. exact (MK_COMB (@lem4080869 A a t a') (@lem4080872 n)). Qed.
Lemma lem4080876 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term686 A s a' a t n) = (term693 A s a t a' n).
Proof. exact (MK_COMB (@lem4080848 A t n s a) (@lem4080873 A a t a' n)). Qed.
Lemma lem4080879 {A : Type'} (s : A -> Prop) (a' : A) (a : A) (t : A -> Prop) (n : nat) : (term693 A s a t a' n) = (term686 A s a' a t n).
Proof. exact (SYM (@lem4080876 A s a t a' n)). Qed.
Lemma lem4080881 (p : Prop) : p = (term252 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4080882 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term693 A s a t a' n) = (term694 A s a t a' n).
Proof. exact (@lem4080881 (term693 A s a t a' n)). Qed.
Lemma lem4080883 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term694 A s a t a' n) = (term693 A s a t a' n).
Proof. exact (SYM (@lem4080882 A s a t a' n)). Qed.
Lemma lem4080884 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term695 A s a t a' n) : term695 A s a t a' n.
Proof. exact (h1). Qed.
Lemma lem4080887 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term694 A s a t a' n) : term694 A s a t a' n.
Proof. exact (h1). Qed.
Lemma lem4080888 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term696 A s a t a' n.
Proof. exact (fun h0 : term694 A s a t a' n => @lem4080887 A s a t a' n h0). Qed.
Lemma lem4080889 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term696 A s a t a' n) : term696 A s a t a' n.
Proof. exact (h1). Qed.
Lemma lem4080890 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term694 A s a t a' n) : term694 A s a t a' n.
Proof. exact (h1). Qed.
Lemma lem4080891 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term694 A s a t a' n) (h2 : term696 A s a t a' n) : term694 A s a t a' n.
Proof. exact (@lem4080889 A s a t a' n h2 (@lem4080890 A s a t a' n h1)). Qed.
Lemma lem4080892 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term694 A s a t a' n) : term697 A s a t a' n.
Proof. exact (fun h0 : term696 A s a t a' n => @lem4080891 A s a t a' n h1 h0). Qed.
Lemma lem4080893 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term696 A s a t a' n) : term696 A s a t a' n.
Proof. exact (h1). Qed.
Lemma lem4080894 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term694 A s a t a' n) (h2 : term696 A s a t a' n) : term694 A s a t a' n.
Proof. exact (@lem4080892 A s a t a' n h1 (@lem4080893 A s a t a' n h2)). Qed.
Lemma lem4080895 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term696 A s a t a' n) : term696 A s a t a' n.
Proof. exact (fun h0 : term694 A s a t a' n => @lem4080894 A s a t a' n h0 h1). Qed.
Lemma lem4080896 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term698 A s a t a' n.
Proof. exact (fun h0 : term696 A s a t a' n => @lem4080895 A s a t a' n h0). Qed.
Lemma lem4080899 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term696 A s a t a' n.
Proof. exact (@lem4080896 A s a t a' n (@lem4080888 A s a t a' n)). Qed.
Lemma lem4080900 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term696 A s a t a' n.
Proof. exact (@lem4080899 A s a t a' n). Qed.
Lemma lem4080922 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4080923 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term694 A s a t a' n) = (term699 A s a t a' n).
Proof. exact (@lem4080922 (term695 A s a t a' n)). Qed.
Lemma lem4080925 (t : Prop) : (term61 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4080926 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term699 A s a t a' n) = (term693 A s a t a' n).
Proof. exact (@lem4080925 (term693 A s a t a' n)). Qed.
Lemma lem4080929 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term694 A s a t a' n) = (term693 A s a t a' n).
Proof. exact (TRANS (@lem4080923 A s a t a' n) (@lem4080926 A s a t a' n)). Qed.
Lemma lem4080952 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term700 A a t a' n) = (term701 A a t a' n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4080929 A s a t a' n)). Qed.
Lemma lem4080953 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4080954 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term702 A a t a' n) = (term703 A a t a' n).
Proof. exact (MK_COMB (@lem4080953 A) (@lem4080952 A a t a' n)). Qed.
Lemma lem4080959 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : (term704 A t a' n) = (term705 A t a' n).
Proof. exact (fun_ext (fun a : A => @lem4080954 A a t a' n)). Qed.
Lemma lem4080960 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4080961 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : (term706 A t a' n) = (term707 A t a' n).
Proof. exact (MK_COMB (@lem4080960 A) (@lem4080959 A t a' n)). Qed.
Lemma lem4080966 {A : Type'} (a' : A) (n : nat) : (term708 A a' n) = (term709 A a' n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4080961 A t a' n)). Qed.
Lemma lem4080967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4080968 {A : Type'} (a' : A) (n : nat) : (term710 A a' n) = (term711 A a' n).
Proof. exact (MK_COMB (@lem4080967 A) (@lem4080966 A a' n)). Qed.
Lemma lem4080973 {A : Type'} (n : nat) : (term712 A n) = (term713 A n).
Proof. exact (fun_ext (fun a' : A => @lem4080968 A a' n)). Qed.
Lemma lem4080974 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4080975 {A : Type'} (n : nat) : (term714 A n) = (term715 A n).
Proof. exact (MK_COMB (@lem4080974 A) (@lem4080973 A n)). Qed.
Lemma lem4080980 {A : Type'} : (term716 A) = (term717 A).
Proof. exact (fun_ext (fun n : nat => @lem4080975 A n)). Qed.
Lemma lem4080981 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4080990 {A : Type'} : (term718 A) = (term719 A).
Proof. exact (MK_COMB (@lem4080981) (@lem4080980 A)). Qed.
Lemma lem4080999 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term692 A a t a' n) = (term692 A a t a' n).
Proof. exact (eq_refl (term692 A a t a' n)). Qed.
Lemma lem4081010 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term439 A n s a) = (term439 A n s a).
Proof. exact (eq_refl (term439 A n s a)). Qed.
Lemma lem4081015 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term432 A t s x) = (term432 A t s x).
Proof. exact (eq_refl (term432 A t s x)). Qed.
Lemma lem4081016 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term434 A t s) = (term434 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081015 A t s x)). Qed.
Lemma lem4081017 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081018 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term435 A t s) = (term435 A t s).
Proof. exact (MK_COMB (@lem4081017 A) (@lem4081016 A t s)). Qed.
Lemma lem4081019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4081020 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term436 A t s) = (term436 A t s).
Proof. exact (MK_COMB (@lem4081019) (@lem4081018 A t s)). Qed.
Lemma lem4081021 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term440 A t n s a) = (term440 A t n s a).
Proof. exact (MK_COMB (@lem4081020 A t s) (@lem4081010 A n s a)). Qed.
Lemma lem4081028 {A : Type'} (t : A -> Prop) (n : nat) : (term679 A t n) = (term679 A t n).
Proof. exact (eq_refl (term679 A t n)). Qed.
Lemma lem4081029 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term688 A t n s a) = (term688 A t n s a).
Proof. exact (MK_COMB (@lem4081028 A t n) (@lem4081021 A t n s a)). Qed.
Lemma lem4081032 {A : Type'} (t : A -> Prop) (a : A) : (term687 A t a) = (term687 A t a).
Proof. exact (eq_refl (term687 A t a)). Qed.
Lemma lem4081033 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term689 A t n s a) = (term689 A t n s a).
Proof. exact (MK_COMB (@lem4081032 A t a) (@lem4081029 A t n s a)). Qed.
Lemma lem4081034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4081035 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term690 A t n s a) = (term690 A t n s a).
Proof. exact (MK_COMB (@lem4081034) (@lem4081033 A t n s a)). Qed.
Lemma lem4081036 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term693 A s a t a' n) = (term693 A s a t a' n).
Proof. exact (MK_COMB (@lem4081035 A t n s a) (@lem4080999 A a t a' n)). Qed.
Lemma lem4081037 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term701 A a t a' n) = (term701 A a t a' n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4081036 A s a t a' n)). Qed.
Lemma lem4081038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4081039 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term703 A a t a' n) = (term703 A a t a' n).
Proof. exact (MK_COMB (@lem4081038 A) (@lem4081037 A a t a' n)). Qed.
Lemma lem4081040 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : (term705 A t a' n) = (term705 A t a' n).
Proof. exact (fun_ext (fun a : A => @lem4081039 A a t a' n)). Qed.
Lemma lem4081041 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081042 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : (term707 A t a' n) = (term707 A t a' n).
Proof. exact (MK_COMB (@lem4081041 A) (@lem4081040 A t a' n)). Qed.
Lemma lem4081043 {A : Type'} (a' : A) (n : nat) : (term709 A a' n) = (term709 A a' n).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4081042 A t a' n)). Qed.
Lemma lem4081044 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4081045 {A : Type'} (a' : A) (n : nat) : (term711 A a' n) = (term711 A a' n).
Proof. exact (MK_COMB (@lem4081044 A) (@lem4081043 A a' n)). Qed.
Lemma lem4081046 {A : Type'} (n : nat) : (term713 A n) = (term713 A n).
Proof. exact (fun_ext (fun a' : A => @lem4081045 A a' n)). Qed.
Lemma lem4081047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081048 {A : Type'} (n : nat) : (term715 A n) = (term715 A n).
Proof. exact (MK_COMB (@lem4081047 A) (@lem4081046 A n)). Qed.
Lemma lem4081049 {A : Type'} : (term717 A) = (term717 A).
Proof. exact (fun_ext (fun n : nat => @lem4081048 A n)). Qed.
Lemma lem4081050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4081051 {A : Type'} : (term719 A) = (term719 A).
Proof. exact (MK_COMB (@lem4081050) (@lem4081049 A)). Qed.
Lemma lem4081110 {A : Type'} : (term718 A) = (term719 A).
Proof. exact (TRANS (@lem4080990 A) (@lem4081051 A)). Qed.
Lemma lem4081111 {A : Type'} : (term719 A) = (term718 A).
Proof. exact (SYM (@lem4081110 A)). Qed.
Lemma lem4081112 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term689 A t n s a.
Proof. exact (h1). Qed.
Lemma lem4081115 (p : Prop) : p = (term252 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4081116 (n : nat) : ((term691 n) = n) = (term720 n).
Proof. exact (@lem4081115 ((term691 n) = n)). Qed.
Lemma lem4081117 (n : nat) : (term720 n) = ((term691 n) = n).
Proof. exact (SYM (@lem4081116 n)). Qed.
Lemma lem4081131 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term432 A t s x) = (term479 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4081132 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term434 A t s) = (term480 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081131 A t s x)). Qed.
Lemma lem4081133 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081134 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term435 A t s) = (term481 A t s).
Proof. exact (MK_COMB (@lem4081133 A) (@lem4081132 A t s)). Qed.
Lemma lem4081141 {A : Type'} (n : nat) (s : A -> Prop) : (term399 A n s) = (term482 A n s).
Proof. exact (@lem17265 (@FINITE A s) (term396 A n s)). Qed.
Lemma lem4081142 {A : Type'} (s : A -> Prop) (a : A) : (term437 A s a) = (term437 A s a).
Proof. exact (eq_refl (term437 A s a)). Qed.
Lemma lem4081143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4081144 {A : Type'} (n : nat) (s : A -> Prop) : (term438 A n s) = (term483 A n s).
Proof. exact (MK_COMB (@lem4081143) (@lem4081141 A n s)). Qed.
Lemma lem4081145 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term439 A n s a) = (term484 A n s a).
Proof. exact (MK_COMB (@lem4081144 A n s) (@lem4081142 A s a)). Qed.
Lemma lem4081146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4081147 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term436 A t s) = (term485 A t s).
Proof. exact (MK_COMB (@lem4081146) (@lem4081134 A t s)). Qed.
Lemma lem4081148 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term440 A t n s a) = (term486 A t n s a).
Proof. exact (MK_COMB (@lem4081147 A t s) (@lem4081145 A n s a)). Qed.
Lemma lem4081150 {A : Type'} (t : A -> Prop) (n : nat) : (term679 A t n) = (term679 A t n).
Proof. exact (eq_refl (term679 A t n)). Qed.
Lemma lem4081151 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term688 A t n s a) = (term721 A t n s a).
Proof. exact (MK_COMB (@lem4081150 A t n) (@lem4081148 A t n s a)). Qed.
Lemma lem4081153 {A : Type'} (t : A -> Prop) (a : A) : (term687 A t a) = (term687 A t a).
Proof. exact (eq_refl (term687 A t a)). Qed.
Lemma lem4081190 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term689 A t n s a) = (term722 A t n s a).
Proof. exact (MK_COMB (@lem4081153 A t a) (@lem4081151 A t n s a)). Qed.
Lemma lem4081191 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term722 A t n s a.
Proof. exact (EQ_MP (@lem4081190 A t n s a) (@lem4081112 A t n s a h1)). Qed.
Lemma lem4081201 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (h1 : term446 A a t a') : term446 A a t a'.
Proof. exact (h1). Qed.
Lemma lem4081208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4081213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4081214 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4081213 A Prop f x). Qed.
Lemma lem4081216 {A : Type'} (s : A -> Prop) (a : A) : (s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4081214 A s a). Qed.
Lemma lem4081217 {A : Type'} (s : A -> Prop) (a : A) : (term437 A s a) = (term489 A s a).
Proof. exact (MK_COMB (@lem4081208) (@lem4081216 A s a)). Qed.
Lemma lem4081234 {A : Type'} (n : nat) (s : A -> Prop) : (term483 A n s) = (term483 A n s).
Proof. exact (eq_refl (term483 A n s)). Qed.
Lemma lem4081235 {A : Type'} (n : nat) (s : A -> Prop) (a : A) : (term484 A n s a) = (term490 A n s a).
Proof. exact (MK_COMB (@lem4081234 A n s) (@lem4081217 A s a)). Qed.
Lemma lem4081240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4081241 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4081240 A Prop f x). Qed.
Lemma lem4081243 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4081241 A s x). Qed.
Lemma lem4081244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4081249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4081250 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4081249 A Prop f x). Qed.
Lemma lem4081252 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4081250 A t x). Qed.
Lemma lem4081253 {A : Type'} (t : A -> Prop) (x : A) : (term437 A t x) = (term489 A t x).
Proof. exact (MK_COMB (@lem4081244) (@lem4081252 A t x)). Qed.
Lemma lem4081254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4081255 {A : Type'} (t : A -> Prop) (x : A) : (term491 A t x) = (term492 A t x).
Proof. exact (MK_COMB (@lem4081254) (@lem4081253 A t x)). Qed.
Lemma lem4081256 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term479 A t s x) = (term493 A t s x).
Proof. exact (MK_COMB (@lem4081255 A t x) (@lem4081243 A s x)). Qed.
Lemma lem4081257 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term480 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081256 A t s x)). Qed.
Lemma lem4081258 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081259 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term481 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4081258 A) (@lem4081257 A t s)). Qed.
Lemma lem4081260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4081261 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term485 A t s) = (term496 A t s).
Proof. exact (MK_COMB (@lem4081260) (@lem4081259 A t s)). Qed.
Lemma lem4081262 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term486 A t n s a) = (term497 A t n s a).
Proof. exact (MK_COMB (@lem4081261 A t s) (@lem4081235 A n s a)). Qed.
Lemma lem4081277 {A : Type'} (t : A -> Prop) (n : nat) : (term679 A t n) = (term679 A t n).
Proof. exact (eq_refl (term679 A t n)). Qed.
Lemma lem4081278 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term721 A t n s a) = (term723 A t n s a).
Proof. exact (MK_COMB (@lem4081277 A t n) (@lem4081262 A t n s a)). Qed.
Lemma lem4081283 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4081284 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4081283 A Prop f x). Qed.
Lemma lem4081286 {A : Type'} (t : A -> Prop) (a : A) : (t a) = (@I (A -> Prop) t a).
Proof. exact (@lem4081284 A t a). Qed.
Lemma lem4081287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4081288 {A : Type'} (t : A -> Prop) (a : A) : (term687 A t a) = (term724 A t a).
Proof. exact (MK_COMB (@lem4081287) (@lem4081286 A t a)). Qed.
Lemma lem4081289 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) : (term722 A t n s a) = (term725 A t n s a).
Proof. exact (MK_COMB (@lem4081288 A t a) (@lem4081278 A t n s a)). Qed.
Lemma lem4081290 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term725 A t n s a.
Proof. exact (EQ_MP (@lem4081289 A t n s a) (@lem4081191 A t n s a h1)). Qed.
Lemma lem4081295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4081296 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4081295 A Prop f x). Qed.
Lemma lem4081298 {A : Type'} (t : A -> Prop) (a' : A) : (t a') = (@I (A -> Prop) t a').
Proof. exact (@lem4081296 A t a'). Qed.
Lemma lem4081305 {A : Type'} (a' : A) (a : A) : (term445 A a' a) = (term445 A a' a).
Proof. exact (eq_refl (term445 A a' a)). Qed.
Lemma lem4081306 {A : Type'} (a : A) (t : A -> Prop) (a' : A) : (term446 A a t a') = (term499 A a t a').
Proof. exact (MK_COMB (@lem4081305 A a' a) (@lem4081298 A t a')). Qed.
Lemma lem4081307 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (h1 : term446 A a t a') : term499 A a t a'.
Proof. exact (EQ_MP (@lem4081306 A a t a') (@lem4081201 A a t a' h1)). Qed.
Lemma lem4081324 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term723 A t n s a.
Proof. exact (proj2 (@lem4081290 A t n s a h1)). Qed.
Lemma lem4081326 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term497 A t n s a.
Proof. exact (proj2 (@lem4081324 A t n s a h1)). Qed.
Lemma lem4081328 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term490 A n s a.
Proof. exact (proj2 (@lem4081326 A t n s a h1)). Qed.
Lemma lem4081329 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term495 A t s.
Proof. exact (proj1 (@lem4081326 A t n s a h1)). Qed.
Lemma lem4081331 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term482 A n s.
Proof. exact (proj1 (@lem4081328 A t n s a h1)). Qed.
Lemma lem4081355 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term493 A t s x) = (term493 A t s x).
Proof. exact (eq_refl (term493 A t s x)). Qed.
Lemma lem4081356 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081355 A t s x)). Qed.
Lemma lem4081357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081359 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term495 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4081357 A) (@lem4081356 A t s)). Qed.
Lemma lem4081360 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term495 A t s.
Proof. exact (EQ_MP (@lem4081359 A t s) (@lem4081329 A t n s a h1)). Qed.
Lemma lem4081396 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term493 A t s x) = (term493 A t s x).
Proof. exact (eq_refl (term493 A t s x)). Qed.
Lemma lem4081397 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081396 A t s x)). Qed.
Lemma lem4081398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081400 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term495 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4081398 A) (@lem4081397 A t s)). Qed.
Lemma lem4081401 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term495 A t s.
Proof. exact (EQ_MP (@lem4081400 A t s) (@lem4081329 A t n s a h1)). Qed.
Lemma lem4081437 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term493 A t s x) = (term493 A t s x).
Proof. exact (eq_refl (term493 A t s x)). Qed.
Lemma lem4081438 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081437 A t s x)). Qed.
Lemma lem4081439 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081441 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term495 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4081439 A) (@lem4081438 A t s)). Qed.
Lemma lem4081442 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term495 A t s.
Proof. exact (EQ_MP (@lem4081441 A t s) (@lem4081329 A t n s a h1)). Qed.
Lemma lem4081478 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term493 A t s x) = (term493 A t s x).
Proof. exact (eq_refl (term493 A t s x)). Qed.
Lemma lem4081479 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A t s) = (term494 A t s).
Proof. exact (fun_ext (fun x : A => @lem4081478 A t s x)). Qed.
Lemma lem4081480 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4081482 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term495 A t s) = (term495 A t s).
Proof. exact (MK_COMB (@lem4081480 A) (@lem4081479 A t s)). Qed.
Lemma lem4081483 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term495 A t s.
Proof. exact (EQ_MP (@lem4081482 A t s) (@lem4081329 A t n s a h1)). Qed.
Lemma lem4081504 {A : Type'} (_48007 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term502 A t s _48007.
Proof. exact (@lem4081360 A t n s a h1 _48007). Qed.
Lemma lem4081505 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48007 : A) : (term502 A t s _48007) = (term493 A t s _48007).
Proof. exact (eq_refl (term502 A t s _48007)). Qed.
Lemma lem4081507 {A : Type'} (_48008 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term502 A t s _48008.
Proof. exact (@lem4081401 A t n s a h1 _48008). Qed.
Lemma lem4081508 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48008 : A) : (term502 A t s _48008) = (term493 A t s _48008).
Proof. exact (eq_refl (term502 A t s _48008)). Qed.
Lemma lem4081510 {A : Type'} (_48009 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term502 A t s _48009.
Proof. exact (@lem4081442 A t n s a h1 _48009). Qed.
Lemma lem4081511 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48009 : A) : (term502 A t s _48009) = (term493 A t s _48009).
Proof. exact (eq_refl (term502 A t s _48009)). Qed.
Lemma lem4081513 {A : Type'} (_48010 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term502 A t s _48010.
Proof. exact (@lem4081483 A t n s a h1 _48010). Qed.
Lemma lem4081514 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48010 : A) : (term502 A t s _48010) = (term493 A t s _48010).
Proof. exact (eq_refl (term502 A t s _48010)). Qed.
Lemma lem4081763 {A : Type'} (_48007 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term493 A t s _48007.
Proof. exact (EQ_MP (@lem4081505 A t s _48007) (@lem4081504 A _48007 t n s a h1)). Qed.
Lemma lem4081777 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term489 A s a.
Proof. exact (proj2 (@lem4081328 A t n s a h1)). Qed.
Lemma lem4081861 {A : Type'} (_48008 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term493 A t s _48008.
Proof. exact (EQ_MP (@lem4081508 A t s _48008) (@lem4081507 A _48008 t n s a h1)). Qed.
Lemma lem4081875 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term489 A s a.
Proof. exact (proj2 (@lem4081328 A t n s a h1)). Qed.
Lemma lem4082085 {A : Type'} (_48009 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term493 A t s _48009.
Proof. exact (EQ_MP (@lem4081511 A t s _48009) (@lem4081510 A _48009 t n s a h1)). Qed.
Lemma lem4082099 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term489 A s a.
Proof. exact (proj2 (@lem4081328 A t n s a h1)). Qed.
Lemma lem4082182 {A : Type'} (_48010 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term493 A t s _48010.
Proof. exact (EQ_MP (@lem4081514 A t s _48010) (@lem4081513 A _48010 t n s a h1)). Qed.
Lemma lem4082196 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term489 A s a.
Proof. exact (proj2 (@lem4081328 A t n s a h1)). Qed.
Lemma lem4082315 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (proj1 (@lem4081290 A t n s a h1)). Qed.
Lemma lem4082316 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A t a.
Proof. exact (fun h0 : term489 A t a => @lem4082315 A t n s a h1). Qed.
Lemma lem4082318 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082319 {A : Type'} (t : A -> Prop) (a : A) : (term512 A t a) = (@I (A -> Prop) t a).
Proof. exact (@lem4082318 (@I (A -> Prop) t a)). Qed.
Lemma lem4082320 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (EQ_MP (@lem4082319 A t a) (@lem4082316 A t n s a h1)). Qed.
Lemma lem4082326 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4082327 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : (term493 A t s _48007) = (term513 A s t _48007).
Proof. exact (@lem4082326 (@I (A -> Prop) s _48007) (term489 A t _48007)). Qed.
Lemma lem4082333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4082334 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : (term514 A t s _48007) = (term515 A s t _48007).
Proof. exact (MK_COMB (@lem4082333) (@lem4082327 A s t _48007)). Qed.
Lemma lem4082340 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : (term513 A s t _48007) = (term513 A s t _48007).
Proof. exact (eq_refl (term513 A s t _48007)). Qed.
Lemma lem4082341 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : ((term493 A t s _48007) = (term513 A s t _48007)) = ((term513 A s t _48007) = (term513 A s t _48007)).
Proof. exact (MK_COMB (@lem4082334 A s t _48007) (@lem4082340 A s t _48007)). Qed.
Lemma lem4082343 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4082344 (x : Prop) : (x = x) = True.
Proof. exact (@lem4082343 Prop x). Qed.
Lemma lem4082345 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : ((term513 A s t _48007) = (term513 A s t _48007)) = True.
Proof. exact (@lem4082344 (term513 A s t _48007)). Qed.
Lemma lem4082346 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : ((term493 A t s _48007) = (term513 A s t _48007)) = True.
Proof. exact (TRANS (@lem4082341 A s t _48007) (@lem4082345 A s t _48007)). Qed.
Lemma lem4082347 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : True = ((term493 A t s _48007) = (term513 A s t _48007)).
Proof. exact (SYM (@lem4082346 A s t _48007)). Qed.
Lemma lem4082348 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48007 : A) : (term493 A t s _48007) = (term513 A s t _48007).
Proof. exact (EQ_MP (@lem4082347 A s t _48007) (@lem0)). Qed.
Lemma lem4082349 {A : Type'} (_48007 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term513 A s t _48007.
Proof. exact (EQ_MP (@lem4082348 A s t _48007) (@lem4081763 A _48007 t n s a h1)). Qed.
Lemma lem4082351 (b : Prop) (a : Prop) : (a \/ b) = (term516 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4082352 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48007 : A) : (term513 A s t _48007) = (term517 A t s _48007).
Proof. exact (@lem4082351 (term489 A t _48007) (@I (A -> Prop) s _48007)). Qed.
Lemma lem4082354 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4082355 {A : Type'} (t : A -> Prop) (_48007 : A) : (term518 A t _48007) = (@I (A -> Prop) t _48007).
Proof. exact (@lem4082354 (@I (A -> Prop) t _48007)). Qed.
Lemma lem4082356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4082357 {A : Type'} (t : A -> Prop) (_48007 : A) : (term519 A t _48007) = (term520 A t _48007).
Proof. exact (MK_COMB (@lem4082356) (@lem4082355 A t _48007)). Qed.
Lemma lem4082358 {A : Type'} (s : A -> Prop) (_48007 : A) : (@I (A -> Prop) s _48007) = (@I (A -> Prop) s _48007).
Proof. exact (eq_refl (@I (A -> Prop) s _48007)). Qed.
Lemma lem4082359 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48007 : A) : (term517 A t s _48007) = (term521 A t s _48007).
Proof. exact (MK_COMB (@lem4082357 A t _48007) (@lem4082358 A s _48007)). Qed.
Lemma lem4082360 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48007 : A) : (term513 A s t _48007) = (term521 A t s _48007).
Proof. exact (TRANS (@lem4082352 A t s _48007) (@lem4082359 A t s _48007)). Qed.
Lemma lem4082363 {A : Type'} (_48007 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48007.
Proof. exact (EQ_MP (@lem4082360 A t s _48007) (@lem4082349 A _48007 t n s a h1)). Qed.
Lemma lem4082364 {A : Type'} (_48007 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48007.
Proof. exact (@lem4082363 A _48007 t n s a h1). Qed.
Lemma lem4082365 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s a.
Proof. exact (@lem4082364 A a t n s a h1). Qed.
Lemma lem4082368 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (@lem4082365 A t n s a h1 (@lem4082320 A t n s a h1)). Qed.
Lemma lem4082369 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A s a.
Proof. exact (fun h0 : term489 A s a => @lem4082368 A t n s a h1). Qed.
Lemma lem4082371 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082372 {A : Type'} (s : A -> Prop) (a : A) : (term512 A s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4082371 (@I (A -> Prop) s a)). Qed.
Lemma lem4082373 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (EQ_MP (@lem4082372 A s a) (@lem4082369 A t n s a h1)). Qed.
Lemma lem4082376 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4082378 {A : Type'} (s : A -> Prop) (a : A) : (term489 A s a) = (term522 A s a).
Proof. exact (@lem4082376 (@I (A -> Prop) s a)). Qed.
Lemma lem4082381 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term522 A s a.
Proof. exact (EQ_MP (@lem4082378 A s a) (@lem4081777 A t n s a h1)). Qed.
Lemma lem4082384 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (@lem4082381 A t n s a h1 (@lem4082373 A t n s a h1)). Qed.
Lemma lem4082385 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term304.
Proof. exact (fun h0 : ~ False => @lem4082384 A t n s a h1). Qed.
Lemma lem4082387 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082388 : term304 = False.
Proof. exact (@lem4082387 False). Qed.
Lemma lem4082467 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (proj1 (@lem4081290 A t n s a h1)). Qed.
Lemma lem4082468 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A t a.
Proof. exact (fun h0 : term489 A t a => @lem4082467 A t n s a h1). Qed.
Lemma lem4082470 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082471 {A : Type'} (t : A -> Prop) (a : A) : (term512 A t a) = (@I (A -> Prop) t a).
Proof. exact (@lem4082470 (@I (A -> Prop) t a)). Qed.
Lemma lem4082472 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (EQ_MP (@lem4082471 A t a) (@lem4082468 A t n s a h1)). Qed.
Lemma lem4082478 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4082479 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : (term493 A t s _48008) = (term513 A s t _48008).
Proof. exact (@lem4082478 (@I (A -> Prop) s _48008) (term489 A t _48008)). Qed.
Lemma lem4082485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4082486 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : (term514 A t s _48008) = (term515 A s t _48008).
Proof. exact (MK_COMB (@lem4082485) (@lem4082479 A s t _48008)). Qed.
Lemma lem4082492 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : (term513 A s t _48008) = (term513 A s t _48008).
Proof. exact (eq_refl (term513 A s t _48008)). Qed.
Lemma lem4082493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : ((term493 A t s _48008) = (term513 A s t _48008)) = ((term513 A s t _48008) = (term513 A s t _48008)).
Proof. exact (MK_COMB (@lem4082486 A s t _48008) (@lem4082492 A s t _48008)). Qed.
Lemma lem4082495 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4082496 (x : Prop) : (x = x) = True.
Proof. exact (@lem4082495 Prop x). Qed.
Lemma lem4082497 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : ((term513 A s t _48008) = (term513 A s t _48008)) = True.
Proof. exact (@lem4082496 (term513 A s t _48008)). Qed.
Lemma lem4082498 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : ((term493 A t s _48008) = (term513 A s t _48008)) = True.
Proof. exact (TRANS (@lem4082493 A s t _48008) (@lem4082497 A s t _48008)). Qed.
Lemma lem4082499 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : True = ((term493 A t s _48008) = (term513 A s t _48008)).
Proof. exact (SYM (@lem4082498 A s t _48008)). Qed.
Lemma lem4082500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48008 : A) : (term493 A t s _48008) = (term513 A s t _48008).
Proof. exact (EQ_MP (@lem4082499 A s t _48008) (@lem0)). Qed.
Lemma lem4082501 {A : Type'} (_48008 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term513 A s t _48008.
Proof. exact (EQ_MP (@lem4082500 A s t _48008) (@lem4081861 A _48008 t n s a h1)). Qed.
Lemma lem4082503 (b : Prop) (a : Prop) : (a \/ b) = (term516 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4082504 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48008 : A) : (term513 A s t _48008) = (term517 A t s _48008).
Proof. exact (@lem4082503 (term489 A t _48008) (@I (A -> Prop) s _48008)). Qed.
Lemma lem4082506 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4082507 {A : Type'} (t : A -> Prop) (_48008 : A) : (term518 A t _48008) = (@I (A -> Prop) t _48008).
Proof. exact (@lem4082506 (@I (A -> Prop) t _48008)). Qed.
Lemma lem4082508 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4082509 {A : Type'} (t : A -> Prop) (_48008 : A) : (term519 A t _48008) = (term520 A t _48008).
Proof. exact (MK_COMB (@lem4082508) (@lem4082507 A t _48008)). Qed.
Lemma lem4082510 {A : Type'} (s : A -> Prop) (_48008 : A) : (@I (A -> Prop) s _48008) = (@I (A -> Prop) s _48008).
Proof. exact (eq_refl (@I (A -> Prop) s _48008)). Qed.
Lemma lem4082511 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48008 : A) : (term517 A t s _48008) = (term521 A t s _48008).
Proof. exact (MK_COMB (@lem4082509 A t _48008) (@lem4082510 A s _48008)). Qed.
Lemma lem4082512 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48008 : A) : (term513 A s t _48008) = (term521 A t s _48008).
Proof. exact (TRANS (@lem4082504 A t s _48008) (@lem4082511 A t s _48008)). Qed.
Lemma lem4082515 {A : Type'} (_48008 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48008.
Proof. exact (EQ_MP (@lem4082512 A t s _48008) (@lem4082501 A _48008 t n s a h1)). Qed.
Lemma lem4082516 {A : Type'} (_48008 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48008.
Proof. exact (@lem4082515 A _48008 t n s a h1). Qed.
Lemma lem4082517 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s a.
Proof. exact (@lem4082516 A a t n s a h1). Qed.
Lemma lem4082520 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (@lem4082517 A t n s a h1 (@lem4082472 A t n s a h1)). Qed.
Lemma lem4082521 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A s a.
Proof. exact (fun h0 : term489 A s a => @lem4082520 A t n s a h1). Qed.
Lemma lem4082523 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082524 {A : Type'} (s : A -> Prop) (a : A) : (term512 A s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4082523 (@I (A -> Prop) s a)). Qed.
Lemma lem4082525 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (EQ_MP (@lem4082524 A s a) (@lem4082521 A t n s a h1)). Qed.
Lemma lem4082528 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4082530 {A : Type'} (s : A -> Prop) (a : A) : (term489 A s a) = (term522 A s a).
Proof. exact (@lem4082528 (@I (A -> Prop) s a)). Qed.
Lemma lem4082533 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term522 A s a.
Proof. exact (EQ_MP (@lem4082530 A s a) (@lem4081875 A t n s a h1)). Qed.
Lemma lem4082536 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (@lem4082533 A t n s a h1 (@lem4082525 A t n s a h1)). Qed.
Lemma lem4082537 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term304.
Proof. exact (fun h0 : ~ False => @lem4082536 A t n s a h1). Qed.
Lemma lem4082539 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082540 : term304 = False.
Proof. exact (@lem4082539 False). Qed.
Lemma lem4082638 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (proj1 (@lem4081290 A t n s a h1)). Qed.
Lemma lem4082639 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A t a.
Proof. exact (fun h0 : term489 A t a => @lem4082638 A t n s a h1). Qed.
Lemma lem4082641 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082642 {A : Type'} (t : A -> Prop) (a : A) : (term512 A t a) = (@I (A -> Prop) t a).
Proof. exact (@lem4082641 (@I (A -> Prop) t a)). Qed.
Lemma lem4082643 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (EQ_MP (@lem4082642 A t a) (@lem4082639 A t n s a h1)). Qed.
Lemma lem4082649 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4082650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : (term493 A t s _48009) = (term513 A s t _48009).
Proof. exact (@lem4082649 (@I (A -> Prop) s _48009) (term489 A t _48009)). Qed.
Lemma lem4082656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4082657 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : (term514 A t s _48009) = (term515 A s t _48009).
Proof. exact (MK_COMB (@lem4082656) (@lem4082650 A s t _48009)). Qed.
Lemma lem4082663 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : (term513 A s t _48009) = (term513 A s t _48009).
Proof. exact (eq_refl (term513 A s t _48009)). Qed.
Lemma lem4082664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : ((term493 A t s _48009) = (term513 A s t _48009)) = ((term513 A s t _48009) = (term513 A s t _48009)).
Proof. exact (MK_COMB (@lem4082657 A s t _48009) (@lem4082663 A s t _48009)). Qed.
Lemma lem4082666 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4082667 (x : Prop) : (x = x) = True.
Proof. exact (@lem4082666 Prop x). Qed.
Lemma lem4082668 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : ((term513 A s t _48009) = (term513 A s t _48009)) = True.
Proof. exact (@lem4082667 (term513 A s t _48009)). Qed.
Lemma lem4082669 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : ((term493 A t s _48009) = (term513 A s t _48009)) = True.
Proof. exact (TRANS (@lem4082664 A s t _48009) (@lem4082668 A s t _48009)). Qed.
Lemma lem4082670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : True = ((term493 A t s _48009) = (term513 A s t _48009)).
Proof. exact (SYM (@lem4082669 A s t _48009)). Qed.
Lemma lem4082671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48009 : A) : (term493 A t s _48009) = (term513 A s t _48009).
Proof. exact (EQ_MP (@lem4082670 A s t _48009) (@lem0)). Qed.
Lemma lem4082672 {A : Type'} (_48009 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term513 A s t _48009.
Proof. exact (EQ_MP (@lem4082671 A s t _48009) (@lem4082085 A _48009 t n s a h1)). Qed.
Lemma lem4082674 (b : Prop) (a : Prop) : (a \/ b) = (term516 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4082675 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48009 : A) : (term513 A s t _48009) = (term517 A t s _48009).
Proof. exact (@lem4082674 (term489 A t _48009) (@I (A -> Prop) s _48009)). Qed.
Lemma lem4082677 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4082678 {A : Type'} (t : A -> Prop) (_48009 : A) : (term518 A t _48009) = (@I (A -> Prop) t _48009).
Proof. exact (@lem4082677 (@I (A -> Prop) t _48009)). Qed.
Lemma lem4082679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4082680 {A : Type'} (t : A -> Prop) (_48009 : A) : (term519 A t _48009) = (term520 A t _48009).
Proof. exact (MK_COMB (@lem4082679) (@lem4082678 A t _48009)). Qed.
Lemma lem4082681 {A : Type'} (s : A -> Prop) (_48009 : A) : (@I (A -> Prop) s _48009) = (@I (A -> Prop) s _48009).
Proof. exact (eq_refl (@I (A -> Prop) s _48009)). Qed.
Lemma lem4082682 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48009 : A) : (term517 A t s _48009) = (term521 A t s _48009).
Proof. exact (MK_COMB (@lem4082680 A t _48009) (@lem4082681 A s _48009)). Qed.
Lemma lem4082683 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48009 : A) : (term513 A s t _48009) = (term521 A t s _48009).
Proof. exact (TRANS (@lem4082675 A t s _48009) (@lem4082682 A t s _48009)). Qed.
Lemma lem4082686 {A : Type'} (_48009 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48009.
Proof. exact (EQ_MP (@lem4082683 A t s _48009) (@lem4082672 A _48009 t n s a h1)). Qed.
Lemma lem4082687 {A : Type'} (_48009 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48009.
Proof. exact (@lem4082686 A _48009 t n s a h1). Qed.
Lemma lem4082688 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s a.
Proof. exact (@lem4082687 A a t n s a h1). Qed.
Lemma lem4082691 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (@lem4082688 A t n s a h1 (@lem4082643 A t n s a h1)). Qed.
Lemma lem4082692 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A s a.
Proof. exact (fun h0 : term489 A s a => @lem4082691 A t n s a h1). Qed.
Lemma lem4082694 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082695 {A : Type'} (s : A -> Prop) (a : A) : (term512 A s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4082694 (@I (A -> Prop) s a)). Qed.
Lemma lem4082696 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (EQ_MP (@lem4082695 A s a) (@lem4082692 A t n s a h1)). Qed.
Lemma lem4082699 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4082701 {A : Type'} (s : A -> Prop) (a : A) : (term489 A s a) = (term522 A s a).
Proof. exact (@lem4082699 (@I (A -> Prop) s a)). Qed.
Lemma lem4082704 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term522 A s a.
Proof. exact (EQ_MP (@lem4082701 A s a) (@lem4082099 A t n s a h1)). Qed.
Lemma lem4082707 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (@lem4082704 A t n s a h1 (@lem4082696 A t n s a h1)). Qed.
Lemma lem4082708 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term304.
Proof. exact (fun h0 : ~ False => @lem4082707 A t n s a h1). Qed.
Lemma lem4082710 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082711 : term304 = False.
Proof. exact (@lem4082710 False). Qed.
Lemma lem4082809 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (proj1 (@lem4081290 A t n s a h1)). Qed.
Lemma lem4082810 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A t a.
Proof. exact (fun h0 : term489 A t a => @lem4082809 A t n s a h1). Qed.
Lemma lem4082812 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082813 {A : Type'} (t : A -> Prop) (a : A) : (term512 A t a) = (@I (A -> Prop) t a).
Proof. exact (@lem4082812 (@I (A -> Prop) t a)). Qed.
Lemma lem4082814 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) t a.
Proof. exact (EQ_MP (@lem4082813 A t a) (@lem4082810 A t n s a h1)). Qed.
Lemma lem4082820 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4082821 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : (term493 A t s _48010) = (term513 A s t _48010).
Proof. exact (@lem4082820 (@I (A -> Prop) s _48010) (term489 A t _48010)). Qed.
Lemma lem4082827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4082828 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : (term514 A t s _48010) = (term515 A s t _48010).
Proof. exact (MK_COMB (@lem4082827) (@lem4082821 A s t _48010)). Qed.
Lemma lem4082834 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : (term513 A s t _48010) = (term513 A s t _48010).
Proof. exact (eq_refl (term513 A s t _48010)). Qed.
Lemma lem4082835 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : ((term493 A t s _48010) = (term513 A s t _48010)) = ((term513 A s t _48010) = (term513 A s t _48010)).
Proof. exact (MK_COMB (@lem4082828 A s t _48010) (@lem4082834 A s t _48010)). Qed.
Lemma lem4082837 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4082838 (x : Prop) : (x = x) = True.
Proof. exact (@lem4082837 Prop x). Qed.
Lemma lem4082839 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : ((term513 A s t _48010) = (term513 A s t _48010)) = True.
Proof. exact (@lem4082838 (term513 A s t _48010)). Qed.
Lemma lem4082840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : ((term493 A t s _48010) = (term513 A s t _48010)) = True.
Proof. exact (TRANS (@lem4082835 A s t _48010) (@lem4082839 A s t _48010)). Qed.
Lemma lem4082841 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : True = ((term493 A t s _48010) = (term513 A s t _48010)).
Proof. exact (SYM (@lem4082840 A s t _48010)). Qed.
Lemma lem4082842 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_48010 : A) : (term493 A t s _48010) = (term513 A s t _48010).
Proof. exact (EQ_MP (@lem4082841 A s t _48010) (@lem0)). Qed.
Lemma lem4082843 {A : Type'} (_48010 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term513 A s t _48010.
Proof. exact (EQ_MP (@lem4082842 A s t _48010) (@lem4082182 A _48010 t n s a h1)). Qed.
Lemma lem4082845 (b : Prop) (a : Prop) : (a \/ b) = (term516 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4082846 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48010 : A) : (term513 A s t _48010) = (term517 A t s _48010).
Proof. exact (@lem4082845 (term489 A t _48010) (@I (A -> Prop) s _48010)). Qed.
Lemma lem4082848 (a : Prop) : (term61 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4082849 {A : Type'} (t : A -> Prop) (_48010 : A) : (term518 A t _48010) = (@I (A -> Prop) t _48010).
Proof. exact (@lem4082848 (@I (A -> Prop) t _48010)). Qed.
Lemma lem4082850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4082851 {A : Type'} (t : A -> Prop) (_48010 : A) : (term519 A t _48010) = (term520 A t _48010).
Proof. exact (MK_COMB (@lem4082850) (@lem4082849 A t _48010)). Qed.
Lemma lem4082852 {A : Type'} (s : A -> Prop) (_48010 : A) : (@I (A -> Prop) s _48010) = (@I (A -> Prop) s _48010).
Proof. exact (eq_refl (@I (A -> Prop) s _48010)). Qed.
Lemma lem4082853 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48010 : A) : (term517 A t s _48010) = (term521 A t s _48010).
Proof. exact (MK_COMB (@lem4082851 A t _48010) (@lem4082852 A s _48010)). Qed.
Lemma lem4082854 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_48010 : A) : (term513 A s t _48010) = (term521 A t s _48010).
Proof. exact (TRANS (@lem4082846 A t s _48010) (@lem4082853 A t s _48010)). Qed.
Lemma lem4082857 {A : Type'} (_48010 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48010.
Proof. exact (EQ_MP (@lem4082854 A t s _48010) (@lem4082843 A _48010 t n s a h1)). Qed.
Lemma lem4082858 {A : Type'} (_48010 : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s _48010.
Proof. exact (@lem4082857 A _48010 t n s a h1). Qed.
Lemma lem4082859 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term521 A t s a.
Proof. exact (@lem4082858 A a t n s a h1). Qed.
Lemma lem4082862 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (@lem4082859 A t n s a h1 (@lem4082814 A t n s a h1)). Qed.
Lemma lem4082863 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term512 A s a.
Proof. exact (fun h0 : term489 A s a => @lem4082862 A t n s a h1). Qed.
Lemma lem4082865 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082866 {A : Type'} (s : A -> Prop) (a : A) : (term512 A s a) = (@I (A -> Prop) s a).
Proof. exact (@lem4082865 (@I (A -> Prop) s a)). Qed.
Lemma lem4082867 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : @I (A -> Prop) s a.
Proof. exact (EQ_MP (@lem4082866 A s a) (@lem4082863 A t n s a h1)). Qed.
Lemma lem4082870 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4082872 {A : Type'} (s : A -> Prop) (a : A) : (term489 A s a) = (term522 A s a).
Proof. exact (@lem4082870 (@I (A -> Prop) s a)). Qed.
Lemma lem4082875 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term522 A s a.
Proof. exact (EQ_MP (@lem4082872 A s a) (@lem4082196 A t n s a h1)). Qed.
Lemma lem4082878 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (@lem4082875 A t n s a h1 (@lem4082867 A t n s a h1)). Qed.
Lemma lem4082879 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term304.
Proof. exact (fun h0 : ~ False => @lem4082878 A t n s a h1). Qed.
Lemma lem4082881 (p : Prop) : (term296 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4082882 : term304 = False.
Proof. exact (@lem4082881 False). Qed.
Lemma lem4082884 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (EQ_MP (@lem4082882) (@lem4082879 A t n s a h1)). Qed.
Lemma lem4082886 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (EQ_MP (@lem4082711) (@lem4082708 A t n s a h1)). Qed.
Lemma lem4082887 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (EQ_MP (@lem4082540) (@lem4082537 A t n s a h1)). Qed.
Lemma lem4082889 {A : Type'} (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : False.
Proof. exact (EQ_MP (@lem4082388) (@lem4082385 A t n s a h1)). Qed.
Lemma lem4082890 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : False.
Proof. exact (or_elim (@lem4081307 A a t a' h2) (fun h0 : a' = a => @lem4082886 A t n s a h1) (fun h0 : @I (A -> Prop) t a' => @lem4082884 A t n s a h1)). Qed.
Lemma lem4082891 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : False.
Proof. exact (or_elim (@lem4081307 A a t a' h2) (fun h0 : a' = a => @lem4082889 A t n s a h1) (fun h0 : @I (A -> Prop) t a' => @lem4082887 A t n s a h1)). Qed.
Lemma lem4082892 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : False.
Proof. exact (or_elim (@lem4081331 A t n s a h1) (fun h0 : term305 A s => @lem4082891 A n s a t a' h1 h2) (fun h0 : term396 A n s => @lem4082890 A n s a t a' h1 h2)). Qed.
Lemma lem4082893 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : (term446 A a t a') = False.
Proof. exact (prop_ext (fun h3 : term446 A a t a' => @lem4082892 A n s a t a' h1 h2) (fun h3 : False => @lem4081201 A a t a' h2)). Qed.
Lemma lem4082894 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : False.
Proof. exact (EQ_MP (@lem4082893 A n s a t a' h1 h2) (@lem4081201 A a t a' h2)). Qed.
Lemma lem4082895 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : term720 n.
Proof. exact (fun h0 : term726 n => @lem4082894 A n s a t a' h1 h2). Qed.
Lemma lem4082896 {A : Type'} (n : nat) (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (h1 : term689 A t n s a) (h2 : term446 A a t a') : (term691 n) = n.
Proof. exact (EQ_MP (@lem4081117 n) (@lem4082895 A n s a t a' h1 h2)). Qed.
Lemma lem4082897 {A : Type'} (a' : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (a : A) (h1 : term689 A t n s a) : term692 A a t a' n.
Proof. exact (fun h0 : term446 A a t a' => @lem4082896 A n s a t a' h1 h0). Qed.
Lemma lem4082898 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term693 A s a t a' n.
Proof. exact (fun h0 : term689 A t n s a => @lem4082897 A a' t n s a h0). Qed.
Lemma lem4082903 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : term703 A a t a' n.
Proof. exact (fun s : A -> Prop => @lem4082898 A s a t a' n). Qed.
Lemma lem4082908 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : term707 A t a' n.
Proof. exact (fun a : A => @lem4082903 A a t a' n). Qed.
Lemma lem4082913 {A : Type'} (a' : A) (n : nat) : term711 A a' n.
Proof. exact (fun t : A -> Prop => @lem4082908 A t a' n). Qed.
Lemma lem4082918 {A : Type'} (n : nat) : term715 A n.
Proof. exact (fun a' : A => @lem4082913 A a' n). Qed.
Lemma lem4082923 {A : Type'} : term719 A.
Proof. exact (fun n : nat => @lem4082918 A n). Qed.
Lemma lem4082924 {A : Type'} : term718 A.
Proof. exact (EQ_MP (@lem4081111 A) (@lem4082923 A)). Qed.
Lemma lem4082925 {A : Type'} (n : nat) : term727 A n.
Proof. exact (@lem4082924 A n). Qed.
Lemma lem4082926 {A : Type'} (n : nat) : (term727 A n) = (term714 A n).
Proof. exact (eq_refl (term727 A n)). Qed.
Lemma lem4082927 {A : Type'} (n : nat) : term714 A n.
Proof. exact (EQ_MP (@lem4082926 A n) (@lem4082925 A n)). Qed.
Lemma lem4082928 {A : Type'} (n : nat) (a' : A) : term728 A n a'.
Proof. exact (@lem4082927 A n a'). Qed.
Lemma lem4082929 {A : Type'} (a' : A) (n : nat) : (term728 A n a') = (term710 A a' n).
Proof. exact (eq_refl (term728 A n a')). Qed.
Lemma lem4082930 {A : Type'} (a' : A) (n : nat) : term710 A a' n.
Proof. exact (EQ_MP (@lem4082929 A a' n) (@lem4082928 A n a')). Qed.
Lemma lem4082931 {A : Type'} (a' : A) (n : nat) (t : A -> Prop) : term729 A a' n t.
Proof. exact (@lem4082930 A a' n t). Qed.
Lemma lem4082932 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : (term729 A a' n t) = (term706 A t a' n).
Proof. exact (eq_refl (term729 A a' n t)). Qed.
Lemma lem4082933 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) : term706 A t a' n.
Proof. exact (EQ_MP (@lem4082932 A t a' n) (@lem4082931 A a' n t)). Qed.
Lemma lem4082934 {A : Type'} (t : A -> Prop) (a' : A) (n : nat) (a : A) : term730 A t a' n a.
Proof. exact (@lem4082933 A t a' n a). Qed.
Lemma lem4082935 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term730 A t a' n a) = (term702 A a t a' n).
Proof. exact (eq_refl (term730 A t a' n a)). Qed.
Lemma lem4082936 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) : term702 A a t a' n.
Proof. exact (EQ_MP (@lem4082935 A a t a' n) (@lem4082934 A t a' n a)). Qed.
Lemma lem4082937 {A : Type'} (a : A) (t : A -> Prop) (a' : A) (n : nat) (s : A -> Prop) : term731 A a t a' n s.
Proof. exact (@lem4082936 A a t a' n s). Qed.
Lemma lem4082938 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : (term731 A a t a' n s) = (term694 A s a t a' n).
Proof. exact (eq_refl (term731 A a t a' n s)). Qed.
Lemma lem4082939 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term694 A s a t a' n.
Proof. exact (EQ_MP (@lem4082938 A s a t a' n) (@lem4082937 A a t a' n s)). Qed.
Lemma lem4082941 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term694 A s a t a' n.
Proof. exact (@lem4080900 A s a t a' n (@lem4082939 A s a t a' n)). Qed.
Lemma lem4082942 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term695 A s a t a' n) : False.
Proof. exact (@lem4082941 A s a t a' n (@lem4080884 A s a t a' n h1)). Qed.
Lemma lem4082943 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term695 A s a t a' n) : (term695 A s a t a' n) = False.
Proof. exact (prop_ext (fun h2 : term695 A s a t a' n => @lem4082942 A s a t a' n h1) (fun h2 : False => @lem4080884 A s a t a' n h1)). Qed.
Lemma lem4082944 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) (h1 : term695 A s a t a' n) : False.
Proof. exact (EQ_MP (@lem4082943 A s a t a' n h1) (@lem4080884 A s a t a' n h1)). Qed.
Lemma lem4082945 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term694 A s a t a' n.
Proof. exact (fun h0 : term695 A s a t a' n => @lem4082944 A s a t a' n h0). Qed.
Lemma lem4082946 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) (a' : A) (n : nat) : term693 A s a t a' n.
Proof. exact (EQ_MP (@lem4080883 A s a t a' n) (@lem4082945 A s a t a' n)). Qed.
Lemma lem4082947 {A : Type'} (s : A -> Prop) (a' : A) (a : A) (t : A -> Prop) (n : nat) : term686 A s a' a t n.
Proof. exact (EQ_MP (@lem4080879 A s a' a t n) (@lem4082946 A s a t a' n)). Qed.
Lemma lem4082948 {A : Type'} (s : A -> Prop) (a' : A) (a : A) (t : A -> Prop) (n : nat) : term685 A s a' a t n.
Proof. exact (EQ_MP (@lem4080776 A s a' a t n) (@lem4082947 A s a' a t n)). Qed.
Lemma lem4082951 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : term663 A a' a t n.
Proof. exact (EQ_MP (@lem4080706 A a' a t n) (@lem0)). Qed.
Lemma lem4082952 {A : Type'} (a' : A) (a : A) (t : A -> Prop) (n : nat) : term665 A a' a t n.
Proof. exact (fun h0 : term339 A a t => @lem4082951 A a' a t n). Qed.
Lemma lem4082953 {A : Type'} (a' : A) (n : nat) (a : A) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @IN A a t) (h5 : @SUBSET A t s) : term667 A a' a t n.
Proof. exact (@lem4082948 A s a' a t n (@lem4080721 A n a t s h1 h2 h3 h4 h5)). Qed.
Lemma lem4082954 {A : Type'} (a' : A) (n : nat) (a : A) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @IN A a t) (h5 : @SUBSET A t s) : (@IN A a t) = (term667 A a' a t n).
Proof. exact (prop_ext (fun h6 : @IN A a t => @lem4082953 A a' n a t s h1 h2 h3 h4 h5) (fun h6 : term667 A a' a t n => @lem4080645 A a t h4)). Qed.
Lemma lem4082955 {A : Type'} (a' : A) (n : nat) (a : A) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @IN A a t) (h5 : @SUBSET A t s) : term667 A a' a t n.
Proof. exact (EQ_MP (@lem4082954 A a' n a t s h1 h2 h3 h4 h5) (@lem4080645 A a t h4)). Qed.
Lemma lem4082956 {A : Type'} (a' : A) (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term669 A a' a t n.
Proof. exact (fun h0 : @IN A a t => @lem4082955 A a' n a t s h1 h2 h3 h0 h4). Qed.
Lemma lem4082957 {A : Type'} (a' : A) (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term672 A a' a t n.
Proof. exact (conj (@lem4082956 A a' a n t s h1 h2 h3 h4) (@lem4082952 A a' a t n)). Qed.
Lemma lem4082958 {A : Type'} (a' : A) (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term650 A a' a t n.
Proof. exact (EQ_MP (@lem4080644 A a' a t n) (@lem4082957 A a' a n t s h1 h2 h3 h4)). Qed.
Lemma lem4082963 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term654 A a t n.
Proof. exact (fun a' : A => @lem4082958 A a' a n t s h1 h2 h3 h4). Qed.
Lemma lem4082964 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term653 A a t n.
Proof. exact (EQ_MP (@lem4080626 A a t n h3) (@lem4082963 A a n t s h1 h2 h3 h4)). Qed.
Lemma lem4082965 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : (@SUBSET A t s) = (term653 A a t n).
Proof. exact (prop_ext (fun h5 : @SUBSET A t s => @lem4082964 A a n t s h1 h2 h3 h4) (fun h5 : term653 A a t n => @lem4079856 A t s h4)). Qed.
Lemma lem4082966 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term653 A a t n.
Proof. exact (EQ_MP (@lem4082965 A a n t s h1 h2 h3 h4) (@lem4079856 A t s h4)). Qed.
Lemma lem4082967 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : (term399 A n s) = (term653 A a t n).
Proof. exact (prop_ext (fun h5 : term399 A n s => @lem4082966 A a n t s h1 h2 h3 h4) (fun h5 : term653 A a t n => @lem4079854 A n s h2)). Qed.
Lemma lem4082968 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term653 A a t n.
Proof. exact (EQ_MP (@lem4082967 A a n t s h1 h2 h3 h4) (@lem4079854 A n s h2)). Qed.
Lemma lem4082969 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : (term339 A a s) = (term653 A a t n).
Proof. exact (prop_ext (fun h5 : term339 A a s => @lem4082968 A a n t s h1 h2 h3 h4) (fun h5 : term653 A a t n => @lem4079850 A a s h1)). Qed.
Lemma lem4082970 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term653 A a t n.
Proof. exact (EQ_MP (@lem4082969 A a n t s h1 h2 h3 h4) (@lem4079850 A a s h1)). Qed.
Lemma lem4082971 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term732 A a t n.
Proof. exact (conj (@lem4079848 A a n t s h1 h2 h3 h4) (@lem4082970 A a n t s h1 h2 h3 h4)). Qed.
Lemma lem4082972 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term733 A s a t n.
Proof. exact (conj (@lem4078897 A a n t s h1 h2 h3 h4) (@lem4082971 A a n t s h1 h2 h3 h4)). Qed.
Lemma lem4082973 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term361 A a s n.
Proof. exact (ex_intro (term734 A a s n) (@INSERT A a t) (@lem4082972 A a n t s h1 h2 h3 h4)). Qed.
Lemma lem4082974 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term414 A s t n) : @HAS_SIZE A t n.
Proof. exact (proj2 (@lem4077331 A s t n h1)). Qed.
Lemma lem4082975 {A : Type'} (s : A -> Prop) (t : A -> Prop) (n : nat) (h1 : term414 A s t n) : @SUBSET A t s.
Proof. exact (proj1 (@lem4077331 A s t n h1)). Qed.
Lemma lem4082976 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : (@HAS_SIZE A t n) = (term361 A a s n).
Proof. exact (prop_ext (fun h5 : @HAS_SIZE A t n => @lem4082973 A a n t s h1 h2 h3 h4) (fun h5 : term361 A a s n => @lem4077332 A t n h3)). Qed.
Lemma lem4082977 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term361 A a s n.
Proof. exact (EQ_MP (@lem4082976 A a n t s h1 h2 h3 h4) (@lem4077332 A t n h3)). Qed.
Lemma lem4082978 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : (@SUBSET A t s) = (term361 A a s n).
Proof. exact (prop_ext (fun h5 : @SUBSET A t s => @lem4082977 A a n t s h1 h2 h3 h4) (fun h5 : term361 A a s n => @lem4077333 A t s h4)). Qed.
Lemma lem4082979 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) (h3 : @HAS_SIZE A t n) (h4 : @SUBSET A t s) : term361 A a s n.
Proof. exact (EQ_MP (@lem4082978 A a n t s h1 h2 h3 h4) (@lem4077333 A t s h4)). Qed.
Lemma lem4082980 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term414 A s t n) (h3 : term399 A n s) (h4 : @SUBSET A t s) : (@HAS_SIZE A t n) = (term361 A a s n).
Proof. exact (prop_ext (fun h5 : @HAS_SIZE A t n => @lem4082979 A a n t s h1 h3 h5 h4) (fun h5 : term361 A a s n => @lem4082974 A s t n h2)). Qed.
Lemma lem4082981 {A : Type'} (a : A) (n : nat) (t : A -> Prop) (s : A -> Prop) (h1 : term339 A a s) (h2 : term414 A s t n) (h3 : term399 A n s) (h4 : @SUBSET A t s) : term361 A a s n.
Proof. exact (EQ_MP (@lem4082980 A a n t s h1 h2 h3 h4) (@lem4082974 A s t n h2)). Qed.
Lemma lem4082982 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term414 A s t n) (h3 : term399 A n s) : (@SUBSET A t s) = (term361 A a s n).
Proof. exact (prop_ext (fun h4 : @SUBSET A t s => @lem4082981 A a n t s h1 h2 h3 h4) (fun h4 : term361 A a s n => @lem4082975 A s t n h2)). Qed.
Lemma lem4082983 {A : Type'} (a : A) (t : A -> Prop) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term414 A s t n) (h3 : term399 A n s) : term361 A a s n.
Proof. exact (EQ_MP (@lem4082982 A a t n s h1 h2 h3) (@lem4082975 A s t n h2)). Qed.
Lemma lem4082984 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term408 A s n) (h2 : term339 A a s) (h3 : term399 A n s) : term361 A a s n.
Proof. exact (ex_elim (@lem4077330 A s n h1) (fun t : A -> Prop => fun h0 : term735 A s n t => @lem4082983 A a t n s h2 h0 h3)). Qed.
Lemma lem4082985 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) : term413 A a s n.
Proof. exact (fun h0 : term408 A s n => @lem4082984 A a n s h0 h1 h2). Qed.
Lemma lem4082986 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term339 A a s) (h2 : term399 A n s) : term412 A a s n.
Proof. exact (EQ_MP (@lem4077329 A a n s h2) (@lem4082985 A a n s h1 h2)). Qed.
Lemma lem4082987 {A : Type'} (a : A) (n : nat) (s : A -> Prop) (h1 : term208 A n) (h2 : term339 A a s) (h3 : term399 A n s) : term361 A a s n.
Proof. exact (@lem4082986 A a n s h2 h3 (@lem4077276 A s n h1)). Qed.
Lemma lem4082988 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term208 A n) (h2 : term339 A a s) : term404 A a s n.
Proof. exact (fun h0 : term399 A n s => @lem4082987 A a n s h1 h2 h0). Qed.
Lemma lem4082989 {A : Type'} (n : nat) (a : A) (s : A -> Prop) (h1 : term208 A n) (h2 : term339 A a s) : term312 A a s n.
Proof. exact (EQ_MP (@lem4077272 A n a s h2) (@lem4082988 A n a s h1 h2)). Qed.
Lemma lem4082990 {A : Type'} (a : A) (s : A -> Prop) (n : nat) (h1 : term208 A n) : term315 A a s n.
Proof. exact (fun h0 : term339 A a s => @lem4082989 A n a s h1 h0). Qed.
Lemma lem4082995 {A : Type'} (a : A) (n : nat) (h1 : term208 A n) : term319 A a n.
Proof. exact (fun s : A -> Prop => @lem4082990 A a s n h1). Qed.
Lemma lem4083000 {A : Type'} (n : nat) (h1 : term208 A n) : term323 A n.
Proof. exact (fun a : A => @lem4082995 A a n h1). Qed.
Lemma lem4083001 {A : Type'} (n : nat) (h1 : term208 A n) : term325 A n.
Proof. exact (EQ_MP (@lem4076908 A n) (@lem4083000 A n h1)). Qed.
Lemma lem4083002 {A : Type'} (n : nat) (h1 : term208 A n) : term251 A n.
Proof. exact (@lem4076792 A n (@lem4083001 A n h1)). Qed.
Lemma lem4083003 {A : Type'} (n : nat) (h1 : term208 A n) : term212 A n.
Proof. exact (EQ_MP (@lem4076125 A n) (@lem4083002 A n h1)). Qed.
Lemma lem4083004 {A : Type'} : term204 A.
Proof. exact (EQ_MP (@lem4076074 A) (@lem4076767 A)). Qed.
Lemma lem4083005 {A : Type'} (n : nat) : term214 A n.
Proof. exact (fun h0 : term208 A n => @lem4083003 A n h0). Qed.
Lemma lem4083010 {A : Type'} : term218 A.
Proof. exact (fun n : nat => @lem4083005 A n). Qed.
Lemma lem4083011 {A : Type'} : term220 A.
Proof. exact (conj (@lem4083004 A) (@lem4083010 A)). Qed.
Lemma lem4083012 {A : Type'} : term225 A.
Proof. exact (@lem4076030 A (@lem4083011 A)). Qed.
